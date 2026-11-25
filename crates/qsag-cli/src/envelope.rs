//! Versioned passphrase sealing with a 32 MiB data-independent Balloon KDF.

use crate::cli::{Args, CliError, Secret32, ZeroizingBuf, read_bounded_file};
use crate::codec::Json;
use crate::vault::set;
use qsag_accel::keccak::cshake256_framed_xof;

const FORMAT: &str = "cshake256-balloon-v2";
const LEGACY_FORMAT: &str = "cshake256-iterated-v1";
pub const KDF_ROUNDS: u32 = 100_000;

pub fn passphrase(args: &Args) -> Result<Option<ZeroizingBuf>, CliError> {
    passphrase_named(args, "passphrase-env", "passphrase-file")
}

/// A passphrase taken from the named environment-variable or file option.
pub fn passphrase_named(
    args: &Args,
    env_option: &str,
    file_option: &str,
) -> Result<Option<ZeroizingBuf>, CliError> {
    let pass = match (args.get(env_option), args.get(file_option)) {
        (Some(_), Some(_)) => return Err(CliError::usage("choose one passphrase source")),
        (Some(name), None) => Some(ZeroizingBuf::new(
            std::env::var_os(name)
                .ok_or_else(|| CliError::input("passphrase environment variable unavailable"))?
                .into_encoded_bytes(),
        )),
        (None, Some(path)) => Some(read_bounded_file(path, 4096)?),
        (None, None) => None,
    };
    if pass.as_ref().is_some_and(|p| p.is_empty()) {
        return Err(CliError::input("empty passphrase"));
    }
    Ok(pass)
}

fn secret_field_name(json: &Json) -> Result<&'static str, CliError> {
    match (json.get("secret_key").is_some(), json.get("seed").is_some()) {
        (true, false) => Ok("secret_key"),
        (false, true) => Ok("seed"),
        (true, true) => Err(CliError::input(
            "key file cannot contain both secret_key and seed",
        )),
        (false, false) => Err(CliError::input("key file is missing secret material")),
    }
}

/// Everything the envelope tag does not cover: the envelope's own fields, the secret
/// itself (covered as ciphertext), and the vault state that moves with every use.
const MUTABLE_FIELDS: &[&str] = &[
    "envelope",
    "salt",
    "envelope_tag",
    "vault_device",
    "vault_inode",
    "uses_completed",
    "ledger_checkpoint_gen",
    "ledger_checkpoint_tag",
    "ceremony_checkpoint_gen",
    "ceremony_checkpoint_tag",
    "belt_checkpoint_gen",
    "belt_checkpoint_tag",
    "reservoir_generation",
    "reservoir_commit",
    "state_mac",
];

fn immutable_header_bytes(json: &Json, secret_field: &str) -> ZeroizingBuf {
    let mut excluded = MUTABLE_FIELDS.to_vec();
    excluded.push(secret_field);
    crate::persist::authenticated_bytes(json, &excluded)
}

pub(crate) fn derive_v1(pass: &[u8], salt: &[u8; 32], scheme: &str) -> (Secret32, Secret32) {
    let mut state = Secret32::new([0u8; 32]);
    cshake256_framed_xof(
        b"QSAG.ENVELOPE.KDF.V1",
        &[pass, salt, scheme.as_bytes()],
        &mut state.0,
    );
    for i in 0..KDF_ROUNDS {
        let mut next = Secret32::new([0u8; 32]);
        cshake256_framed_xof(
            b"QSAG.ENVELOPE.ITER.V1",
            &[&state.0, salt, &i.to_le_bytes()],
            &mut next.0,
        );
        state = next;
    }
    let mut enc = Secret32::new([0u8; 32]);
    cshake256_framed_xof(
        b"QSAG.ENVELOPE.ENC.V1",
        &[&state.0, salt, scheme.as_bytes()],
        &mut enc.0,
    );
    let mut mac = Secret32::new([0u8; 32]);
    cshake256_framed_xof(
        b"QSAG.ENVELOPE.MAC.V1",
        &[&state.0, salt, scheme.as_bytes()],
        &mut mac.0,
    );
    (enc, mac)
}

// Balloon's expand/mix/extract graph, using 64-byte cSHAKE256 digests.
// The public salt selects three independent dependencies for every block in
// each of three passes. The operation counter distinguishes every node.
// The format identifier fixes all parameters and the little-endian encoding.
pub(crate) fn derive_v2(pass: &[u8], salt: &[u8; 32], scheme: &str) -> (Secret32, Secret32) {
    use qsag_core::sponge::keccak::Cshake256Xof;
    use qsag_core::wipe::{SecretBytes, SecretVec};

    const BLOCKS: usize = 1 << 19;
    const PASSES: usize = 3;
    let mut memory = SecretVec::new(vec![[0u8; 64]; BLOCKS]);
    cshake256_framed_xof(
        b"QSAG.ENVELOPE.BALLOON.INIT.V2",
        &[pass, salt, scheme.as_bytes()],
        &mut memory[0],
    );
    let domain = Cshake256Xof::new(b"QSAG.ENVELOPE.BALLOON.BLOCK.V2");
    let mut counter = 0u32;
    let mut scratch = SecretBytes::<64>::zeroed();
    let mut compress = |a: &[u8; 64], b: &[u8]| {
        let mut h = domain.clone();
        h.absorb(&counter.to_le_bytes());
        h.absorb(a);
        h.absorb(b);
        h.squeeze(&mut scratch.0);
        counter += 1;
        // Install the digest via the caller, including when inputs alias a destination.
        scratch.0
    };
    for i in 1..BLOCKS {
        memory[i] = compress(&memory[i - 1], &[]);
    }

    let mut schedule = Cshake256Xof::new(b"QSAG.ENVELOPE.BALLOON.INDICES.V2");
    schedule.absorb(salt);
    for _ in 0..PASSES {
        for i in 0..BLOCKS {
            let previous = i.wrapping_sub(1) & (BLOCKS - 1);
            memory[i] = compress(&memory[previous], &memory[i]);
            let mut indices = [0u8; 12];
            schedule.squeeze(&mut indices);
            for &word in indices.as_chunks::<4>().0 {
                let j = u32::from_le_bytes(word) as usize & (BLOCKS - 1);
                memory[i] = compress(&memory[i], &memory[j]);
            }
        }
    }

    let root = &memory[BLOCKS - 1];
    let mut enc = Secret32::zeroed();
    let mut mac = Secret32::zeroed();
    cshake256_framed_xof(
        b"QSAG.ENVELOPE.ENC.V2",
        &[root, salt, scheme.as_bytes()],
        &mut enc.0,
    );
    cshake256_framed_xof(
        b"QSAG.ENVELOPE.MAC.V2",
        &[root, salt, scheme.as_bytes()],
        &mut mac.0,
    );
    (enc, mac)
}

fn crypt(bytes: &mut [u8], enc_key: &Secret32, salt: &[u8; 32], scheme: &str, field: &str) {
    for (i, block) in bytes.chunks_mut(32).enumerate() {
        let mut stream = Secret32::new([0u8; 32]);
        cshake256_framed_xof(
            b"QSAG.ENVELOPE.STREAM.V1",
            &[
                &enc_key.0,
                salt,
                scheme.as_bytes(),
                field.as_bytes(),
                &(i as u64).to_le_bytes(),
            ],
            &mut stream.0,
        );
        for (a, b) in block.iter_mut().zip(stream.iter()) {
            *a ^= b;
        }
    }
}

fn tag(
    format: &str,
    json: &Json,
    scheme: &str,
    field: &str,
    salt: &[u8; 32],
    ciphertext: &[u8],
    mac_key: &Secret32,
) -> Secret32 {
    let header = immutable_header_bytes(json, field);
    let mut out = Secret32::new([0u8; 32]);
    cshake256_framed_xof(
        b"QSAG.ENVELOPE.TAG.V1",
        &[
            &mac_key.0,
            format.as_bytes(),
            scheme.as_bytes(),
            field.as_bytes(),
            salt,
            &header,
            ciphertext,
        ],
        &mut out.0,
    );
    out
}

/// Lowercase hex of secret bytes, as ASCII in a wiping buffer allocated once at its final size.
fn encode_hex(bytes: &[u8]) -> ZeroizingBuf {
    fn digit(n: u8) -> u8 {
        b'0' + n + (39 & core::hint::black_box(u8::from(n > 9).wrapping_neg()))
    }
    let mut out = ZeroizingBuf::new(vec![0; bytes.len() * 2]);
    for (pair, &b) in out.0.as_chunks_mut::<2>().0.iter_mut().zip(bytes) {
        *pair = [digit(b >> 4), digit(b & 15)];
    }
    out
}

/// Strict hex: even length, `[0-9a-fA-F]` only. Surrounding whitespace is ignored.
fn decode_hex(text: &str) -> Result<ZeroizingBuf, CliError> {
    let text = text.trim();
    if !text.len().is_multiple_of(2) {
        return Err(CliError::input("hex string has odd length"));
    }
    // Invalid bytes set bit 7. Fold that bit over the entire input before
    // reporting failure, so the error position cannot short-circuit decoding.
    fn nibble(c: u8) -> u8 {
        let d = c.wrapping_sub(b'0');
        let a = (c | 0x20).wrapping_sub(b'a');
        let decimal = core::hint::black_box(u8::from(d < 10).wrapping_neg());
        let alpha = core::hint::black_box(u8::from(a < 6).wrapping_neg());
        (d & decimal) | (a.wrapping_add(10) & alpha) | (0x80 & !(decimal | alpha))
    }
    let mut decoded = ZeroizingBuf::new(vec![0; text.len() / 2]);
    let mut invalid = 0;
    for (out, &[hi, lo]) in decoded.0.iter_mut().zip(text.as_bytes().as_chunks::<2>().0) {
        let (hi, lo) = (nibble(hi), nibble(lo));
        invalid |= hi | lo;
        *out = hi << 4 | lo;
    }
    if invalid & 0x80 != 0 {
        return Err(CliError::input("hex string contains a non-hex character"));
    }
    Ok(decoded)
}

fn hex_field(json: &Json, field: &str) -> Result<ZeroizingBuf, CliError> {
    decode_hex(json.field_str(field)?)
}

fn hex_field32(json: &Json, field: &str) -> Result<[u8; 32], CliError> {
    hex_field(json, field)?
        .as_slice()
        .try_into()
        .map_err(|_| CliError::input(format!("{field} must be exactly 32 bytes of hex")))
}

fn hex_json(bytes: &[u8]) -> Json {
    let mut text = encode_hex(bytes);
    Json::Str(String::from_utf8(core::mem::take(&mut text.0)).expect("hex digits are ASCII"))
}

pub fn seal(json: &mut Json, pass: &[u8]) -> Result<(), CliError> {
    if pass.is_empty() {
        return Err(CliError::input("empty passphrase"));
    }
    if json.get("envelope").is_some()
        || json.get("salt").is_some()
        || json.get("envelope_tag").is_some()
    {
        return Err(CliError::input("key file is already sealed"));
    }
    let scheme = json.field_str("scheme")?.to_owned();
    let field = secret_field_name(json)?;
    let mut bytes = hex_field(json, field)?;
    let mut salt = [0; 32];
    qsag_accel::fill_os_random(&mut salt).map_err(|e| CliError::io("drawing envelope salt", e))?;
    let (enc, mac) = derive_v2(pass, &salt, &scheme);
    crypt(&mut bytes.0, &enc, &salt, &scheme, field);
    let auth = tag(FORMAT, json, &scheme, field, &salt, &bytes, &mac);
    set(json, field, hex_json(&bytes));
    set(json, "envelope", Json::str(FORMAT));
    set(json, "salt", hex_json(&salt));
    set(json, "envelope_tag", hex_json(&auth.0));
    Ok(())
}

/// The secret material of a key file, decrypted or, for an unsealed file, decoded. The bytes
/// live only in wiping buffers: they are never written back into a JSON tree as hex text,
/// and the type is neither `Clone` nor `Debug`.
pub struct OpenedSecret {
    field: &'static str,
    bytes: ZeroizingBuf,
}

impl OpenedSecret {
    fn of(&self, field: &str) -> Result<&[u8], CliError> {
        if self.field == field {
            Ok(&self.bytes)
        } else {
            Err(CliError::input(format!(
                "missing or non-string field \"{field}\""
            )))
        }
    }

    /// The raw secret key of a scheme whose key file stores one.
    pub fn secret_key(&self) -> Result<&[u8], CliError> {
        self.of("secret_key")
    }

    /// The 32-byte master seed of a scheme whose key file stores one.
    pub fn seed(&self) -> Result<Secret32, CliError> {
        let bytes = self.of("seed")?;
        let mut seed = Secret32::new([0u8; 32]);
        if bytes.len() != seed.0.len() {
            return Err(CliError::input("seed must be exactly 32 bytes of hex"));
        }
        seed.0.copy_from_slice(bytes);
        Ok(seed)
    }

    /// The vault MAC key material: the canonical lowercase hex of the secret, as bytes.
    pub fn vault_key_material(&self) -> ZeroizingBuf {
        encode_hex(&self.bytes)
    }
}

pub fn open(json: &Json, pass: Option<&[u8]>) -> Result<OpenedSecret, CliError> {
    if json.get("envelope").is_none() {
        if json.get("salt").is_some() || json.get("envelope_tag").is_some() {
            return Err(CliError::input("damaged sealed envelope header"));
        }
        if pass.is_some() {
            return Err(CliError::input(
                "passphrase supplied for unencrypted key file",
            ));
        }
        let field = secret_field_name(json)?;
        return Ok(OpenedSecret {
            field,
            bytes: hex_field(json, field)?,
        });
    }
    let format = json.field_str("envelope")?;
    if !matches!(format, FORMAT | LEGACY_FORMAT) {
        return Err(CliError::input("unsupported sealed envelope"));
    }
    let pass = pass.ok_or_else(|| {
        CliError::usage("sealed key requires --passphrase-env or --passphrase-file")
    })?;
    if pass.is_empty() {
        return Err(CliError::input("empty passphrase"));
    }
    let scheme = json.field_str("scheme")?;
    let field = secret_field_name(json)?;
    let salt = hex_field32(json, "salt")?;
    let actual = crate::codec::from_hex_secret32(json.field_str("envelope_tag")?, "envelope_tag")?;
    let mut bytes = hex_field(json, field)?;
    let (enc, mac) = if format == LEGACY_FORMAT {
        derive_v1(pass, &salt, scheme)
    } else {
        derive_v2(pass, &salt, scheme)
    };
    let expected = tag(format, json, scheme, field, &salt, &bytes, &mac);
    if !qsag_accel::ct::ct_eq_bytes(&expected.0, &actual.0) {
        return Err(CliError::input("wrong passphrase or damaged sealed key"));
    }
    crypt(&mut bytes.0, &enc, &salt, scheme, field);
    Ok(OpenedSecret { field, bytes })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn envelope_hex_handles_all_octets_and_checks_every_position() {
        let bytes: Vec<_> = (0..=255).collect();
        let encoded = hex_json(&bytes);
        let text = encoded.as_str().unwrap();
        assert_eq!(decode_hex(text).unwrap().0, bytes);
        assert_eq!(decode_hex(&text.to_ascii_uppercase()).unwrap().0, bytes);
        for c in 0..=127u8 {
            assert_eq!(
                decode_hex(&format!("0{}00", char::from(c))).is_ok(),
                c.is_ascii_hexdigit()
            );
        }
    }

    #[test]
    fn opens_pinned_v1_vault() {
        let vault = Json::object(vec![
            ("scheme", Json::str("test")),
            ("envelope", Json::str(LEGACY_FORMAT)),
            ("salt", Json::hex(&[7; 32])),
            (
                "seed",
                Json::str("2e6800d77fbe37c675bc251b4696f26e243e02d8437bc026501ddef5b3d0d794"),
            ),
            (
                "envelope_tag",
                Json::str("ca8178f0231be58ef0a5817580c9ec088c2225d05decf94fb050d250d850a1f0"),
            ),
        ]);
        assert_eq!(
            open(&vault, Some(b"correct horse"))
                .unwrap()
                .seed()
                .unwrap()
                .0,
            [42; 32]
        );
    }

    #[test]
    fn roundtrip_wrong_passphrase_and_tampering() {
        const { assert!(KDF_ROUNDS >= 100_000) };
        let (enc_a, mac_a) = derive_v2(b"correct horse", &[7u8; 32], "test-a");
        // Full-cost vectors from an independent OpenSSL cSHAKE256 implementation.
        assert_eq!(
            crate::codec::to_hex(&enc_a.0),
            "70ae1680cf3d6cd58aec3341d8a96a27b2cf58ad2058d1d9c393fc21988ed19b"
        );
        assert_eq!(
            crate::codec::to_hex(&mac_a.0),
            "cceba68c2ff342b5c5efdf62f6085d141cb801c54e48f926c18568c0df80472e"
        );
        assert_ne!(
            enc_a.0, mac_a.0,
            "encryption and MAC subkeys must be separated"
        );
        let (enc_b, mac_b) = derive_v2(b"correct horse", &[7u8; 32], "test-b");
        assert_ne!(enc_a.0, enc_b.0);
        assert_ne!(mac_a.0, mac_b.0);

        for field in ["seed", "secret_key"] {
            let mut key = Json::object(vec![
                ("scheme", Json::str("test")),
                ("enrollment_nonce", Json::hex(&[9u8; 16])),
                (field, Json::hex(&[42; 32])),
            ]);
            seal(&mut key, b"correct horse").unwrap();
            assert_eq!(key.field_str("envelope").unwrap(), FORMAT);
            assert_ne!(key.field_hex(field).unwrap().0, vec![42; 32]);
            let other = if field == "seed" {
                "secret_key"
            } else {
                "seed"
            };
            let opened = open(&key, Some(b"correct horse")).unwrap();
            assert_eq!(opened.of(field).unwrap(), &[42u8; 32][..]);
            assert!(opened.of(other).is_err());
            assert_eq!(opened.seed().is_ok(), field == "seed");
            assert_eq!(opened.secret_key().is_ok(), field == "secret_key");
            // The vault key material is the hex text an unsealed file would have carried.
            assert_eq!(opened.vault_key_material().0, "2a".repeat(32).into_bytes());
            drop(opened);
            assert!(open(&key, Some(b"wrong")).is_err());
            assert!(open(&key, Some(b"")).is_err());
            assert!(open(&key, None).is_err());

            // Mutable vault state updates remain compatible without re-sealing.
            let mut progressed = key.clone();
            set(&mut progressed, "uses_completed", Json::num(3));
            set(&mut progressed, "state_mac", Json::hex(&[0xAB; 32]));
            assert_eq!(
                open(&progressed, Some(b"correct horse"))
                    .unwrap()
                    .of(field)
                    .unwrap(),
                &[42u8; 32][..]
            );

            // Tampering immutable header metadata fails MAC before decryption.
            let mut bad_nonce = key.clone();
            set(&mut bad_nonce, "enrollment_nonce", Json::hex(&[10u8; 16]));
            assert!(open(&bad_nonce, Some(b"correct horse")).is_err());

            let mut bad_scheme = key.clone();
            set(&mut bad_scheme, "scheme", Json::str("other"));
            assert!(open(&bad_scheme, Some(b"correct horse")).is_err());

            // Stripping `"envelope"` while leaving `"salt"` or `"envelope_tag"` fails closed.
            let mut stripped = key.clone();
            if let Json::Object(fields) = &mut stripped {
                fields.retain(|(name, _)| name != "envelope");
            }
            assert!(open(&stripped, None).is_err());
            assert!(open(&stripped, Some(b"correct horse")).is_err());

            // Tampering ciphertext fails MAC before decryption.
            set(&mut key, field, Json::hex(&[0; 32]));
            assert!(open(&key, Some(b"correct horse")).is_err());
        }
    }

    #[test]
    fn rejects_dual_secret_fields_and_unsolicited_passphrase() {
        let mut ambiguous = Json::object(vec![
            ("scheme", Json::str("test")),
            ("seed", Json::hex(&[1u8; 32])),
            ("secret_key", Json::hex(&[2u8; 64])),
        ]);
        assert!(seal(&mut ambiguous, b"correct horse").is_err());
        assert!(open(&ambiguous, None).is_err());

        let unsealed = Json::object(vec![
            ("scheme", Json::str("test")),
            ("seed", Json::hex(&[1u8; 32])),
        ]);
        assert!(open(&unsealed, Some(b"unexpected")).is_err());
        let opened = open(&unsealed, None).unwrap();
        assert_eq!(opened.seed().unwrap().0, [1u8; 32]);
        assert_eq!(opened.vault_key_material().0, "01".repeat(32).into_bytes());

        // A seed of the wrong length is refused where it is used, never truncated or padded.
        let short = Json::object(vec![
            ("scheme", Json::str("test")),
            ("seed", Json::hex(&[1u8; 31])),
        ]);
        assert!(open(&short, None).unwrap().seed().is_err());
        // The opened secret is a wiping buffer and can not be copied or printed.
        assert!(std::mem::needs_drop::<OpenedSecret>());
    }
}
