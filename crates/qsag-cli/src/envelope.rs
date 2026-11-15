//! Versioned passphrase sealing. Fixed-cost iterated cSHAKE256 KDF; no external dependencies.
//! The KDF is deliberately iterated, not a claim of Argon2-style memory hardness.

use crate::cli::{Args, CliError, Secret32, ZeroizingBuf, os_random_32, read_bounded_file};
use crate::codec::{Json, from_hex_exact, from_hex_secret32};
use crate::vault::set;
use qsag_accel::keccak::cshake256_framed_xof;

const FORMAT: &str = "cshake256-iterated-v1";
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
        (Some(name), None) => Some(ZeroizingBuf(
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
const MUTABLE_FIELDS: [&str; 13] = [
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
    "state_mac",
];

fn immutable_header_bytes(json: &Json, secret_field: &str) -> ZeroizingBuf {
    let mut excluded = MUTABLE_FIELDS.to_vec();
    excluded.push(secret_field);
    crate::persist::authenticated_bytes(json, &excluded)
}

fn derive(pass: &[u8], salt: &[u8; 32], scheme: &str) -> (Secret32, Secret32) {
    let mut state = Secret32([0u8; 32]);
    cshake256_framed_xof(
        b"QSAG.ENVELOPE.KDF.V1",
        &[pass, salt, scheme.as_bytes()],
        &mut state.0,
    );
    for i in 0..KDF_ROUNDS {
        let mut next = Secret32([0u8; 32]);
        cshake256_framed_xof(
            b"QSAG.ENVELOPE.ITER.V1",
            &[&state.0, salt, &i.to_le_bytes()],
            &mut next.0,
        );
        state = next;
    }
    let mut enc = Secret32([0u8; 32]);
    cshake256_framed_xof(
        b"QSAG.ENVELOPE.ENC.V1",
        &[&state.0, salt, scheme.as_bytes()],
        &mut enc.0,
    );
    let mut mac = Secret32([0u8; 32]);
    cshake256_framed_xof(
        b"QSAG.ENVELOPE.MAC.V1",
        &[&state.0, salt, scheme.as_bytes()],
        &mut mac.0,
    );
    (enc, mac)
}

fn crypt(bytes: &mut [u8], enc_key: &Secret32, salt: &[u8; 32], scheme: &str, field: &str) {
    for (i, block) in bytes.chunks_mut(32).enumerate() {
        let mut stream = Secret32([0u8; 32]);
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
    json: &Json,
    scheme: &str,
    field: &str,
    salt: &[u8; 32],
    ciphertext: &[u8],
    mac_key: &Secret32,
) -> Secret32 {
    let header = immutable_header_bytes(json, field);
    let mut out = Secret32([0u8; 32]);
    cshake256_framed_xof(
        b"QSAG.ENVELOPE.TAG.V1",
        &[
            &mac_key.0,
            FORMAT.as_bytes(),
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
    let mut bytes = json.field_hex(field)?;
    let salt = os_random_32()?;
    let (enc, mac) = derive(pass, &salt, &scheme);
    crypt(&mut bytes.0, &enc, &salt, &scheme, field);
    let auth = tag(json, &scheme, field, &salt, &bytes, &mac);
    set(json, field, Json::hex(&bytes));
    set(json, "envelope", Json::str(FORMAT));
    set(json, "salt", Json::hex(&salt));
    set(json, "envelope_tag", Json::hex(&auth.0));
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
        let mut seed = Secret32([0u8; 32]);
        if bytes.len() != seed.0.len() {
            return Err(CliError::input("seed must be exactly 32 bytes of hex"));
        }
        seed.0.copy_from_slice(bytes);
        Ok(seed)
    }

    /// The vault MAC key material: the canonical lowercase hex of the secret, as bytes.
    pub fn vault_key_material(&self) -> ZeroizingBuf {
        crate::codec::to_hex_zeroizing(&self.bytes)
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
            bytes: json.field_hex(field)?,
        });
    }
    if json.field_str("envelope")? != FORMAT {
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
    let salt = from_hex_exact(json.field_str("salt")?, "salt")?;
    let actual = from_hex_secret32(json.field_str("envelope_tag")?, "envelope_tag")?;
    let mut bytes = json.field_hex(field)?;
    let (enc, mac) = derive(pass, &salt, scheme);
    let expected = tag(json, scheme, field, &salt, &bytes, &mac);
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
    fn roundtrip_wrong_passphrase_and_tampering() {
        const { assert!(KDF_ROUNDS >= 100_000) };
        let (enc_a, mac_a) = derive(b"correct horse", &[7u8; 32], "test-a");
        assert_ne!(
            enc_a.0, mac_a.0,
            "encryption and MAC subkeys must be separated"
        );
        let (enc_b, mac_b) = derive(b"correct horse", &[7u8; 32], "test-b");
        assert_ne!(enc_a.0, enc_b.0);
        assert_ne!(mac_a.0, mac_b.0);

        for field in ["seed", "secret_key"] {
            let mut key = Json::object(vec![
                ("scheme", Json::str("test")),
                ("enrollment_nonce", Json::hex(&[9u8; 16])),
                (field, Json::hex(&[42; 32])),
            ]);
            seal(&mut key, b"correct horse").unwrap();
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
