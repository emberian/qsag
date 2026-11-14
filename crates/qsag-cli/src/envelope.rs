//! Versioned passphrase sealing. Fixed-cost iterated cSHAKE256 KDF; no external dependencies.
//! The KDF is deliberately iterated, not a claim of Argon2-style memory hardness.

use crate::cli::{Args, CliError, Secret32, ZeroizingBuf, os_random_32, read_bounded_file};
use crate::codec::{Json, from_hex_exact, from_hex_secret32};
use crate::vault::set;
use qsag_accel::keccak::cshake256_framed_xof;

const FORMAT: &str = "cshake256-iterated-v1";
pub const KDF_ROUNDS: u32 = 100_000;

pub fn passphrase(args: &Args) -> Result<Option<ZeroizingBuf>, CliError> {
    let pass = match (args.get("passphrase-env"), args.get("passphrase-file")) {
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

fn immutable_header_bytes(json: &Json, secret_field: &str) -> ZeroizingBuf {
    let mut header = json.clone();
    if let Json::Object(fields) = &mut header {
        fields.retain(|(name, _)| {
            !matches!(
                name.as_str(),
                "envelope"
                    | "salt"
                    | "envelope_tag"
                    | "vault_device"
                    | "vault_inode"
                    | "uses_completed"
                    | "ledger_checkpoint_gen"
                    | "ledger_checkpoint_tag"
                    | "state_mac"
            ) && name != secret_field
        });
    }
    ZeroizingBuf(header.to_pretty().into_bytes())
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

pub fn open(json: &Json, pass: Option<&[u8]>) -> Result<Json, CliError> {
    if json.get("envelope").is_none() {
        if json.get("salt").is_some() || json.get("envelope_tag").is_some() {
            return Err(CliError::input("damaged sealed envelope header"));
        }
        if pass.is_some() {
            return Err(CliError::input(
                "passphrase supplied for unencrypted key file",
            ));
        }
        let _ = secret_field_name(json)?;
        return Ok(json.clone());
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
    let mut opened = json.clone();
    set(&mut opened, field, Json::hex(&bytes));
    Ok(opened)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip_wrong_passphrase_and_tampering() {
        const { assert!(KDF_ROUNDS >= 100_000) };
        let (enc_a, mac_a) = derive(b"correct horse", &[7u8; 32], "test-a");
        assert_ne!(enc_a.0, mac_a.0, "encryption and MAC subkeys must be separated");
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
            assert_eq!(
                open(&key, Some(b"correct horse"))
                    .unwrap()
                    .field_hex(field)
                    .unwrap()
                    .0,
                vec![42; 32]
            );
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
                    .field_hex(field)
                    .unwrap()
                    .0,
                vec![42; 32]
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
        assert!(open(&unsealed, None).is_ok());
    }
}
