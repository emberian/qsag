//! `addr`: address encoding, decoding, and hybrid identity commitments.

use qsag_addr::{
    AddressVersion, HybridPinnedEnvelope, HybridSuiteSpec, KeyIdentityKind, QsagAddress,
    WitnessSuiteTag,
};

use crate::cli::{Args, CliError, read_text};
use crate::codec::{Json, from_hex};
use crate::keys::public_key_of;

/// Extract `(WitnessSuiteTag, canonical_public_key_bytes)` from any supported CLI public key file.
pub fn extract_suite_and_public_bytes(path: &str) -> Result<(WitnessSuiteTag, Vec<u8>), CliError> {
    let text = read_text(path)?;
    let json = Json::parse(&text)?;
    match json.field_str("format")? {
        crate::keys::PUBLIC_FORMAT => {
            let (scheme, public_key) = public_key_of(path)?;
            let tag = scheme
                .suite_tag()
                .ok_or_else(|| CliError::usage("this scheme has no address encoding"))?;
            Ok((tag, public_key))
        }
        crate::quorum::PUBLIC_FORMAT => {
            let scheme = json.field_str("scheme")?;
            let tag = crate::schemes::suite_tag_for_cli_scheme(scheme)?;
            let bytes = if scheme.eq_ignore_ascii_case("hem-jorts-poseidon2") {
                if json.get("validator_public_key").is_some() {
                    json.field_hex("validator_public_key")?.0.clone()
                } else {
                    json.field_hex("public_key")?.0.clone()
                }
            } else {
                let mut key = json.field_hex("pk_seed")?.0.clone();
                key.extend_from_slice(&json.field_hex("pk_root")?);
                key
            };
            Ok((tag, bytes))
        }
        "qsag-quorum-coupon-root-v1" => {
            let scheme = json.field_str("scheme")?;
            let tag = crate::schemes::suite_tag_for_cli_scheme(scheme)?;
            let mut key = json.field_hex("pk_seed")?.0.clone();
            key.extend_from_slice(&json.field_hex("pk_root")?);
            Ok((tag, key))
        }
        "qsag-cred-mldsa-public-v1" => {
            let scheme = json.field_str("scheme")?;
            let tag = crate::schemes::suite_tag_for_cli_scheme(scheme)?;
            Ok((tag, json.field_hex("public_key")?.0.clone()))
        }
        _ => Err(CliError::input(format!("{path} is not a public key file"))),
    }
}

const ADDR_HELP: &str = "\
qsag addr encode --public <path> [--hrp <hrp>] [--v2]
qsag addr decode <address> [--hrp <expected-hrp>]
qsag addr hybrid --suite <suite> --classical-pk <hexfile> --pq-pk <hexfile> [--hrp <hrp>] [--v2]

encode   address of a public key file written by `qsag keygen`
decode   strictly decode a Bech32m address; exit code 2 if it is malformed
hybrid   conjunctive classical + post-quantum identity: validates each key's exact length and
         encoding for the suite, then prints the identity commitment and address.
         Suites: hybrid-secp256k1-mldsa44 (33-byte compressed key + 1312-byte key),
                 hybrid-ed25519-mldsa65  (32-byte key + 1952-byte key)

  --v2     use the algebraic Poseidon2 commitment instead of cSHAKE256
  --json   machine-readable output
";

fn address_json(address: &QsagAddress) -> Result<Json, CliError> {
    let encoded = address
        .encode()
        .map_err(|e| CliError::usage(format!("address encoding failed: {e:?}")))?;
    Ok(Json::object(vec![
        ("address", Json::str(encoded)),
        ("hrp", Json::str(address.hrp.clone())),
        ("version", Json::num(address.version as u8)),
        ("suite_tag", Json::str(format!("{:?}", address.suite_tag))),
        ("identity_kind", Json::str(format!("{:?}", address.kind))),
        ("commitment", Json::hex(&address.commitment_256)),
    ]))
}

fn emit(args: &Args, json: Json) -> Result<(), CliError> {
    if args.flag("json") {
        print!("{}", json.to_pretty());
    } else {
        println!("{}", json.field_str("address")?);
    }
    Ok(())
}

pub fn run(raw: &[String]) -> Result<(), CliError> {
    let args = Args::parse(
        raw,
        &["public", "hrp", "suite", "classical-pk", "pq-pk"],
        &["v2", "json", "help"],
    )?;
    let verb = args.positional.first().map(String::as_str);
    if args.flag("help") || verb.is_none() {
        print!("{ADDR_HELP}");
        return if args.flag("help") {
            Ok(())
        } else {
            Err(CliError::usage("addr requires encode, decode, or hybrid"))
        };
    }
    let hrp = args.get("hrp").unwrap_or("qsp");
    let version = if args.flag("v2") {
        AddressVersion::V2Poseidon2
    } else {
        AddressVersion::V1Cshake256
    };
    let derive = |tag, kind, preimage: &[u8]| {
        match version {
            AddressVersion::V1Cshake256 => {
                QsagAddress::from_pubkey_cshake256(hrp, tag, kind, preimage)
            }
            AddressVersion::V2Poseidon2 => {
                QsagAddress::from_pubkey_poseidon2(hrp, tag, kind, preimage)
            }
        }
        .map_err(|e| CliError::usage(format!("address derivation failed: {e:?}")))
    };
    match (verb, args.positional.len()) {
        (Some("encode"), 1) => {
            let (tag, public_key) = extract_suite_and_public_bytes(args.require("public")?)?;
            emit(
                &args,
                address_json(&derive(
                    tag,
                    KeyIdentityKind::SingleOrThreshold,
                    &public_key,
                )?)?,
            )
        }
        (Some("decode"), 2) => {
            let decoded = match args.get("hrp") {
                Some(expected) => QsagAddress::decode_for_hrp(&args.positional[1], expected),
                None => QsagAddress::decode(&args.positional[1]),
            }
            .map_err(|e| CliError::verify(format!("invalid address: {e:?}")))?;
            let json = address_json(&decoded)?;
            if args.flag("json") {
                print!("{}", json.to_pretty());
            } else {
                println!(
                    "valid: suite {} kind {} commitment {}",
                    json.field_str("suite_tag")?,
                    json.field_str("identity_kind")?,
                    json.field_str("commitment")?
                );
            }
            Ok(())
        }
        (Some("hybrid"), 1) => {
            let tag = match args.require("suite")? {
                "hybrid-secp256k1-mldsa44" => WitnessSuiteTag::HybridSecp256k1MlDsa44,
                "hybrid-ed25519-mldsa65" => WitnessSuiteTag::HybridEd25519MlDsa65,
                other => return Err(CliError::usage(format!("unknown hybrid suite '{other}'"))),
            };
            let spec =
                HybridSuiteSpec::for_suite(tag).map_err(|e| CliError::usage(format!("{e:?}")))?;
            let classical = from_hex(&read_text(args.require("classical-pk")?)?)?;
            let pq = from_hex(&read_text(args.require("pq-pk")?)?)?;
            spec.validate_public_keys(&classical, &pq)
                .map_err(|e| CliError::verify(format!("hybrid key rejected: {e:?}")))?;
            let classical_digest = HybridPinnedEnvelope::hash_classical_pk(&spec, &classical);
            let pq_digest = HybridPinnedEnvelope::hash_pq_pk(&spec, &pq);
            let id_commit =
                HybridPinnedEnvelope::compute_id_commit(&spec, &classical_digest, &pq_digest);
            let Json::Object(ref mut members) = address_json(&derive(
                tag,
                KeyIdentityKind::HybridConjunctive,
                &id_commit,
            )?)?
            else {
                return Err(CliError::usage("internal: address is not an object"));
            };
            members.push(("id_commit".to_string(), Json::hex(&id_commit)));
            members.push((
                "classical_algorithm".to_string(),
                Json::str(format!("{:?}", spec.classical)),
            ));
            members.push((
                "pq_algorithm".to_string(),
                Json::str(format!("{:?}", spec.pq)),
            ));
            emit(&args, Json::Object(core::mem::take(members)))
        }
        _ => Err(CliError::usage(
            "usage: qsag addr <encode|decode|hybrid> ... (try --help)",
        )),
    }
}
