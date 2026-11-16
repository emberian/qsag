//! `qsag policy macaroon` and `qsag policy biscuit` attenuated capability CLI subcommands.
//!
//! Exposes both capability families from `qsag-policy`:
//! 1. [`SpongeMacaroon`]: 256-bit `cSHAKE256` bearer capabilities with offline first-party caveat
//!    attenuation and bound third-party discharges (`MacaroonVerifier`).
//! 2. [`PqBiscuit`]: post-quantum public-key capability delegation chains backed by one-time
//!    `Compact1122` (`FrontierSumFts`) hops, stateful [`PqBiscuitAuthorityKey`] Merkle mints
//!    fenced by external monotone anchors, single-use [`PqBiscuitStepKey`] retirement before
//!    output release, and mandatory terminal sealing with optional request PoP binding.

use std::path::Path;

use qsag_accel::CpuReferenceBackend;
use qsag_accel::keccak::cshake256_framed_32;
use qsag_fts::{FrontierDpTable, FrontierFtsProfile};
use qsag_policy::{
    CapabilityError, CapabilityRequest, Caveat, Discharge, MacaroonVerifier, PqBiscuit,
    PqBiscuitAuthorityKey, PqBiscuitAuthorityPublicKey, PqBiscuitStepKey, SpongeMacaroon,
};

use crate::anchor::{
    ANCHOR_FLAG_OPTIONS, ANCHOR_VALUE_OPTIONS, AnchorConfig, FsExternalMountAnchor,
    enforce_anchor_requirement, require_anchor_or_waiver,
};
use crate::cli::{
    Args, CliError, MAX_KEY_FILE_BYTES, Secret32, ZeroizingBuf, exit, os_random_32,
    read_bounded_file, write_new,
};
use crate::codec::{Json, from_hex, from_hex_exact, to_hex};
use crate::persist::replace;
use crate::policy_ledger::unix_now;
use crate::vault::Vault;

const MACAROON_KEY_FORMAT: &str = "qsag-macaroon-key-v1";
const MACAROON_TOKEN_FORMAT: &str = "qsag-macaroon-token-v1";
const BISCUIT_AUTH_SK_FORMAT: &str = "qsag-biscuit-authority-secret-v1";
const BISCUIT_AUTH_PK_FORMAT: &str = "qsag-biscuit-authority-public-v1";
const BISCUIT_STEP_SK_FORMAT: &str = "qsag-biscuit-step-secret-v1";
const BISCUIT_TOKEN_FORMAT: &str = "qsag-biscuit-token-v1";
const BISCUIT_ANCHOR_DOMAIN: &str = "biscuit_authority";

const MACAROON_HELP: &str = "\
qsag policy macaroon <keygen|issue|attenuate|issue-discharge|bind-discharge|verify> [options]

256-bit cSHAKE256 attenuated bearer capabilities and third-party discharges:

  keygen           --out <key.json> [--passphrase-env <VAR> | --passphrase-file <PATH>]
  issue            --key <key.json> --audience-hex <64-hex> [--id-hex <64-hex>] --out <tok.json> [caveats]
  attenuate        --in <tok.json> --out <tok.json> [caveats]
  issue-discharge  --key <tp-key.json> --id-hex <64-hex> --audience-hex <64-hex> --out <dis.json> [caveats]
  bind-discharge   --parent <tok.json> --discharge <dis.json> --out <bound.json>
  verify           --key <key.json> --in <tok.json> --audience-hex <64-hex> --resource-hex <64-hex>
                   [--actions <u64>] [--amount <u128>] [--now <secs>]
                   [--discharge <bound.json> --discharge-key <tp-key.json>]

Caveat flags (conjunctive; order preserved):
  --expires-at <secs>        require request timestamp < secs
  --not-before <secs>        require request timestamp >= secs
  --resource-hex <64-hex>    pin 32-byte target resource digest
  --actions <u64>            bitmask of permitted action bits
  --max-amount <u128>        maximum spend units permitted
  --third-party-hex <64-hex> require bound discharge for 32-byte caveat id (primary tokens only)
";

const BISCUIT_HELP: &str = "\
qsag policy biscuit <keygen|mint|attenuate|seal|verify> [options]

Post-quantum public-key capability chains over one-time Compact1122 (FrontierSumFts) hops:

  keygen     --secret-out <sk.json> --public-out <pk.json> [--tree-height <0..=8>]
             [--authority-id-hex <64-hex>] [--anchor-dir <dir> | --anchor-tpm-nv <idx> |
             --anchor-vmgenid | --ephemeral-unanchored] [--passphrase-*]
  mint       --secret <sk.json> --audience-hex <64-hex> [--token-id-hex <64-hex>]
             --token-out <biscuit.json> --step-key-out <step1.sk> [caveats] [anchor options]
  attenuate  --in <biscuit.json> --step-key <step.sk> --token-out <next.json>
             --step-key-out <next.sk> [caveats]
  seal       --in <biscuit.json> --step-key <step.sk> --out <sealed.json>
             [--bind-request --audience-hex <64-hex> --resource-hex <64-hex>
              [--actions <u64>] [--amount <u128>] [--now <secs>]]
  verify     --public <pk.json> --in <sealed.json> --audience-hex <64-hex>
             --resource-hex <64-hex> [--actions <u64>] [--amount <u128>] [--now <secs>]

First-party caveat flags:
  --expires-at <secs>  --not-before <secs>  --resource-hex <64-hex>
  --actions <u64>      --max-amount <u128>
";

const CAVEAT_OPTIONS: &[&str] = &[
    "expires-at",
    "not-before",
    "resource-hex",
    "actions",
    "max-amount",
    "third-party-hex",
];

fn map_cap_err(err: CapabilityError) -> CliError {
    match err {
        CapabilityError::Malformed | CapabilityError::InvalidTag => {
            CliError::new(exit::VERIFY_FAILED, format!("capability verification failed: {err:?}"))
        }
        CapabilityError::TooManyCaveats
        | CapabilityError::Denied
        | CapabilityError::MissingDischarge
        | CapabilityError::UnboundDischarge
        | CapabilityError::UnusedDischarge => {
            CliError::new(exit::POLICY_DENIED, format!("capability denied: {err:?}"))
        }
    }
}

fn load_json_checked(path: &str, expected_format: &str) -> Result<Json, CliError> {
    let raw = read_bounded_file(path, MAX_KEY_FILE_BYTES)?;
    let text = std::str::from_utf8(&raw.0)
        .map_err(|_| CliError::input(format!("{path} is not valid UTF-8")))?;
    let json = Json::parse(text)?;
    let fmt = json.field_str("format")?;
    if fmt != expected_format {
        return Err(CliError::input(format!(
            "{path}: expected format {expected_format}, found {fmt}"
        )));
    }
    Ok(json)
}

fn parse_caveats(args: &Args, allow_third_party: bool) -> Result<Vec<Caveat>, CliError> {
    let mut caveats = Vec::new();
    if let Some(nb) = args.get_u64("not-before")? {
        caveats.push(Caveat::NotBefore(nb));
    }
    if let Some(exp) = args.get_u64("expires-at")? {
        caveats.push(Caveat::ExpiresAt(exp));
    }
    if let Some(res_hex) = args.get("resource-hex") {
        caveats.push(Caveat::Resource(from_hex_exact(res_hex, "--resource-hex")?));
    }
    if let Some(actions) = args.get_u64("actions")? {
        caveats.push(Caveat::Actions(actions));
    }
    if let Some(max_amt) = args.get_u128("max-amount")? {
        caveats.push(Caveat::MaxAmount(max_amt));
    }
    if let Some(tp_hex) = args.get("third-party-hex") {
        if !allow_third_party {
            return Err(CliError::usage(
                "--third-party-hex applies only to primary macaroon capabilities",
            ));
        }
        caveats.push(Caveat::ThirdParty(from_hex_exact(
            tp_hex,
            "--third-party-hex",
        )?));
    }
    Ok(caveats)
}

fn parse_capability_request(args: &Args) -> Result<CapabilityRequest, CliError> {
    let audience = from_hex_exact(args.require("audience-hex")?, "--audience-hex")?;
    let resource = from_hex_exact(args.require("resource-hex")?, "--resource-hex")?;
    let actions = args.get_u64("actions")?.unwrap_or(0);
    let amount = args.get_u128("amount")?.unwrap_or(0);
    let now = match args.get_u64("now")? {
        Some(t) => t,
        None => unix_now()?,
    };
    Ok(CapabilityRequest {
        audience,
        resource,
        actions,
        amount,
        now,
    })
}

fn load_macaroon_key(path: &str, pass: Option<&[u8]>) -> Result<Secret32, CliError> {
    let mut vault = Vault::acquire(path, false)?;
    let json = load_json_checked(path, MACAROON_KEY_FORMAT)?;
    let opened = crate::envelope::open(&json, pass)?;
    vault.set_key_material(&opened);
    vault.authenticate(&json)?;
    opened.seed()
}

fn save_macaroon_token(path: &str, token: &SpongeMacaroon) -> Result<Json, CliError> {
    let wire = ZeroizingBuf::new(token.to_bytes());
    let hex = crate::codec::to_hex_zeroizing(&wire);
    let hex_str = String::from_utf8(hex.0.clone())
        .map_err(|_| CliError::state("encoding macaroon hex failed"))?;
    let doc = Json::object(vec![
        ("format", Json::str(MACAROON_TOKEN_FORMAT)),
        ("is_discharge", Json::Bool(token.is_discharge())),
        ("identifier", Json::hex(token.identifier())),
        ("audience", Json::hex(token.audience())),
        ("caveat_count", Json::num(token.caveats().len())),
        ("token_bytes", Json::num(wire.len())),
        ("token", Json::Str(hex_str)),
    ]);
    let encoded = ZeroizingBuf::new(doc.to_pretty().into_bytes());
    write_new(path, &encoded, true)?;
    Ok(doc)
}

fn load_macaroon_token(path: &str) -> Result<SpongeMacaroon, CliError> {
    let doc = load_json_checked(path, MACAROON_TOKEN_FORMAT)?;
    let raw = from_hex(doc.field_str("token")?)?;
    SpongeMacaroon::from_bytes(&raw).map_err(map_cap_err)
}

pub fn run_macaroon(raw: &[String]) -> Result<(), CliError> {
    let Some((sub, rest)) = raw.split_first() else {
        print!("{MACAROON_HELP}");
        return Err(CliError::usage(
            "macaroon requires keygen, issue, attenuate, issue-discharge, bind-discharge, or verify",
        ));
    };
    if sub == "--help" || sub == "-h" || sub == "help" {
        print!("{MACAROON_HELP}");
        return Ok(());
    }
    match sub.as_str() {
        "keygen" => macaroon_keygen(rest),
        "issue" | "mint" => macaroon_issue(rest, false),
        "issue-discharge" => macaroon_issue(rest, true),
        "attenuate" => macaroon_attenuate(rest),
        "bind-discharge" => macaroon_bind_discharge(rest),
        "verify" => macaroon_verify(rest),
        other => Err(CliError::usage(format!(
            "unknown macaroon subcommand '{other}' (try `qsag policy macaroon --help`)"
        ))),
    }
}

fn macaroon_keygen(raw: &[String]) -> Result<(), CliError> {
    let args = Args::parse(
        raw,
        &["out", "passphrase-env", "passphrase-file"],
        &["json", "help"],
    )?;
    if args.flag("help") {
        print!("{MACAROON_HELP}");
        return Ok(());
    }
    args.no_positionals()?;
    let out = args.require("out")?;
    let passphrase = crate::envelope::passphrase(&args)?;
    let mut vault = Vault::acquire(out, true)?;
    let root_key = Secret32::new(os_random_32()?);
    let nonce = Secret32::new(os_random_32()?);
    let key_id = cshake256_framed_32(b"QSAG.CLI.MACAROON.KEYID.V1", &[&root_key.0]);
    let mut file = Json::object(vec![
        ("format", Json::str(MACAROON_KEY_FORMAT)),
        ("scheme", Json::str("sponge-macaroon-cshake256")),
        ("enrollment_nonce", Json::hex(&nonce.0[..16])),
        ("key_id", Json::hex(&key_id)),
        ("seed", Json::hex(&root_key.0)),
    ]);
    vault.set_key_material(&crate::envelope::open(&file, None)?);
    if let Some(pass) = &passphrase {
        crate::envelope::seal(&mut file, pass)?;
    }
    vault.bind(&mut file)?;
    vault.seal(&mut file)?;
    let bytes = ZeroizingBuf::new(file.to_pretty().into_bytes());
    write_new(out, &bytes, true)?;
    let summary = Json::object(vec![
        ("format", Json::str(MACAROON_KEY_FORMAT)),
        ("key_id", Json::hex(&key_id)),
        ("out", Json::str(out)),
    ]);
    if args.flag("json") {
        print!("{}", summary.to_pretty());
    } else {
        println!("wrote macaroon key {out} (id {})", to_hex(&key_id));
    }
    Ok(())
}

fn macaroon_issue(raw: &[String], is_discharge: bool) -> Result<(), CliError> {
    let mut opts = vec![
        "key",
        "id-hex",
        "audience-hex",
        "out",
        "passphrase-env",
        "passphrase-file",
    ];
    opts.extend_from_slice(CAVEAT_OPTIONS);
    let args = Args::parse(raw, &opts, &["json", "help"])?;
    if args.flag("help") {
        print!("{MACAROON_HELP}");
        return Ok(());
    }
    args.no_positionals()?;
    let key_path = args.require("key")?;
    let out_path = args.require("out")?;
    let audience: [u8; 32] = from_hex_exact(args.require("audience-hex")?, "--audience-hex")?;
    let id: [u8; 32] = match args.get("id-hex") {
        Some(hex) => from_hex_exact(hex, "--id-hex")?,
        None if !is_discharge => os_random_32()?,
        None => return Err(CliError::usage("issue-discharge requires --id-hex")),
    };
    let caveats = parse_caveats(&args, !is_discharge)?;
    let passphrase = crate::envelope::passphrase(&args)?;
    let root_key = load_macaroon_key(key_path, passphrase.as_deref().map(Vec::as_slice))?;
    let mut token = if is_discharge {
        SpongeMacaroon::issue_discharge(&root_key.0, id, audience)
    } else {
        SpongeMacaroon::issue(&root_key.0, id, audience)
    };
    for c in caveats {
        token.attenuate(c).map_err(map_cap_err)?;
    }
    let _saved = save_macaroon_token(out_path, &token)?;
    let summary = Json::object(vec![
        ("is_discharge", Json::Bool(is_discharge)),
        ("identifier", Json::hex(&id)),
        ("audience", Json::hex(&audience)),
        ("caveat_count", Json::num(token.caveats().len())),
        ("out", Json::str(out_path)),
    ]);
    if args.flag("json") {
        print!("{}", summary.to_pretty());
    } else {
        println!(
            "wrote {} macaroon {out_path} ({} caveats)",
            if is_discharge { "discharge" } else { "primary" },
            token.caveats().len()
        );
    }
    Ok(())
}

fn macaroon_attenuate(raw: &[String]) -> Result<(), CliError> {
    let mut opts = vec!["in", "out"];
    opts.extend_from_slice(CAVEAT_OPTIONS);
    let args = Args::parse(raw, &opts, &["json", "help"])?;
    if args.flag("help") {
        print!("{MACAROON_HELP}");
        return Ok(());
    }
    args.no_positionals()?;
    let in_path = args.require("in")?;
    let out_path = args.require("out")?;
    let mut token = load_macaroon_token(in_path)?;
    let caveats = parse_caveats(&args, !token.is_discharge())?;
    if caveats.is_empty() {
        return Err(CliError::usage(
            "attenuate requires at least one caveat option",
        ));
    }
    for c in caveats {
        token.attenuate(c).map_err(map_cap_err)?;
    }
    let _ = save_macaroon_token(out_path, &token)?;
    let summary = Json::object(vec![
        ("identifier", Json::hex(token.identifier())),
        ("caveat_count", Json::num(token.caveats().len())),
        ("out", Json::str(out_path)),
    ]);
    if args.flag("json") {
        print!("{}", summary.to_pretty());
    } else {
        println!(
            "wrote attenuated macaroon {out_path} ({} caveats)",
            token.caveats().len()
        );
    }
    Ok(())
}

fn macaroon_bind_discharge(raw: &[String]) -> Result<(), CliError> {
    let args = Args::parse(
        raw,
        &["parent", "discharge", "out"],
        &["json", "help"],
    )?;
    if args.flag("help") {
        print!("{MACAROON_HELP}");
        return Ok(());
    }
    args.no_positionals()?;
    let parent = load_macaroon_token(args.require("parent")?)?;
    let mut discharge = load_macaroon_token(args.require("discharge")?)?;
    let out_path = args.require("out")?;
    parent
        .bind_discharge(&mut discharge)
        .map_err(map_cap_err)?;
    let _ = save_macaroon_token(out_path, &discharge)?;
    let summary = Json::object(vec![
        ("parent_identifier", Json::hex(parent.identifier())),
        ("discharge_identifier", Json::hex(discharge.identifier())),
        ("caveat_count", Json::num(discharge.caveats().len())),
        ("out", Json::str(out_path)),
    ]);
    if args.flag("json") {
        print!("{}", summary.to_pretty());
    } else {
        println!("wrote bound discharge {out_path}");
    }
    Ok(())
}

fn macaroon_verify(raw: &[String]) -> Result<(), CliError> {
    let args = Args::parse(
        raw,
        &[
            "key",
            "in",
            "audience-hex",
            "resource-hex",
            "actions",
            "amount",
            "now",
            "discharge",
            "discharge-key",
            "passphrase-env",
            "passphrase-file",
            "discharge-passphrase-env",
            "discharge-passphrase-file",
        ],
        &["json", "help"],
    )?;
    if args.flag("help") {
        print!("{MACAROON_HELP}");
        return Ok(());
    }
    args.no_positionals()?;
    let pass = crate::envelope::passphrase(&args)?;
    let root_key = load_macaroon_key(args.require("key")?, pass.as_deref().map(Vec::as_slice))?;
    let token = load_macaroon_token(args.require("in")?)?;
    let req = parse_capability_request(&args)?;

    let discharge_pair = match (args.get("discharge"), args.get("discharge-key")) {
        (Some(d_path), Some(dk_path)) => {
            let d_pass = crate::envelope::passphrase_named(
                &args,
                "discharge-passphrase-env",
                "discharge-passphrase-file",
            )?;
            let d_tok = load_macaroon_token(d_path)?;
            let d_key = load_macaroon_key(dk_path, d_pass.as_deref().map(Vec::as_slice))?;
            Some((d_tok, d_key))
        }
        (None, None) => None,
        _ => {
            return Err(CliError::usage(
                "--discharge and --discharge-key must be supplied together",
            ));
        }
    };

    let discharges: Vec<Discharge<'_>> = match &discharge_pair {
        Some((d_tok, d_key)) => vec![Discharge {
            token: d_tok,
            root_key: &d_key.0,
        }],
        None => Vec::new(),
    };

    let verifier = MacaroonVerifier::new(&root_key.0, *token.identifier(), req.audience);
    verifier
        .verify(&token, &req, &discharges)
        .map_err(map_cap_err)?;

    let summary = Json::object(vec![
        ("valid", Json::Bool(true)),
        ("identifier", Json::hex(token.identifier())),
        ("audience", Json::hex(&req.audience)),
        ("caveat_count", Json::num(token.caveats().len())),
        ("discharges_verified", Json::num(discharges.len())),
    ]);
    if args.flag("json") {
        print!("{}", summary.to_pretty());
    } else {
        println!(
            "valid macaroon {} ({} caveats)",
            to_hex(token.identifier()),
            token.caveats().len()
        );
    }
    Ok(())
}

