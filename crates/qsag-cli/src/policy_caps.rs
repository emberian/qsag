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
             --anchor-vmgenid | --ephemeral-unanchored] [--passphrase-env <VAR> | --passphrase-file <PATH>]
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
  --passphrase-env <VAR> / --passphrase-file <PATH>  seal keygen or unlock mint authority
  --vault-dir <dir>  local custody directory for external anchor isolation
  --allow-single-disk-anchor  permit a distinct anchor directory on the same filesystem
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
        CapabilityError::Malformed | CapabilityError::InvalidTag => CliError::new(
            exit::VERIFY_FAILED,
            format!("capability verification failed: {err:?}"),
        ),
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
    let args = Args::parse(raw, &["parent", "discharge", "out"], &["json", "help"])?;
    if args.flag("help") {
        print!("{MACAROON_HELP}");
        return Ok(());
    }
    args.no_positionals()?;
    let parent = load_macaroon_token(args.require("parent")?)?;
    let mut discharge = load_macaroon_token(args.require("discharge")?)?;
    let out_path = args.require("out")?;
    parent.bind_discharge(&mut discharge).map_err(map_cap_err)?;
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

pub fn run_biscuit(raw: &[String]) -> Result<(), CliError> {
    let Some((sub, rest)) = raw.split_first() else {
        print!("{BISCUIT_HELP}");
        return Err(CliError::usage(
            "biscuit requires keygen, mint, attenuate, seal, or verify",
        ));
    };
    if sub == "--help" || sub == "-h" || sub == "help" {
        print!("{BISCUIT_HELP}");
        return Ok(());
    }
    match sub.as_str() {
        "keygen" => biscuit_keygen(rest),
        "mint" => biscuit_mint(rest),
        "attenuate" => biscuit_attenuate(rest),
        "seal" => biscuit_seal(rest),
        "verify" => biscuit_verify(rest),
        other => Err(CliError::usage(format!(
            "unknown biscuit subcommand '{other}' (try `qsag policy biscuit --help`)"
        ))),
    }
}

fn save_step_key(path: &str, step: &PqBiscuitStepKey) -> Result<(), CliError> {
    let mut vault = Vault::acquire(path, true)?;
    let enrollment = Secret32::new(os_random_32()?);
    let raw = step.to_secret_bytes();
    let hex = crate::codec::to_hex_zeroizing(&raw);
    let hex_str = String::from_utf8(hex.0.clone())
        .map_err(|_| CliError::state("encoding step key hex failed"))?;
    let mut doc = Json::object(vec![
        ("format", Json::str(BISCUIT_STEP_SK_FORMAT)),
        ("enrollment_nonce", Json::hex(&enrollment[..16])),
        ("spent", Json::Bool(false)),
        ("hop_index", Json::num(step.hop_index())),
        ("pk_root", Json::hex(step.pk_root())),
        ("secret_key", Json::Str(hex_str)),
    ]);
    vault.set_key_material(&crate::envelope::open(&doc, None)?);
    vault.bind(&mut doc)?;
    vault.seal(&mut doc)?;
    let bytes = ZeroizingBuf::new(doc.to_pretty().into_bytes());
    write_new(path, &bytes, true)
}

fn consume_step_key(path: &str) -> Result<PqBiscuitStepKey, CliError> {
    // Keep the inode-bound vault lock from the initial read through durable
    // retirement: competing attenuate/seal processes must not spend one key twice.
    let mut vault = Vault::acquire(path, false)?;
    let doc = load_json_checked(path, BISCUIT_STEP_SK_FORMAT)?;
    if matches!(doc.get("spent"), Some(Json::Bool(true))) {
        return Err(CliError::state(
            "PqBiscuit step key was already spent (one-time Compact1122 key cannot be reused)",
        ));
    }
    let opened = crate::envelope::open(&doc, None)?;
    vault.set_key_material(&opened);
    vault.authenticate(&doc)?;
    let step = PqBiscuitStepKey::from_secret_bytes(opened.secret_key()?).map_err(map_cap_err)?;
    // Retire and wipe the one-time step key on disk BEFORE signing/releasing the hop!
    let mut tombstone = Json::object(vec![
        ("format", Json::str(BISCUIT_STEP_SK_FORMAT)),
        (
            "enrollment_nonce",
            Json::str(doc.field_str("enrollment_nonce")?),
        ),
        ("secret_key", Json::str("")),
        ("spent", Json::Bool(true)),
        ("retired", Json::Bool(true)),
        ("hop_index", Json::num(step.hop_index())),
        ("pk_root", Json::hex(step.pk_root())),
    ]);
    vault.bind(&mut tombstone)?;
    // Advance the companion MAC before replacing the secret. Any interrupted
    // update fails closed, as does restoring only the old secret file.
    vault.seal(&mut tombstone)?;
    replace(Path::new(path), tombstone.to_pretty().as_bytes(), || Ok(()))
        .map_err(|e| CliError::io("retiring one-time biscuit step key", e))?;
    Ok(step)
}

fn save_biscuit_token(path: &str, token: &PqBiscuit) -> Result<Json, CliError> {
    let wire = token.to_bytes().map_err(map_cap_err)?;
    let doc = Json::object(vec![
        ("format", Json::str(BISCUIT_TOKEN_FORMAT)),
        ("token_id", Json::hex(token.token_id())),
        ("audience", Json::hex(token.audience())),
        (
            "authority_leaf_index",
            Json::num(token.authority_leaf_index()),
        ),
        ("hops", Json::num(token.blocks().len())),
        ("sealed", Json::Bool(token.is_sealed())),
        ("request_bound", Json::Bool(token.is_request_bound())),
        ("token_bytes", Json::num(wire.len())),
        ("token", Json::hex(&wire)),
    ]);
    write_new(path, doc.to_pretty().as_bytes(), false)?;
    Ok(doc)
}

fn load_biscuit_token(path: &str) -> Result<PqBiscuit, CliError> {
    let doc = load_json_checked(path, BISCUIT_TOKEN_FORMAT)?;
    let raw = doc.field_hex("token")?;
    PqBiscuit::from_bytes(&raw).map_err(map_cap_err)
}

fn biscuit_anchor_mac(authority_sk_bytes: &[u8], authority_id: &[u8; 32]) -> Secret32 {
    // Derive from the master_seed bytes [8..40] inside `AUTHORITY_SK_MAGIC || master_seed || ...`
    Secret32::new(cshake256_framed_32(
        b"QSAG.CLI.BISCUIT.ANCHOR.MAC.V1",
        &[&authority_sk_bytes[8..40], authority_id],
    ))
}

fn biscuit_keygen(raw: &[String]) -> Result<(), CliError> {
    let mut opts = vec![
        "secret-out",
        "public-out",
        "tree-height",
        "authority-id-hex",
        "passphrase-env",
        "passphrase-file",
    ];
    opts.extend_from_slice(ANCHOR_VALUE_OPTIONS);
    let mut flags = vec!["json", "help"];
    flags.extend_from_slice(ANCHOR_FLAG_OPTIONS);
    let args = Args::parse(raw, &opts, &flags)?;
    if args.flag("help") {
        print!("{BISCUIT_HELP}");
        return Ok(());
    }
    args.no_positionals()?;
    let anchor_cfg = AnchorConfig::from_args(&args)?;
    require_anchor_or_waiver(
        anchor_cfg.is_some(),
        args.flag("ephemeral-unanchored"),
        "anchor-dir",
    )?;
    let secret_out = args.require("secret-out")?;
    let public_out = args.require("public-out")?;
    let tree_height_u64 = args.get_u64("tree-height")?.unwrap_or(4);
    let tree_height = u8::try_from(tree_height_u64)
        .ok()
        .filter(|&h| h <= qsag_policy::MAX_AUTHORITY_TREE_HEIGHT)
        .ok_or_else(|| CliError::usage("--tree-height must be between 0 and 8"))?;
    let authority_id: [u8; 32] = match args.get("authority-id-hex") {
        Some(hex) => from_hex_exact(hex, "--authority-id-hex")?,
        None => os_random_32()?,
    };
    let passphrase = crate::envelope::passphrase(&args)?;
    if let Some(cfg) = &anchor_cfg {
        cfg.validate_isolation(&[secret_out], &[], true)?;
    }

    let mut vault = Vault::acquire(secret_out, true)?;
    let master_seed = Secret32::new(os_random_32()?);
    let nonce = Secret32::new(os_random_32()?);
    let auth_sk = PqBiscuitAuthorityKey::keygen(
        master_seed.0,
        authority_id,
        tree_height,
        &CpuReferenceBackend,
    )
    .map_err(map_cap_err)?;
    let pk = *auth_sk.public_key();
    let sk_bytes = auth_sk.to_secret_bytes();

    let anchor_seal = match &anchor_cfg {
        Some(cfg) => {
            let mac = biscuit_anchor_mac(&sk_bytes, &pk.authority_id);
            let anchor = FsExternalMountAnchor::provision_fresh(
                cfg,
                &[secret_out],
                &[],
                BISCUIT_ANCHOR_DOMAIN,
                pk.authority_id,
                mac.0,
            )?;
            anchor.advance_floor(BISCUIT_ANCHOR_DOMAIN.as_bytes(), 0)?;
            Some(anchor.lock_identity_seal())
        }
        None => None,
    };

    let sk_hex = crate::codec::to_hex_zeroizing(&sk_bytes);
    let sk_hex_str = String::from_utf8(sk_hex.0.clone())
        .map_err(|_| CliError::state("encoding biscuit authority secret key failed"))?;
    let mut secret_fields = vec![
        ("format", Json::str(BISCUIT_AUTH_SK_FORMAT)),
        ("scheme", Json::str("pq-biscuit-compact1122")),
        ("enrollment_nonce", Json::hex(&nonce.0[..16])),
        ("authority_id", Json::hex(&pk.authority_id)),
        ("tree_height", Json::num(pk.tree_height)),
        ("uses_completed", Json::num(0u32)),
    ];
    if let Some(seal) = &anchor_seal {
        secret_fields.push(("anchor_required", Json::Bool(true)));
        secret_fields.push(("anchor_ceremony_seal", Json::hex(seal)));
    }
    secret_fields.push(("secret_key", Json::Str(sk_hex_str)));
    let mut secret_doc = Json::object(secret_fields);

    vault.set_key_material(&crate::envelope::open(&secret_doc, None)?);
    if let Some(pass) = &passphrase {
        crate::envelope::seal(&mut secret_doc, pass)?;
    }
    vault.bind(&mut secret_doc)?;
    vault.seal(&mut secret_doc)?;
    let secret_raw = ZeroizingBuf::new(secret_doc.to_pretty().into_bytes());
    write_new(secret_out, &secret_raw, true)?;

    let pk_doc = Json::object(vec![
        ("format", Json::str(BISCUIT_AUTH_PK_FORMAT)),
        ("scheme", Json::str("pq-biscuit-compact1122")),
        ("authority_id", Json::hex(&pk.authority_id)),
        ("tree_height", Json::num(pk.tree_height)),
        ("max_mints", Json::num(1u32 << pk.tree_height)),
        ("merkle_root", Json::hex(&pk.merkle_root)),
        ("public_key", Json::hex(&pk.to_bytes())),
    ]);
    write_new(public_out, pk_doc.to_pretty().as_bytes(), false)?;

    if args.flag("json") {
        print!("{}", pk_doc.to_pretty());
    } else {
        println!(
            "wrote PqBiscuit authority {} ({} max mints)",
            public_out,
            1u32 << pk.tree_height
        );
    }
    Ok(())
}

fn biscuit_mint(raw: &[String]) -> Result<(), CliError> {
    let mut opts = vec![
        "secret",
        "audience-hex",
        "token-id-hex",
        "token-out",
        "step-key-out",
        "passphrase-env",
        "passphrase-file",
    ];
    opts.extend_from_slice(&CAVEAT_OPTIONS[..5]); // first-party caveats only
    opts.extend_from_slice(ANCHOR_VALUE_OPTIONS);
    let mut flags = vec!["json", "help"];
    flags.extend_from_slice(ANCHOR_FLAG_OPTIONS);
    let args = Args::parse(raw, &opts, &flags)?;
    if args.flag("help") {
        print!("{BISCUIT_HELP}");
        return Ok(());
    }
    args.no_positionals()?;
    let anchor_cfg = AnchorConfig::from_args(&args)?;
    require_anchor_or_waiver(
        anchor_cfg.is_some(),
        args.flag("ephemeral-unanchored"),
        "anchor-dir",
    )?;
    let secret_path = args.require("secret")?;
    let token_out = args.require("token-out")?;
    let step_out = args.require("step-key-out")?;
    let audience: [u8; 32] = from_hex_exact(args.require("audience-hex")?, "--audience-hex")?;
    let token_id: [u8; 32] = match args.get("token-id-hex") {
        Some(hex) => from_hex_exact(hex, "--token-id-hex")?,
        None => os_random_32()?,
    };
    let caveats = parse_caveats(&args, false)?;
    let passphrase = crate::envelope::passphrase(&args)?;

    let mut vault = Vault::acquire(secret_path, false)?;
    let mut secret_doc = load_json_checked(secret_path, BISCUIT_AUTH_SK_FORMAT)?;
    enforce_anchor_requirement(&secret_doc, anchor_cfg.as_ref())?;
    let opened = crate::envelope::open(&secret_doc, passphrase.as_deref().map(Vec::as_slice))?;
    vault.set_key_material(&opened);
    vault.authenticate(&secret_doc)?;

    let sk_raw = opened.secret_key()?;
    let mut auth_sk = PqBiscuitAuthorityKey::from_secret_bytes(sk_raw).map_err(map_cap_err)?;
    let recorded_uses = u32::try_from(secret_doc.field_u64("uses_completed")?)
        .map_err(|_| CliError::state("uses_completed overflow"))?;
    if auth_sk.next_leaf() < recorded_uses {
        auth_sk
            .advance_next_leaf(recorded_uses)
            .map_err(map_cap_err)?;
    }

    let anchor_opt = match &anchor_cfg {
        Some(cfg) => {
            let mac = biscuit_anchor_mac(sk_raw, &auth_sk.public_key().authority_id);
            let anchor = FsExternalMountAnchor::open_existing(
                cfg,
                &[secret_path],
                &[],
                BISCUIT_ANCHOR_DOMAIN,
                auth_sk.public_key().authority_id,
                mac.0,
            )?;
            anchor.verify_expected_seal(&secret_doc, "anchor_ceremony_seal")?;
            anchor.verify_floor_at_least(
                BISCUIT_ANCHOR_DOMAIN.as_bytes(),
                u64::from(auth_sk.next_leaf()),
            )?;
            Some(anchor)
        }
        None => None,
    };

    if auth_sk.remaining_mints() == 0 {
        return Err(CliError::state("PqBiscuit authority leaf budget exhausted"));
    }

    let step_entropy = Secret32::new(os_random_32()?);
    let hedge = Secret32::new(os_random_32()?);
    let dp = FrontierDpTable::build(FrontierFtsProfile::Compact1122);
    let (token, step1) = auth_sk
        .mint(
            &dp,
            token_id,
            audience,
            &caveats,
            step_entropy.0,
            &hedge.0,
            &CpuReferenceBackend,
        )
        .map_err(map_cap_err)?;

    // Persist the consumed leaf before advancing the external floor. Failed resealing
    // must leave both states unchanged; a later anchor failure only burns a leaf.
    let updated_sk = auth_sk.to_secret_bytes();
    let updated_hex = crate::codec::to_hex_zeroizing(&updated_sk);
    let updated_str = String::from_utf8(updated_hex.0.clone())
        .map_err(|_| CliError::state("encoding updated biscuit authority key failed"))?;
    if let Json::Object(fields) = &mut secret_doc {
        fields.retain(|(k, _)| {
            !matches!(
                k.as_str(),
                "uses_completed"
                    | "secret_key"
                    | "envelope"
                    | "salt"
                    | "envelope_tag"
                    | "state_mac"
            )
        });
        fields.push(("uses_completed".into(), Json::num(auth_sk.next_leaf())));
        fields.push(("secret_key".into(), Json::Str(updated_str)));
    }
    vault.set_key_material(&crate::envelope::open(&secret_doc, None)?);
    if let Some(pass) = &passphrase {
        crate::envelope::seal(&mut secret_doc, pass)?;
    }
    vault.seal(&mut secret_doc)?;
    let updated_bytes = ZeroizingBuf::new(secret_doc.to_pretty().into_bytes());
    replace(Path::new(secret_path), &updated_bytes, || Ok(()))
        .map_err(|e| CliError::io("persisting advanced biscuit authority vault", e))?;
    if let Some(anchor) = &anchor_opt {
        anchor.advance_floor(
            BISCUIT_ANCHOR_DOMAIN.as_bytes(),
            u64::from(auth_sk.next_leaf()),
        )?;
    }

    save_step_key(step_out, &step1)?;
    let doc = save_biscuit_token(token_out, &token)?;
    if args.flag("json") {
        print!("{}", doc.to_pretty());
    } else {
        println!(
            "minted PqBiscuit {token_out} (leaf {}, remaining {}) and step key {step_out}",
            token.authority_leaf_index(),
            auth_sk.remaining_mints()
        );
    }
    Ok(())
}

fn biscuit_attenuate(raw: &[String]) -> Result<(), CliError> {
    let mut opts = vec!["in", "step-key", "token-out", "step-key-out"];
    opts.extend_from_slice(&CAVEAT_OPTIONS[..5]);
    let args = Args::parse(raw, &opts, &["json", "help"])?;
    if args.flag("help") {
        print!("{BISCUIT_HELP}");
        return Ok(());
    }
    args.no_positionals()?;
    let token = load_biscuit_token(args.require("in")?)?;
    let token_out = args.require("token-out")?;
    let step_out = args.require("step-key-out")?;
    let caveats = parse_caveats(&args, false)?;
    let step = consume_step_key(args.require("step-key")?)?;
    let next_entropy = Secret32::new(os_random_32()?);
    let hedge = Secret32::new(os_random_32()?);
    let dp = FrontierDpTable::build(FrontierFtsProfile::Compact1122);
    let (attenuated, next_step) = step
        .attenuate(
            &token,
            &dp,
            &caveats,
            next_entropy.0,
            &hedge.0,
            &CpuReferenceBackend,
        )
        .map_err(map_cap_err)?;
    save_step_key(step_out, &next_step)?;
    let doc = save_biscuit_token(token_out, &attenuated)?;
    if args.flag("json") {
        print!("{}", doc.to_pretty());
    } else {
        println!(
            "attenuated PqBiscuit {token_out} (hops {}) and next step key {step_out}",
            attenuated.blocks().len()
        );
    }
    Ok(())
}

fn biscuit_seal(raw: &[String]) -> Result<(), CliError> {
    let args = Args::parse(
        raw,
        &[
            "in",
            "step-key",
            "out",
            "audience-hex",
            "resource-hex",
            "actions",
            "amount",
            "now",
        ],
        &["bind-request", "json", "help"],
    )?;
    if args.flag("help") {
        print!("{BISCUIT_HELP}");
        return Ok(());
    }
    args.no_positionals()?;
    let token = load_biscuit_token(args.require("in")?)?;
    let out_path = args.require("out")?;
    let bound_req = if args.flag("bind-request") {
        Some(parse_capability_request(&args)?)
    } else {
        None
    };
    let step = consume_step_key(args.require("step-key")?)?;
    let hedge = Secret32::new(os_random_32()?);
    let dp = FrontierDpTable::build(FrontierFtsProfile::Compact1122);
    let sealed = step
        .seal(
            &token,
            &dp,
            bound_req.as_ref(),
            &hedge.0,
            &CpuReferenceBackend,
        )
        .map_err(map_cap_err)?;
    let doc = save_biscuit_token(out_path, &sealed)?;
    if args.flag("json") {
        print!("{}", doc.to_pretty());
    } else {
        println!(
            "sealed PqBiscuit {out_path} ({} hops, request_bound={})",
            sealed.blocks().len(),
            sealed.is_request_bound()
        );
    }
    Ok(())
}

fn biscuit_verify(raw: &[String]) -> Result<(), CliError> {
    let args = Args::parse(
        raw,
        &[
            "public",
            "in",
            "audience-hex",
            "resource-hex",
            "actions",
            "amount",
            "now",
        ],
        &["json", "help"],
    )?;
    if args.flag("help") {
        print!("{BISCUIT_HELP}");
        return Ok(());
    }
    args.no_positionals()?;
    let pk_doc = load_json_checked(args.require("public")?, BISCUIT_AUTH_PK_FORMAT)?;
    let pk = PqBiscuitAuthorityPublicKey::from_bytes(&pk_doc.field_hex("public_key")?)
        .map_err(map_cap_err)?;
    let token = load_biscuit_token(args.require("in")?)?;
    let req = parse_capability_request(&args)?;
    let dp = FrontierDpTable::build(FrontierFtsProfile::Compact1122);
    token.verify(&pk, &dp, &req).map_err(map_cap_err)?;
    let summary = Json::object(vec![
        ("valid", Json::Bool(true)),
        ("token_id", Json::hex(token.token_id())),
        ("authority_id", Json::hex(&pk.authority_id)),
        ("hops", Json::num(token.blocks().len())),
        ("request_bound", Json::Bool(token.is_request_bound())),
    ]);
    if args.flag("json") {
        print!("{}", summary.to_pretty());
    } else {
        println!(
            "valid PqBiscuit {} ({} hops)",
            to_hex(token.token_id()),
            token.blocks().len()
        );
    }
    Ok(())
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;

    #[test]
    fn biscuit_step_retirement_serializes_competing_spenders_and_rejects_replay() {
        let root = std::env::temp_dir().join(format!(
            "qsag-biscuit-step-{}-{}",
            std::process::id(),
            to_hex(&os_random_32().unwrap()),
        ));
        crate::persist::private_dir(root.to_str().unwrap(), true).unwrap();
        let path = root.join("step.json");
        let path = path.to_str().unwrap();
        let dp = FrontierDpTable::build(FrontierFtsProfile::Compact1122);
        let mut authority =
            PqBiscuitAuthorityKey::keygen([31; 32], [32; 32], 1, &CpuReferenceBackend).unwrap();
        let (_, step) = authority
            .mint(
                &dp,
                [33; 32],
                [34; 32],
                &[],
                [35; 32],
                &[36; 32],
                &CpuReferenceBackend,
            )
            .unwrap();
        save_step_key(path, &step).unwrap();
        let snapshot = std::fs::read(path).unwrap();
        let barrier = std::sync::Barrier::new(8);
        let successes = std::thread::scope(|scope| {
            let handles: Vec<_> = (0..8)
                .map(|_| {
                    let barrier = &barrier;
                    scope.spawn(move || {
                        barrier.wait();
                        consume_step_key(path).is_ok()
                    })
                })
                .collect();
            handles
                .into_iter()
                .map(|h| usize::from(h.join().unwrap()))
                .sum::<usize>()
        });
        assert_eq!(successes, 1);
        let tombstone = std::fs::read_to_string(path).unwrap();
        assert!(tombstone.contains("\"retired\": true"));
        assert!(!tombstone.contains(&to_hex(&step.to_secret_bytes())));
        std::fs::write(path, snapshot).unwrap();
        assert!(
            consume_step_key(path).is_err(),
            "the companion state must reject a restored step key"
        );
        std::fs::remove_dir_all(root).unwrap();
    }
}
