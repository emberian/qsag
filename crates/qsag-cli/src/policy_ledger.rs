//! Persistent custody policy ledger and the signing gate built on it.
//!
//! A ledger directory holds one authenticated root file, one committee checkpoint with its
//! generation fence, and one authenticated record per proposed intent:
//!
//! ```text
//! <ledger-dir>/                 owner-only
//!   ledger.json                 policy, committee, sealed provisioning seed (vault-locked)
//!   guards/committee.ckpt       every party's durable guard checkpoint: window, spend,
//!                               burned intent nonces and sessions, retired barrier slots
//!   guards/committee.fence      FsPolicyGenerationFence: monotone checkpoint generation
//!   intents/<intent-id>.json    proposed intent and its recorded approvals
//! ```
//!
//! All guard checkpoints are replaced together by one rename, so an interrupted release
//! leaves either every approving guard burned or none of them. The guards are the authority
//! on what was released: an intent whose nonce they have burned is spent whatever its record
//! says.
//!
//! Custody model: every guard share is derived from the one provisioning seed in `ledger.json`,
//! so the committee lives on a single host. The ledger gives durable, replay-proof,
//! velocity-capped authorization across invocations; it does not give separation between the
//! approving parties. With `--anchor-dir` the fence generation is also ratcheted in an
//! external monotone anchor, so restoring an old copy of the whole ledger directory is refused.
//!
//! Capacity: a guard share carries 64 single-use barrier slots, so one ledger authorizes at
//! most 64 intents per approving party.

use std::path::Path;

use qsag_accel::ct::ct_eq_bytes;
use qsag_accel::keccak::cshake256_framed_32;
use qsag_addr::{QsagAddress, WitnessSuiteTag};
use qsag_policy::{
    AuthorizedSignReleaseToken, BDOZ_PREPROC_SLOTS, FsPolicyGenerationFence, InitiatorPeerMac,
    PolicySignerGuardShare, PolicyViolation, QuorumTierRule, SigningPayloadBinding,
    TransactionIntent, TransactionPolicy, WindowAdvanceAuthorization,
    trusted_dealer_setup_for_testing,
};

use crate::anchor::{AnchorConfig, FsExternalMountAnchor};
use crate::cli::{
    Args, CliError, MAX_KEY_FILE_BYTES, Secret32, ZeroizingBuf, exit, os_random_32, private_dir,
    read_bounded_file, read_input, read_text, replace_secret, write_new,
};
use crate::codec::{Json, from_hex_exact, to_hex};
use crate::vault::{Vault, set};

const ROOT_FORMAT: &str = "qsag-policy-ledger-v1";
const ROOT_SCHEME: &str = "policy-guard-ledger";
const POLICY_FORMAT: &str = "qsag-policy-v1";
const INTENT_FORMAT: &str = "qsag-policy-intent-v1";
const CUSTODY_MODEL: &str = "single-host guard committee derived from one provisioning seed";
const ANCHOR_DOMAIN: &str = "policy_fence";
const ANCHOR_SEAL_FIELD: &str = "anchor_fence_seal";
const BUNDLE_MAGIC: &[u8; 8] = b"QSAGPLB1";
const BUNDLE_DOMAIN: &[u8] = b"QSAG.CLI.POLICY.COMMITTEE_CHECKPOINT.V1";
const MAX_BUNDLE_BYTES: u64 = 4 * 1024 * 1024;
const POLICY_REVISION: u64 = 1;
const DEFAULT_INTENT_TTL_SECS: u64 = 86_400;
/// How far an intent timestamp may run ahead of the local clock.
const CLOCK_SKEW_SECS: u64 = 60;
const MAX_PARTIES: usize = 16;
const MAX_ALLOWLIST: usize = 1024;
const MAX_TIERS: usize = 16;
const STATE_PROPOSED: &str = "proposed";
const STATE_RELEASED: &str = "released";
/// Field of a secret key file that pins the key to one policy ledger.
pub const KEY_PIN_FIELD: &str = "policy_ledger_id";

/// Options of `sign`, `quorum sign` and the key generators that select a policy ledger.
pub const GATE_VALUE_OPTIONS: [&str; 5] = [
    "policy-ledger-dir",
    "policy-intent",
    "policy-anchor-dir",
    "policy-passphrase-env",
    "policy-passphrase-file",
];
pub const GATE_FLAG_OPTIONS: [&str; 1] = ["policy-allow-single-disk-anchor"];

pub const GATE_HELP: &str = "\
  --policy-ledger-dir <dir>   enforce the custody policy ledger in <dir> before any key state moves
  --policy-intent <id>        the proposed and approved intent this signature releases
  --policy-anchor-dir <dir>   the ledger's external monotone anchor (required if enrolled with one)
  --policy-allow-single-disk-anchor  permit that anchor on the ledger's filesystem device
  --policy-passphrase-env <VAR> / --policy-passphrase-file <PATH>  unlock a sealed ledger
";

fn denied(reason: impl std::fmt::Display) -> CliError {
    CliError::new(
        exit::POLICY_DENIED,
        format!("policy denied the request: {reason}"),
    )
}

fn violation(v: PolicyViolation) -> CliError {
    denied(format_args!("{v:?}"))
}

fn rolled_back(what: impl std::fmt::Display) -> CliError {
    CliError::state(format!("CorruptOrRolledBackPolicyLedger: {what}"))
}

pub fn unix_now() -> Result<u64, CliError> {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs())
        .map_err(|_| CliError::state("system clock is before the Unix epoch"))
}

/// The identifier an intent binds a signing key by: the scheme name and the public key bytes.
pub fn signing_key_id(scheme: &str, public_key: &[u8]) -> [u8; 32] {
    cshake256_framed_32(
        b"QSAG.CLI.POLICY.KEY_ID.V1",
        &[scheme.as_bytes(), public_key],
    )
}

fn join(dir: &str, parts: &[&str]) -> Result<String, CliError> {
    let mut path = Path::new(dir).to_path_buf();
    for part in parts {
        path.push(part);
    }
    path.to_str()
        .map(str::to_owned)
        .ok_or_else(|| CliError::usage("ledger path is not UTF-8"))
}

fn root_path(dir: &str) -> Result<String, CliError> {
    join(dir, &["ledger.json"])
}

fn bundle_path(dir: &str) -> Result<String, CliError> {
    join(dir, &["guards", "committee.ckpt"])
}

fn fence_path(dir: &str) -> Result<String, CliError> {
    join(dir, &["guards", "committee.fence"])
}

fn intent_path(dir: &str, id: &[u8; 32]) -> Result<String, CliError> {
    join(dir, &["intents", &format!("{}.json", to_hex(id))])
}

fn party_secret(seed: &Secret32, label: &[u8], party: u16) -> Secret32 {
    Secret32(cshake256_framed_32(
        b"QSAG.CLI.POLICY.LEDGER.KDF.V1",
        &[&seed.0, label, &party.to_be_bytes()],
    ))
}

fn suite_name(tag: WitnessSuiteTag) -> String {
    format!("{tag:?}")
}

fn suite_by_name(name: &str) -> Result<WitnessSuiteTag, CliError> {
    (0x0100u16..=0x06FF)
        .filter_map(|v| WitnessSuiteTag::from_u16(v).ok())
        .find(|tag| suite_name(*tag) == name)
        .ok_or_else(|| CliError::input(format!("unknown witness suite '{name}'")))
}

fn party_list(json: &Json, key: &str) -> Result<Vec<u16>, CliError> {
    let bad = || CliError::input(format!("\"{key}\" must be an array of party identifiers"));
    json.get(key)
        .and_then(Json::as_array)
        .ok_or_else(bad)?
        .iter()
        .map(|item| {
            item.as_u64()
                .and_then(|v| u16::try_from(v).ok())
                .ok_or_else(bad)
        })
        .collect()
}

fn parse_party_csv(text: &str, what: &str) -> Result<Vec<u16>, CliError> {
    let mut ids = text
        .split(',')
        .map(|item| {
            item.trim()
                .parse::<u16>()
                .map_err(|_| CliError::usage(format!("{what} must be comma-separated party ids")))
        })
        .collect::<Result<Vec<u16>, CliError>>()?;
    let listed = ids.len();
    ids.sort_unstable();
    ids.dedup();
    if ids.len() != listed {
        return Err(CliError::usage(format!("{what} lists a party twice")));
    }
    Ok(ids)
}

fn party_json(ids: &[u16]) -> Json {
    Json::Array(ids.iter().map(|id| Json::num(*id)).collect())
}

fn bool_field(json: &Json, key: &str) -> Result<bool, CliError> {
    match json.get(key) {
        Some(Json::Bool(flag)) => Ok(*flag),
        _ => Err(CliError::input(format!(
            "missing or non-boolean field \"{key}\""
        ))),
    }
}

/// The committee and timing parameters fixed when a ledger is created.
struct Committee {
    parties: Vec<u16>,
    /// Length of one velocity window in seconds; zero keeps a single window for the ledger's life.
    window_secs: u64,
    intent_ttl_secs: u64,
}

fn policy_from_json(json: &Json) -> Result<(TransactionPolicy, Committee), CliError> {
    if json.field_str("format")? != POLICY_FORMAT {
        return Err(CliError::input(format!(
            "policy is not a {POLICY_FORMAT} document"
        )));
    }
    let allow = json
        .get("recipient_allowlist")
        .and_then(Json::as_array)
        .ok_or_else(|| CliError::input("\"recipient_allowlist\" must be an array of addresses"))?;
    if allow.is_empty() || allow.len() > MAX_ALLOWLIST {
        return Err(CliError::input(
            "recipient_allowlist must hold 1..=1024 addresses",
        ));
    }
    let suite = suite_by_name(json.field_str("suite")?)?;
    let mut recipient_allowlist = Vec::with_capacity(allow.len());
    for item in allow {
        let text = item
            .as_str()
            .ok_or_else(|| CliError::input("recipient_allowlist entries must be addresses"))?;
        let address = QsagAddress::decode(text)
            .map_err(|e| CliError::input(format!("allowlisted address rejected: {e:?}")))?;
        if address.suite_tag != suite {
            return Err(CliError::input(
                "allowlisted address does not use the policy's pinned suite",
            ));
        }
        recipient_allowlist.push(address.commitment_256);
    }
    let tiers = json
        .get("quorum_tiers")
        .and_then(Json::as_array)
        .ok_or_else(|| CliError::input("\"quorum_tiers\" must be an array"))?;
    if tiers.is_empty() || tiers.len() > MAX_TIERS {
        return Err(CliError::input("quorum_tiers must hold 1..=16 tiers"));
    }
    let mut quorum_tiers = Vec::with_capacity(tiers.len());
    for tier in tiers {
        let min_approvers = u16::try_from(tier.field_u64("min_approvers")?)
            .map_err(|_| CliError::input("min_approvers out of range"))?;
        if min_approvers < 2 {
            return Err(CliError::input(
                "every quorum tier needs at least two approvers",
            ));
        }
        quorum_tiers.push(QuorumTierRule {
            max_amount_units: tier.field_u128("max_amount_units")?,
            min_approvers,
            require_hardware_guardian: bool_field(tier, "require_hardware_guardian")?,
        });
    }
    if quorum_tiers
        .windows(2)
        .any(|w| w[0].max_amount_units >= w[1].max_amount_units)
    {
        return Err(CliError::input(
            "quorum_tiers must be listed by strictly increasing max_amount_units",
        ));
    }
    let hardware_guardian_party = match json.get("hardware_guardian_party") {
        None | Some(Json::Null) => None,
        Some(value) => Some(
            value
                .as_u64()
                .and_then(|v| u16::try_from(v).ok())
                .ok_or_else(|| CliError::input("hardware_guardian_party must be a party id"))?,
        ),
    };
    let mut parties = party_list(json, "parties")?;
    let listed = parties.len();
    parties.sort_unstable();
    parties.dedup();
    if parties.len() != listed || !(2..=MAX_PARTIES).contains(&listed) {
        return Err(CliError::input(
            "parties must hold 2..=16 distinct party ids",
        ));
    }
    if hardware_guardian_party.is_some_and(|g| !parties.contains(&g)) {
        return Err(CliError::input(
            "hardware_guardian_party is not a committee party",
        ));
    }
    let policy = TransactionPolicy {
        chain_id: json.field_u64("chain_id")?,
        pinned_suite: suite,
        recipient_allowlist,
        max_single_tx_amount: json.field_u128("max_single_tx_amount")?,
        velocity_window_cap: json.field_u128("velocity_window_cap")?,
        valid_not_before_secs: json.field_u64("valid_not_before_secs")?,
        valid_not_after_secs: json.field_u64("valid_not_after_secs")?,
        forbid_initiator_self_approval: bool_field(json, "forbid_initiator_self_approval")?,
        hardware_guardian_party,
        quorum_tiers,
    };
    if policy.valid_not_before_secs > policy.valid_not_after_secs {
        return Err(CliError::input("policy validity interval is empty"));
    }
    let optional = |key: &str, default: u64| match json.get(key) {
        None => Ok(default),
        Some(_) => json.field_u64(key),
    };
    let committee = Committee {
        parties,
        window_secs: optional("window_secs", 0)?,
        intent_ttl_secs: optional("intent_ttl_secs", DEFAULT_INTENT_TTL_SECS)?,
    };
    if committee.intent_ttl_secs == 0 {
        return Err(CliError::input("intent_ttl_secs must be positive"));
    }
    Ok((policy, committee))
}

/// The canonical stored form: allowlist entries are kept as their 32-byte commitments.
fn policy_to_json(policy: &TransactionPolicy, committee: &Committee) -> Json {
    let mut members = vec![
        ("chain_id", Json::num(policy.chain_id)),
        ("suite", Json::str(suite_name(policy.pinned_suite))),
        (
            "recipient_commitments",
            Json::Array(
                policy
                    .recipient_allowlist
                    .iter()
                    .map(|c| Json::hex(c))
                    .collect(),
            ),
        ),
        (
            "max_single_tx_amount",
            Json::num(policy.max_single_tx_amount),
        ),
        ("velocity_window_cap", Json::num(policy.velocity_window_cap)),
        (
            "valid_not_before_secs",
            Json::num(policy.valid_not_before_secs),
        ),
        (
            "valid_not_after_secs",
            Json::num(policy.valid_not_after_secs),
        ),
        (
            "forbid_initiator_self_approval",
            Json::Bool(policy.forbid_initiator_self_approval),
        ),
    ];
    if let Some(guardian) = policy.hardware_guardian_party {
        members.push(("hardware_guardian_party", Json::num(guardian)));
    }
    members.push((
        "quorum_tiers",
        Json::Array(
            policy
                .quorum_tiers
                .iter()
                .map(|tier| {
                    Json::object(vec![
                        ("max_amount_units", Json::num(tier.max_amount_units)),
                        ("min_approvers", Json::num(tier.min_approvers)),
                        (
                            "require_hardware_guardian",
                            Json::Bool(tier.require_hardware_guardian),
                        ),
                    ])
                })
                .collect(),
        ),
    ));
    members.push(("parties", party_json(&committee.parties)));
    members.push(("window_secs", Json::num(committee.window_secs)));
    members.push(("intent_ttl_secs", Json::num(committee.intent_ttl_secs)));
    Json::object(members)
}

fn stored_policy(json: &Json) -> Result<(TransactionPolicy, Committee), CliError> {
    let corrupt = || rolled_back("stored policy is malformed");
    let commitments = json
        .get("recipient_commitments")
        .and_then(Json::as_array)
        .ok_or_else(corrupt)?;
    let mut recipient_allowlist = Vec::with_capacity(commitments.len());
    for item in commitments {
        recipient_allowlist.push(
            from_hex_exact(item.as_str().ok_or_else(corrupt)?, "recipient commitment")
                .map_err(|_| corrupt())?,
        );
    }
    let mut quorum_tiers = Vec::new();
    for tier in json
        .get("quorum_tiers")
        .and_then(Json::as_array)
        .ok_or_else(corrupt)?
    {
        quorum_tiers.push(QuorumTierRule {
            max_amount_units: tier.field_u128("max_amount_units").map_err(|_| corrupt())?,
            min_approvers: u16::try_from(tier.field_u64("min_approvers").map_err(|_| corrupt())?)
                .map_err(|_| corrupt())?,
            require_hardware_guardian: bool_field(tier, "require_hardware_guardian")
                .map_err(|_| corrupt())?,
        });
    }
    let hardware_guardian_party = match json.get("hardware_guardian_party") {
        None => None,
        Some(value) => Some(
            value
                .as_u64()
                .and_then(|v| u16::try_from(v).ok())
                .ok_or_else(corrupt)?,
        ),
    };
    let field = |key: &str| json.field_u64(key).map_err(|_| corrupt());
    let wide = |key: &str| json.field_u128(key).map_err(|_| corrupt());
    let policy = TransactionPolicy {
        chain_id: field("chain_id")?,
        pinned_suite: suite_by_name(json.field_str("suite").map_err(|_| corrupt())?)
            .map_err(|_| corrupt())?,
        recipient_allowlist,
        max_single_tx_amount: wide("max_single_tx_amount")?,
        velocity_window_cap: wide("velocity_window_cap")?,
        valid_not_before_secs: field("valid_not_before_secs")?,
        valid_not_after_secs: field("valid_not_after_secs")?,
        forbid_initiator_self_approval: bool_field(json, "forbid_initiator_self_approval")
            .map_err(|_| corrupt())?,
        hardware_guardian_party,
        quorum_tiers,
    };
    let committee = Committee {
        parties: party_list(json, "parties").map_err(|_| corrupt())?,
        window_secs: field("window_secs")?,
        intent_ttl_secs: field("intent_ttl_secs")?,
    };
    if committee.parties.len() < 2
        || committee.parties.len() > MAX_PARTIES
        || committee.parties.windows(2).any(|w| w[0] >= w[1])
    {
        return Err(corrupt());
    }
    Ok((policy, committee))
}

/// Binds the provisioning seed, the policy and the committee into one public identifier.
fn ledger_id(
    seed: &Secret32,
    policy: &TransactionPolicy,
    committee: &Committee,
    nonce: &[u8],
) -> [u8; 32] {
    let commitment = Secret32(cshake256_framed_32(
        b"QSAG.CLI.POLICY.LEDGER_ID.SEED.V1",
        &[&seed.0],
    ));
    let mut parties = Vec::with_capacity(committee.parties.len() * 2);
    for party in &committee.parties {
        parties.extend_from_slice(&party.to_be_bytes());
    }
    cshake256_framed_32(
        b"QSAG.CLI.POLICY.LEDGER_ID.V1",
        &[
            &commitment.0,
            &policy.canonical_digest(),
            &parties,
            &committee.window_secs.to_be_bytes(),
            &committee.intent_ttl_secs.to_be_bytes(),
            nonce,
        ],
    )
}

/// Whether the ledger was enrolled with an external anchor, checked against the options given.
fn anchor_enrolled(root: &Json, supplied: bool) -> Result<bool, CliError> {
    let required = match root.get("anchor_required") {
        None => false,
        Some(Json::Bool(flag)) => *flag,
        Some(_) => return Err(rolled_back("anchor requirement is malformed")),
    };
    match (required, supplied) {
        (true, false) => Err(CliError::state(
            "policy ledger was enrolled with an external anchor; its anchor directory is required",
        )),
        (false, true) => Err(CliError::state(
            "policy ledger was not enrolled with an external anchor",
        )),
        (flag, _) => Ok(flag),
    }
}

/// Every party's exported guard checkpoint at one generation, under one MAC.
fn encode_bundle(
    key: &Secret32,
    ledger: &[u8; 32],
    generation: u64,
    checkpoints: &[(u16, Vec<u8>)],
) -> Vec<u8> {
    let mut out = BUNDLE_MAGIC.to_vec();
    out.extend_from_slice(ledger);
    out.extend_from_slice(&generation.to_be_bytes());
    out.extend_from_slice(&(checkpoints.len() as u16).to_be_bytes());
    for (party, bytes) in checkpoints {
        out.extend_from_slice(&party.to_be_bytes());
        out.extend_from_slice(&(bytes.len() as u32).to_be_bytes());
        out.extend_from_slice(bytes);
    }
    let tag = cshake256_framed_32(BUNDLE_DOMAIN, &[&key.0, &out]);
    out.extend_from_slice(&tag);
    out
}

/// A decoded committee checkpoint: its generation and each party's guard checkpoint.
#[derive(Debug, PartialEq)]
struct Bundle<'a> {
    generation: u64,
    checkpoints: Vec<(u16, &'a [u8])>,
}

fn decode_bundle<'a>(
    key: &Secret32,
    ledger: &[u8; 32],
    bytes: &'a [u8],
) -> Result<Bundle<'a>, CliError> {
    let bad = || rolled_back("committee checkpoint is malformed");
    let split = bytes.len().checked_sub(32).ok_or_else(bad)?;
    let (body, tag) = bytes.split_at(split);
    if !ct_eq_bytes(&cshake256_framed_32(BUNDLE_DOMAIN, &[&key.0, body]), tag) {
        return Err(rolled_back("committee checkpoint failed authentication"));
    }
    let mut rest = body;
    let mut take = |n: usize| -> Result<&'a [u8], CliError> {
        let (head, tail) = rest.split_at_checked(n).ok_or_else(bad)?;
        rest = tail;
        Ok(head)
    };
    if take(8)? != BUNDLE_MAGIC || !ct_eq_bytes(take(32)?, ledger) {
        return Err(bad());
    }
    let generation = u64::from_be_bytes(take(8)?.try_into().map_err(|_| bad())?);
    let count = u16::from_be_bytes(take(2)?.try_into().map_err(|_| bad())?);
    let mut checkpoints = Vec::with_capacity(count as usize);
    for _ in 0..count {
        let party = u16::from_be_bytes(take(2)?.try_into().map_err(|_| bad())?);
        let len = u32::from_be_bytes(take(4)?.try_into().map_err(|_| bad())?);
        checkpoints.push((party, take(len as usize)?));
    }
    if !rest.is_empty() {
        return Err(bad());
    }
    Ok(Bundle {
        generation,
        checkpoints,
    })
}

fn anchor_config(
    args: &Args,
    dir: &str,
    dir_option: &str,
    flag: &str,
) -> Result<Option<AnchorConfig>, CliError> {
    let anchor_dir = args.get(dir_option).map(str::to_owned);
    let allow_single_disk = args.flag(flag);
    if anchor_dir.is_none() && allow_single_disk {
        return Err(CliError::usage(format!("--{flag} requires --{dir_option}")));
    }
    Ok(anchor_dir.map(|anchor_dir| AnchorConfig {
        anchor_dir,
        vault_dir: Some(dir.to_owned()),
        allow_single_disk,
    }))
}

/// Provision the committee's guard shares from the ledger seed. The same seed always yields
/// the same shares, which is what lets a later invocation restore their durable checkpoints.
fn provision_guards(
    seed: &Secret32,
    ledger: &[u8; 32],
    parties: &[u16],
) -> Result<Vec<PolicySignerGuardShare>, CliError> {
    let entropy = party_secret(seed, b"guard dealer entropy", 0);
    let authority = party_secret(seed, b"window authority", 0);
    trusted_dealer_setup_for_testing(entropy.0, parties)
        .into_iter()
        .map(|guard| {
            guard
                .with_window_authority(*ledger, authority.0)
                .map_err(|e| CliError::state(format!("provisioning policy guard failed: {e:?}")))
        })
        .collect()
}

fn write_bundle(
    seed: &Secret32,
    ledger: &[u8; 32],
    generation: u64,
    guards: &[PolicySignerGuardShare],
) -> Vec<u8> {
    let checkpoints: Vec<(u16, Vec<u8>)> = guards
        .iter()
        .map(|guard| {
            let key = party_secret(seed, b"guard checkpoint key", guard.party_id);
            (
                guard.party_id,
                guard.export_durable_checkpoint(&key.0, generation),
            )
        })
        .collect();
    encode_bundle(
        &party_secret(seed, b"committee checkpoint mac", 0),
        ledger,
        generation,
        &checkpoints,
    )
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Access {
    /// Authenticate and report; never write.
    Inspect,
    /// Recover interrupted writes and permit new ones.
    Update,
}

/// An authenticated, exclusively locked policy ledger with every guard share restored.
pub struct OpenLedger {
    dir: String,
    _vault: Vault,
    id: [u8; 32],
    policy: TransactionPolicy,
    committee: Committee,
    seed: Secret32,
    guards: Vec<PolicySignerGuardShare>,
    /// Generation of the committee checkpoint on disk.
    generation: u64,
    fence: FsPolicyGenerationFence,
    anchor: Option<FsExternalMountAnchor>,
}

impl OpenLedger {
    fn open(
        dir: &str,
        passphrase: Option<&[u8]>,
        anchor_cfg: Option<&AnchorConfig>,
        access: Access,
    ) -> Result<Self, CliError> {
        private_dir(dir, false)?;
        for sub in ["guards", "intents"] {
            private_dir(&join(dir, &[sub])?, false)?;
        }
        let root = root_path(dir)?;
        let mut vault = Vault::acquire(&root, false)?;
        let text = read_text(&root)?;
        let on_disk = Json::parse(&text)?;
        if on_disk.field_str("format")? != ROOT_FORMAT
            || on_disk.field_str("scheme")? != ROOT_SCHEME
        {
            return Err(CliError::input(format!(
                "{root} is not a {ROOT_FORMAT} file"
            )));
        }
        let opened = crate::envelope::open(&on_disk, passphrase)?;
        vault.set_key_material(&opened);
        vault.authenticate(&on_disk)?;
        let anchored = anchor_enrolled(&on_disk, anchor_cfg.is_some())?;
        let seed = opened.seed()?;
        let (policy, committee) = stored_policy(
            on_disk
                .get("policy")
                .ok_or_else(|| rolled_back("stored policy is missing"))?,
        )?;
        let nonce = on_disk.field_hex("enrollment_nonce")?;
        let id = ledger_id(&seed, &policy, &committee, &nonce);
        let recorded: [u8; 32] = from_hex_exact(on_disk.field_str("ledger_id")?, "ledger_id")?;
        if !ct_eq_bytes(&id, &recorded) {
            return Err(rolled_back("ledger identifier does not match its contents"));
        }
        let mut fence = FsPolicyGenerationFence::open_existing(
            fence_path(dir)?,
            party_secret(&seed, b"fence key", 0).0,
        )
        .map_err(|e| rolled_back(format_args!("generation fence: {e}")))?;
        let anchor = match (anchored, anchor_cfg) {
            (true, Some(cfg)) => {
                let anchor = FsExternalMountAnchor::open_existing(
                    cfg,
                    &[&root],
                    &[dir],
                    ANCHOR_DOMAIN,
                    id,
                    party_secret(&seed, b"fence anchor mac", 0).0,
                )?;
                anchor.verify_expected_seal(&on_disk, ANCHOR_SEAL_FIELD)?;
                anchor.verify_floor_at_least(ANCHOR_DOMAIN.as_bytes(), fence.generation())?;
                Some(anchor)
            }
            _ => None,
        };

        let bundle = read_bounded_file(&bundle_path(dir)?, MAX_BUNDLE_BYTES)
            .map_err(|e| rolled_back(format_args!("committee checkpoint: {}", e.message)))?;
        let bundle_key = party_secret(&seed, b"committee checkpoint mac", 0);
        let Bundle {
            generation,
            checkpoints,
        } = decode_bundle(&bundle_key, &id, &bundle)?;
        if generation < fence.generation() {
            return Err(rolled_back(
                "committee checkpoint is older than its generation fence",
            ));
        }
        let mut guards = provision_guards(&seed, &id, &committee.parties)?;
        if checkpoints.len() != guards.len() {
            return Err(rolled_back(
                "committee checkpoint does not cover the committee",
            ));
        }
        for (guard, (party, checkpoint)) in guards.iter_mut().zip(&checkpoints) {
            let restored = (*party == guard.party_id)
                .then(|| {
                    guard.restore_from_durable_checkpoint(
                        checkpoint,
                        &party_secret(&seed, b"guard checkpoint key", *party).0,
                        generation,
                    )
                })
                .and_then(Result::ok);
            if restored != Some(generation) || guard.is_poisoned() {
                return Err(rolled_back(format_args!(
                    "party {} guard checkpoint was refused",
                    guard.party_id
                )));
            }
        }
        if access == Access::Update {
            // A crash between the checkpoint rename and its fence leaves the fence behind.
            fence
                .ratchet_to(generation)
                .map_err(|e| rolled_back(format_args!("generation fence: {e}")))?;
            if let Some(anchor) = &anchor {
                anchor.advance_floor(ANCHOR_DOMAIN.as_bytes(), generation)?;
            }
        }
        Ok(Self {
            dir: dir.to_owned(),
            _vault: vault,
            id,
            policy,
            committee,
            seed,
            guards,
            generation,
            fence,
            anchor,
        })
    }

    pub fn id(&self) -> &[u8; 32] {
        &self.id
    }

    fn index_of(&self, party: u16) -> Result<usize, CliError> {
        self.committee
            .parties
            .iter()
            .position(|p| *p == party)
            .ok_or_else(|| {
                CliError::usage(format!("party {party} is not in this ledger's committee"))
            })
    }

    /// Checkpoint every guard in one rename, then fence the new generation locally and in
    /// the external anchor. Nothing derived from the new state is released before this returns.
    fn persist(&mut self) -> Result<(), CliError> {
        let generation = self
            .generation
            .max(self.fence.generation())
            .checked_add(1)
            .ok_or_else(|| CliError::state("policy checkpoint generation exhausted"))?;
        let bundle = write_bundle(&self.seed, &self.id, generation, &self.guards);
        replace_secret(&bundle_path(&self.dir)?, &bundle)?;
        self.generation = generation;
        self.fence
            .ratchet_to(generation)
            .map_err(|e| CliError::io("ratcheting policy generation fence", e))?;
        if let Some(anchor) = &self.anchor {
            anchor.advance_floor(ANCHOR_DOMAIN.as_bytes(), generation)?;
        }
        Ok(())
    }

    fn current_window(&self) -> u64 {
        self.guards
            .iter()
            .map(PolicySignerGuardShare::current_window_id)
            .max()
            .unwrap_or(0)
    }

    /// Bring every guard to the velocity window `now` falls in. Windows only move forward:
    /// a clock that runs backwards leaves the committee in its newest window.
    fn sync_window(&mut self, now: u64) -> Result<(), CliError> {
        let by_clock = now.checked_div(self.committee.window_secs).unwrap_or(0);
        let target = self.current_window().max(by_clock);
        let authority = party_secret(&self.seed, b"window authority", 0);
        let mut moved = false;
        for guard in &mut self.guards {
            let current = guard.current_window_id();
            if current >= target {
                continue;
            }
            let authorization =
                WindowAdvanceAuthorization::new(&authority.0, &self.id, current, target);
            guard
                .advance_velocity_window(&authorization)
                .map_err(|e| CliError::state(format!("advancing velocity window failed: {e:?}")))?;
            moved = true;
        }
        if moved {
            self.persist()?;
        }
        Ok(())
    }

    /// Whether the guards have burned this intent. They are the authority: a record that
    /// says otherwise, in either direction, is not believed.
    fn is_burned(&self, intent: &TransactionIntent) -> bool {
        self.guards
            .iter()
            .any(|guard| guard.is_nonce_burned(&intent.nonce))
    }

    /// The window spend the listed parties jointly account for. A quorum the policy accepts
    /// contains the accounting guardian or the whole committee, so this is the committee's spend.
    fn window_spend(&self, parties: &[u16]) -> Result<u128, CliError> {
        let mut spend = 0;
        for party in parties {
            spend = self.guards[self.index_of(*party)?]
                .accumulated_window_spend()
                .max(spend);
        }
        Ok(spend)
    }

    fn record_key(&self) -> Secret32 {
        party_secret(&self.seed, b"intent record mac", 0)
    }

    fn record_mac(&self, record: &Json) -> [u8; 32] {
        let mut unsigned = record.clone();
        if let Json::Object(fields) = &mut unsigned {
            fields.retain(|(name, _)| name != "record_mac");
        }
        cshake256_framed_32(
            b"QSAG.CLI.POLICY.INTENT_RECORD.V1",
            &[
                &self.record_key().0,
                &self.id,
                unsigned.to_pretty().as_bytes(),
            ],
        )
    }

    fn load_record(&self, id: &[u8; 32]) -> Result<IntentRecord, CliError> {
        let path = intent_path(&self.dir, id)?;
        if std::fs::symlink_metadata(&path).is_err() {
            return Err(denied(format_args!(
                "intent {} was never proposed to this ledger",
                to_hex(id)
            )));
        }
        let bytes = read_bounded_file(&path, MAX_KEY_FILE_BYTES)?;
        let json = Json::parse(
            std::str::from_utf8(&bytes.0).map_err(|_| rolled_back("intent record is not UTF-8"))?,
        )
        .map_err(|_| rolled_back("intent record is malformed"))?;
        let recorded = json
            .field_hex("record_mac")
            .map_err(|_| rolled_back("intent record is unauthenticated"))?;
        if !ct_eq_bytes(&recorded, &self.record_mac(&json)) {
            return Err(rolled_back("intent record failed authentication"));
        }
        let record = IntentRecord::from_json(&json)?;
        if !ct_eq_bytes(&record.intent.canonical_digest(), id) {
            return Err(rolled_back("intent record does not match its identifier"));
        }
        Ok(record)
    }

    fn store_record(&self, record: &IntentRecord, create: bool) -> Result<(), CliError> {
        let id = record.intent.canonical_digest();
        let mut json = record.to_json(&self.id)?;
        let mac = self.record_mac(&json);
        set(&mut json, "record_mac", Json::hex(&mac));
        let path = intent_path(&self.dir, &id)?;
        let bytes = json.to_pretty();
        if create {
            write_new(&path, bytes.as_bytes(), true)
        } else {
            replace_secret(&path, bytes.as_bytes())
        }
    }

    /// Build, policy-check and record a new intent. Nothing in the guards moves.
    fn propose(
        &mut self,
        request: &Proposal<'_>,
        now: u64,
    ) -> Result<(IntentRecord, Vec<u8>), CliError> {
        self.sync_window(now)?;
        let initiator = self.index_of(request.initiator)?;
        for party in request.approvers {
            self.index_of(*party)?;
        }
        // Per-party ledgers see the committee's whole window spend only through a quorum that
        // contains the accounting guardian or every party; the guards refuse any other.
        let accounted = self.policy.velocity_window_cap == u128::MAX
            || request.approvers.len() == self.committee.parties.len()
            || self
                .policy
                .hardware_guardian_party
                .is_some_and(|guardian| request.approvers.contains(&guardian));
        if !accounted {
            return Err(violation(PolicyViolation::MissingHardwareGuardian));
        }
        let spend = self.window_spend(request.approvers)?;
        let window = self.current_window();
        let accumulator = cshake256_framed_32(
            b"QSAG.CLI.POLICY.WINDOW_STATE.V1",
            &[&self.id, &window.to_be_bytes(), &spend.to_be_bytes()],
        );
        let (mut intent, _) = TransactionIntent::builder(
            self.policy.chain_id,
            self.policy.pinned_suite,
            request.recipient.clone(),
            request.amount_units,
        )
        .rolling_window(spend, accumulator)
        .window_id(window)
        .timestamp_secs(now)
        .initiator_and_approvers(request.initiator, request.approvers)
        .bind_signing_payload(
            &SigningPayloadBinding {
                key_id: request.key_id,
                payload: request.payload,
                ctx: request.ctx,
                session_id: os_random_32()?,
                policy_revision: POLICY_REVISION,
                quorum: request.approvers,
                authority_pk: self.id,
            },
            &self.policy,
        )
        .map_err(violation)?;
        let signing_bytes = self.guards[initiator]
            .authenticate_initiated_intent(&self.policy, &mut intent)
            .map_err(violation)?;
        let record = IntentRecord {
            intent,
            approvals: Vec::new(),
        };
        self.store_record(&record, true)?;
        Ok((record, signing_bytes))
    }

    fn approve(&mut self, id: &[u8; 32], party: u16) -> Result<IntentRecord, CliError> {
        self.index_of(party)?;
        let mut record = self.load_record(id)?;
        if self.is_burned(&record.intent) {
            return Err(denied("intent was already released"));
        }
        if !record.intent.approver_parties.contains(&party) {
            return Err(denied(format_args!(
                "party {party} is not an approver of this intent"
            )));
        }
        self.policy.evaluate(&record.intent).map_err(violation)?;
        if !record.approvals.contains(&party) {
            record.approvals.push(party);
            record.approvals.sort_unstable();
            self.store_record(&record, false)?;
        }
        Ok(record)
    }

    /// Release one intent for exactly this key, message and context. Every refusal happens
    /// before anything durable moves; on success the spend, the intent nonce and the session
    /// are burned in every approving guard and fenced before this returns.
    fn authorize(
        &mut self,
        id: &[u8; 32],
        key_id: &[u8; 32],
        message: &[u8],
        ctx: &[u8],
        retry: bool,
        now: u64,
    ) -> Result<Authorization, CliError> {
        let record = self.load_record(id)?;
        let intent = &record.intent;
        let policy_digest = self.policy.canonical_digest();
        let bound = message == intent.to_canonical_signing_bytes(&policy_digest)
            && ct_eq_bytes(key_id, &intent.signing_key_id)
            && ct_eq_bytes(
                &cshake256_framed_32(b"QSAG.POLICY.CTX.V1", &[ctx]),
                &intent.signing_context_digest,
            )
            && ct_eq_bytes(&intent.guard_authority_pk, &self.id);
        if !bound {
            return Err(denied(
                "the key, message or context is not the one this intent authorizes",
            ));
        }
        let authorization = Authorization {
            policy_digest,
            intent_id: *id,
            amount_units: intent.amount_units,
        };
        if self.is_burned(intent) {
            // Resuming an interrupted signing re-signs the same bytes under the same key and
            // spends nothing new; that is the only way a released intent is honoured again.
            return if retry {
                Ok(authorization)
            } else {
                Err(violation(PolicyViolation::DuplicateIntentNonce))
            };
        }
        let missing: Vec<String> = intent
            .approver_parties
            .iter()
            .filter(|p| !record.approvals.contains(p))
            .map(u16::to_string)
            .collect();
        if !missing.is_empty() {
            return Err(denied(format_args!(
                "intent is unapproved: no recorded approval from party {}",
                missing.join(", ")
            )));
        }
        if intent.timestamp_secs > now.saturating_add(CLOCK_SKEW_SECS)
            || now.saturating_sub(intent.timestamp_secs) > self.committee.intent_ttl_secs
            || now > self.policy.valid_not_after_secs
        {
            return Err(violation(PolicyViolation::TimestampOutsideWindow));
        }
        let quorum: Vec<usize> = intent
            .approver_parties
            .iter()
            .map(|party| self.index_of(*party))
            .collect::<Result<_, _>>()?;
        self.sync_window(now)?;
        if intent.window_id != self.current_window() {
            return Err(violation(PolicyViolation::WindowIdMismatch));
        }
        let spend = self.window_spend(&intent.approver_parties)?;
        if intent.rolling_window_spent != spend {
            return Err(denied(format_args!(
                "intent was proposed against a window spend of {} but the ledger now records {spend}; propose it again",
                intent.rolling_window_spent
            )));
        }
        // A refusal inside the barrier leaves the checkpoint on disk untouched: the guards
        // that moved in memory are dropped with this handle.
        let tokens = run_barrier(&self.policy, &mut self.guards, &quorum, intent, spend)
            .map_err(violation)?;
        for token in &tokens {
            if !token.matches_signing_for_policy(
                key_id,
                message,
                ctx,
                &intent.quorum_ids,
                &policy_digest,
                &self.id,
            ) {
                return Err(CliError::verify(
                    "release token is not bound to the approved signing request",
                ));
            }
        }
        self.persist()?;
        Ok(authorization)
    }
}

/// The four-round committed MAC barrier among the approving guards. Each guard re-evaluates
/// the policy, authenticates the initiator, and checks the window, nonce and projected spend
/// against its own restored ledger before it commits.
fn run_barrier(
    policy: &TransactionPolicy,
    guards: &mut [PolicySignerGuardShare],
    quorum: &[usize],
    intent: &TransactionIntent,
    window_spend: u128,
) -> Result<Vec<AuthorizedSignReleaseToken>, PolicyViolation> {
    let mut round1 = Vec::with_capacity(quorum.len());
    let mut commits = Vec::with_capacity(quorum.len());
    for &index in quorum {
        let (state, commit) = guards[index].round1_commit_intent_authenticated(
            policy,
            intent,
            intent.session_id,
            intent.timestamp_secs,
            window_spend,
        )?;
        round1.push(state);
        commits.push(commit);
    }
    let mut round2 = Vec::with_capacity(quorum.len());
    let mut opens = Vec::with_capacity(quorum.len());
    for (state, &index) in round1.into_iter().zip(quorum) {
        let (state, open) = state.round2_open_delta(&mut guards[index], &commits)?;
        round2.push(state);
        opens.push(open);
    }
    let mut round3 = Vec::with_capacity(quorum.len());
    let mut sigma_commits = Vec::with_capacity(quorum.len());
    for (state, &index) in round2.into_iter().zip(quorum) {
        let (state, commit) = state.round3_commit_sigma(&mut guards[index], &opens)?;
        round3.push(state);
        sigma_commits.push(commit);
    }
    let mut round4 = Vec::with_capacity(quorum.len());
    let mut sigma_opens = Vec::with_capacity(quorum.len());
    for (state, &index) in round3.into_iter().zip(quorum) {
        let (state, open) = state.round4_open_sigma(&mut guards[index], &sigma_commits)?;
        round4.push(state);
        sigma_opens.push(open);
    }
    let mut tokens = Vec::with_capacity(quorum.len());
    for (state, &index) in round4.into_iter().zip(quorum) {
        tokens.push(state.finalize(&mut guards[index], &sigma_opens)?);
    }
    Ok(tokens)
}

struct Proposal<'a> {
    key_id: [u8; 32],
    payload: &'a [u8],
    ctx: &'a [u8],
    recipient: QsagAddress,
    amount_units: u128,
    initiator: u16,
    approvers: &'a [u16],
}

struct IntentRecord {
    intent: TransactionIntent,
    approvals: Vec<u16>,
}

impl IntentRecord {
    fn to_json(&self, ledger: &[u8; 32]) -> Result<Json, CliError> {
        let i = &self.intent;
        let recipient = i
            .recipient
            .encode()
            .map_err(|e| CliError::state(format!("recipient address encoding failed: {e:?}")))?;
        let macs = i
            .initiator_macs
            .iter()
            .map(|m| {
                Json::object(vec![
                    ("approver_party", Json::num(m.approver_party)),
                    ("mac_tag", Json::hex(&m.mac_tag)),
                ])
            })
            .collect();
        Ok(Json::object(vec![
            ("format", Json::str(INTENT_FORMAT)),
            ("ledger_id", Json::hex(ledger)),
            ("intent_id", Json::hex(&i.canonical_digest())),
            ("approvals", party_json(&self.approvals)),
            ("chain_id", Json::num(i.chain_id)),
            ("suite", Json::str(suite_name(i.suite))),
            ("recipient", Json::str(recipient)),
            ("amount_units", Json::num(i.amount_units)),
            ("rolling_window_spent", Json::num(i.rolling_window_spent)),
            ("window_id", Json::num(i.window_id)),
            ("nonce", Json::hex(&i.nonce)),
            ("timestamp_secs", Json::num(i.timestamp_secs)),
            ("initiator_party", Json::num(i.initiator_party)),
            ("initiator_macs", Json::Array(macs)),
            ("approver_parties", party_json(&i.approver_parties)),
            ("payload_digest", Json::hex(&i.payload_digest)),
            ("guard_authority", Json::hex(&i.guard_authority_pk)),
            (
                "rolling_window_accumulator",
                Json::hex(&i.rolling_window_accumulator),
            ),
            ("signing_key_id", Json::hex(&i.signing_key_id)),
            ("policy_revision", Json::num(i.policy_revision)),
            ("message_digest", Json::hex(&i.message_digest)),
            (
                "signing_context_digest",
                Json::hex(&i.signing_context_digest),
            ),
            ("session_id", Json::hex(&i.session_id)),
            ("quorum_ids", party_json(&i.quorum_ids)),
        ]))
    }

    fn from_json(json: &Json) -> Result<Self, CliError> {
        let corrupt = || rolled_back("intent record is malformed");
        let text = |key: &str| json.field_str(key).map_err(|_| corrupt());
        let digest = |key: &str| -> Result<[u8; 32], CliError> {
            from_hex_exact(text(key)?, key).map_err(|_| corrupt())
        };
        let number = |key: &str| json.field_u64(key).map_err(|_| corrupt());
        let party = |key: &str| u16::try_from(number(key)?).map_err(|_| corrupt());
        if text("format")? != INTENT_FORMAT {
            return Err(corrupt());
        }
        let mut initiator_macs = Vec::new();
        for item in json
            .get("initiator_macs")
            .and_then(Json::as_array)
            .ok_or_else(corrupt)?
        {
            initiator_macs.push(InitiatorPeerMac {
                approver_party: u16::try_from(
                    item.field_u64("approver_party").map_err(|_| corrupt())?,
                )
                .map_err(|_| corrupt())?,
                mac_tag: from_hex_exact(
                    item.field_str("mac_tag").map_err(|_| corrupt())?,
                    "mac_tag",
                )
                .map_err(|_| corrupt())?,
            });
        }
        let intent = TransactionIntent {
            chain_id: number("chain_id")?,
            suite: suite_by_name(text("suite")?).map_err(|_| corrupt())?,
            recipient: QsagAddress::decode(text("recipient")?).map_err(|_| corrupt())?,
            amount_units: json.field_u128("amount_units").map_err(|_| corrupt())?,
            rolling_window_spent: json
                .field_u128("rolling_window_spent")
                .map_err(|_| corrupt())?,
            window_id: number("window_id")?,
            nonce: digest("nonce")?,
            timestamp_secs: number("timestamp_secs")?,
            initiator_party: party("initiator_party")?,
            initiator_macs,
            approver_parties: party_list(json, "approver_parties").map_err(|_| corrupt())?,
            payload_digest: digest("payload_digest")?,
            guard_authority_pk: digest("guard_authority")?,
            rolling_window_accumulator: digest("rolling_window_accumulator")?,
            signing_key_id: digest("signing_key_id")?,
            policy_revision: number("policy_revision")?,
            message_digest: digest("message_digest")?,
            signing_context_digest: digest("signing_context_digest")?,
            session_id: digest("session_id")?,
            quorum_ids: party_list(json, "quorum_ids").map_err(|_| corrupt())?,
        };
        Ok(Self {
            intent,
            approvals: party_list(json, "approvals").map_err(|_| corrupt())?,
        })
    }
}

/// What a released intent commits the signing ceremony to.
