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
//! The enrollment policy selects `preprocessing_slots`; every slot remains single use.

use std::path::Path;

use qsag_accel::ct::ct_eq_bytes;
use qsag_accel::keccak::cshake256_framed_32;
use qsag_addr::{QsagAddress, WitnessSuiteTag};
use qsag_policy::{
    BDOZ_PREPROC_SLOTS, FsPolicyGenerationFence, InitiatorPeerMac, PolicySignerGuardShare,
    PolicyViolation, QuorumTierRule, SharedWindowSpendLedger, SigningPayloadBinding,
    TransactionIntent, TransactionPolicy, WindowAdvanceAuthorization,
    evaluate_policy_committed_barrier_with_ledger,
};

use crate::anchor::{
    AnchorConfig, AnchorRequirementError, FsExternalMountAnchor, anchor_requirement,
};
use crate::cli::{
    Args, CliError, MAX_KEY_FILE_BYTES, Secret32, ZeroizingBuf, exit, os_random_32, private_dir,
    read_bounded_file, read_input, read_text, replace_secret, write_new,
};
use crate::codec::{Json, from_hex_exact, to_hex};
use crate::dealerless_ceremony::provision_distributed_policy_guards_with_capacity;
use crate::vault::{Vault, set};

const ROOT_FORMAT: &str = "qsag-policy-ledger-v2";
const ROOT_SCHEME: &str = "policy-guard-ledger";
const POLICY_FORMAT: &str = "qsag-policy-v1";
const INTENT_FORMAT: &str = "qsag-policy-intent-v1";
const CUSTODY_MODEL: &str = "single-host guard committee derived from one provisioning seed";
const ANCHOR_DOMAIN: &str = "policy_fence";
const ANCHOR_SEAL_FIELD: &str = "anchor_fence_seal";
const BUNDLE_MAGIC: &[u8; 8] = b"QSAGPLB2";
const BUNDLE_DOMAIN: &[u8] = b"QSAG.CLI.POLICY.COMMITTEE_CHECKPOINT.V1";
const MAX_BUNDLE_BYTES: u64 = 256 * 1024 * 1024;
const POLICY_REVISION: u64 = 1;
const DEFAULT_INTENT_TTL_SECS: u64 = 86_400;
/// How far an intent timestamp may run ahead of the local clock.
const CLOCK_SKEW_SECS: u64 = 60;
const MAX_PARTIES: usize = 64;
const MAX_ALLOWLIST: usize = 1024;
const MAX_TIERS: usize = 64;
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
    Secret32::new(cshake256_framed_32(
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
    preprocessing_slots: usize,
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
        return Err(CliError::input("quorum_tiers must hold 1..=64 tiers"));
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
            "parties must hold 2..=64 distinct party ids",
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
        preprocessing_slots: usize::try_from(optional(
            "preprocessing_slots",
            BDOZ_PREPROC_SLOTS as u64,
        )?)
        .map_err(|_| CliError::input("preprocessing capacity does not fit usize"))?,
        parties,
        window_secs: optional("window_secs", 0)?,
        intent_ttl_secs: optional("intent_ttl_secs", DEFAULT_INTENT_TTL_SECS)?,
    };
    if committee.preprocessing_slots == 0
        || committee.preprocessing_slots > qsag_policy::MAX_POLICY_CAPACITY
    {
        return Err(CliError::input(
            "preprocessing_slots must be in 1..=1048576",
        ));
    }
    if committee.intent_ttl_secs == 0 {
        return Err(CliError::input("intent_ttl_secs must be positive"));
    }
    Ok((policy, committee))
}

/// The canonical stored form: allowlist entries are kept as their 32-byte commitments.
fn policy_to_json(policy: &TransactionPolicy, committee: &Committee) -> Json {
    let mut members = vec![
        (
            "preprocessing_slots",
            Json::num(committee.preprocessing_slots),
        ),
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
        preprocessing_slots: usize::try_from(field("preprocessing_slots")?)
            .map_err(|_| corrupt())?,
        parties: party_list(json, "parties").map_err(|_| corrupt())?,
        window_secs: field("window_secs")?,
        intent_ttl_secs: field("intent_ttl_secs")?,
    };
    if committee.preprocessing_slots == 0
        || committee.preprocessing_slots > qsag_policy::MAX_POLICY_CAPACITY
        || committee.parties.len() < 2
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
    let commitment = Secret32::new(cshake256_framed_32(
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
            &(committee.preprocessing_slots as u64).to_be_bytes(),
            nonce,
        ],
    )
}

/// Whether the ledger was enrolled with an external anchor, checked against the options given.
fn anchor_enrolled(root: &Json, supplied: bool) -> Result<bool, CliError> {
    anchor_requirement(root, supplied).map_err(|e| match e {
        AnchorRequirementError::Malformed => rolled_back("anchor requirement is malformed"),
        AnchorRequirementError::AnchorMissing => CliError::state(
            "policy ledger was enrolled with an external anchor; its anchor directory is required",
        ),
        AnchorRequirementError::NotEnrolled => {
            CliError::state("policy ledger was not enrolled with an external anchor")
        }
    })
}

/// Every party's exported guard checkpoint at one generation, under one MAC.
fn encode_bundle(
    key: &Secret32,
    ledger: &[u8; 32],
    generation: u64,
    checkpoints: &[(u16, Vec<u8>)],
    shared: &[u8],
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
    out.extend_from_slice(&(shared.len() as u32).to_be_bytes());
    out.extend_from_slice(shared);
    let tag = cshake256_framed_32(BUNDLE_DOMAIN, &[&key.0, &out]);
    out.extend_from_slice(&tag);
    out
}

/// A decoded committee checkpoint: its generation and each party's guard checkpoint.
#[derive(Debug, PartialEq)]
struct Bundle<'a> {
    generation: u64,
    checkpoints: Vec<(u16, &'a [u8])>,
    shared: &'a [u8],
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
    let len = u32::from_be_bytes(take(4)?.try_into().map_err(|_| bad())?) as usize;
    let shared = take(len)?;
    if !rest.is_empty() {
        return Err(bad());
    }
    Ok(Bundle {
        generation,
        checkpoints,
        shared,
    })
}

/// Provision the committee's guard shares from the ledger seed. The same seed always yields
/// the same shares, which is what lets a later invocation restore their durable checkpoints.
fn provision_guards(
    seed: &Secret32,
    ledger: &[u8; 32],
    parties: &[u16],
    slots: usize,
) -> Result<Vec<PolicySignerGuardShare>, CliError> {
    let entropy = party_secret(seed, b"guard dealer entropy", 0);
    let authority = party_secret(seed, b"window authority", 0);
    provision_distributed_policy_guards_with_capacity(entropy.0, parties, slots)
        .map_err(|e| CliError::state(format!("provisioning policy guard failed: {e:?}")))?
        .into_iter()
        .map(|guard| {
            guard
                .with_window_authority(*ledger, authority.0)
                .map_err(|e| CliError::state(format!("provisioning policy guard failed: {e:?}")))
        })
        .collect()
}

fn write_bundle<'a>(
    seed: &Secret32,
    ledger: &[u8; 32],
    generation: u64,
    guards: impl IntoIterator<Item = &'a PolicySignerGuardShare>,
    shared: &SharedWindowSpendLedger,
) -> Vec<u8> {
    let mut checkpoints: Vec<(u16, Vec<u8>)> = guards
        .into_iter()
        .map(|guard| {
            let key = party_secret(seed, b"guard checkpoint key", guard.party_id);
            (
                guard.party_id,
                guard.export_durable_checkpoint(&key.0, generation),
            )
        })
        .collect();
    checkpoints.sort_unstable_by_key(|c| c.0);
    encode_bundle(
        &party_secret(seed, b"committee checkpoint mac", 0),
        ledger,
        generation,
        &checkpoints,
        &shared.export_durable_checkpoint(&party_secret(seed, b"shared checkpoint key", 0).0),
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
    shared: SharedWindowSpendLedger,
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
            shared: shared_bytes,
        } = decode_bundle(&bundle_key, &id, &bundle)?;
        if generation < fence.generation() {
            return Err(rolled_back(
                "committee checkpoint is older than its generation fence",
            ));
        }
        let mut guards = provision_guards(
            &seed,
            &id,
            &committee.parties,
            committee.preprocessing_slots,
        )?;
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
        let mut shared = SharedWindowSpendLedger::new(&policy, 0)
            .with_window_authority(id, party_secret(&seed, b"window authority", 0).0)
            .map_err(violation)?;
        shared
            .restore_from_durable_checkpoint(
                shared_bytes,
                &party_secret(&seed, b"shared checkpoint key", 0).0,
                0,
            )
            .map_err(|_| rolled_back("shared accounting checkpoint refused"))?;
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
            shared,
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
        let bundle = write_bundle(&self.seed, &self.id, generation, &self.guards, &self.shared);
        if bundle.len() as u64 > MAX_BUNDLE_BYTES {
            return Err(CliError::state(
                "policy checkpoint exceeds the configured file budget",
            ));
        }
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
        if target > self.shared.current_window_id() {
            let authorization = WindowAdvanceAuthorization::new(
                &authority.0,
                &self.id,
                self.shared.current_window_id(),
                target,
            );
            self.shared
                .advance_velocity_window(&authorization)
                .map_err(violation)?;
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

    /// The shared accumulator is authoritative across every subset of the committee.
    fn window_spend(&self, parties: &[u16]) -> Result<u128, CliError> {
        for party in parties {
            self.index_of(*party)?;
        }
        Ok(self.shared.accumulated_window_spend())
    }

    fn record_key(&self) -> Secret32 {
        party_secret(&self.seed, b"intent record mac", 0)
    }

    fn record_mac(&self, record: &Json) -> [u8; 32] {
        let unsigned = crate::persist::authenticated_bytes(record, &["record_mac"]);
        cshake256_framed_32(
            b"QSAG.CLI.POLICY.INTENT_RECORD.V1",
            &[&self.record_key().0, &self.id, &unsigned],
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
        let (mut selected, others): (Vec<_>, Vec<_>) = std::mem::take(&mut self.guards)
            .into_iter()
            .partition(|g| intent.approver_parties.contains(&g.party_id));
        let generation = self
            .generation
            .checked_add(1)
            .ok_or_else(|| CliError::state("policy checkpoint generation exhausted"))?;
        let result = evaluate_policy_committed_barrier_with_ledger(
            &self.policy,
            intent,
            intent.session_id,
            intent.timestamp_secs,
            &mut selected,
            &mut self.shared,
            |shared, participating| {
                let bundle = write_bundle(
                    &self.seed,
                    &self.id,
                    generation,
                    participating.iter().chain(&others),
                    shared,
                );
                if bundle.len() as u64 > MAX_BUNDLE_BYTES {
                    return Err(PolicyViolation::LedgerPersistenceFailed);
                }
                replace_secret(
                    &bundle_path(&self.dir)
                        .map_err(|_| PolicyViolation::LedgerPersistenceFailed)?,
                    &bundle,
                )
                .map_err(|_| PolicyViolation::LedgerPersistenceFailed)?;
                self.fence
                    .ratchet_to(generation)
                    .map_err(|_| PolicyViolation::LedgerPersistenceFailed)?;
                if let Some(anchor) = &self.anchor {
                    anchor
                        .advance_floor(ANCHOR_DOMAIN.as_bytes(), generation)
                        .map_err(|_| PolicyViolation::LedgerPersistenceFailed)?;
                }
                Ok(())
            },
            &qsag_accel::CpuReferenceBackend::new(),
        );
        selected.extend(others);
        selected.sort_unstable_by_key(|g| g.party_id);
        self.guards = selected;
        let token = result.map_err(violation)?;
        self.generation = generation;
        let tokens = [token];
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
        Ok(authorization)
    }
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
pub struct Authorization {
    pub policy_digest: [u8; 32],
    pub intent_id: [u8; 32],
    pub amount_units: u128,
}

/// The policy gate of one signing invocation. It holds the ledger's exclusive lock from the
/// moment the options are parsed until the signature has been written.
pub struct Gate {
    ledger: OpenLedger,
    intent: Option<[u8; 32]>,
}

impl Gate {
    /// `None` when the invocation names no policy ledger.
    pub fn from_args(args: &Args, needs_intent: bool) -> Result<Option<Self>, CliError> {
        let Some(dir) = args.get("policy-ledger-dir") else {
            let stray = GATE_VALUE_OPTIONS
                .iter()
                .find(|name| args.get(name).is_some())
                .or_else(|| GATE_FLAG_OPTIONS.iter().find(|name| args.flag(name)));
            return match stray {
                Some(name) => Err(CliError::usage(format!(
                    "--{name} requires --policy-ledger-dir"
                ))),
                None => Ok(None),
            };
        };
        let intent = match (args.get("policy-intent"), needs_intent) {
            (Some(hex), true) => Some(from_hex_exact(hex, "--policy-intent")?),
            (None, true) => {
                return Err(CliError::usage(
                    "--policy-ledger-dir requires --policy-intent <id>",
                ));
            }
            (Some(_), false) => {
                return Err(CliError::usage("--policy-intent does not apply here"));
            }
            (None, false) => None,
        };
        let passphrase = crate::envelope::passphrase_named(
            args,
            "policy-passphrase-env",
            "policy-passphrase-file",
        )?;
        let anchor_cfg = AnchorConfig::for_vault(
            args,
            dir,
            "policy-anchor-dir",
            "policy-allow-single-disk-anchor",
        )?;
        let access = if needs_intent {
            Access::Update
        } else {
            Access::Inspect
        };
        let ledger = OpenLedger::open(
            dir,
            passphrase.as_deref().map(Vec::as_slice),
            anchor_cfg.as_ref(),
            access,
        )?;
        Ok(Some(Self { ledger, intent }))
    }

    pub fn ledger_id(&self) -> &[u8; 32] {
        self.ledger.id()
    }

    /// The amount the gated intent will commit, read before anything is released.
    pub fn intent_amount(&self) -> Result<u128, CliError> {
        let id = self
            .intent
            .ok_or_else(|| CliError::usage("no policy intent selected"))?;
        Ok(self.ledger.load_record(&id)?.intent.amount_units)
    }

    /// Release the selected intent for this key, message and context, or refuse.
    pub fn authorize(
        &mut self,
        key_id: &[u8; 32],
        message: &[u8],
        ctx: &[u8],
        retry: bool,
    ) -> Result<Authorization, CliError> {
        let id = self
            .intent
            .ok_or_else(|| CliError::usage("no policy intent selected"))?;
        self.ledger
            .authorize(&id, key_id, message, ctx, retry, unix_now()?)
    }
}

/// A key enrolled against a policy ledger signs only through that ledger's gate.
pub fn enforce_key_pin(secret: &Json, gate: Option<&Gate>) -> Result<(), CliError> {
    let pinned = match secret.get(KEY_PIN_FIELD) {
        None => return Ok(()),
        Some(value) => from_hex_exact::<32>(
            value.as_str().ok_or_else(crate::vault::corrupt)?,
            KEY_PIN_FIELD,
        )
        .map_err(|_| crate::vault::corrupt())?,
    };
    match gate {
        None => Err(CliError::state(
            "key is enrolled against a custody policy ledger; pass --policy-ledger-dir and --policy-intent",
        )),
        Some(gate) if !ct_eq_bytes(gate.ledger_id(), &pinned) => Err(CliError::state(
            "key is enrolled against a different custody policy ledger",
        )),
        Some(_) => Ok(()),
    }
}

/// The value to store under [`KEY_PIN_FIELD`] when a key generator is given a policy ledger.
pub fn key_pin_from_args(args: &Args) -> Result<Option<[u8; 32]>, CliError> {
    Ok(Gate::from_args(args, false)?.map(|gate| *gate.ledger_id()))
}

/// The policy identifier and spend a gated stateful ceremony commits into its journal.
pub fn ceremony_spend(amount_units: u128) -> Result<u64, CliError> {
    u64::try_from(amount_units).map_err(|_| {
        CliError::usage(
            "intent amount exceeds the 64-bit spend a stateful ceremony journal records",
        )
    })
}

fn public_key_id(path: &str) -> Result<[u8; 32], CliError> {
    let text = read_text(path)?;
    let json = Json::parse(&text)?;
    let scheme = json.field_str("scheme")?;
    match json.field_str("format")? {
        crate::keys::PUBLIC_FORMAT => {
            let key = json.field_hex("public_key").map_err(|_| {
                CliError::usage("this public key has no single signing key to bind an intent to")
            })?;
            Ok(signing_key_id(scheme, &key))
        }
        crate::quorum::PUBLIC_FORMAT => {
            let mut key = json.field_hex("pk_seed")?.0.clone();
            key.extend_from_slice(&json.field_hex("pk_root")?);
            Ok(signing_key_id(scheme, &key))
        }
        _ => Err(CliError::input(format!("{path} is not a public key file"))),
    }
}

const INIT_HELP: &str = "\
qsag policy init --ledger-dir <dir> --policy <policy.json> --accept-single-host-custody [options]

Create a persistent custody policy ledger. <dir> must be absent or empty; it is created
owner-only. The policy document (format qsag-policy-v1) fixes the chain, the pinned witness
suite, the recipient allowlist, the single-transfer and rolling-window caps, the validity
interval, the quorum tiers, the committee `parties`, and optionally `window_secs` (length of
one velocity window; 0 or absent keeps one window for the ledger's life) and
`intent_ttl_secs` (how long a proposed intent stays signable; default 86400).

Every guard share is derived from one provisioning seed stored in <dir>/ledger.json, so the
committee lives on this host: the ledger makes authorization durable, replay-proof and
velocity-capped across invocations, and does not separate the approving parties from each
other. Set `preprocessing_slots` in the enrollment policy to budget single-use barrier slots.

  --anchor-dir <dir>            ratchet every guard generation in an external monotone anchor,
                                so restoring an old copy of the ledger directory is refused
  --allow-single-disk-anchor    permit --anchor-dir on the ledger's filesystem device
  --ephemeral-unanchored        enroll a disposable ledger without rollback protection
                                (required when --anchor-dir is absent)
  --passphrase-env <VAR> / --passphrase-file <PATH>  seal the provisioning seed
  --json                        print the ledger identifier and policy digest as JSON
";

fn init(raw: &[String]) -> Result<(), CliError> {
    let args = Args::parse(
        raw,
        &[
            "ledger-dir",
            "policy",
            "anchor-dir",
            "passphrase-env",
            "passphrase-file",
        ],
        &[
            "accept-single-host-custody",
            "allow-single-disk-anchor",
            "ephemeral-unanchored",
            "json",
            "help",
        ],
    )?;
    if args.flag("help") {
        print!("{INIT_HELP}");
        return Ok(());
    }
    args.no_positionals()?;
    let dir = args.require("ledger-dir")?;
    if !args.flag("accept-single-host-custody") {
        return Err(CliError::usage(
            "policy init requires --accept-single-host-custody: one provisioning seed on this host derives every guard share",
        ));
    }
    crate::anchor::require_anchor_or_waiver(
        args.get("anchor-dir").is_some(),
        args.flag("ephemeral-unanchored"),
        "anchor-dir",
    )?;
    let policy_text = read_text(args.require("policy")?)?;
    let (policy, committee) = policy_from_json(&Json::parse(&policy_text)?)?;
    let passphrase = crate::envelope::passphrase(&args)?;
    let anchor_cfg = AnchorConfig::for_vault(&args, dir, "anchor-dir", "allow-single-disk-anchor")?;

    private_dir(dir, true)?;
    let occupied = std::fs::read_dir(dir)
        .map_err(|e| CliError::io(format_args!("reading {dir}"), e))?
        .next()
        .is_some();
    if occupied {
        return Err(CliError::state(format!(
            "{dir} is not empty; a policy ledger is created only in a fresh directory"
        )));
    }
    let root = root_path(dir)?;
    if let Some(cfg) = &anchor_cfg {
        cfg.validate_isolation(&[&root], &[dir], true)?;
    }
    for sub in ["guards", "intents"] {
        private_dir(&join(dir, &[sub])?, true)?;
    }
    let mut vault = Vault::acquire(&root, true)?;
    let seed = Secret32::new(os_random_32()?);
    let nonce = os_random_32()?;
    let nonce = &nonce[..16];
    let id = ledger_id(&seed, &policy, &committee, nonce);

    let guards = provision_guards(
        &seed,
        &id,
        &committee.parties,
        committee.preprocessing_slots,
    )?;
    let shared = SharedWindowSpendLedger::new(&policy, 0)
        .with_window_authority(id, party_secret(&seed, b"window authority", 0).0)
        .map_err(violation)?;
    let generation = 1;
    write_new(
        &bundle_path(dir)?,
        &write_bundle(&seed, &id, generation, &guards, &shared),
        true,
    )?;
    FsPolicyGenerationFence::create_new(
        fence_path(dir)?,
        party_secret(&seed, b"fence key", 0).0,
        generation,
    )
    .map_err(|e| CliError::io("creating policy generation fence", e))?;
    let anchor_seal = match &anchor_cfg {
        Some(cfg) => {
            let anchor = FsExternalMountAnchor::provision_fresh(
                cfg,
                &[&root],
                &[dir],
                ANCHOR_DOMAIN,
                id,
                party_secret(&seed, b"fence anchor mac", 0).0,
            )?;
            anchor.advance_floor(ANCHOR_DOMAIN.as_bytes(), generation)?;
            Some(anchor.lock_identity_seal())
        }
        None => None,
    };

    let mut file = Json::object(vec![
        ("format", Json::str(ROOT_FORMAT)),
        ("scheme", Json::str(ROOT_SCHEME)),
        ("custody_model", Json::str(CUSTODY_MODEL)),
        ("enrollment_nonce", Json::hex(nonce)),
        ("ledger_id", Json::hex(&id)),
        ("policy_digest", Json::hex(&policy.canonical_digest())),
        ("policy", policy_to_json(&policy, &committee)),
    ]);
    if let Some(seal) = &anchor_seal {
        set(&mut file, "anchor_required", Json::Bool(true));
        set(&mut file, ANCHOR_SEAL_FIELD, Json::hex(seal));
    }
    set(&mut file, "seed", Json::hex(&seed.0));
    vault.set_key_material(&crate::envelope::open(&file, None)?);
    if let Some(pass) = &passphrase {
        crate::envelope::seal(&mut file, pass)?;
    }
    vault.bind(&mut file)?;
    vault.seal(&mut file)?;
    let encoded = ZeroizingBuf::new(file.to_pretty().into_bytes());
    // Written last: a directory without it was never a usable ledger.
    write_new(&root, &encoded.0, true)?;

    if args.flag("json") {
        print!(
            "{}",
            Json::object(vec![
                ("ledger_id", Json::hex(&id)),
                ("policy_digest", Json::hex(&policy.canonical_digest())),
                ("custody_model", Json::str(CUSTODY_MODEL)),
                ("parties", party_json(&committee.parties)),
                ("anchored", Json::Bool(anchor_cfg.is_some())),
            ])
            .to_pretty()
        );
    } else {
        println!("created policy ledger {} in {dir}", to_hex(&id));
    }
    Ok(())
}

const LEDGER_OPTIONS: [&str; 4] = [
    "ledger-dir",
    "anchor-dir",
    "passphrase-env",
    "passphrase-file",
];

fn open_from_args(args: &Args, access: Access) -> Result<OpenLedger, CliError> {
    let dir = args.require("ledger-dir")?;
    let passphrase = crate::envelope::passphrase(args)?;
    let anchor_cfg = AnchorConfig::for_vault(args, dir, "anchor-dir", "allow-single-disk-anchor")?;
    OpenLedger::open(
        dir,
        passphrase.as_deref().map(Vec::as_slice),
        anchor_cfg.as_ref(),
        access,
    )
}

const LEDGER_HELP: &str = "\
  --anchor-dir <dir>            the ledger's external monotone anchor (required if enrolled with one)
  --allow-single-disk-anchor    permit --anchor-dir on the ledger's filesystem device
  --passphrase-env <VAR> / --passphrase-file <PATH>  unlock a sealed ledger
";

const PROPOSE_HELP: &str = "\
qsag policy propose --ledger-dir <dir> --public <key.json> --payload <file> --recipient <address>
                    --amount <units> --initiator <party> --approvers <a,b,..> --message-out <path>

Build a transfer intent, evaluate the ledger's policy on it against the current velocity
window, authenticate it as the initiator, and record it. Exit code 3 means the policy
refused it; nothing is recorded then. The file written to --message-out is the canonical
intent envelope: it is the exact message `qsag sign` or `qsag quorum sign` must be given.

  --public <key.json>   public key of the key that will sign (single-signer or quorum)
  --payload <file>      application transaction bytes the intent commits to
  --ctx-hex <hex>       SLH-DSA context string the signer will use (default: empty)
  --json                print the intent as JSON
";

fn propose(raw: &[String]) -> Result<(), CliError> {
    let mut options = LEDGER_OPTIONS.to_vec();
    options.extend([
        "public",
        "payload",
        "recipient",
        "amount",
        "initiator",
        "approvers",
        "message-out",
        "ctx-hex",
    ]);
    let args = Args::parse(raw, &options, &["allow-single-disk-anchor", "json", "help"])?;
    if args.flag("help") {
        print!("{PROPOSE_HELP}{LEDGER_HELP}");
        return Ok(());
    }
    args.no_positionals()?;
    let key_id = public_key_id(args.require("public")?)?;
    let payload = read_input(args.require("payload")?)?;
    let ctx = crate::codec::from_hex(args.get("ctx-hex").unwrap_or(""))?;
    let recipient = QsagAddress::decode(args.require("recipient")?)
        .map_err(|e| CliError::usage(format!("--recipient rejected: {e:?}")))?;
    let amount_units: u128 = args
        .require("amount")?
        .parse()
        .map_err(|_| CliError::usage("--amount must be a non-negative integer"))?;
    let initiator: u16 = args
        .require("initiator")?
        .parse()
        .map_err(|_| CliError::usage("--initiator must be a party id"))?;
    let approvers = parse_party_csv(args.require("approvers")?, "--approvers")?;
    let message_out = args.require("message-out")?;
    if std::fs::symlink_metadata(message_out).is_ok() {
        return Err(CliError::usage(format!("{message_out} already exists")));
    }
    let mut ledger = open_from_args(&args, Access::Update)?;
    let (record, signing_bytes) = ledger.propose(
        &Proposal {
            key_id,
            payload: &payload,
            ctx: &ctx,
            recipient,
            amount_units,
            initiator,
            approvers: &approvers,
        },
        unix_now()?,
    )?;
    write_new(message_out, &signing_bytes, false)?;
    report_record(&args, ledger.id(), &record, "proposed")
}

fn report_record(
    args: &Args,
    ledger: &[u8; 32],
    record: &IntentRecord,
    verb: &str,
) -> Result<(), CliError> {
    let id = record.intent.canonical_digest();
    if args.flag("json") {
        print!("{}", record.to_json(ledger)?.to_pretty());
    } else {
        println!(
            "{verb} intent {} ({} of {} approvals recorded)",
            to_hex(&id),
            record.approvals.len(),
            record.intent.approver_parties.len()
        );
    }
    Ok(())
}

const APPROVE_HELP: &str = "\
qsag policy approve --ledger-dir <dir> --intent <id> --party <party>

Record one approver's approval of a proposed intent. An intent is signable only once every
one of its approvers has a recorded approval. Exit code 3 means the party is not an approver
of the intent, the intent was already released, or the policy no longer accepts it.

  --json                print the intent as JSON
";

fn approve(raw: &[String]) -> Result<(), CliError> {
    let mut options = LEDGER_OPTIONS.to_vec();
    options.extend(["intent", "party"]);
    let args = Args::parse(raw, &options, &["allow-single-disk-anchor", "json", "help"])?;
    if args.flag("help") {
        print!("{APPROVE_HELP}{LEDGER_HELP}");
        return Ok(());
    }
    args.no_positionals()?;
    let id: [u8; 32] = from_hex_exact(args.require("intent")?, "--intent")?;
    let party: u16 = args
        .require("party")?
        .parse()
        .map_err(|_| CliError::usage("--party must be a party id"))?;
    let mut ledger = open_from_args(&args, Access::Update)?;
    let record = ledger.approve(&id, party)?;
    report_record(&args, ledger.id(), &record, "approved")
}

const STATUS_HELP: &str = "\
qsag policy status --ledger-dir <dir> [--json]

Authenticate a policy ledger and report its identifier, policy digest, velocity window,
per-party spend and checkpoint generation, and its recorded intents. Writes nothing.
";

fn status(raw: &[String]) -> Result<(), CliError> {
    let args = Args::parse(
        raw,
        &LEDGER_OPTIONS,
        &["allow-single-disk-anchor", "json", "help"],
    )?;
    if args.flag("help") {
        print!("{STATUS_HELP}{LEDGER_HELP}");
        return Ok(());
    }
    args.no_positionals()?;
    let ledger = open_from_args(&args, Access::Inspect)?;
    let mut records = Vec::new();
    let intents_dir = join(&ledger.dir, &["intents"])?;
    for entry in std::fs::read_dir(&intents_dir)
        .map_err(|e| CliError::io(format_args!("reading {intents_dir}"), e))?
    {
        let name = entry
            .map_err(|e| CliError::io(format_args!("reading {intents_dir}"), e))?
            .file_name();
        let Some(hex) = name.to_str().and_then(|n| n.strip_suffix(".json")) else {
            continue;
        };
        let Ok(id) = from_hex_exact::<32>(hex, "intent id") else {
            continue;
        };
        records.push(ledger.load_record(&id)?);
    }
    records.sort_by_key(|r| (r.intent.timestamp_secs, r.intent.canonical_digest()));
    let state = |r: &IntentRecord| {
        if ledger.is_burned(&r.intent) {
            STATE_RELEASED
        } else {
            STATE_PROPOSED
        }
    };
    let parties: Vec<Json> = ledger
        .guards
        .iter()
        .map(|guard| {
            let released = records
                .iter()
                .filter(|r| guard.is_nonce_burned(&r.intent.nonce))
                .count();
            Json::object(vec![
                ("party", Json::num(guard.party_id)),
                ("window_id", Json::num(guard.current_window_id())),
                ("window_spend", Json::num(guard.accumulated_window_spend())),
                ("intents_released", Json::num(released)),
                (
                    "release_capacity",
                    Json::num(ledger.committee.preprocessing_slots),
                ),
            ])
        })
        .collect();
    let intents: Vec<Json> = records
        .iter()
        .map(|r| {
            Json::object(vec![
                ("intent_id", Json::hex(&r.intent.canonical_digest())),
                ("state", Json::str(state(r))),
                ("amount_units", Json::num(r.intent.amount_units)),
                ("approvals", party_json(&r.approvals)),
                ("approver_parties", party_json(&r.intent.approver_parties)),
            ])
        })
        .collect();
    let report = Json::object(vec![
        ("ledger_id", Json::hex(ledger.id())),
        (
            "policy_digest",
            Json::hex(&ledger.policy.canonical_digest()),
        ),
        ("custody_model", Json::str(CUSTODY_MODEL)),
        ("anchored", Json::Bool(ledger.anchor.is_some())),
        ("checkpoint_generation", Json::num(ledger.generation)),
        (
            "velocity_window_cap",
            Json::num(ledger.policy.velocity_window_cap),
        ),
        ("window_id", Json::num(ledger.current_window())),
        (
            "window_spend",
            Json::num(ledger.window_spend(&ledger.committee.parties)?),
        ),
        ("parties", Json::Array(parties)),
        ("intents", Json::Array(intents)),
    ]);
    if args.flag("json") {
        print!("{}", report.to_pretty());
    } else {
        println!(
            "ledger {} window {} spend {} of {}",
            report.field_str("ledger_id")?,
            ledger.current_window(),
            ledger.window_spend(&ledger.committee.parties)?,
            ledger.policy.velocity_window_cap
        );
        for r in &records {
            println!(
                "  {} {} amount {} approvals {}/{}",
                to_hex(&r.intent.canonical_digest()),
                state(r),
                r.intent.amount_units,
                r.approvals.len(),
                r.intent.approver_parties.len()
            );
        }
    }
    Ok(())
}

/// `qsag policy <init|propose|approve|status>`; `None` if `verb` is not a ledger subcommand.
pub fn run(verb: &str, rest: &[String]) -> Option<Result<(), CliError>> {
    Some(match verb {
        "init" => init(rest),
        "propose" => propose(rest),
        "approve" => approve(rest),
        "status" => status(rest),
        _ => return None,
    })
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;
    use qsag_addr::KeyIdentityKind;

    const NOW: u64 = 1_750_000_000;
    const DAY: u64 = 86_400;

    fn recipient() -> QsagAddress {
        QsagAddress::from_pubkey_cshake256(
            "qsp",
            WitnessSuiteTag::SlhDsa128s,
            KeyIdentityKind::SingleOrThreshold,
            b"treasury cold wallet",
        )
        .unwrap()
    }

    fn policy_document(window_secs: u64) -> String {
        Json::object(vec![
            ("format", Json::str(POLICY_FORMAT)),
            ("chain_id", Json::num(1)),
            ("suite", Json::str("SlhDsa128s")),
            (
                "recipient_allowlist",
                Json::Array(vec![Json::str(recipient().encode().unwrap())]),
            ),
            ("max_single_tx_amount", Json::num(1_000)),
            ("velocity_window_cap", Json::num(1_500)),
            ("valid_not_before_secs", Json::num(1_700_000_000u64)),
            ("valid_not_after_secs", Json::num(1_800_000_000u64)),
            ("forbid_initiator_self_approval", Json::Bool(true)),
            ("hardware_guardian_party", Json::num(3)),
            (
                "quorum_tiers",
                Json::Array(vec![Json::object(vec![
                    ("max_amount_units", Json::num(1_000)),
                    ("min_approvers", Json::num(2)),
                    ("require_hardware_guardian", Json::Bool(true)),
                ])]),
            ),
            ("parties", party_json(&[1, 2, 3])),
            ("window_secs", Json::num(window_secs)),
        ])
        .to_pretty()
    }

    struct Scratch(std::path::PathBuf);
    impl Scratch {
        fn new() -> Self {
            let dir = std::env::temp_dir().join(format!(
                "qsag-policy-ledger-{}",
                to_hex(&os_random_32().unwrap())
            ));
            std::fs::create_dir(&dir).unwrap();
            Self(dir)
        }
        fn path(&self, name: &str) -> String {
            self.0.join(name).to_str().unwrap().to_owned()
        }
        fn create(&self, window_secs: u64) -> String {
            std::fs::write(self.path("policy.json"), policy_document(window_secs)).unwrap();
            let args: Vec<String> = [
                "--ledger-dir",
                &self.path("ledger"),
                "--policy",
                &self.path("policy.json"),
                "--accept-single-host-custody",
                "--ephemeral-unanchored",
            ]
            .iter()
            .map(|s| s.to_string())
            .collect();
            init(&args).unwrap();
            self.path("ledger")
        }
    }
    impl Drop for Scratch {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    fn open(dir: &str) -> OpenLedger {
        OpenLedger::open(dir, None, None, Access::Update).unwrap()
    }

    const KEY: [u8; 32] = [0x4B; 32];

    /// Propose and fully approve one transfer in separate ledger sessions.
    fn approved(dir: &str, amount: u128, now: u64) -> Result<([u8; 32], Vec<u8>), CliError> {
        let (record, message) = open(dir).propose(
            &Proposal {
                key_id: KEY,
                payload: b"wire transfer",
                ctx: b"",
                recipient: recipient(),
                amount_units: amount,
                initiator: 1,
                approvers: &[2, 3],
            },
            now,
        )?;
        let id = record.intent.canonical_digest();
        for party in [2, 3] {
            open(dir).approve(&id, party)?;
        }
        Ok((id, message))
    }

    #[test]
    fn guardian_free_partial_quorum_uses_durable_shared_accounting() {
        let scratch = Scratch::new();
        let mut document = Json::parse(&policy_document(0)).unwrap();
        set(&mut document, "hardware_guardian_party", Json::num(1));
        let mut tiers = document
            .get("quorum_tiers")
            .unwrap()
            .as_array()
            .unwrap()
            .to_vec();
        for tier in &mut tiers {
            set(tier, "require_hardware_guardian", Json::Bool(false));
        }
        set(&mut document, "quorum_tiers", Json::Array(tiers));
        std::fs::write(scratch.path("policy.json"), document.to_pretty()).unwrap();
        let dir = scratch.path("ledger");
        let args: Vec<_> = [
            "--ledger-dir",
            &dir,
            "--policy",
            &scratch.path("policy.json"),
            "--accept-single-host-custody",
            "--ephemeral-unanchored",
        ]
        .iter()
        .map(|s| s.to_string())
        .collect();
        init(&args).unwrap();
        let mut ledger = open(&dir);
        let (record, message) = ledger
            .propose(
                &Proposal {
                    key_id: KEY,
                    payload: b"partial quorum",
                    ctx: b"",
                    recipient: recipient(),
                    amount_units: 800,
                    initiator: 1,
                    approvers: &[2, 3],
                },
                NOW,
            )
            .unwrap();
        let mut required = ledger.policy.clone();
        required.quorum_tiers[0].require_hardware_guardian = true;
        assert_eq!(
            required.evaluate(&record.intent),
            Err(PolicyViolation::MissingHardwareGuardian)
        );
        let id = record.intent.canonical_digest();
        let mut record = record;
        record.approvals = vec![2, 3];
        ledger.store_record(&record, false).unwrap();
        ledger
            .authorize(&id, &KEY, &message, b"", false, NOW)
            .unwrap();
        assert_eq!(ledger.shared.accumulated_window_spend(), 800);
        drop(ledger);
        let ledger = open(&dir);
        assert_eq!(ledger.shared.accumulated_window_spend(), 800);
        assert!(ledger.shared.is_nonce_burned(&record.intent.nonce));
    }

    #[test]
    fn spend_nonces_and_approvals_persist_across_sessions() {
        let scratch = Scratch::new();
        let dir = scratch.create(0);
        let (record, message) = open(&dir)
            .propose(
                &Proposal {
                    key_id: KEY,
                    payload: b"wire transfer",
                    ctx: b"",
                    recipient: recipient(),
                    amount_units: 800,
                    initiator: 1,
                    approvers: &[2, 3],
                },
                NOW,
            )
            .unwrap();
        let id = record.intent.canonical_digest();

        // Unapproved, then half approved: refused, and the checkpoint does not move.
        let generations = |dir: &str| -> (u64, Vec<u8>) {
            (
                open(dir).generation,
                std::fs::read(bundle_path(dir).unwrap()).unwrap(),
            )
        };
        let before = generations(&dir);
        for approver in [2, 3] {
            let err = open(&dir)
                .authorize(&id, &KEY, &message, b"", false, NOW)
                .err()
                .unwrap();
            assert_eq!(err.code, exit::POLICY_DENIED, "{}", err.message);
            assert!(err.message.contains("unapproved"), "{}", err.message);
            open(&dir).approve(&id, approver).unwrap();
        }
        assert_eq!(generations(&dir), before);
        // A party outside the intent's approvers cannot approve it.
        assert_eq!(
            open(&dir).approve(&id, 1).err().unwrap().code,
            exit::POLICY_DENIED
        );

        // Wrong key, wrong message and wrong context are refused before release.
        for (key, msg, ctx) in [
            (&[0u8; 32], &message[..], &b""[..]),
            (&KEY, &b"another message"[..], &b""[..]),
            (&KEY, &message[..], &b"ctx"[..]),
        ] {
            let err = open(&dir)
                .authorize(&id, key, msg, ctx, false, NOW)
                .err()
                .unwrap();
            assert_eq!(err.code, exit::POLICY_DENIED);
        }
        assert_eq!(generations(&dir), before);

        let granted = open(&dir)
            .authorize(&id, &KEY, &message, b"", false, NOW)
            .unwrap();
        assert_eq!(granted.amount_units, 800);
        let after = open(&dir);
        assert_eq!(after.window_spend(&[2, 3]).unwrap(), 800);
        assert!(after.guards[1].is_nonce_burned(&record.intent.nonce));
        assert!(after.guards[2].is_session_burned(&record.intent.session_id));
        // The initiator took no part in the barrier and accounts for no spend.
        assert_eq!(after.guards[0].accumulated_window_spend(), 0);
        assert!(!after.guards[0].is_nonce_burned(&record.intent.nonce));
        assert_eq!(after.generation, before.0 + 1);
        assert_eq!(after.fence.generation(), after.generation);
        drop(after);

        // Replay is refused; resuming the same ceremony is the one exception.
        let replay = open(&dir)
            .authorize(&id, &KEY, &message, b"", false, NOW)
            .err()
            .unwrap();
        assert_eq!(replay.code, exit::POLICY_DENIED);
        assert!(replay.message.contains("DuplicateIntentNonce"));
        open(&dir)
            .authorize(&id, &KEY, &message, b"", true, NOW)
            .unwrap();
        assert!(
            open(&dir)
                .authorize(&id, &KEY, b"other", b"", true, NOW)
                .is_err()
        );
        assert_eq!(open(&dir).window_spend(&[2, 3]).unwrap(), 800);

        // The record carries no release state to roll back: the guards burned the nonce.
        assert_eq!(
            open(&dir).approve(&id, 2).err().unwrap().code,
            exit::POLICY_DENIED
        );
        let released = generations(&dir);
        let err = open(&dir)
            .authorize(&id, &KEY, &message, b"", false, NOW)
            .err()
            .unwrap();
        assert!(
            err.message.contains("DuplicateIntentNonce"),
            "{}",
            err.message
        );
        assert_eq!(generations(&dir), released);
    }

    #[test]
    fn velocity_cap_holds_across_sessions_and_resets_only_with_the_window() {
        let scratch = Scratch::new();
        let dir = scratch.create(DAY);
        // Two intents proposed against the same spend: only the first can be released.
        let (first, first_msg) = approved(&dir, 800, NOW).unwrap();
        let (second, second_msg) = approved(&dir, 700, NOW).unwrap();
        open(&dir)
            .authorize(&first, &KEY, &first_msg, b"", false, NOW)
            .unwrap();
        let stale = open(&dir)
            .authorize(&second, &KEY, &second_msg, b"", false, NOW)
            .err()
            .unwrap();
        assert_eq!(stale.code, exit::POLICY_DENIED);
        assert_eq!(open(&dir).window_spend(&[2, 3]).unwrap(), 800);

        // Proposed again against the recorded spend it fits exactly; one unit more does not.
        let (third, third_msg) = approved(&dir, 700, NOW + 1).unwrap();
        open(&dir)
            .authorize(&third, &KEY, &third_msg, b"", false, NOW + 1)
            .unwrap();
        let over = approved(&dir, 1, NOW + 2).err().unwrap();
        assert_eq!(over.code, exit::POLICY_DENIED);
        assert!(over.message.contains("VelocityCap"), "{}", over.message);
        let single = approved(&dir, 1_001, NOW + 2).err().unwrap();
        assert!(single.message.contains("SingleTxCap"), "{}", single.message);

        // The next window starts empty; an intent stamped in the old window is refused.
        let (late, late_msg) = approved(&dir, 0, NOW + 3).unwrap();
        let next = NOW + DAY;
        let err = open(&dir)
            .authorize(&late, &KEY, &late_msg, b"", false, next)
            .err()
            .unwrap();
        assert!(err.message.contains("WindowIdMismatch"), "{}", err.message);
        assert_eq!(open(&dir).window_spend(&[1, 2, 3]).unwrap(), 0);
        let (fresh, fresh_msg) = approved(&dir, 1_000, next).unwrap();
        open(&dir)
            .authorize(&fresh, &KEY, &fresh_msg, b"", false, next)
            .unwrap();
        // A clock that steps back does not reopen the previous window.
        let ledger = open(&dir);
        assert_eq!(ledger.current_window(), next / DAY);
        assert_eq!(ledger.window_spend(&[2, 3]).unwrap(), 1_000);
        drop(ledger);
        assert!(approved(&dir, 600, NOW).is_err());
    }

    #[test]
    fn stale_and_future_intents_are_refused() {
        let scratch = Scratch::new();
        let dir = scratch.create(0);
        let (id, message) = approved(&dir, 10, NOW).unwrap();
        for now in [NOW - CLOCK_SKEW_SECS - 1, NOW + DEFAULT_INTENT_TTL_SECS + 1] {
            let err = open(&dir)
                .authorize(&id, &KEY, &message, b"", false, now)
                .err()
                .unwrap();
            assert!(
                err.message.contains("TimestampOutsideWindow"),
                "{}",
                err.message
            );
        }
        open(&dir)
            .authorize(
                &id,
                &KEY,
                &message,
                b"",
                false,
                NOW + DEFAULT_INTENT_TTL_SECS,
            )
            .unwrap();
    }

    #[test]
    fn rolled_back_or_damaged_state_fails_closed() {
        let scratch = Scratch::new();
        let dir = scratch.create(0);
        let checkpoint = bundle_path(&dir).unwrap();
        let old = std::fs::read(&checkpoint).unwrap();
        let (id, message) = approved(&dir, 100, NOW).unwrap();
        open(&dir)
            .authorize(&id, &KEY, &message, b"", false, NOW)
            .unwrap();
        let current = std::fs::read(&checkpoint).unwrap();
        assert_ne!(old, current);

        let refused = |dir: &str| {
            for access in [Access::Inspect, Access::Update] {
                let err = OpenLedger::open(dir, None, None, access).err().unwrap();
                assert_eq!(err.code, exit::STATE_CONFLICT, "{}", err.message);
            }
        };
        // The pre-spend checkpoint under the advanced fence.
        std::fs::write(&checkpoint, &old).unwrap();
        refused(&dir);
        // Truncated, extended, empty, and with one bit flipped in each region.
        std::fs::write(&checkpoint, &current[..current.len() - 1]).unwrap();
        refused(&dir);
        std::fs::write(&checkpoint, [&current[..], &[0u8]].concat()).unwrap();
        refused(&dir);
        std::fs::write(&checkpoint, b"").unwrap();
        refused(&dir);
        for at in [0, 20, 44, 60, current.len() / 2, current.len() - 1] {
            let mut flipped = current.clone();
            flipped[at] ^= 1;
            std::fs::write(&checkpoint, &flipped).unwrap();
            refused(&dir);
        }
        // A symlink in place of the checkpoint is not followed.
        let aside = scratch.path("aside.ckpt");
        std::fs::write(&aside, &current).unwrap();
        std::fs::remove_file(&checkpoint).unwrap();
        std::os::unix::fs::symlink(&aside, &checkpoint).unwrap();
        refused(&dir);
        std::fs::remove_file(&checkpoint).unwrap();
        std::fs::write(&checkpoint, &current).unwrap();
        assert_eq!(open(&dir).window_spend(&[2, 3]).unwrap(), 100);

        // A checkpoint that reached disk without its fence is adopted, never rolled past.
        let mut ledger = open(&dir);
        let generation = ledger.generation + 1;
        let ahead = write_bundle(
            &ledger.seed,
            &ledger.id,
            generation,
            &ledger.guards,
            &ledger.shared,
        );
        drop(ledger);
        std::fs::write(&checkpoint, &ahead).unwrap();
        let inspected = OpenLedger::open(&dir, None, None, Access::Inspect).unwrap();
        assert_eq!(inspected.fence.generation(), generation - 1);
        drop(inspected);
        ledger = open(&dir);
        assert_eq!(ledger.fence.generation(), generation);
        drop(ledger);
        std::fs::write(&checkpoint, &current).unwrap();
        refused(&dir);
        std::fs::write(&checkpoint, &ahead).unwrap();

        // A damaged intent record, and an edited root file.
        let record = intent_path(&dir, &id).unwrap();
        let text = std::fs::read_to_string(&record).unwrap();
        std::fs::write(
            &record,
            text.replace("\"amount_units\": 100", "\"amount_units\": 1"),
        )
        .unwrap();
        let err = open(&dir).load_record(&id).err().unwrap();
        assert_eq!(err.code, exit::STATE_CONFLICT);
        let root = root_path(&dir).unwrap();
        let text = std::fs::read_to_string(&root).unwrap();
        std::fs::write(
            &root,
            text.replace(
                "\"velocity_window_cap\": 1500",
                "\"velocity_window_cap\": 9999",
            ),
        )
        .unwrap();
        refused(&dir);
    }

    #[test]
    fn committee_checkpoint_codec_rejects_noncanonical_input() {
        let key = Secret32::new([9; 32]);
        let ledger = [3u8; 32];
        let parts = vec![(1u16, vec![1u8, 2, 3]), (2u16, Vec::new())];
        let bytes = encode_bundle(&key, &ledger, 7, &parts, b"shared");
        assert_eq!(
            decode_bundle(&key, &ledger, &bytes).unwrap(),
            Bundle {
                generation: 7,
                checkpoints: vec![(1u16, &[1u8, 2, 3][..]), (2u16, &[][..])],
                shared: b"shared",
            }
        );
        assert!(decode_bundle(&Secret32::new([8; 32]), &ledger, &bytes).is_err());
        assert!(decode_bundle(&key, &[4u8; 32], &bytes).is_err());
        // Authenticated but ill-formed bodies: a length running past the end, trailing bytes.
        let retag = |body: &[u8]| {
            let mut out = body.to_vec();
            out.extend_from_slice(&cshake256_framed_32(BUNDLE_DOMAIN, &[&key.0, body]));
            out
        };
        let body = &bytes[..bytes.len() - 32];
        assert!(decode_bundle(&key, &ledger, &retag(body)).is_ok());
        assert!(decode_bundle(&key, &ledger, &retag(&[body, &[0u8][..]].concat())).is_err());
        assert!(decode_bundle(&key, &ledger, &retag(&body[..body.len() - 1])).is_err());
        let mut long = body.to_vec();
        long[8 + 32 + 8 + 2 + 2 + 3] = 0xFF;
        assert!(decode_bundle(&key, &ledger, &retag(&long)).is_err());
        for len in 0..40 {
            assert!(decode_bundle(&key, &ledger, &bytes[..len]).is_err());
        }
    }

    #[test]
    fn key_pin_requires_the_enrolled_ledger() {
        let scratch = Scratch::new();
        let dir = scratch.create(0);
        let gate = Gate {
            ledger: open(&dir),
            intent: None,
        };
        let pinned = Json::object(vec![(KEY_PIN_FIELD, Json::hex(gate.ledger_id()))]);
        let other = Json::object(vec![(KEY_PIN_FIELD, Json::hex(&[7u8; 32]))]);
        let unpinned = Json::object(vec![("scheme", Json::str("x"))]);
        enforce_key_pin(&pinned, Some(&gate)).unwrap();
        enforce_key_pin(&unpinned, Some(&gate)).unwrap();
        enforce_key_pin(&unpinned, None).unwrap();
        assert_eq!(
            enforce_key_pin(&pinned, None).err().unwrap().code,
            exit::STATE_CONFLICT
        );
        assert_eq!(
            enforce_key_pin(&other, Some(&gate)).err().unwrap().code,
            exit::STATE_CONFLICT
        );
    }

    #[test]
    fn policy_documents_support_64_parties_and_tiers() {
        let mut document = Json::parse(&policy_document(0)).unwrap();
        set(
            &mut document,
            "parties",
            party_json(&(1..=64).collect::<Vec<_>>()),
        );
        let tiers = (1..=64)
            .map(|i| {
                Json::object(vec![
                    ("max_amount_units", Json::num(i * 1000)),
                    ("min_approvers", Json::num(2)),
                    ("require_hardware_guardian", Json::Bool(true)),
                ])
            })
            .collect();
        set(&mut document, "quorum_tiers", Json::Array(tiers));
        let (policy, committee) = policy_from_json(&document).unwrap();
        assert_eq!(committee.parties.len(), 64);
        assert_eq!(policy.quorum_tiers.len(), 64);
        let mut too_many = document.clone();
        set(
            &mut too_many,
            "parties",
            party_json(&(1..=65).collect::<Vec<_>>()),
        );
        assert!(policy_from_json(&too_many).is_err());
        if let Some(Json::Array(tiers)) = document.get("quorum_tiers") {
            let mut too_many_tiers = tiers.clone();
            too_many_tiers.push(Json::object(vec![
                ("max_amount_units", Json::num(65_000)),
                ("min_approvers", Json::num(2)),
                ("require_hardware_guardian", Json::Bool(true)),
            ]));
            set(&mut document, "quorum_tiers", Json::Array(too_many_tiers));
        }
        assert!(policy_from_json(&document).is_err());
    }

    #[test]
    fn policy_documents_are_validated() {
        let good = Json::parse(&policy_document(0)).unwrap();
        let (policy, committee) = policy_from_json(&good).unwrap();
        let (restored, restored_committee) =
            stored_policy(&policy_to_json(&policy, &committee)).unwrap();
        assert_eq!(restored.canonical_digest(), policy.canonical_digest());
        assert_eq!(restored_committee.parties, vec![1, 2, 3]);
        for (field, value) in [
            ("parties", party_json(&[1])),
            ("parties", party_json(&[1, 1, 2])),
            ("hardware_guardian_party", Json::num(9)),
            ("suite", Json::str("NoSuchSuite")),
            ("recipient_allowlist", Json::Array(Vec::new())),
            ("quorum_tiers", Json::Array(Vec::new())),
            ("intent_ttl_secs", Json::num(0)),
            ("format", Json::str("other")),
        ] {
            let mut bad = good.clone();
            set(&mut bad, field, value);
            assert!(policy_from_json(&bad).is_err(), "{field}");
        }
    }
}
