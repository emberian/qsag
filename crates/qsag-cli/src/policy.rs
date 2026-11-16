//! `policy`: the persistent custody policy ledger subcommands (see [`crate::policy_ledger`]),
//! and, when no ledger is named, a stateless evaluation of a fixed custody policy against
//! named transaction scenarios that runs the committed MAC barrier for the approved one.

use qsag_accel::keccak::cshake256_framed_32;
use qsag_addr::{KeyIdentityKind, QsagAddress, WitnessSuiteTag};
use qsag_policy::{
    PolicyViolation, QuorumTierRule, SigningPayloadBinding, TransactionIntent, TransactionPolicy,
};

use crate::cli::{Args, CliError, exit};
use crate::codec::Json;
use crate::dealerless_ceremony::provision_distributed_policy_guards;

const POLICY_HELP: &str = "\
qsag policy <init|propose|approve|status> --ledger-dir <dir> [options]
qsag policy macaroon <keygen|issue|attenuate|issue-discharge|bind-discharge|verify> [options]
qsag policy biscuit <keygen|mint|attenuate|seal|verify> [options]
qsag policy [--ephemeral] [--scenario <name>] [--json]

Persistent custody policy ledger & attenuated capabilities (every subcommand accepts --help):

  init      create a ledger directory from a policy document
  propose   evaluate and record a transfer intent; writes the exact message to sign
  approve   record one approver's approval of a proposed intent
  status    authenticate the ledger and report its window spend and intents
  macaroon  256-bit cSHAKE256 bearer capabilities & bound third-party discharges
  biscuit   post-quantum Compact1122 public-key attenuated capability chains

A proposed and fully approved intent is released by signing its message with
`qsag sign` or `qsag quorum sign` under --policy-ledger-dir and --policy-intent. Signing
refuses an unapproved, over-cap, expired or already released intent before any key state
moves, and the spend, the intent nonce and the session stay burned across invocations.

Without a subcommand nothing is read from or written to disk (--ephemeral says so
explicitly; `qsag policy-demo` is the same evaluation). The command evaluates a fixed
custody policy (allowlisted recipient, 1,000,000-unit single-transfer cap, 5,000,000-unit
rolling cap, two quorum tiers, a hardware guardian for large transfers, and no
self-approval) against named scenarios.

Without --scenario, every scenario is evaluated and compared with its expected outcome; the
approved transfer additionally runs the four-round committed MAC barrier among its approvers
and checks the minted release tokens. Exit code 0 means every outcome matched.

With --scenario, only that scenario is evaluated: exit code 0 if the policy approves it,
exit code 3 if the policy denies it.

Scenarios: approved, unlisted-recipient, over-single-cap, over-velocity-cap, self-approval,
           missing-guardian, expired
";

const PAYLOAD: &[u8] = b"wire-transfer::amount=250000";
const GUARD_AUTHORITY: [u8; 32] = [0x5A; 32];
const CONTEXT: &[u8] = b"qsag:custody:demo";
const NOW: u64 = 1_750_000_000;
const SESSION: [u8; 32] = [0x77; 32];

fn recipient(label: &[u8]) -> Result<QsagAddress, CliError> {
    QsagAddress::from_pubkey_cshake256(
        "qsp",
        WitnessSuiteTag::SlhDsa128s,
        KeyIdentityKind::SingleOrThreshold,
        label,
    )
    .map_err(|e| CliError::usage(format!("{e:?}")))
}

fn policy() -> Result<TransactionPolicy, CliError> {
    Ok(TransactionPolicy {
        chain_id: 1,
        pinned_suite: WitnessSuiteTag::SlhDsa128s,
        recipient_allowlist: vec![recipient(b"treasury cold wallet")?.commitment_256],
        max_single_tx_amount: 1_000_000,
        velocity_window_cap: 5_000_000,
        valid_not_before_secs: 1_700_000_000,
        valid_not_after_secs: 1_800_000_000,
        forbid_initiator_self_approval: true,
        hardware_guardian_party: Some(50),
        quorum_tiers: vec![
            QuorumTierRule {
                max_amount_units: 10_000,
                min_approvers: 2,
                require_hardware_guardian: false,
            },
            QuorumTierRule {
                max_amount_units: 1_000_000,
                min_approvers: 3,
                require_hardware_guardian: true,
            },
        ],
    })
}

fn key_id() -> [u8; 32] {
    qsag_policy::policy_signing_key_id(WitnessSuiteTag::SlhDsa128s, b"demo signing key")
}

/// The parameters a scenario may vary.
struct Request {
    recipient: &'static [u8],
    amount_units: u128,
    rolling_window_spent: u128,
    timestamp_secs: u64,
    initiator: u16,
    approvers: &'static [u16],
}

const APPROVED: Request = Request {
    recipient: b"treasury cold wallet",
    amount_units: 250_000,
    rolling_window_spent: 100_000,
    timestamp_secs: NOW,
    initiator: 10,
    approvers: &[20, 30, 50],
};

impl Request {
    /// Build the canonical intent; the policy is evaluated as part of binding the payload.
    /// Returns the intent and the exact bytes its approvers authorize for signing.
    fn bind(
        &self,
        policy: &TransactionPolicy,
    ) -> Result<Result<(TransactionIntent, Vec<u8>), PolicyViolation>, CliError> {
        let bound = TransactionIntent::builder(
            1,
            WitnessSuiteTag::SlhDsa128s,
            recipient(self.recipient)?,
            self.amount_units,
        )
        .rolling_window(self.rolling_window_spent, [0x33; 32])
        .timestamp_secs(self.timestamp_secs)
        .initiator_and_approvers(self.initiator, self.approvers)
        .bind_signing_payload(
            &SigningPayloadBinding {
                key_id: key_id(),
                payload: PAYLOAD,
                ctx: CONTEXT,
                session_id: SESSION,
                policy_revision: 1,
                quorum: self.approvers,
                authority_pk: GUARD_AUTHORITY,
            },
            policy,
        );
        Ok(bound.and_then(|(mut intent, _)| {
            let guards = provision_distributed_policy_guards([0x99; 32], &[10, 20, 30, 40, 50])?;
            let initiator = guards
                .iter()
                .find(|g| g.party_id == intent.initiator_party)
                .ok_or(PolicyViolation::UnauthenticatedInitiator)?;
            let bytes = initiator.authenticate_initiated_intent(policy, &mut intent)?;
            Ok((intent, bytes))
        }))
    }
}

type Scenario = (&'static str, Option<PolicyViolation>, Request);

fn scenarios() -> [Scenario; 7] {
    [
        ("approved", None, APPROVED),
        (
            "unlisted-recipient",
            Some(PolicyViolation::RecipientNotAllowlisted),
            Request {
                recipient: b"unknown wallet",
                ..APPROVED
            },
        ),
        (
            "over-single-cap",
            Some(PolicyViolation::SingleTxCapExceeded),
            Request {
                amount_units: 1_000_001,
                ..APPROVED
            },
        ),
        (
            "over-velocity-cap",
            Some(PolicyViolation::VelocityCapOverflowOrExceeded),
            Request {
                rolling_window_spent: 4_900_000,
                ..APPROVED
            },
        ),
        (
            "self-approval",
            Some(PolicyViolation::InitiatorSelfApprovalForbidden),
            Request {
                initiator: 20,
                ..APPROVED
            },
        ),
        (
            "missing-guardian",
            Some(PolicyViolation::MissingHardwareGuardian),
            Request {
                approvers: &[20, 30, 40],
                ..APPROVED
            },
        ),
        (
            "expired",
            Some(PolicyViolation::TimestampOutsideWindow),
            Request {
                timestamp_secs: 1_900_000_000,
                ..APPROVED
            },
        ),
    ]
}

/// Run the four-round barrier among the approvers of `intent`; returns the number of release
/// tokens minted, each checked to bind exactly this key, message, context, and quorum.
fn mint_release_tokens(
    policy: &TransactionPolicy,
    intent: &TransactionIntent,
    signing_bytes: &[u8],
) -> Result<usize, CliError> {
    let barrier = |e: PolicyViolation| {
        CliError::new(
            exit::POLICY_DENIED,
            format!("policy barrier refused: {e:?}"),
        )
    };
    let mut guards: Vec<_> = provision_distributed_policy_guards([0x99; 32], &[10, 20, 30, 40, 50])
        .map_err(barrier)?
        .into_iter()
        .filter(|g| intent.quorum_ids.contains(&g.party_id))
        .collect();
    let mut states = Vec::new();
    let mut commits = Vec::new();
    for guard in &mut guards {
        let (state, commit) = guard
            .round1_commit_intent(policy, intent, SESSION, NOW, intent.rolling_window_spent)
            .map_err(barrier)?;
        states.push(state);
        commits.push(commit);
    }
    let mut states2 = Vec::new();
    let mut opens = Vec::new();
    for (state, guard) in states.into_iter().zip(&mut guards) {
        let (state, open) = state.round2_open_delta(guard, &commits).map_err(barrier)?;
        states2.push(state);
        opens.push(open);
    }
    let mut states3 = Vec::new();
    let mut sigma_commits = Vec::new();
    for (state, guard) in states2.into_iter().zip(&mut guards) {
        let (state, commit) = state.round3_commit_sigma(guard, &opens).map_err(barrier)?;
        states3.push(state);
        sigma_commits.push(commit);
    }
    let mut states4 = Vec::new();
    let mut sigma_opens = Vec::new();
    for (state, guard) in states3.into_iter().zip(&mut guards) {
        let (state, open) = state
            .round4_open_sigma(guard, &sigma_commits)
            .map_err(barrier)?;
        states4.push(state);
        sigma_opens.push(open);
    }
    let mut minted = 0;
    for (state, guard) in states4.into_iter().zip(&mut guards) {
        let token = state.finalize(guard, &sigma_opens).map_err(barrier)?;
        let bound = token.matches_signing(&key_id(), signing_bytes, CONTEXT, &intent.quorum_ids)
            && !token.matches_signing(&key_id(), b"another message", CONTEXT, &intent.quorum_ids);
        if !bound {
            return Err(CliError::verify(
                "release token is not bound to the approved signing request",
            ));
        }
        minted += 1;
    }

    // This evaluation is stateless: nothing is written. What a persistent ledger would store
    // is still exercised, by exporting each guard's checkpoint and restoring it into a freshly
    // provisioned share, which must come back with the intent nonce and the session burned.
    let fresh =
        provision_distributed_policy_guards([0x99; 32], &[10, 20, 30, 40, 50]).map_err(barrier)?;
    for (guard, mut restored) in guards.iter().zip(
        fresh
            .into_iter()
            .filter(|g| intent.quorum_ids.contains(&g.party_id)),
    ) {
        let key = cshake256_framed_32(
            b"QSAG.CLI.POLICY.EPHEMERAL.KEY.V1",
            &[&key_id(), &guard.party_id.to_be_bytes()],
        );
        let checkpoint = guard.export_durable_checkpoint(&key, 1);
        let kept = restored
            .restore_from_durable_checkpoint(&checkpoint, &key, 1)
            .is_ok()
            && restored.is_nonce_burned(&intent.nonce)
            && restored.is_session_burned(&SESSION)
            && restored.accumulated_window_spend() == guard.accumulated_window_spend();
        if !kept {
            return Err(CliError::verify(
                "restored policy checkpoint lost burned state",
            ));
        }
    }
    Ok(minted)
}

fn outcome(violation: &Option<PolicyViolation>) -> String {
    match violation {
        None => "approved".to_string(),
        Some(v) => format!("denied: {v:?}"),
    }
}

/// Evaluate every scenario. Returns the policy digest, one row per scenario, and whether
/// every outcome matched its expected outcome.
pub fn evaluate_all() -> Result<([u8; 32], Vec<Json>, bool), CliError> {
    let policy = policy()?;
    let mut rows = Vec::new();
    let mut all_match = true;
    for (name, expected, request) in scenarios() {
        let bound = request.bind(&policy)?;
        let actual = bound.as_ref().err().copied();
        let matches = actual == expected;
        all_match &= matches;
        let mut row = vec![
            ("scenario", Json::str(name)),
            ("outcome", Json::str(outcome(&actual))),
            ("expected", Json::str(outcome(&expected))),
            ("matches_expected", Json::Bool(matches)),
        ];
        if let Ok((intent, signing_bytes)) = &bound {
            row.push((
                "release_tokens_minted",
                Json::num(mint_release_tokens(&policy, intent, signing_bytes)?),
            ));
        }
        rows.push(Json::object(row));
    }
    Ok((policy.canonical_digest(), rows, all_match))
}

pub fn run(raw: &[String]) -> Result<(), CliError> {
    if let Some((verb, rest)) = raw.split_first() {
        match verb.as_str() {
            "macaroon" => return crate::policy_caps::run_macaroon(rest),
            "biscuit" => return crate::policy_caps::run_biscuit(rest),
            _ => {}
        }
        if let Some(result) = crate::policy_ledger::run(verb, rest) {
            return result;
        }
    }
    if raw.iter().any(|arg| arg.starts_with("--ledger-dir")) {
        return Err(CliError::usage(
            "--ledger-dir needs a subcommand: qsag policy <init|propose|approve|status> (try --help)",
        ));
    }
    let args = Args::parse(raw, &["scenario"], &["json", "help", "ephemeral"])?;
    if args.flag("help") {
        print!("{POLICY_HELP}");
        return Ok(());
    }
    args.no_positionals()?;

    if let Some(name) = args.get("scenario") {
        let (_, _, request) = scenarios()
            .into_iter()
            .find(|(n, _, _)| *n == name)
            .ok_or_else(|| CliError::usage(format!("unknown scenario '{name}' (try --help)")))?;
        let actual = request.bind(&policy()?)?.err();
        if args.flag("json") {
            print!(
                "{}",
                Json::object(vec![
                    ("scenario", Json::str(name)),
                    ("outcome", Json::str(outcome(&actual)))
                ])
                .to_pretty()
            );
        } else {
            println!("{name}: {}", outcome(&actual));
        }
        return match actual {
            None => Ok(()),
            Some(v) => Err(CliError::new(
                exit::POLICY_DENIED,
                format!("policy denied the request: {v:?}"),
            )),
        };
    }

    let (policy_digest, rows, all_match) = evaluate_all()?;
    if args.flag("json") {
        print!(
            "{}",
            Json::object(vec![
                ("policy_digest", Json::hex(&policy_digest)),
                ("scenarios", Json::Array(rows))
            ])
            .to_pretty()
        );
    } else {
        for row in &rows {
            let tokens = row.get("release_tokens_minted").and_then(Json::as_u64);
            println!(
                "{:<20} {}{}",
                row.field_str("scenario")?,
                row.field_str("outcome")?,
                tokens.map_or(String::new(), |n| format!(" ({n} release tokens minted)"))
            );
        }
    }
    if all_match {
        Ok(())
    } else {
        Err(CliError::verify(
            "a policy outcome differed from its expected outcome",
        ))
    }
}
