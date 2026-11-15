//! Dealerless 2-of-3 `Jorts` stateful threshold signing ceremonies (`qsag quorum`).
//!
//! Each of the three quorum signers (`party-0.sk`, `party-1.sk`, `party-2.sk` inside
//! `--vault-dir`) holds only its independent 256-bit seed share, an exclusive `.vault.lock`,
//! a durable `FsBeltWal` (`party-p.belt`), and a durable `FsCeremonyJournal`
//! (`party-p.ceremony`). No central secret key is ever reconstructed in key generation or
//! signing. When `--anchor-dir` is supplied, every party's belt WAL and ceremony journal are
//! enrolled against [`crate::anchor::FsExternalMountAnchor`] with single-use ceremony ticket
//! consumption and `CeremonyContext` resource binding.

use std::path::Path;

use qsag_accel::ct::ct_eq_bytes;
use qsag_accel::keccak::cshake256_framed_32;
use qsag_core::belt_latch::FsBeltWal;
use qsag_core::ceremony_journal::{CeremonyContext, CeremonyReservation, FsCeremonyJournal};
use qsag_core::jorts::{
    JortsKeyMaterial, JortsParams, JortsPublicKey, JortsSig, JortsSigner, jorts_keygen_mpc,
    jorts_msg_digest, jorts_verify,
};
use qsag_core::keccak_mpc::{RssKeyShare256, run_dealerless_rss_dkg_2of3};
use qsag_core::preprocessing::PartyPrivateRng;
use qsag_core::rss256::Rss256Engine;

use crate::anchor::{
    AnchorConfig, FsExternalMountAnchor, enforce_anchor_requirement, parse_ceremony_context,
};
use crate::cli::{
    Args, CliError, MAX_SIG_PROOF_BYTES, Secret32, ZeroizingBuf, os_random_32, private_dir,
    read_bounded_file, read_input, read_text, write_new,
};
use crate::codec::{Json, from_hex_exact};
use crate::vault::{
    Vault, corrupt, read_belt_checkpoint, read_ceremony_checkpoint, record_belt_checkpoint,
    record_ceremony_checkpoint, set,
};

const PARTY_SECRET_FORMAT: &str = "qsag-quorum-party-secret-v1";
pub const PUBLIC_FORMAT: &str = "qsag-quorum-public-v1";
const TREE_FORMAT: &str = "qsag-quorum-tree-v1";
const SIG_FORMAT: &str = "qsag-quorum-signature-v1";
const SCHEME_NAME: &str = "jorts-2of3-sha3";
const MAX_CLI_TREE_HEIGHT: u64 = 20;

const QUORUM_HELP: &str = "\
qsag quorum <keygen|sign|refresh|reshare|verify|coupon> [options]

Threshold Jorts custody ceremonies:
  - `--scheme jorts-2of3-sha3` (default): dealerless 2-of-3 RSS Jorts gated by FsBeltWal & FsCeremonyJournal.
  - `--scheme hem-jorts-poseidon2`: dynamic (t, n) Shamir quorum producing canonical 65B/4328B
    JortsPoseidon2 keys & signatures directly aggregatable by untrusted `qsag aggregate`!

subcommands:
  keygen   enroll a quorum custody vault (--vault-dir) and write --public-out
  sign     threshold-sign one monotone leaf epoch across the active quorum
  refresh  proactively refresh (t, n) custodian shares (Π_refresh) in place
  reshare  switch (t, n) -> (t', n') threshold & roster (Π_reshare) under the exact same public key
  verify   verify a qsag quorum signature against --public and --in / --message
  coupon   volatile one-time coupons under a Baggy root key: keygen, session (mint a batch
           and sign from it), verify (see 'qsag quorum coupon --help')
";

const QUORUM_KEYGEN_HELP: &str = "\
qsag quorum keygen --vault-dir <dir> --public-out <path> [options]

Run a dealerless 2-of-3 RSS key generation ceremony with zero central secret reconstruction.

  --vault-dir <dir>             private 0700 directory for party-{0,1,2}.{sk,belt,ceremony}
  --public-out <path>           destination for the quorum public key JSON
  --tree-height <1..=30>         Merkle tree height (default: 3, capacity = 2^height signatures)
  --anchor-dir <dir>            enroll per-party external monotone anchors in <dir>
  --allow-single-disk-anchor    permit --anchor-dir on the same filesystem device as --vault-dir
  --passphrase-env <VAR> / --passphrase-file <PATH>  seal each party secret share
  --policy-ledger-dir <dir>     enroll the quorum against this custody policy ledger: it will
                                then sign only an intent that ledger releases; with
                                --policy-anchor-dir / --policy-passphrase-* as the ledger requires
  --json                        emit the public key JSON to stdout
";

const QUORUM_SIGN_HELP: &str = "\
qsag quorum sign --vault-dir <dir> --epoch <n> --in <file|-> --out <path> [options]

Execute a 2-of-3 Jorts Mode 3A threshold signing ceremony gated by FsBeltWal and FsCeremonyJournal.

  --vault-dir <dir>             directory containing party-{0,1,2}.{sk,belt,ceremony}
  --epoch <n>                   monotone leaf epoch to bind and sign
  --in <file|->                 message path (or '-' for standard input)
  --out <path>                  destination for the quorum signature JSON
  --anchor-dir <dir>            external monotone anchor directory (required if enrolled)
  --allow-single-disk-anchor    permit --anchor-dir on the same filesystem device as --vault-dir
  --policy-id-hex <64-hex>      32-byte policy digest committed into CeremonyContext
  --spend-amount <u64>          spend amount committed into CeremonyContext
  --retry                       recover an already-latched in-flight epoch with identical context
  --deterministic               derive per-attempt session randomness deterministically from cursor
  --passphrase-env <VAR> / --passphrase-file <PATH>  unlock sealed party secret shares
  --json                        emit signing metadata JSON to stdout

Custody policy gate. The message must be the file `qsag policy propose` wrote. An intent
that is unapproved, over a cap, expired, bound to another key or message, or already
released is refused with exit code 3 before a belt latch or a share moves. A quorum
enrolled with --policy-ledger-dir signs only this way. With the gate the ceremony commits
the ledger's policy digest and the intent amount, so --policy-id-hex and --spend-amount
are not accepted. --retry resumes the same epoch and with it the intent this ledger
already released for it.

{GATE}  --policy-retry                sign an already released intent on another epoch: same key,
                                same message, no new spend (after a release whose epoch was refused)
";

const QUORUM_VERIFY_HELP: &str = "\
qsag quorum verify --public <path> --in <file|-> --sig <path> [--json]

Verify a 2-of-3 Jorts quorum signature; exits 0 when valid and 2 when verification fails.
";

fn party_secret_path(vault_dir: &str, party: usize) -> String {
    Path::new(vault_dir)
        .join(format!("party-{party}.sk"))
        .to_string_lossy()
        .into_owned()
}

fn party_belt_path(vault_dir: &str, party: usize) -> String {
    Path::new(vault_dir)
        .join(format!("party-{party}.belt"))
        .to_string_lossy()
        .into_owned()
}

fn party_ceremony_path(vault_dir: &str, party: usize) -> String {
    Path::new(vault_dir)
        .join(format!("party-{party}.ceremony"))
        .to_string_lossy()
        .into_owned()
}

fn tree_path(vault_dir: &str) -> String {
    Path::new(vault_dir)
        .join("quorum-tree.json")
        .to_string_lossy()
        .into_owned()
}

pub(crate) fn ensure_absent(path: &str) -> Result<(), CliError> {
    match std::fs::symlink_metadata(path) {
        Ok(_) => Err(CliError::usage(format!("{path} already exists"))),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(e) => Err(CliError::io(format_args!("inspecting {path}"), e)),
    }
}

fn derive_party_secret(seed: &[u8; 32], party: usize, role: &[u8]) -> Secret32 {
    Secret32(cshake256_framed_32(
        b"QSAG.CLI.QUORUM.PARTY_KDF.V1",
        &[seed, &(party as u64).to_be_bytes(), role],
    ))
}

fn derive_party_key_id(pk: &JortsPublicKey, height: usize, party: usize) -> [u8; 32] {
    cshake256_framed_32(
        b"QSAG.CLI.QUORUM.PARTY_KEY_ID.V1",
        &[
            &pk.pk_seed,
            &pk.pk_root,
            &(height as u64).to_be_bytes(),
            &(party as u64).to_be_bytes(),
        ],
    )
}

fn compute_tree_digest(height: usize, key: &JortsKeyMaterial) -> [u8; 32] {
    let mut flat =
        Vec::with_capacity(64 + 8 + key.levels.iter().map(|l| l.len() * 32).sum::<usize>());
    flat.extend_from_slice(&key.pk.pk_seed);
    flat.extend_from_slice(&key.pk.pk_root);
    flat.extend_from_slice(&(height as u64).to_be_bytes());
    for level in &key.levels {
        flat.extend_from_slice(&(level.len() as u64).to_be_bytes());
        for node in level {
            flat.extend_from_slice(node);
        }
    }
    cshake256_framed_32(b"QSAG.CLI.QUORUM.TREE_DIGEST.V1", &[&flat])
}

fn encode_tree_json(height: usize, key: &JortsKeyMaterial) -> Json {
    let levels: Vec<Json> = key
        .levels
        .iter()
        .map(|lvl| Json::Array(lvl.iter().map(|n| Json::hex(n)).collect()))
        .collect();
    Json::object(vec![
        ("format", Json::str(TREE_FORMAT)),
        ("scheme", Json::str(SCHEME_NAME)),
        ("tree_height", Json::num(height)),
        ("pk_seed", Json::hex(&key.pk.pk_seed)),
        ("pk_root", Json::hex(&key.pk.pk_root)),
        ("levels", Json::Array(levels)),
    ])
}

fn decode_tree_json(
    path: &str,
    expected_height: usize,
    expected_pk: &JortsPublicKey,
    expected_digest: &[u8; 32],
) -> Result<JortsKeyMaterial, CliError> {
    let text = read_text(path)?;
    let json = Json::parse(&text)?;
    if json.field_str("format")? != TREE_FORMAT || json.field_str("scheme")? != SCHEME_NAME {
        return Err(CliError::state("CorruptQuorumTreeMetadata"));
    }
    let height = json.field_u64("tree_height")? as usize;
    let pk_seed: [u8; 32] = from_hex_exact(json.field_str("pk_seed")?, "pk_seed")?;
    let pk_root: [u8; 32] = from_hex_exact(json.field_str("pk_root")?, "pk_root")?;
    if height != expected_height || pk_seed != expected_pk.pk_seed || pk_root != expected_pk.pk_root
    {
        return Err(CliError::state("QuorumTreeHeaderMismatch"));
    }
    let raw_levels = json
        .get("levels")
        .and_then(Json::as_array)
        .ok_or_else(|| CliError::state("CorruptQuorumTreeLevels"))?;
    if raw_levels.len() != expected_height + 1 {
        return Err(CliError::state("CorruptQuorumTreeHeight"));
    }
    let mut levels = Vec::with_capacity(raw_levels.len());
    for (lvl_idx, lvl_json) in raw_levels.iter().enumerate() {
        let expected_nodes = 1usize << (expected_height - lvl_idx);
        let arr = lvl_json
            .as_array()
            .ok_or_else(|| CliError::state("CorruptQuorumTreeLevelArray"))?;
        if arr.len() != expected_nodes {
            return Err(CliError::state("CorruptQuorumTreeLevelWidth"));
        }
        let mut nodes = Vec::with_capacity(expected_nodes);
        for item in arr {
            let s = item
                .as_str()
                .ok_or_else(|| CliError::state("CorruptQuorumTreeNode"))?;
            nodes.push(from_hex_exact(s, "tree_node")?);
        }
        levels.push(nodes);
    }
    let material = JortsKeyMaterial {
        pk: *expected_pk,
        levels,
    };
    let actual_digest = compute_tree_digest(expected_height, &material);
    if !ct_eq_bytes(&actual_digest, expected_digest) {
        return Err(CliError::state("QuorumTreeAuthenticationFailed"));
    }
    Ok(material)
}

fn reconstruct_dkg_shares(
    dkg_session_id: [u8; 32],
    party_seeds: &[Secret32; 3],
    scheme_identity: &[u8; 32],
) -> Result<([RssKeyShare256; 3], [u8; 32]), CliError> {
    let mut dkg_rngs: [PartyPrivateRng; 3] = std::array::from_fn(|p| {
        PartyPrivateRng::from_seed(party_seeds[p].0, b"QSAG.CLI.QUORUM.DKG.RNG.V1")
    });
    let (mut shares, pk_seed) = run_dealerless_rss_dkg_2of3(dkg_session_id, 32, &mut dkg_rngs)
        .map_err(|e| CliError::state(format!("quorum DKG reconstruction failed: {e}")))?;
    for share in &mut shares {
        share
            .bind_scheme_identity(scheme_identity)
            .map_err(|e| CliError::state(format!("quorum key binding failed: {e}")))?;
    }
    Ok((shares, pk_seed))
}

fn encode_jorts_sig(params: &JortsParams, sig: &JortsSig) -> Vec<u8> {
    let mut out = Vec::with_capacity(params.sig_bytes());
    out.extend_from_slice(&sig.epoch.to_be_bytes());
    out.extend_from_slice(&sig.retry_salt);
    out.extend_from_slice(&sig.ctr.to_be_bytes());
    for chain in &sig.chains {
        out.extend_from_slice(chain);
    }
    for node in &sig.auth {
        out.extend_from_slice(node);
    }
    debug_assert_eq!(out.len(), params.sig_bytes());
    out
}

fn decode_jorts_sig(params: &JortsParams, bytes: &[u8]) -> Result<JortsSig, CliError> {
    if bytes.len() != params.sig_bytes() {
        return Err(CliError::verify("quorum signature length mismatch"));
    }
    let epoch = u64::from_be_bytes(bytes[..8].try_into().unwrap());
    let mut retry_salt = [0u8; 32];
    retry_salt.copy_from_slice(&bytes[8..40]);
    let ctr = u32::from_be_bytes(bytes[40..44].try_into().unwrap());
    let mut offset = 44usize;
    let mut chains = Vec::with_capacity(params.wots.chains);
    for _ in 0..params.wots.chains {
        let mut node = [0u8; 32];
        node.copy_from_slice(&bytes[offset..offset + 32]);
        chains.push(node);
        offset += 32;
    }
    let mut auth = Vec::with_capacity(params.height);
    for _ in 0..params.height {
        let mut node = [0u8; 32];
        node.copy_from_slice(&bytes[offset..offset + 32]);
        auth.push(node);
        offset += 32;
    }
    Ok(JortsSig {
        epoch,
        retry_salt,
        ctr,
        chains,
        auth,
    })
}

fn reject_hem_unsupported_keygen_args(args: &Args) -> Result<(), CliError> {
    for opt in [
        "tree-height",
        "anchor-dir",
        "policy-ledger-dir",
        "policy-anchor-dir",
        "policy-passphrase-env",
        "policy-passphrase-file",
    ] {
        if args.get(opt).is_some() {
            return Err(CliError::usage(format!(
                "--{opt} is only supported with --scheme {SCHEME_NAME}"
            )));
        }
    }
    for flag in [
        "allow-single-disk-anchor",
        "policy-allow-single-disk-anchor",
    ] {
        if args.flag(flag) {
            return Err(CliError::usage(format!(
                "--{flag} is only supported with --scheme {SCHEME_NAME}"
            )));
        }
    }
    Ok(())
}

fn reject_hem_unsupported_sign_args(args: &Args) -> Result<(), CliError> {
    for opt in [
        "anchor-dir",
        "policy-id-hex",
        "spend-amount",
        "policy-ledger-dir",
        "policy-intent",
        "policy-anchor-dir",
        "policy-passphrase-env",
        "policy-passphrase-file",
    ] {
        if args.get(opt).is_some() {
            return Err(CliError::usage(format!(
                "--{opt} is only supported with --scheme {SCHEME_NAME}"
            )));
        }
    }
    for flag in [
        "allow-single-disk-anchor",
        "policy-allow-single-disk-anchor",
        "policy-retry",
        "retry",
        "deterministic",
    ] {
        if args.flag(flag) {
            return Err(CliError::usage(format!(
                "--{flag} is only supported with --scheme {SCHEME_NAME}"
            )));
        }
    }
    Ok(())
}

pub fn run(raw: &[String]) -> Result<(), CliError> {
    let Some((sub, rest)) = raw.split_first() else {
        eprint!("{QUORUM_HELP}");
        return Err(CliError::usage(
            "quorum expects a subcommand (keygen, sign, refresh, reshare, verify, coupon)",
        ));
    };
    match sub.as_str() {
        "--help" | "-h" | "help" => {
            print!("{QUORUM_HELP}");
            Ok(())
        }
        "keygen" => keygen(rest),
        "sign" => sign(rest),
        "refresh" => crate::quorum_hem::refresh(rest),
        "reshare" => crate::quorum_hem::reshare(rest),
        "verify" => verify(rest),
        "coupon" => crate::quorum_coupon::run(rest),
        other => Err(CliError::usage(format!(
            "unknown quorum subcommand '{other}' (try 'qsag quorum --help')"
        ))),
    }
}

fn keygen(raw: &[String]) -> Result<(), CliError> {
    let args = Args::parse(
        raw,
        &[
            "scheme",
            "threshold",
            "parties",
            "leaves",
            "seed-file",
            "vault-dir",
            "public-out",
            "tree-height",
            "anchor-dir",
            "passphrase-env",
            "passphrase-file",
            "policy-ledger-dir",
            "policy-anchor-dir",
            "policy-passphrase-env",
            "policy-passphrase-file",
        ],
        &[
            "allow-single-disk-anchor",
            "policy-allow-single-disk-anchor",
            "json",
            "help",
        ],
    )?;
    if args.flag("help") {
        print!("{QUORUM_KEYGEN_HELP}");
        return Ok(());
    }
    args.no_positionals()?;
    match args.get("scheme") {
        Some(crate::quorum_hem::HEM_SCHEME_NAME) => {
            reject_hem_unsupported_keygen_args(&args)?;
            return crate::quorum_hem::keygen(&args);
        }
        Some(SCHEME_NAME) | None => {
            if args.get("threshold").is_some()
                || args.get("parties").is_some()
                || args.get("leaves").is_some()
                || args.get("seed-file").is_some()
            {
                return Err(CliError::usage(
                    "--threshold, --parties, --leaves, and --seed-file apply to --scheme hem-jorts-poseidon2",
                ));
            }
        }
        Some(other) => {
            return Err(CliError::usage(format!(
                "unknown quorum --scheme '{other}' (expected {SCHEME_NAME} or {})",
                crate::quorum_hem::HEM_SCHEME_NAME
            )));
        }
    }
    let policy_pin = crate::policy_ledger::key_pin_from_args(&args)?;
    let vault_dir = args.require("vault-dir")?;
    let public_out = args.require("public-out")?;
    let height_u64 = args.get_u64("tree-height")?.unwrap_or(3);
    if !(1..=MAX_CLI_TREE_HEIGHT).contains(&height_u64) {
        return Err(CliError::usage(format!(
            "--tree-height must be between 1 and {MAX_CLI_TREE_HEIGHT}"
        )));
    }
    let height = height_u64 as usize;
    let params = JortsParams::with_height(height);
    let passphrase = crate::envelope::passphrase(&args)?;
    let anchor_cfg = AnchorConfig::from_quorum_args(&args, vault_dir)?;

    ensure_absent(public_out)?;
    private_dir(vault_dir, true)?;
    let party_sk_paths: [String; 3] = std::array::from_fn(|p| party_secret_path(vault_dir, p));
    let party_sk_refs: [&str; 3] = [
        party_sk_paths[0].as_str(),
        party_sk_paths[1].as_str(),
        party_sk_paths[2].as_str(),
    ];
    let tree_file = tree_path(vault_dir);
    for (p, sk_path) in party_sk_paths.iter().enumerate() {
        ensure_absent(sk_path)?;
        ensure_absent(&party_belt_path(vault_dir, p))?;
        ensure_absent(&party_ceremony_path(vault_dir, p))?;
    }
    ensure_absent(&tree_file)?;

    if let Some(cfg) = &anchor_cfg {
        cfg.validate_isolation(&party_sk_refs, &[vault_dir], true)?;
    }

    let dkg_session_id = os_random_32()?;
    let party_seeds: [Secret32; 3] = [
        Secret32(os_random_32()?),
        Secret32(os_random_32()?),
        Secret32(os_random_32()?),
    ];
    let mut dkg_rngs: [PartyPrivateRng; 3] = std::array::from_fn(|p| {
        PartyPrivateRng::from_seed(party_seeds[p].0, b"QSAG.CLI.QUORUM.DKG.RNG.V1")
    });
    let (shares, pk_seed) = run_dealerless_rss_dkg_2of3(dkg_session_id, 32, &mut dkg_rngs)
        .map_err(|e| CliError::state(format!("dealerless 2-of-3 DKG failed: {e}")))?;

    let keygen_engine_sid = os_random_32()?;
    let keygen_rngs: [PartyPrivateRng; 3] = [
        PartyPrivateRng::from_seed(os_random_32()?, b"QSAG.CLI.QUORUM.KEYGEN.RNG.V1"),
        PartyPrivateRng::from_seed(os_random_32()?, b"QSAG.CLI.QUORUM.KEYGEN.RNG.V1"),
        PartyPrivateRng::from_seed(os_random_32()?, b"QSAG.CLI.QUORUM.KEYGEN.RNG.V1"),
    ];
    let mut engine = Rss256Engine::new(keygen_engine_sid, shares, keygen_rngs)
        .map_err(|e| CliError::state(format!("initializing 2-of-3 MPC engine failed: {e}")))?;
    let key_material = jorts_keygen_mpc(&mut engine, &params)
        .map_err(|e| CliError::state(format!("distributed Jorts keygen failed: {e}")))?;
    debug_assert_eq!(key_material.pk.pk_seed, pk_seed);

    let tree_digest = compute_tree_digest(height, &key_material);
    let tree_json = encode_tree_json(height, &key_material);
    write_new(&tree_file, tree_json.to_pretty().as_bytes(), false)?;

    for (p, sk_path) in party_sk_paths.iter().enumerate() {
        let mut vault = Vault::acquire(sk_path, true)?;
        let party_key_id = derive_party_key_id(&key_material.pk, height, p);
        let belt_mac = derive_party_secret(&party_seeds[p].0, p, b"belt_wal_mac");
        let ceremony_mac = derive_party_secret(&party_seeds[p].0, p, b"ceremony_journal_mac");

        let (belt_wal, belt_seal) = if let Some(cfg) = &anchor_cfg {
            let belt_anchor_mac =
                derive_party_secret(&party_seeds[p].0, p, b"external_belt_anchor_mac");
            let belt_anchor = FsExternalMountAnchor::provision_fresh(
                cfg,
                &party_sk_refs,
                &[vault_dir],
                "quorum_belt",
                party_key_id,
                belt_anchor_mac.0,
            )?;
            let seal = belt_anchor.lock_identity_seal();
            let w = FsBeltWal::provision_genesis_anchored(
                party_belt_path(vault_dir, p),
                belt_mac.0,
                Box::new(belt_anchor),
            )
            .map_err(|e| CliError::io("provisioning anchored belt WAL", e))?;
            (w, Some(seal))
        } else {
            let w = FsBeltWal::provision_genesis(party_belt_path(vault_dir, p), belt_mac.0)
                .map_err(|e| CliError::io("provisioning belt WAL", e))?;
            (w, None)
        };
        let belt_ckpt = belt_wal.checkpoint();

        let (ceremony_journal, ceremony_seal) = if let Some(cfg) = &anchor_cfg {
            let ceremony_anchor_mac =
                derive_party_secret(&party_seeds[p].0, p, b"external_ceremony_anchor_mac");
            let ceremony_anchor = FsExternalMountAnchor::provision_fresh(
                cfg,
                &party_sk_refs,
                &[vault_dir],
                "quorum_ceremony",
                party_key_id,
                ceremony_anchor_mac.0,
            )?;
            let seal = ceremony_anchor.lock_identity_seal();
            let j = FsCeremonyJournal::create_new_anchored(
                party_ceremony_path(vault_dir, p),
                party_key_id,
                ceremony_mac.0,
                Box::new(ceremony_anchor),
            )
            .map_err(|e| CliError::io("provisioning anchored ceremony journal", e))?;
            (j, Some(seal))
        } else {
            let j = FsCeremonyJournal::create_new(
                party_ceremony_path(vault_dir, p),
                party_key_id,
                ceremony_mac.0,
            )
            .map_err(|e| CliError::io("provisioning ceremony journal", e))?;
            (j, None)
        };
        let ceremony_ckpt = ceremony_journal.checkpoint();

        let enrollment_nonce = os_random_32()?;
        let mut fields = vec![
            ("format", Json::str(PARTY_SECRET_FORMAT)),
            ("scheme", Json::str(SCHEME_NAME)),
            ("party_id", Json::num(p)),
            ("tree_height", Json::num(height)),
            ("dkg_session_id", Json::hex(&dkg_session_id)),
            ("pk_seed", Json::hex(&key_material.pk.pk_seed)),
            ("pk_root", Json::hex(&key_material.pk.pk_root)),
            ("tree_digest", Json::hex(&tree_digest)),
            ("enrollment_nonce", Json::hex(&enrollment_nonce[..16])),
            ("uses_completed", Json::num(0)),
            ("belt_checkpoint_gen", Json::num(belt_ckpt.generation)),
            ("belt_checkpoint_tag", Json::hex(&belt_ckpt.tag)),
            (
                "ceremony_checkpoint_gen",
                Json::num(ceremony_ckpt.generation),
            ),
            ("ceremony_checkpoint_tag", Json::hex(&ceremony_ckpt.tag)),
            ("seed", Json::hex(&party_seeds[p].0)),
        ];
        if let (Some(b_seal), Some(c_seal)) = (belt_seal, ceremony_seal) {
            fields.push(("anchor_required", Json::Bool(true)));
            fields.push(("anchor_belt_seal", Json::hex(&b_seal)));
            fields.push(("anchor_ceremony_seal", Json::hex(&c_seal)));
        }
        if let Some(ledger) = &policy_pin {
            fields.push((crate::policy_ledger::KEY_PIN_FIELD, Json::hex(ledger)));
        }
        let mut secret = Json::object(fields);
        vault.set_key_material(&crate::envelope::open(&secret, None)?);
        if let Some(pass) = &passphrase {
            crate::envelope::seal(&mut secret, pass)?;
        }
        vault.bind(&mut secret)?;
        vault.prepare(&mut secret)?;
        let encoded = ZeroizingBuf(secret.to_pretty().into_bytes());
        vault.seal(&mut secret)?;
        write_new(sk_path, &encoded.0, true)?;
    }

    let public = Json::object(vec![
        ("format", Json::str(PUBLIC_FORMAT)),
        ("scheme", Json::str(SCHEME_NAME)),
        ("custody_model", Json::str("dealerless-2of3-rss-jorts")),
        ("tree_height", Json::num(height)),
        ("capacity", Json::num(params.capacity())),
        ("pk_seed", Json::hex(&key_material.pk.pk_seed)),
        ("pk_root", Json::hex(&key_material.pk.pk_root)),
    ]);
    write_new(public_out, public.to_pretty().as_bytes(), false)?;

    if args.flag("json") {
        print!("{}", public.to_pretty());
    } else {
        println!(
            "enrolled 2-of-3 Jorts quorum (height {height}, capacity {}) in {vault_dir} -> {public_out}",
            params.capacity()
        );
    }
    Ok(())
}

struct QuorumHeaderMeta {
    height: usize,
    dkg_session_id: [u8; 32],
    pk: JortsPublicKey,
    tree_digest: [u8; 32],
    anchor_required: bool,
}

struct LoadedParty {
    vault: Vault,
    sk_path: String,
    secret_on_disk: Json,
    seed: Secret32,
    uses_completed: u64,
    party_key_id: [u8; 32],
}

fn sign(raw: &[String]) -> Result<(), CliError> {
    let args = Args::parse(
        raw,
        &[
            "scheme",
            "signers",
            "ackers",
            "vault-dir",
            "epoch",
            "in",
            "message",
            "out",
            "anchor-dir",
            "policy-id-hex",
            "spend-amount",
            "passphrase-env",
            "passphrase-file",
            "policy-ledger-dir",
            "policy-intent",
            "policy-anchor-dir",
            "policy-passphrase-env",
            "policy-passphrase-file",
        ],
        &[
            "allow-single-disk-anchor",
            "policy-allow-single-disk-anchor",
            "policy-retry",
            "retry",
            "deterministic",
            "json",
            "help",
        ],
    )?;
    if args.flag("help") {
        print!(
            "{}",
            QUORUM_SIGN_HELP.replace("{GATE}", crate::policy_ledger::GATE_HELP)
        );
        return Ok(());
    }
    args.no_positionals()?;
    let vault_dir = args.require("vault-dir")?;
    let use_hem = match args.get("scheme") {
        Some(crate::quorum_hem::HEM_SCHEME_NAME) => true,
        Some(SCHEME_NAME) => false,
        Some(other) => {
            return Err(CliError::usage(format!(
                "unknown quorum --scheme '{other}'"
            )));
        }
        None => crate::quorum_hem::is_hem_vault(vault_dir),
    };
    if use_hem {
        reject_hem_unsupported_sign_args(&args)?;
        return crate::quorum_hem::sign(&args);
    }
    if args.get("signers").is_some() || args.get("ackers").is_some() {
        return Err(CliError::usage(
            "--signers and --ackers apply to --scheme hem-jorts-poseidon2 vaults",
        ));
    }
    if args.get("in").is_some() && args.get("message").is_some() {
        return Err(CliError::usage("pass either --message or --in, not both"));
    }
    let epoch = args
        .get_u64("epoch")?
        .ok_or_else(|| CliError::usage("missing required option --epoch"))?;
    let out_path = args.require("out")?;
    ensure_absent(out_path)?;
    let msg_arg = args
        .get("message")
        .or_else(|| args.get("in"))
        .ok_or_else(|| CliError::usage("missing required option --in"))?;
    let message = read_input(msg_arg)?;
    let is_retry = args.flag("retry");
    let deterministic = args.flag("deterministic");
    let has_context_flags =
        args.get("policy-id-hex").is_some() || args.get("spend-amount").is_some();
    let mut base_context = parse_ceremony_context(&args, 0)?;
    let passphrase = crate::envelope::passphrase(&args)?;
    let anchor_cfg = AnchorConfig::from_quorum_args(&args, vault_dir)?;
    // The ledger lock is taken before any party's and held until the signature is written.
    let mut gate = crate::policy_ledger::Gate::from_args(&args, true)?;
    let policy_retry = args.flag("policy-retry");
    if gate.is_none() && policy_retry {
        return Err(CliError::usage(
            "--policy-retry requires --policy-ledger-dir",
        ));
    }
    if gate.is_some() && has_context_flags {
        return Err(CliError::usage(
            "--policy-id-hex and --spend-amount are taken from the released intent under --policy-ledger-dir",
        ));
    }
    if let Some(gate) = &gate {
        // The ceremony journal records a 64-bit spend; refuse a wider one up front.
        crate::policy_ledger::ceremony_spend(gate.intent_amount()?)?;
    }

    private_dir(vault_dir, false)?;
    let party_sk_paths: [String; 3] = std::array::from_fn(|p| party_secret_path(vault_dir, p));
    let party_sk_refs: [&str; 3] = [
        party_sk_paths[0].as_str(),
        party_sk_paths[1].as_str(),
        party_sk_paths[2].as_str(),
    ];

    let mut parties_vec: Vec<LoadedParty> = Vec::with_capacity(3);
    let mut header_meta: Option<QuorumHeaderMeta> = None;

    for (p, sk_path) in party_sk_paths.iter().enumerate() {
        let mut vault = Vault::acquire(sk_path, false)?;
        let raw_text = read_text(sk_path)?;
        let secret_on_disk = Json::parse(&raw_text)?;
        if secret_on_disk.field_str("format")? != PARTY_SECRET_FORMAT
            || secret_on_disk.field_str("scheme")? != SCHEME_NAME
            || secret_on_disk.field_u64("party_id")? != p as u64
        {
            return Err(corrupt());
        }
        let opened = crate::envelope::open(&secret_on_disk, passphrase.as_deref())?;
        vault.set_key_material(&opened);
        vault.authenticate(&secret_on_disk)?;
        crate::policy_ledger::enforce_key_pin(&secret_on_disk, gate.as_ref())?;
        let anchor_req = enforce_anchor_requirement(&secret_on_disk, anchor_cfg.as_ref())?;

        let height_u64 = secret_on_disk.field_u64("tree_height")?;
        if !(1..=MAX_CLI_TREE_HEIGHT).contains(&height_u64) {
            return Err(corrupt());
        }
        let height = height_u64 as usize;
        let dkg_sid: [u8; 32] = from_hex_exact(
            secret_on_disk.field_str("dkg_session_id")?,
            "dkg_session_id",
        )?;
        let pk_seed: [u8; 32] = from_hex_exact(secret_on_disk.field_str("pk_seed")?, "pk_seed")?;
        let pk_root: [u8; 32] = from_hex_exact(secret_on_disk.field_str("pk_root")?, "pk_root")?;
        let tree_digest: [u8; 32] =
            from_hex_exact(secret_on_disk.field_str("tree_digest")?, "tree_digest")?;
        let pk = JortsPublicKey { pk_seed, pk_root };

        match &header_meta {
            None => {
                header_meta = Some(QuorumHeaderMeta {
                    height,
                    dkg_session_id: dkg_sid,
                    pk,
                    tree_digest,
                    anchor_required: anchor_req,
                })
            }
            Some(m0) => {
                if m0.height != height
                    || !ct_eq_bytes(&m0.dkg_session_id, &dkg_sid)
                    || m0.pk != pk
                    || !ct_eq_bytes(&m0.tree_digest, &tree_digest)
                    || m0.anchor_required != anchor_req
                {
                    return Err(CliError::state("QuorumPartyMetadataMismatch"));
                }
            }
        }

        let seed = opened.seed()?;
        let uses_completed = secret_on_disk.field_u64("uses_completed")?;
        let party_key_id = derive_party_key_id(&pk, height, p);
        parties_vec.push(LoadedParty {
            vault,
            sk_path: sk_path.clone(),
            secret_on_disk,
            seed,
            uses_completed,
            party_key_id,
        });
    }

    let QuorumHeaderMeta {
        height,
        dkg_session_id,
        pk,
        tree_digest,
        anchor_required: _,
    } = header_meta.ok_or_else(corrupt)?;
    let params = JortsParams::with_height(height);
    if epoch >= params.capacity() {
        return Err(CliError::state("epoch exceeds quorum tree capacity"));
    }

    if let Some(cfg) = &anchor_cfg {
        cfg.validate_isolation(&party_sk_refs, &[vault_dir], false)?;
    }

    let key_material = decode_tree_json(&tree_path(vault_dir), height, &pk, &tree_digest)?;

    let mut wals_vec: Vec<FsBeltWal> = Vec::with_capacity(3);
    let mut journals_vec: Vec<FsCeremonyJournal> = Vec::with_capacity(3);
    let mut ceremony_anchors: Vec<Option<FsExternalMountAnchor>> = Vec::with_capacity(3);

    for (p, party) in parties_vec.iter().enumerate() {
        let local_belt_ckpt = read_belt_checkpoint(&party.secret_on_disk)?;
        let local_ceremony_ckpt = read_ceremony_checkpoint(&party.secret_on_disk)?;
        let belt_mac = derive_party_secret(&party.seed.0, p, b"belt_wal_mac");
        let ceremony_mac = derive_party_secret(&party.seed.0, p, b"ceremony_journal_mac");

        let wal = if let Some(cfg) = &anchor_cfg {
            let belt_anchor_mac =
                derive_party_secret(&party.seed.0, p, b"external_belt_anchor_mac");
            let belt_anchor = FsExternalMountAnchor::open_existing(
                cfg,
                &party_sk_refs,
                &[vault_dir],
                "quorum_belt",
                party.party_key_id,
                belt_anchor_mac.0,
            )?;
            belt_anchor.verify_expected_seal(&party.secret_on_disk, "anchor_belt_seal")?;
            let w = FsBeltWal::open_existing_anchored(
                party_belt_path(vault_dir, p),
                belt_mac.0,
                Box::new(belt_anchor),
            )
            .map_err(|_| CliError::state("CorruptOrRolledBackBeltWal"))?;
            let w_ckpt = w.checkpoint();
            if w_ckpt.generation < local_belt_ckpt.generation
                || (w_ckpt.generation == local_belt_ckpt.generation
                    && !ct_eq_bytes(&w_ckpt.tag, &local_belt_ckpt.tag))
            {
                return Err(CliError::state("CorruptOrRolledBackBeltWal"));
            }
            w
        } else {
            FsBeltWal::open_existing_at_least(
                party_belt_path(vault_dir, p),
                belt_mac.0,
                local_belt_ckpt,
            )
            .map_err(|_| CliError::state("CorruptOrRolledBackBeltWal"))?
        };
        wals_vec.push(wal);

        if let Some(cfg) = &anchor_cfg {
            let ceremony_anchor_mac =
                derive_party_secret(&party.seed.0, p, b"external_ceremony_anchor_mac");
            let ceremony_anchor = FsExternalMountAnchor::open_existing(
                cfg,
                &party_sk_refs,
                &[vault_dir],
                "quorum_ceremony",
                party.party_key_id,
                ceremony_anchor_mac.0,
            )?;
            ceremony_anchor.verify_expected_seal(&party.secret_on_disk, "anchor_ceremony_seal")?;
            let j = FsCeremonyJournal::open_existing_anchored(
                party_ceremony_path(vault_dir, p),
                party.party_key_id,
                ceremony_mac.0,
                Box::new(ceremony_anchor.clone()),
            )
            .map_err(|_| CliError::state("CorruptOrRolledBackCeremonyJournal"))?;
            let j_ckpt = j.checkpoint();
            if j_ckpt.generation < local_ceremony_ckpt.generation
                || (j_ckpt.generation == local_ceremony_ckpt.generation
                    && !ct_eq_bytes(&j_ckpt.tag, &local_ceremony_ckpt.tag))
            {
                return Err(CliError::state("CorruptOrRolledBackCeremonyJournal"));
            }
            journals_vec.push(j);
            ceremony_anchors.push(Some(ceremony_anchor));
        } else {
            let j = FsCeremonyJournal::open_existing_at_least(
                party_ceremony_path(vault_dir, p),
                party.party_key_id,
                ceremony_mac.0,
                local_ceremony_ckpt,
            )
            .map_err(|_| CliError::state("CorruptOrRolledBackCeremonyJournal"))?;
            journals_vec.push(j);
            ceremony_anchors.push(None);
        }
    }

    let wals: [FsBeltWal; 3] = wals_vec
        .try_into()
        .map_err(|_| CliError::state("internal quorum WAL count mismatch"))?;
    let mut journals: [FsCeremonyJournal; 3] = journals_vec
        .try_into()
        .map_err(|_| CliError::state("internal quorum journal count mismatch"))?;

    let party_seeds: [Secret32; 3] = [
        Secret32(parties_vec[0].seed.0),
        Secret32(parties_vec[1].seed.0),
        Secret32(parties_vec[2].seed.0),
    ];
    let (shares, derived_pk_seed) =
        reconstruct_dkg_shares(dkg_session_id, &party_seeds, &tree_digest)?;
    if !ct_eq_bytes(&derived_pk_seed, &pk.pk_seed) {
        return Err(CliError::state("QuorumDkgPublicSeedMismatch"));
    }

    let max_uses = parties_vec
        .iter()
        .map(|p| p.uses_completed)
        .max()
        .unwrap_or(0);
    let max_journal_gen = journals
        .iter()
        .map(|j| j.checkpoint().generation)
        .max()
        .unwrap_or(1);
    let next_cursor = max_uses
        .max(max_journal_gen)
        .checked_add(1)
        .ok_or_else(|| CliError::state("quorum ceremony cursor exhausted"))?;

    let msg_digest = jorts_msg_digest(&pk, &message);
    let attempt_entropy = if deterministic {
        Secret32([0u8; 32])
    } else {
        Secret32(os_random_32()?)
    };
    let online_session_id = cshake256_framed_32(
        b"QSAG.CLI.QUORUM.ONLINE_SID.V1",
        &[
            &attempt_entropy.0,
            &dkg_session_id,
            &tree_digest,
            &next_cursor.to_be_bytes(),
            &epoch.to_be_bytes(),
            &msg_digest,
        ],
    );
    // Drawn up front so an entropy failure stops the ceremony instead of thinning a hedge.
    let mut party_fresh = [
        Secret32([0u8; 32]),
        Secret32([0u8; 32]),
        Secret32([0u8; 32]),
    ];
    if !deterministic {
        for fresh in &mut party_fresh {
            fresh.0 = os_random_32()?;
        }
    }
    let online_rngs: [PartyPrivateRng; 3] = std::array::from_fn(|p| {
        let hedge = Secret32(cshake256_framed_32(
            b"QSAG.CLI.QUORUM.ONLINE_RNG.V1",
            &[
                &party_seeds[p].0,
                &party_fresh[p].0,
                &online_session_id,
                &(p as u64).to_be_bytes(),
                &next_cursor.to_be_bytes(),
            ],
        ));
        PartyPrivateRng::from_seed(hedge.0, b"QSAG.CLI.QUORUM.ONLINE_RNG_STREAM.V1")
    });

    // Every check that needs no durable write has passed. Release the intent for exactly
    // this quorum key and message before a belt latch, a journal or a share moves.
    let mut policy_fields: Vec<(&str, Json)> = Vec::new();
    if let Some(gate) = gate.as_mut() {
        let granted = gate.authorize(
            &crate::policy_ledger::signing_key_id(
                SCHEME_NAME,
                &[&pk.pk_seed[..], &pk.pk_root[..]].concat(),
            ),
            &message,
            &[],
            is_retry || policy_retry,
        )?;
        base_context.policy_id = granted.policy_digest;
        base_context.spend_amount = crate::policy_ledger::ceremony_spend(granted.amount_units)?;
        policy_fields.push(("policy_ledger_id", Json::hex(gate.ledger_id())));
        policy_fields.push(("policy_digest", Json::hex(&granted.policy_digest)));
        policy_fields.push(("policy_intent", Json::hex(&granted.intent_id)));
        policy_fields.push(("spend_amount", Json::num(granted.amount_units)));
    }

    let mut engine = Rss256Engine::new(online_session_id, shares, online_rngs)
        .map_err(|e| CliError::state(format!("initializing quorum signing engine failed: {e}")))?;
    let mut signer = JortsSigner::new(params, key_material, wals, engine.keys())
        .map_err(|e| CliError::state(format!("recovering quorum belt latches failed: {e}")))?;

    let prepared = signer
        .prepare_sign_mode3a(&mut engine, epoch, &message)
        .map_err(|e| CliError::state(format!("quorum belt latch refused epoch {epoch}: {e}")))?;

    let context = CeremonyContext {
        policy_id: base_context.policy_id,
        spend_amount: base_context.spend_amount,
        mpc_nonce_epoch: next_cursor,
    };

    let mut ceremony_ids = [[0u8; 32]; 3];
    let mut permits_opt: [Option<qsag_core::ceremony_journal::CeremonyReleasePermit>; 3] =
        [None, None, None];
    for p in 0..3 {
        let cid = cshake256_framed_32(
            b"QSAG.CLI.QUORUM.CEREMONY_ID.V1",
            &[
                &online_session_id,
                &parties_vec[p].party_key_id,
                &epoch.to_be_bytes(),
                &next_cursor.to_be_bytes(),
                &prepared.records()[p].binding(),
            ],
        );
        ceremony_ids[p] = cid;
        let permit = journals[p]
            .persist_with_context(
                CeremonyReservation {
                    ceremony_id: cid,
                    key_id: parties_vec[p].party_key_id,
                    epoch_or_codeword: prepared.records()[p].binding(),
                    seed_burn_cursor: next_cursor,
                    hedge_generation: next_cursor,
                },
                Some(epoch),
                is_retry,
                context,
            )
            .map_err(|_| {
                CliError::state(
                    "CorruptOrConflictingCeremonyJournal (pass --retry to recover an in-flight epoch with identical context)",
                )
            })?;
        permits_opt[p] = Some(permit);
    }
    let permits = [
        permits_opt[0].take().unwrap(),
        permits_opt[1].take().unwrap(),
        permits_opt[2].take().unwrap(),
    ];

    signer
        .install_ceremony_permits(
            &prepared,
            [&journals[0], &journals[1], &journals[2]],
            permits,
        )
        .map_err(|e| CliError::state(format!("installing quorum ceremony permits failed: {e}")))?;

    for p in 0..3 {
        if let Some(anchor) = &ceremony_anchors[p] {
            anchor
                .consume_ceremony_ticket(journals[p].checkpoint(), &ceremony_ids[p])
                .map_err(|_| CliError::state("CeremonyTicketAlreadyConsumedOrCorrupt"))?;
        }
    }

    for (p, party) in parties_vec.iter_mut().enumerate() {
        let belt_ckpt = signer.latches()[p].wal().checkpoint();
        let ceremony_ckpt = journals[p].checkpoint();
        record_belt_checkpoint(&mut party.secret_on_disk, belt_ckpt);
        record_ceremony_checkpoint(&mut party.secret_on_disk, ceremony_ckpt);
        set(
            &mut party.secret_on_disk,
            "uses_completed",
            Json::num(next_cursor - 1),
        );
        party
            .vault
            .reserve(&party.sk_path, &mut party.secret_on_disk)?;
    }

    let sig = signer
        .complete_sign_mode3a(&mut engine, prepared, &message)
        .map_err(|e| CliError::state(format!("quorum Mode 3A signing failed: {e}")))?;
    if !jorts_verify(&params, &pk, &message, &sig) {
        return Err(CliError::verify(
            "verify-before-release aborted faulted quorum signature",
        ));
    }

    let sig_bytes = ZeroizingBuf(encode_jorts_sig(&params, &sig));
    let mut sig_fields = vec![
        ("format", Json::str(SIG_FORMAT)),
        ("scheme", Json::str(SCHEME_NAME)),
        ("tree_height", Json::num(height)),
        ("epoch", Json::num(sig.epoch)),
        ("pk_seed", Json::hex(&pk.pk_seed)),
        ("pk_root", Json::hex(&pk.pk_root)),
    ];
    if has_context_flags {
        sig_fields.push(("policy_id", Json::hex(&context.policy_id)));
        sig_fields.push(("spend_amount", Json::num(context.spend_amount)));
    }
    sig_fields.extend(policy_fields);
    sig_fields.push(("signature", Json::hex(&sig_bytes.0)));
    let sig_json = Json::object(sig_fields);
    write_new(out_path, sig_json.to_pretty().as_bytes(), false)?;

    if args.flag("json") {
        let report = Json::object(vec![
            ("scheme", Json::str(SCHEME_NAME)),
            ("epoch", Json::num(sig.epoch)),
            ("signature_bytes", Json::num(sig_bytes.len())),
            ("out", Json::str(out_path)),
        ]);
        print!("{}", report.to_pretty());
    } else {
        println!(
            "signed quorum epoch {} ({} bytes) -> {out_path}",
            sig.epoch,
            sig_bytes.len()
        );
    }
    Ok(())
}

fn verify(raw: &[String]) -> Result<(), CliError> {
    let args = Args::parse(raw, &["public", "in", "message", "sig"], &["json", "help"])?;
    if args.flag("help") {
        print!("{QUORUM_VERIFY_HELP}");
        return Ok(());
    }
    args.no_positionals()?;
    if args.get("in").is_some() && args.get("message").is_some() {
        return Err(CliError::usage("pass either --message or --in, not both"));
    }
    let pub_path = args.require("public")?;
    let sig_path = args.require("sig")?;
    let msg_arg = args
        .get("message")
        .or_else(|| args.get("in"))
        .ok_or_else(|| CliError::usage("missing required option --in (or --message)"))?;
    let message = read_input(msg_arg)?;

    let pub_text = read_text(pub_path)?;
    let pub_json = Json::parse(&pub_text)?;
    if pub_json.field_str("format")? != PUBLIC_FORMAT {
        return Err(CliError::input("unexpected quorum public key format"));
    }
    if pub_json.field_str("scheme")? == crate::quorum_hem::HEM_SCHEME_NAME {
        return crate::quorum_hem::verify(&pub_json, &message, sig_path, args.flag("json"));
    }
    if pub_json.field_str("scheme")? != SCHEME_NAME {
        return Err(CliError::input("unexpected quorum public key scheme"));
    }
    let height_u64 = pub_json.field_u64("tree_height")?;
    if !(1..=30).contains(&height_u64) {
        return Err(CliError::input("unsupported quorum tree height"));
    }
    let params = JortsParams::with_height(height_u64 as usize);
    let pk = JortsPublicKey {
        pk_seed: from_hex_exact(pub_json.field_str("pk_seed")?, "pk_seed")?,
        pk_root: from_hex_exact(pub_json.field_str("pk_root")?, "pk_root")?,
    };

    let sig_raw = read_bounded_file(sig_path, MAX_SIG_PROOF_BYTES)?;
    let sig_str = std::str::from_utf8(&sig_raw.0)
        .map_err(|_| CliError::input(format!("{sig_path} is not UTF-8 text")))?;
    let sig_json = Json::parse(sig_str)?;
    if sig_json.field_str("format")? != SIG_FORMAT || sig_json.field_str("scheme")? != SCHEME_NAME {
        return Err(CliError::input("unexpected quorum signature format"));
    }
    if sig_json.field_u64("tree_height")? != height_u64 {
        return Err(CliError::verify("quorum signature tree height mismatch"));
    }
    let sig_bytes = sig_json.field_hex("signature")?;
    let sig = decode_jorts_sig(&params, &sig_bytes)?;
    if sig.epoch != sig_json.field_u64("epoch")? {
        return Err(CliError::verify("quorum signature epoch header mismatch"));
    }
    if !jorts_verify(&params, &pk, &message, &sig) {
        return Err(CliError::verify("quorum signature verification failed"));
    }

    if args.flag("json") {
        let report = Json::object(vec![
            ("valid", Json::Bool(true)),
            ("scheme", Json::str(SCHEME_NAME)),
            ("epoch", Json::num(sig.epoch)),
        ]);
        print!("{}", report.to_pretty());
    } else {
        println!("VALID ({SCHEME_NAME}, epoch {})", sig.epoch);
    }
    Ok(())
}

#[cfg(test)]
mod hem_flag_guard_tests {
    use super::*;

    #[test]
    fn hem_keygen_rejects_unsupported_jorts2of3_flags_before_dispatch() {
        for bad in [
            vec!["--tree-height", "4"],
            vec!["--anchor-dir", "/tmp/nonexistent-anchor"],
            vec!["--allow-single-disk-anchor"],
            vec!["--policy-ledger-dir", "/tmp/nonexistent-ledger"],
            vec!["--policy-anchor-dir", "/tmp/nonexistent-pol-anchor"],
            vec!["--policy-passphrase-env", "QSAG_TEST_NO_SUCH_ENV"],
            vec!["--policy-passphrase-file", "/tmp/nonexistent-pass"],
            vec!["--policy-allow-single-disk-anchor"],
        ] {
            let mut argv: Vec<String> = vec![
                "keygen".into(),
                "--scheme".into(),
                crate::quorum_hem::HEM_SCHEME_NAME.into(),
                "--vault-dir".into(),
                "/tmp/qsag-cli1-should-never-touch".into(),
                "--public-out".into(),
                "/tmp/qsag-cli1-should-never-touch.pub".into(),
            ];
            argv.extend(bad.iter().map(|s| (*s).to_owned()));
            let err = run(&argv).expect_err("unsupported HEM keygen flag must fail closed");
            assert_eq!(
                err.code, 1,
                "expected usage exit code 1 for {bad:?}: {}",
                err.message
            );
            assert!(
                err.message
                    .contains("only supported with --scheme jorts-2of3-sha3"),
                "unexpected error message for {bad:?}: {}",
                err.message
            );
        }
    }

    #[test]
    fn hem_sign_rejects_unsupported_jorts2of3_flags_before_dispatch() {
        for bad in [
            vec!["--anchor-dir", "/tmp/nonexistent-anchor"],
            vec!["--allow-single-disk-anchor"],
            vec![
                "--policy-id-hex",
                "1111111111111111111111111111111111111111111111111111111111111111",
            ],
            vec!["--spend-amount", "100"],
            vec!["--policy-ledger-dir", "/tmp/nonexistent-ledger"],
            vec!["--policy-intent", "/tmp/nonexistent-intent"],
            vec!["--policy-anchor-dir", "/tmp/nonexistent-pol-anchor"],
            vec!["--policy-passphrase-env", "QSAG_TEST_NO_SUCH_ENV"],
            vec!["--policy-passphrase-file", "/tmp/nonexistent-pass"],
            vec!["--policy-allow-single-disk-anchor"],
            vec!["--policy-retry"],
            vec!["--retry"],
            vec!["--deterministic"],
        ] {
            let mut argv: Vec<String> = vec![
                "sign".into(),
                "--scheme".into(),
                crate::quorum_hem::HEM_SCHEME_NAME.into(),
                "--vault-dir".into(),
                "/tmp/qsag-cli1-should-never-touch".into(),
                "--message".into(),
                "/tmp/qsag-cli1-msg".into(),
                "--out".into(),
                "/tmp/qsag-cli1-sig".into(),
            ];
            argv.extend(bad.iter().map(|s| (*s).to_owned()));
            let err = run(&argv).expect_err("unsupported HEM sign flag must fail closed");
            assert_eq!(
                err.code, 1,
                "expected usage exit code 1 for {bad:?}: {}",
                err.message
            );
            assert!(
                err.message
                    .contains("only supported with --scheme jorts-2of3-sha3"),
                "unexpected error message for {bad:?}: {}",
                err.message
            );
        }
    }
}
