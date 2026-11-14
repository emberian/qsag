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
const MAX_CLI_TREE_HEIGHT: u64 = 8;

const QUORUM_HELP: &str = "\
qsag quorum <keygen|sign|verify> [options]

Dealerless 2-of-3 Jorts stateful threshold signing backed by per-party FsBeltWal
and FsCeremonyJournal state (and optional --anchor-dir external monotone anchors).

subcommands:
  keygen   run a dealerless 2-of-3 RSS ceremony into --vault-dir and write --public-out
  sign     latch, reserve CeremonyContext, and sign one epoch across the 3 party vaults
  verify   verify a qsag quorum signature against --public and --in
";

const QUORUM_KEYGEN_HELP: &str = "\
qsag quorum keygen --vault-dir <dir> --public-out <path> [options]

Run a dealerless 2-of-3 RSS key generation ceremony with zero central secret reconstruction.

  --vault-dir <dir>             private 0700 directory for party-{0,1,2}.{sk,belt,ceremony}
  --public-out <path>           destination for the quorum public key JSON
  --tree-height <1..=8>         Merkle tree height (default: 3, capacity = 2^height signatures)
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

fn ensure_absent(path: &str) -> Result<(), CliError> {
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

