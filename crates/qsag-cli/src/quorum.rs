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
qsag quorum <keygen|sign|reanchor-tpm|refresh|reshare|verify|coupon> [options]

Threshold Jorts custody ceremonies:
  - `--scheme jorts-2of3-sha3` (default): dealerless 2-of-3 RSS Jorts gated by FsBeltWal & FsCeremonyJournal.
  - `--scheme hem-jorts-poseidon2`: dynamic (t, n) Shamir quorum producing canonical 65B/4328B
    JortsPoseidon2 keys & signatures directly aggregatable by untrusted `qsag aggregate`!

subcommands:
  wire     run one isolated CNF custodian over TCP (qsag quorum wire --help)
  keygen   enroll a quorum custody vault (--vault-dir) and write --public-out
  sign     threshold-sign one monotone leaf epoch across the active quorum
  reanchor-tpm  move a jorts-2of3 quorum that was enrolled on one shared TPM2 NV counter
           onto six counters of its own (see 'qsag quorum reanchor-tpm --help')
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
  --tree-height <1..=20>         Merkle tree height (default: 3, capacity = 2^height signatures)
  --anchor-dir <dir>            enroll per-party external monotone anchors in <dir>
  --anchor-tpm-nv <base>         six never-incremented TPM2 NV counters: party p belt=base+2p,
                                ceremony=base+2p+1 (tpm2_nvdefine <index> -C o -s 8
                                -a \"authread|authwrite|no_da|nt=counter\")
  --ephemeral-unanchored        enroll a disposable quorum without rollback protection
                                (an anchor or this waiver is required)
  --allow-single-disk-anchor    permit --anchor-dir on the same filesystem device as --vault-dir;
                                it then stops a restore of the vault directory only: a volume
                                or VM snapshot rewinds the anchor with it
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
  --anchor-tpm-nv <base>         same six-counter base reserved at enrollment
  --allow-single-disk-anchor    permit --anchor-dir on the same filesystem device as --vault-dir;
                                it then stops a restore of the vault directory only: a volume
                                or VM snapshot rewinds the anchor with it
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

/// A quorum reserves six TPM2 NV counters from `--anchor-tpm-nv <base>`: party `p` has
/// `base + 2p` for its belt anchor and `base + 2p + 1` for its ceremony anchor. Every
/// anchor seals its own counter value, so no two may share an index.
const QUORUM_TPM_SLOTS: u32 = 6;

fn quorum_tpm_slot(
    cfg: &AnchorConfig,
    party: usize,
    ceremony: bool,
) -> Result<AnchorConfig, CliError> {
    cfg.tpm_slot(2 * party as u32 + u32::from(ceremony), QUORUM_TPM_SLOTS)
}

fn derive_party_secret(seed: &[u8; 32], party: usize, role: &[u8]) -> Secret32 {
    Secret32::new(cshake256_framed_32(
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
    let height = usize::try_from(json.field_u64("tree_height")?)
        .map_err(|_| CliError::state("QuorumTreeHeaderMismatch"))?;
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
        "policy-ledger-dir",
        "policy-anchor-dir",
        "policy-anchor-tpm-nv",
        "policy-anchor-tpm-device",
        "policy-anchor-tpm-auth-env",
        "policy-passphrase-env",
        "policy-passphrase-file",
    ] {
        if args.get(opt).is_some() {
            return Err(CliError::usage(format!(
                "--{opt} is only supported with --scheme {SCHEME_NAME}"
            )));
        }
    }
    for flag in crate::policy_ledger::GATE_FLAG_OPTIONS {
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
        "policy-id-hex",
        "spend-amount",
        "policy-ledger-dir",
        "policy-intent",
        "policy-anchor-dir",
        "policy-anchor-tpm-nv",
        "policy-anchor-tpm-device",
        "policy-anchor-tpm-auth-env",
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
        "policy-allow-single-disk-anchor",
        "policy-vmgenid",
        "policy-vmgenid-strict",
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

/// Whether loading the party secrets is the start of a release.
enum PolicyPin<'a> {
    /// A signature may follow: a ledger-pinned key needs its gate.
    Enforce(Option<&'a crate::policy_ledger::Gate>),
    /// Anchor maintenance: no leaf is spent and no key state changes.
    NothingReleased,
}

/// Lock, authenticate and decode the three party secrets of a vault.
fn load_parties(
    party_sk_paths: &[String; 3],
    passphrase: Option<&[u8]>,
    pin: PolicyPin<'_>,
    anchor_cfg: Option<&AnchorConfig>,
) -> Result<(Vec<LoadedParty>, QuorumHeaderMeta), CliError> {
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
        let opened = crate::envelope::open(&secret_on_disk, passphrase)?;
        vault.set_key_material(&opened);
        vault.authenticate(&secret_on_disk)?;
        if let PolicyPin::Enforce(gate) = pin {
            crate::policy_ledger::enforce_key_pin(&secret_on_disk, gate)?;
        }
        let anchor_req = enforce_anchor_requirement(&secret_on_disk, anchor_cfg)?;

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
    Ok((parties_vec, header_meta.ok_or_else(corrupt)?))
}

/// The six anchor domains of a quorum in TPM slot order.
fn quorum_tpm_domains(parties: &[LoadedParty]) -> Vec<crate::anchor::TpmDomain<'static>> {
    let mut domains = Vec::with_capacity(6);
    for (p, party) in parties.iter().enumerate() {
        for (ceremony, domain, role) in [
            (false, "quorum_belt", &b"external_belt_anchor_mac"[..]),
            (
                true,
                "quorum_ceremony",
                &b"external_ceremony_anchor_mac"[..],
            ),
        ] {
            domains.push(crate::anchor::TpmDomain {
                slot: 2 * p as u32 + u32::from(ceremony),
                domain,
                key_id: party.party_key_id,
                mac_key: derive_party_secret(&party.seed.0, p, role).0,
            });
        }
    }
    domains
}

/// A quorum enrolled on one shared TPM2 NV counter cannot open; say why and how to
/// repair it instead of reporting the lagging seals as a rollback.
fn refuse_shared_tpm_index(
    cfg: &AnchorConfig,
    party_sk_refs: &[&str],
    vault_dir: &str,
    parties: &[LoadedParty],
) -> Result<(), CliError> {
    if !cfg.shared_tpm_index_enrollment(
        party_sk_refs,
        &[vault_dir],
        &quorum_tpm_domains(parties),
    )? {
        return Ok(());
    }
    let index = cfg.tpm_nv_index.unwrap_or_default();
    Err(CliError::state(format!(
        "this quorum was enrolled with one TPM2 NV counter ({index:#010x}) shared by all six of its anchors. Each anchor seals the exact count, so only the newest seal matches the counter and the vault cannot open. Its state can still be proven current: define six new counters and run `qsag quorum reanchor-tpm --vault-dir {vault_dir} --anchor-tpm-nv {index:#010x} --new-anchor-tpm-nv <new base>`"
    )))
}

const QUORUM_REANCHOR_HELP: &str = "\
qsag quorum reanchor-tpm --vault-dir <dir> --anchor-tpm-nv <shared index> --new-anchor-tpm-nv <base> [options]

Repair a quorum that was enrolled with one TPM2 NV counter shared by its six anchors
(qsag before per-domain counters). Such a vault cannot open: every seal but the
newest lags the shared counter. This command proves the vault's state is the newest
the TPM has seen (the newest seal on disk equals the live counter; no other domain
could have advanced), then binds each anchor to its own never-written counter:
party p belt = base+2p, ceremony = base+2p+1. No key material or leaf state changes.

A vault whose newest seal is behind the counter is refused: it was rolled back, or
something else used the index. An interrupted run can be repeated. Keep the shared
source counter defined: every migration retires one source count and records it.

The new counters need an ADMIN auth-change policy for crash-safe TPM reservation.
Create the public policy once (no secrets in this file):
  tpm2_startauthsession -g sha256 -S reanchor.ctx
  tpm2_policycommandcode -S reanchor.ctx TPM2_CC_NV_ChangeAuth
  tpm2_policypassword -S reanchor.ctx
  tpm2_policynvwritten -S reanchor.ctx -L reanchor.policy c
  tpm2_flushcontext reanchor.ctx
Then define each NEW index with the policy and the initial index password used by
--anchor-tpm-auth-env (omit -p for an empty password):
  tpm2_nvdefine <index> -C o -s 8 -g sha256 -L reanchor.policy -a \"authread|authwrite|no_da|nt=counter\" -p <initial-index-password>
Do not undefine existing anchors. Re-anchoring replaces each destination password
with its domain's derived secret; ordinary qsag opens derive it automatically.
Already-moved legacy counters are verified with their existing seals and passwords.
Those old records do not name their historical source; --anchor-tpm-nv explicitly
authorizes retirement of the source index you provide.

  --vault-dir <dir>              the quorum vault
  --anchor-tpm-nv <index>        the shared counter the quorum was enrolled with
  --new-anchor-tpm-nv <base>     six never-written counters provisioned as above
  --anchor-tpm-device <path> / --anchor-tpm-auth-env <VAR>  as at enrollment (both ranges)
  --anchor-dir <dir> / --anchor-vmgenid / --allow-single-disk-anchor  as at enrollment
  --passphrase-env <VAR> / --passphrase-file <PATH>  unlock sealed party secrets
";

fn reanchor_tpm(raw: &[String]) -> Result<(), CliError> {
    let args = Args::parse(
        raw,
        &[
            "vault-dir",
            "anchor-dir",
            "anchor-tpm-nv",
            "new-anchor-tpm-nv",
            "anchor-tpm-device",
            "anchor-tpm-auth-env",
            "passphrase-env",
            "passphrase-file",
        ],
        &[
            "help",
            "json",
            "anchor-vmgenid",
            "anchor-vmgenid-strict",
            "allow-single-disk-anchor",
        ],
    )?;
    if args.flag("help") {
        print!("{QUORUM_REANCHOR_HELP}");
        return Ok(());
    }
    args.no_positionals()?;
    let vault_dir = args.require("vault-dir")?;
    args.require("anchor-tpm-nv")?;
    let new_base = crate::anchor::parse_tpm_nv_index(args.require("new-anchor-tpm-nv")?)?;
    let passphrase = crate::envelope::passphrase(&args)?;
    let cfg = AnchorConfig::from_quorum_args(&args, vault_dir)?
        .ok_or_else(|| CliError::usage("reanchor-tpm requires --anchor-tpm-nv"))?;
    private_dir(vault_dir, false)?;
    let party_sk_paths: [String; 3] = std::array::from_fn(|p| party_secret_path(vault_dir, p));
    let party_sk_refs: [&str; 3] = [
        party_sk_paths[0].as_str(),
        party_sk_paths[1].as_str(),
        party_sk_paths[2].as_str(),
    ];
    // The party vault locks are held until every anchor has been moved and verified.
    let (parties, _) = load_parties(
        &party_sk_paths,
        passphrase.as_deref().map(Vec::as_slice),
        PolicyPin::NothingReleased,
        Some(&cfg),
    )?;
    cfg.reanchor_shared_tpm_index(
        new_base,
        QUORUM_TPM_SLOTS,
        &party_sk_refs,
        &[vault_dir],
        &quorum_tpm_domains(&parties),
    )?;
    if args.flag("json") {
        print!(
            "{}",
            Json::object(vec![
                ("reanchored", Json::Bool(true)),
                ("anchor_tpm_nv_base", Json::num(u64::from(new_base))),
                ("counters", Json::num(u64::from(QUORUM_TPM_SLOTS))),
            ])
            .to_pretty()
        );
    } else {
        println!(
            "re-anchored quorum {vault_dir}: six anchors now on TPM2 NV counters {new_base:#010x}..={:#010x}; sign with --anchor-tpm-nv {new_base:#010x}",
            new_base + QUORUM_TPM_SLOTS - 1
        );
    }
    Ok(())
}

pub fn run(raw: &[String]) -> Result<(), CliError> {
    let Some((sub, rest)) = raw.split_first() else {
        eprint!("{QUORUM_HELP}");
        return Err(CliError::usage(
            "quorum expects a subcommand (keygen, sign, reanchor-tpm, refresh, reshare, verify, coupon)",
        ));
    };
    match sub.as_str() {
        "--help" | "-h" | "help" => {
            print!("{QUORUM_HELP}");
            Ok(())
        }
        "wire" => crate::quorum_wire::run(rest),
        "keygen" => keygen(rest),
        "sign" => sign(rest),
        "reanchor-tpm" => reanchor_tpm(rest),
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
            "anchor-tpm-nv",
            "anchor-tpm-device",
            "anchor-tpm-auth-env",
            "passphrase-env",
            "passphrase-file",
            "policy-ledger-dir",
            "policy-anchor-dir",
            "policy-anchor-tpm-nv",
            "policy-anchor-tpm-device",
            "policy-anchor-tpm-auth-env",
            "policy-passphrase-env",
            "policy-passphrase-file",
        ],
        &[
            "allow-single-disk-anchor",
            "anchor-vmgenid",
            "anchor-vmgenid-strict",
            "ephemeral-unanchored",
            "policy-allow-single-disk-anchor",
            "policy-vmgenid",
            "policy-vmgenid-strict",
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
    crate::anchor::refuse_policy_tpm_overlap(&args, QUORUM_TPM_SLOTS)?;
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
    crate::anchor::preflight_tpm_enrollment(anchor_cfg.as_ref(), &args, QUORUM_TPM_SLOTS)?;
    crate::anchor::require_anchor_or_waiver(
        anchor_cfg.is_some(),
        args.flag("ephemeral-unanchored"),
        "anchor-dir",
    )?;

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
        Secret32::new(os_random_32()?),
        Secret32::new(os_random_32()?),
        Secret32::new(os_random_32()?),
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
                &quorum_tpm_slot(cfg, p, false)?,
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
                &quorum_tpm_slot(cfg, p, true)?,
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
        let encoded = ZeroizingBuf::new(secret.to_pretty().into_bytes());
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
            "anchor-tpm-nv",
            "anchor-tpm-device",
            "anchor-tpm-auth-env",
            "policy-id-hex",
            "spend-amount",
            "passphrase-env",
            "passphrase-file",
            "policy-ledger-dir",
            "policy-intent",
            "policy-anchor-dir",
            "policy-anchor-tpm-nv",
            "policy-anchor-tpm-device",
            "policy-anchor-tpm-auth-env",
            "policy-passphrase-env",
            "policy-passphrase-file",
        ],
        &[
            "allow-single-disk-anchor",
            "anchor-vmgenid",
            "anchor-vmgenid-strict",
            "ephemeral-unanchored",
            "policy-allow-single-disk-anchor",
            "policy-vmgenid",
            "policy-vmgenid-strict",
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
    crate::anchor::refuse_policy_tpm_overlap(&args, QUORUM_TPM_SLOTS)?;
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
    if let Some(cfg) = &anchor_cfg {
        cfg.tpm_slot(0, QUORUM_TPM_SLOTS)?;
    }
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
        crate::policy_ledger::ceremony_spend(gate.intent_amount()?)?;
    }
    crate::anchor::require_anchor_or_waiver(
        anchor_cfg.is_some(),
        args.flag("ephemeral-unanchored"),
        "anchor-dir",
    )?;

    private_dir(vault_dir, false)?;
    let party_sk_paths: [String; 3] = std::array::from_fn(|p| party_secret_path(vault_dir, p));
    let party_sk_refs: [&str; 3] = [
        party_sk_paths[0].as_str(),
        party_sk_paths[1].as_str(),
        party_sk_paths[2].as_str(),
    ];

    let (mut parties_vec, header_meta) = load_parties(
        &party_sk_paths,
        passphrase.as_deref().map(Vec::as_slice),
        PolicyPin::Enforce(gate.as_ref()),
        anchor_cfg.as_ref(),
    )?;
    if let Some(cfg) = &anchor_cfg {
        refuse_shared_tpm_index(cfg, &party_sk_refs, vault_dir, &parties_vec)?;
        cfg.check_tpm_range(QUORUM_TPM_SLOTS, crate::anchor::TpmUse::Reopen)?;
    }

    let QuorumHeaderMeta {
        height,
        dkg_session_id,
        pk,
        tree_digest,
        anchor_required: _,
    } = header_meta;
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
                &quorum_tpm_slot(cfg, p, false)?,
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
                &quorum_tpm_slot(cfg, p, true)?,
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
        Secret32::new(parties_vec[0].seed.0),
        Secret32::new(parties_vec[1].seed.0),
        Secret32::new(parties_vec[2].seed.0),
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
        Secret32::new([0u8; 32])
    } else {
        Secret32::new(os_random_32()?)
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
        Secret32::new([0u8; 32]),
        Secret32::new([0u8; 32]),
        Secret32::new([0u8; 32]),
    ];
    if !deterministic {
        for fresh in &mut party_fresh {
            fresh.0 = os_random_32()?;
        }
    }
    let online_rngs: [PartyPrivateRng; 3] = std::array::from_fn(|p| {
        let hedge = Secret32::new(cshake256_framed_32(
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
                qsag_addr::WitnessSuiteTag::QuorumJorts,
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

    let _ = &ceremony_anchors;

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

    let sig_bytes = ZeroizingBuf::new(encode_jorts_sig(&params, &sig));
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

#[cfg(all(test, unix))]
mod tpm_anchor_tests {
    use super::*;
    use crate::anchor::tpm_model;

    const BASE: u32 = 0x0180_0001;

    struct Scratch(std::path::PathBuf);

    impl Scratch {
        fn new(label: &str) -> Self {
            let root = std::env::temp_dir().join(format!(
                "qsag-quorum-tpm-{label}-{}",
                crate::codec::to_hex(&os_random_32().unwrap()[..8])
            ));
            private_dir(root.to_str().unwrap(), true).unwrap();
            Self(root)
        }

        fn path(&self, name: &str) -> String {
            self.0.join(name).to_str().unwrap().to_owned()
        }
    }

    impl Drop for Scratch {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    fn quorum(args: &[&str]) -> Result<(), CliError> {
        run(&args.iter().map(|s| (*s).to_owned()).collect::<Vec<_>>())
    }

    fn regular_files(dir: &str) -> Vec<(std::path::PathBuf, Vec<u8>)> {
        let mut files: Vec<_> = std::fs::read_dir(dir)
            .unwrap()
            .map(|e| e.unwrap().path())
            .filter(|p| std::fs::symlink_metadata(p).unwrap().is_file())
            .map(|p| {
                let bytes = std::fs::read(&p).unwrap();
                (p, bytes)
            })
            .collect();
        files.sort();
        files
    }

    // The real `quorum keygen` and `quorum sign` call chains against one TPM. With a
    // single shared NV index every later anchor's provisioning increment left the earlier
    // seals behind, and the first reopen reported a rollback on honest storage.
    #[test]
    fn tpm_anchored_quorum_reopens_and_refuses_rollback_of_each_domain() {
        let scratch = Scratch::new("domains");
        let installed = tpm_model::install(BASE, QUORUM_TPM_SLOTS, 41);
        let tpm = &installed.0;
        let vault = scratch.path("vault");
        let pk_path = scratch.path("pk");
        let message = scratch.path("message");
        std::fs::write(&message, b"TPM multi-domain regression").unwrap();
        quorum(&[
            "keygen",
            "--vault-dir",
            &vault,
            "--public-out",
            &pk_path,
            "--tree-height",
            "1",
            "--anchor-tpm-nv",
            "0x01800001",
        ])
        .unwrap();
        let enrolled = regular_files(&vault);

        let sign = |epoch: &str, out: &str| {
            quorum(&[
                "sign",
                "--vault-dir",
                &vault,
                "--epoch",
                epoch,
                "--in",
                &message,
                "--out",
                out,
                "--anchor-tpm-nv",
                "0x01800001",
            ])
        };
        // Honest storage: all six anchors reopen and the leaf is spent.
        sign("0", &scratch.path("sig0")).unwrap();
        assert!(
            tpm.counts().values().all(|n| n.is_some_and(|n| n > 41)),
            "every reserved counter backs one domain: {:?}",
            tpm.counts()
        );

        // Restoring the whole vault in place (every inode kept) must not reopen leaf 0.
        let spent = regular_files(&vault);
        for (path, bytes) in &enrolled {
            std::fs::write(path, bytes).unwrap();
        }
        let err = sign("0", &scratch.path("sig0-again")).unwrap_err();
        assert!(
            format!("{err:?}").contains("lags TPM2 NV monotonic counter"),
            "{err:?}"
        );
        assert!(!Path::new(&scratch.path("sig0-again")).exists());
        for (path, bytes) in &spent {
            std::fs::write(path, bytes).unwrap();
        }
        sign("1", &scratch.path("sig1")).unwrap();

        // Each of the six domains on its own.
        let cfg = AnchorConfig {
            tpm_nv_index: Some(BASE),
            vault_dir: Some(vault.clone()),
            ..Default::default()
        };
        for p in 0..3 {
            let secret =
                Json::parse(&std::fs::read_to_string(party_secret_path(&vault, p)).unwrap())
                    .unwrap();
            let seed: [u8; 32] = from_hex_exact(secret.field_str("seed").unwrap(), "seed").unwrap();
            let pk = JortsPublicKey {
                pk_seed: from_hex_exact(secret.field_str("pk_seed").unwrap(), "pk_seed").unwrap(),
                pk_root: from_hex_exact(secret.field_str("pk_root").unwrap(), "pk_root").unwrap(),
            };
            let key_id = derive_party_key_id(&pk, 1, p);
            for (slot, domain, role) in [
                (
                    2 * p as u32,
                    "quorum_belt",
                    &b"external_belt_anchor_mac"[..],
                ),
                (
                    2 * p as u32 + 1,
                    "quorum_ceremony",
                    &b"external_ceremony_anchor_mac"[..],
                ),
            ] {
                tpm_model::assert_domain_reopens_and_refuses_rollback(
                    tpm,
                    &cfg,
                    &vault,
                    BASE + slot,
                    domain,
                    key_id,
                    derive_party_secret(&seed, p, role).0,
                );
            }
        }
    }

    const SHARED: u32 = 0x0180_0040;
    const NEW_BASE: u32 = 0x0180_0050;

    fn keygen_at_base(vault: &str, pk: &str) {
        quorum(&[
            "keygen",
            "--vault-dir",
            vault,
            "--public-out",
            pk,
            "--tree-height",
            "1",
            "--anchor-tpm-nv",
            "0x01800001",
        ])
        .unwrap();
    }

    fn domains_of(vault: &str, cfg: &AnchorConfig) -> Vec<crate::anchor::TpmDomain<'static>> {
        let paths: [String; 3] = std::array::from_fn(|p| party_secret_path(vault, p));
        let (parties, _) =
            load_parties(&paths, None, PolicyPin::NothingReleased, Some(cfg)).unwrap();
        quorum_tpm_domains(&parties)
    }

    /// Turn the vault into what a release before per-domain counters left on disk.
    fn make_shared(tpm: &tpm_model::ModelTpm2, vault: &str) {
        let cfg = AnchorConfig {
            tpm_nv_index: Some(BASE),
            vault_dir: Some(vault.to_owned()),
            ..Default::default()
        };
        let paths: [String; 3] = std::array::from_fn(|p| party_secret_path(vault, p));
        let refs: Vec<&str> = paths.iter().map(String::as_str).collect();
        tpm_model::make_shared_index_enrollment(
            tpm,
            &cfg,
            SHARED,
            QUORUM_TPM_SLOTS,
            &refs,
            &[vault],
            &domains_of(vault, &cfg),
        );
    }

    fn reanchor(vault: &str) -> Result<(), CliError> {
        quorum(&[
            "reanchor-tpm",
            "--vault-dir",
            vault,
            "--anchor-tpm-nv",
            "0x01800040",
            "--new-anchor-tpm-nv",
            "0x01800050",
        ])
    }

    // A quorum enrolled on one shared counter could never open, and said "rollback".
    // It now names the cause and the command, and that command moves every anchor to
    // its own counter after proving the disk is the newest state the TPM has seen.
    #[test]
    fn shared_index_quorum_names_the_remedy_and_reanchors_across_an_interrupted_run() {
        let scratch = Scratch::new("reanchor");
        let installed = tpm_model::install(BASE, QUORUM_TPM_SLOTS, 41);
        let tpm = &installed.0;
        tpm.define_counter(SHARED, b"");
        // The fourth new counter does not exist yet: the first run stops there.
        for slot in (0..QUORUM_TPM_SLOTS).filter(|slot| *slot != 3) {
            tpm.define_rebind_counter(NEW_BASE + slot, b"");
        }
        let vault = scratch.path("vault");
        let message = scratch.path("message");
        std::fs::write(&message, b"re-anchored quorum").unwrap();
        keygen_at_base(&vault, &scratch.path("pk"));
        make_shared(tpm, &vault);
        let before_migration = regular_files(&vault);
        let sign = |base: &str, epoch: &str, out: &str| {
            quorum(&[
                "sign",
                "--vault-dir",
                &vault,
                "--epoch",
                epoch,
                "--in",
                &message,
                "--out",
                out,
                "--anchor-tpm-nv",
                base,
            ])
        };

        let err = sign("0x01800040", "0", &scratch.path("never")).unwrap_err();
        assert!(
            err.message.contains("shared by all six")
                && err.message.contains("quorum reanchor-tpm")
                && !err.message.contains("rollback"),
            "{err:?}"
        );

        let err = reanchor(&vault).unwrap_err();
        assert!(err.message.contains("0x01800053"), "{err:?}");
        let moved: Vec<bool> = (0..QUORUM_TPM_SLOTS)
            .filter(|slot| *slot != 3)
            .map(|slot| tpm.count(NEW_BASE + slot).is_some())
            .collect();
        assert_eq!(
            moved,
            [true, true, true, false, false],
            "oldest seals first"
        );
        assert!(sign("0x01800050", "0", &scratch.path("never")).is_err());

        tpm.define_rebind_counter(NEW_BASE + 3, b"");
        reanchor(&vault).unwrap();
        let settled = tpm.counts();
        // Crash composition: all TPM seals committed, but the ticket binding write
        // has not happened. Restoring only those old ticket bytes must repair the
        // bindings without reserving or incrementing any counter again.
        let mut restored_tickets = 0;
        for (path, bytes) in &before_migration {
            if path
                .extension()
                .is_some_and(|extension| extension == "anchor")
            {
                std::fs::write(path, bytes).unwrap();
                restored_tickets += 1;
            }
        }
        assert_eq!(restored_tickets, QUORUM_TPM_SLOTS);
        reanchor(&vault).unwrap();
        assert_eq!(
            tpm.counts(),
            settled,
            "ticket repair must not repeat TPM retirement"
        );
        reanchor(&vault).unwrap();
        assert_eq!(tpm.counts(), settled, "a repeated run only verifies");

        sign("0x01800050", "0", &scratch.path("sig0")).unwrap();
        assert!(sign("0x01800040", "1", &scratch.path("never")).is_err());
        assert!(!Path::new(&scratch.path("never")).exists());
        let cfg = AnchorConfig {
            tpm_nv_index: Some(NEW_BASE),
            vault_dir: Some(vault.clone()),
            ..Default::default()
        };
        for domain in domains_of(&vault, &cfg) {
            tpm_model::assert_domain_reopens_and_refuses_rollback(
                tpm,
                &cfg,
                &vault,
                NEW_BASE + domain.slot,
                domain.domain,
                domain.key_id,
                domain.mac_key,
            );
        }
        // A different, fully provisioned fresh range must not turn an old shared
        // snapshot into current custody. Only source retirement can reject this:
        // none of these destinations has been written or is missing its policy.
        const OTHER_BASE: u32 = 0x0180_0070;
        for slot in 0..QUORUM_TPM_SLOTS {
            tpm.define_rebind_counter(OTHER_BASE + slot, b"");
        }
        let counts = tpm.counts();
        for (path, bytes) in &before_migration {
            std::fs::write(path, bytes).unwrap();
        }
        let err = quorum(&[
            "reanchor-tpm",
            "--vault-dir",
            &vault,
            "--anchor-tpm-nv",
            "0x01800040",
            "--new-anchor-tpm-nv",
            "0x01800070",
        ])
        .unwrap_err();
        assert!(err.message.contains("older than the TPM"), "{err:?}");
        assert_eq!(
            tpm.counts(),
            counts,
            "a fresh destination cannot bypass source retirement"
        );
        let restored = scratch.path("restored-whole-vault");
        std::fs::create_dir(&restored).unwrap();
        for (path, bytes) in &before_migration {
            std::fs::write(Path::new(&restored).join(path.file_name().unwrap()), bytes).unwrap();
        }
        assert!(
            quorum(&[
                "reanchor-tpm",
                "--vault-dir",
                &restored,
                "--anchor-tpm-nv",
                "0x01800040",
                "--new-anchor-tpm-nv",
                "0x01800070",
            ])
            .is_err()
        );
        assert_eq!(tpm.counts(), counts);
    }

    #[test]
    fn reanchor_finishes_legacy_partial_and_complete_moves_without_redefining_counters() {
        for moved in [1, QUORUM_TPM_SLOTS] {
            let scratch = Scratch::new("reanchor-legacy");
            let installed = tpm_model::install(BASE, QUORUM_TPM_SLOTS, 41);
            let tpm = &installed.0;
            tpm.define_counter(SHARED, b"");
            for slot in 0..QUORUM_TPM_SLOTS {
                if slot < moved {
                    tpm.define_counter(NEW_BASE + slot, b"");
                } else {
                    tpm.define_rebind_counter(NEW_BASE + slot, b"");
                }
            }
            let vault = scratch.path("vault");
            keygen_at_base(&vault, &scratch.path("pk"));
            make_shared(tpm, &vault);
            let shared = AnchorConfig {
                tpm_nv_index: Some(SHARED),
                vault_dir: Some(vault.clone()),
                ..Default::default()
            };
            let domains = domains_of(&vault, &shared);
            for domain in domains.iter().take(moved as usize) {
                tpm_model::legacy_move_shared_domain(
                    tpm,
                    &shared,
                    NEW_BASE + domain.slot,
                    &vault,
                    domain,
                );
            }
            let source = tpm.count(SHARED).unwrap();
            reanchor(&vault).unwrap();
            assert_eq!(
                tpm.count(SHARED),
                Some(source + u64::from(QUORUM_TPM_SLOTS))
            );
            let settled = tpm.counts();
            reanchor(&vault).unwrap();
            assert_eq!(tpm.counts(), settled);
        }
    }

    // Re-anchoring is not a way around the TPM: a disk older than the shared counter
    // is refused, and so is a vault that was never on a shared counter.
    #[test]
    fn reanchoring_refuses_a_disk_behind_the_shared_counter_and_a_vault_that_is_not_shared() {
        use qsag_core::anti_rollback::{Tpm2Transport, marshal_tpm2_nv_increment_cmd};
        let scratch = Scratch::new("reanchor-refused");
        let installed = tpm_model::install(BASE, QUORUM_TPM_SLOTS, 41);
        let tpm = &installed.0;
        tpm.define_counter(SHARED, b"");
        for slot in 0..QUORUM_TPM_SLOTS {
            tpm.define_counter(NEW_BASE + slot, b"");
        }
        let vault = scratch.path("vault");
        keygen_at_base(&vault, &scratch.path("pk"));

        // Enrolled one counter per domain: nothing to repair, and naming its base as
        // "the shared index" does not move anything.
        let err = quorum(&[
            "reanchor-tpm",
            "--vault-dir",
            &vault,
            "--anchor-tpm-nv",
            "0x01800001",
            "--new-anchor-tpm-nv",
            "0x01800050",
        ])
        .unwrap_err();
        assert!(err.message.contains("bound to neither"), "{err:?}");

        // Shared, and then the counter moves on without the disk: what the TPM shows
        // when the newest domain advanced after this disk image was taken.
        make_shared(tpm, &vault);
        tpm.transmit(&marshal_tpm2_nv_increment_cmd(SHARED, SHARED, b"").unwrap())
            .unwrap();
        let err = reanchor(&vault).unwrap_err();
        assert!(err.message.contains("older than the TPM"), "{err:?}");
        assert!(
            (0..QUORUM_TPM_SLOTS).all(|slot| tpm.count(NEW_BASE + slot).is_none()),
            "a refused re-anchoring writes no counter"
        );
    }

    // A range the TPM cannot serve is refused before the vault exists: numerically
    // out of the NV handle space, or with a counter that was never defined.
    #[test]
    fn tpm_anchored_quorum_checks_its_whole_counter_range_before_enrolling() {
        let scratch = Scratch::new("range");
        let installed = tpm_model::install(BASE, QUORUM_TPM_SLOTS - 1, 41);
        for (base, reason) in [
            ("0x01fffffb", "needs 6 distinct NV indices"),
            ("0x01800001", "TPM2 NV counter 0x01800006"),
        ] {
            let vault = scratch.path("vault");
            let err = quorum(&[
                "keygen",
                "--vault-dir",
                &vault,
                "--public-out",
                &scratch.path("pk"),
                "--tree-height",
                "1",
                "--anchor-tpm-nv",
                base,
            ])
            .unwrap_err();
            assert!(format!("{err:?}").contains(reason), "{err:?}");
            assert!(!Path::new(&vault).exists(), "preflight precedes enrollment");
        }
        assert!(
            installed.0.counts().values().all(Option::is_none),
            "a refused enrollment increments nothing"
        );
    }
}
