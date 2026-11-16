//! Dynamic `(t, n)` Shamir quorum-switching CLI ceremonies (`--scheme hem-jorts-poseidon2`)
//! backed by [`qsag_quorum::hem_quorum::HemDynamicShamirQuorum`].
//!
//! Produces canonical 65-byte [`qsag_agg::ValidatorPublicKey`]s and 4,328-byte
//! [`qsag_agg::ValidatorSignature`]s accepted directly by untrusted public `qsag aggregate`
//! and `qsag verify-aggregate` (`BciksJohnsonQrom128`), while supporting proactive share
//! refresh (`qsag quorum refresh`) and `(t, n) -> (t', n')` roster/threshold switching
//! (`qsag quorum reshare`) without changing the validator public key.
//!
//! # Vault layout and crash behaviour
//!
//! ```text
//! <vault>/quorum-meta.json             the committed state (format v2)
//! <vault>/quorum-meta.json.vault.lock  exclusive lock; its inode is recorded in the meta
//! <vault>/directory.bin                public directory, written once
//! <vault>/custodian-<p>.g<G>.share     custodian p's share for generation G
//! ```
//!
//! Every state change writes a complete new generation of share files beside the current
//! one and then replaces `quorum-meta.json` with one atomic rename. The meta names the
//! generation, carries a digest of every share file and of itself, and is the only commit
//! point: before the rename the vault is the old generation, after it the new one. Share
//! files of any other generation are leftovers and are wiped the next time the vault is
//! opened. A crash at any point leaves a vault that opens.
//!
//! Signing reserves a leaf, commits the generation without it, and only then combines the
//! signers' shares of that leaf. A crash after the commit loses the leaf; no crash leaves a
//! leaf on disk after its shares were combined.
//!
//! A reshare touches two vaults. The old vault first records where it is being reshared to;
//! while that record stands it does not sign. The new vault's meta is the commit point. An
//! old vault opened with the record still present retires itself if the new vault was
//! committed, and otherwise discards the staged new vault and carries on.
//!
//! Vaults written by earlier versions (`qsag-hem-quorum-meta-v1`, shares named
//! `custodian-<p>.share`, with or without a lock file) are converted in place by the first
//! command that opens them.

use std::path::Path;

use qsag_accel::keccak::{cshake256_framed_32, cshake256_framed_xof};
use qsag_agg::{
    AggSigProfile, ValidatorPublicKey, ValidatorSignature, verify_individual_signature,
};
use qsag_core::preprocessing::PartyPrivateRng;
use qsag_core::{ExternalMonotoneAnchor, LedgerCheckpoint};
use qsag_quorum::hem_quorum::{
    HEM_JORTS_MAX_LEAVES, HEM_JORTS_PK_BYTES, HEM_JORTS_SIG_BYTES, HemDynamicShamirQuorum,
    HemJortsPublicKey, HemJortsSignature, HemQuorumError, HemQuorumPublicDirectory,
    HemShamirCustodianShare, MAX_HEM_QUORUM_PARTIES, verify_hem_jorts_signature,
};

use crate::anchor::{
    ANCHOR_FLAG_OPTIONS, ANCHOR_NO_VAULT_VALUE_OPTIONS, AnchorConfig, FsExternalMountAnchor,
    require_anchor_or_waiver,
};

use crate::cli::{
    Args, CliError, MAX_KEY_FILE_BYTES, MAX_SIG_PROOF_BYTES, Secret32, ZeroizingBuf, os_random_32,
    private_dir, read_bounded_file, read_input, read_text, replace_secret, sync_parent, write_new,
};
use crate::codec::{Json, from_hex_exact};
use crate::quorum::PUBLIC_FORMAT;
use crate::vault::Vault;

pub const HEM_SCHEME_NAME: &str = "hem-jorts-poseidon2";
const HEM_META_FORMAT_V1: &str = "qsag-hem-quorum-meta-v1";
const HEM_META_FORMAT: &str = "qsag-hem-quorum-meta-v2";
const SIG_FORMAT: &str = "qsag-quorum-signature-v1";
const MAX_VAULT_FILE_BYTES: u64 = 16 * 1024 * 1024;

const HEM_ENVELOPE_FORMAT: &str = "cshake256-iterated-v1";
const HEM_SHARE_SEAL_MAGIC: &[u8; 24] = b"QSAG.HEM.SHARE.SEAL.V1\0\0";
const HEM_SHARE_SEAL_HEADER_BYTES: usize = 24 + 8 + 8 + 32 + 32;

pub const HEM_REFRESH_HELP: &str = "\
qsag quorum refresh --vault-dir <dir> [--passphrase-env <VAR> | --passphrase-file <PATH>] [--deterministic] [--json]

Execute proactive share refresh (Π_refresh) across all (t, n) custodians in --vault-dir,
advancing quorum_epoch and overwriting custodian share files in place while preserving
the exact 65-byte validator public key and monotone leaf high-water mark.
--deterministic fixes only the session ID; private ceremony entropy remains fresh.
";

pub const HEM_RESHARE_HELP: &str = "\
qsag quorum reshare --vault-dir <old_dir> [--signers <i,j,..>] --new-threshold <t'> --new-parties <n'> --out-vault-dir <new_dir> [--public-out <path>] [--passphrase-env <VAR> | --passphrase-file <PATH>] [--new-passphrase-env <VAR> | --new-passphrase-file <PATH>] [--deterministic] [--json]

Execute dynamic (t, n) -> (t', n') quorum-switching (Π_reshare) using >= t custodians from
--vault-dir, writing the new (t', n') custodian vault into --out-vault-dir WITHOUT changing
the 65-byte validator public key, and permanently invalidating/wiping the retired vault.
When --vault-dir is passphrase-sealed and --new-passphrase-* is omitted, the new vault is
re-sealed under the source passphrase with a fresh KDF salt.
--deterministic fixes only the session ID; private ceremony entropy remains fresh.
";

// The local vault CLI hosts all custodians, but each protocol stream still needs
// independent private entropy; deterministic session identifiers are only context.
fn fresh_party_rngs(n: usize) -> Result<Vec<PartyPrivateRng>, CliError> {
    (0..n)
        .map(|_| {
            let seed = Secret32::new(os_random_32()?);
            Ok(PartyPrivateRng::from_seed(
                seed.0,
                b"QSAG.CLI.HEM.PRIVATE/v1",
            ))
        })
        .collect()
}

fn parse_party_list(spec: &str, flag_name: &str, n: usize) -> Result<Vec<usize>, CliError> {
    let mut out = Vec::new();
    for part in spec.split(',') {
        let trimmed = part.trim();
        if trimmed.is_empty() {
            continue;
        }
        let idx: usize = trimmed.parse().map_err(|_| {
            CliError::usage(format!("--{flag_name} must be comma-separated indices"))
        })?;
        if idx >= n {
            return Err(CliError::usage(format!(
                "--{flag_name} index {idx} out of range (parties = {n})"
            )));
        }
        if out.contains(&idx) {
            return Err(CliError::usage(format!(
                "duplicate party index {idx} in --{flag_name}"
            )));
        }
        out.push(idx);
    }
    if out.is_empty() {
        return Err(CliError::usage(format!("--{flag_name} must not be empty")));
    }
    Ok(out)
}

fn map_quorum_err(err: HemQuorumError) -> CliError {
    match err {
        HemQuorumError::InvalidQuorum { t, n } => {
            CliError::usage(format!("invalid quorum parameters (t={t}, n={n})"))
        }
        HemQuorumError::InvalidActiveLeaves { active_leaves } => {
            CliError::usage(format!("invalid active leaves ({active_leaves})"))
        }
        HemQuorumError::PartyOutOfRange { party, n } => {
            CliError::usage(format!("party {party} out of range for n={n}"))
        }
        HemQuorumError::DuplicateParty { party } => {
            CliError::usage(format!("duplicate party {party}"))
        }
        HemQuorumError::NotEnoughSigners { have, need } => {
            CliError::state(format!("NotEnoughSigners: have {have}, need {need}"))
        }
        HemQuorumError::ShareInvalidated { party } => {
            CliError::state(format!("ShareInvalidated: party {party} was retired"))
        }
        HemQuorumError::QuorumEpochMismatch {
            expected,
            got,
            party,
        } => CliError::state(format!(
            "QuorumEpochMismatch on party {party}: expected {expected}, got {got}"
        )),
        HemQuorumError::LeafExhausted | HemQuorumError::LatchRefused => {
            CliError::state(format!("quorum monotone leaf latch refused: {err}"))
        }
        other => CliError::verify(format!("quorum verification error: {other}")),
    }
}

fn write_public_json(
    pk: &HemJortsPublicKey,
    t: usize,
    n: usize,
    quorum_epoch: u64,
    active_leaves: usize,
) -> Json {
    let pk_bytes = pk.to_bytes();
    Json::object(vec![
        ("format", Json::str(PUBLIC_FORMAT)),
        ("scheme", Json::str(HEM_SCHEME_NAME)),
        (
            "custody_model",
            Json::str("dynamic-shamir-hem-jorts-poseidon2"),
        ),
        ("threshold", Json::num(t)),
        ("parties", Json::num(n)),
        ("quorum_epoch", Json::num(quorum_epoch)),
        ("active_leaves", Json::num(active_leaves)),
        ("public_key_bytes", Json::num(HEM_JORTS_PK_BYTES)),
        ("validator_public_key", Json::hex(&pk_bytes)),
    ])
}

// ---------------------------------------------------------------------------------------
// Paths and file names
// ---------------------------------------------------------------------------------------

fn join(vault_dir: &str, name: &str) -> String {
    Path::new(vault_dir)
        .join(name)
        .to_string_lossy()
        .into_owned()
}

fn meta_path(vault_dir: &str) -> String {
    join(vault_dir, "quorum-meta.json")
}

fn directory_path(vault_dir: &str) -> String {
    join(vault_dir, "directory.bin")
}

fn lock_path(vault_dir: &str) -> String {
    format!("{}.vault.lock", meta_path(vault_dir))
}

fn share_path(vault_dir: &str, party: usize, generation: u64) -> String {
    join(vault_dir, &format!("custodian-{party}.g{generation}.share"))
}

fn legacy_share_path(vault_dir: &str, party: usize) -> String {
    join(vault_dir, &format!("custodian-{party}.share"))
}

fn canonical_number(text: &str) -> Option<u64> {
    let value: u64 = text.parse().ok()?;
    (value.to_string() == text).then_some(value)
}

/// `custodian-<p>.share` -> `(p, None)`; `custodian-<p>.g<G>.share` -> `(p, Some(G))`.
fn parse_share_name(name: &str) -> Option<(u64, Option<u64>)> {
    let rest = name.strip_prefix("custodian-")?.strip_suffix(".share")?;
    match rest.split_once(".g") {
        None => Some((canonical_number(rest)?, None)),
        Some((party, generation)) => Some((
            canonical_number(party)?,
            Some(canonical_number(generation)?),
        )),
    }
}

/// A temporary file left by an interrupted [`replace_secret`] of one of this vault's files.
fn is_stale_temporary(name: &str) -> bool {
    let Some(rest) = name.strip_suffix(".tmp") else {
        return false;
    };
    let Some((base, nonce)) = rest.rsplit_once('.') else {
        return false;
    };
    nonce.len() == 64
        && nonce.bytes().all(|b| b.is_ascii_hexdigit())
        && (base == "quorum-meta.json" || parse_share_name(base).is_some())
}

pub fn is_hem_vault(vault_dir: &str) -> bool {
    Path::new(&meta_path(vault_dir)).exists()
}

fn exists(path: &str) -> Result<bool, CliError> {
    match std::fs::symlink_metadata(path) {
        Ok(_) => Ok(true),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(false),
        Err(e) => Err(CliError::io(format_args!("inspecting {path}"), e)),
    }
}

fn ensure_absent(path: &str) -> Result<(), CliError> {
    if exists(path)? {
        return Err(CliError::usage(format!("{path} already exists")));
    }
    Ok(())
}

fn vault_file_names(vault_dir: &str) -> Result<Vec<String>, CliError> {
    let mut names = Vec::new();
    let entries = std::fs::read_dir(vault_dir)
        .map_err(|e| CliError::io(format_args!("listing {vault_dir}"), e))?;
    for entry in entries {
        let entry = entry.map_err(|e| CliError::io(format_args!("listing {vault_dir}"), e))?;
        if let Some(name) = entry.file_name().to_str() {
            names.push(name.to_owned());
        }
    }
    Ok(names)
}

/// Refuse a directory that already holds any vault file, before anything is written to it.
/// A lock file on its own is allowed: an interrupted earlier attempt may have left one.
fn ensure_no_vault_files(vault_dir: &str) -> Result<(), CliError> {
    if !exists(vault_dir)? {
        return Ok(());
    }
    ensure_absent(&meta_path(vault_dir))?;
    ensure_absent(&directory_path(vault_dir))?;
    for name in vault_file_names(vault_dir)? {
        if parse_share_name(&name).is_some() {
            return Err(CliError::usage(format!(
                "{} already exists",
                join(vault_dir, &name)
            )));
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------------------
// Crash boundaries
// ---------------------------------------------------------------------------------------

/// A point between two durable writes. Each transaction reports the ones it passes; an
/// error returned from the observer stops the transaction there, leaving the disk as a
/// crash at that point would. Commands run with [`no_crash`]; the tests stop at every one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Step {
    /// One share file of the next generation is on disk; the meta still names the old one.
    ShareStaged,
    /// The meta was replaced: the new generation is the vault's state.
    MetaCommitted,
    /// Share files of other generations were wiped and removed.
    StaleRemoved,
    /// Signing only: the reserved leaf is burned on disk and has not been used yet.
    LeafBurned,
    /// Reshare only: the new vault's directory and lock exist.
    TargetPrepared,
    /// Reshare only: the old vault records where it is being reshared to.
    IntentRecorded,
    /// Reshare only: an interrupted reshare was undone and the old vault is live again.
    IntentCleared,
}

type Hook<'a> = &'a mut dyn FnMut(Step) -> Result<(), CliError>;

fn no_crash(_: Step) -> Result<(), CliError> {
    Ok(())
}

// ---------------------------------------------------------------------------------------
// Lock
// ---------------------------------------------------------------------------------------

/// The identity `(device, inode)` of a held lock file, as [`Vault::bind`] reports it.
fn lock_identity(lock: &Vault) -> Result<(u64, u64), CliError> {
    let mut probe = Json::object(Vec::new());
    lock.bind(&mut probe)?;
    Ok((
        probe.field_u64("vault_device")?,
        probe.field_u64("vault_inode")?,
    ))
}

/// Take the exclusive lock of an existing vault. The second value says the lock file was
/// created by this call.
///
/// Only a vault written before lock files existed (meta format v1) may lack one; it gets a
/// lock here, created exclusively, so two commands racing on such a vault end up holding
/// the same file one after the other. A v2 vault records its lock's inode in the meta and
/// is refused when the lock is missing or is a different file.
fn lock_existing_vault(vault_dir: &str) -> Result<(Vault, bool), CliError> {
    private_dir(vault_dir, false)?;
    let mp = meta_path(vault_dir);
    if exists(&lock_path(vault_dir))? {
        return Ok((Vault::acquire(&mp, false)?, false));
    }
    let meta = Json::parse(&read_text(&mp)?)?;
    if meta.field_str("format")? != HEM_META_FORMAT_V1 {
        // Unless another command converted the vault since the check above, a current
        // vault without its lock is refused.
        if exists(&lock_path(vault_dir))? {
            return Ok((Vault::acquire(&mp, false)?, false));
        }
        return Err(crate::vault::corrupt());
    }
    if meta
        .get("invalidated")
        .and_then(Json::as_bool)
        .unwrap_or(false)
    {
        return Err(retired());
    }
    match Vault::acquire(&mp, true) {
        Ok(lock) => Ok((lock, true)),
        // Another command created it first: wait for that one.
        Err(_) => Ok((Vault::acquire(&mp, false)?, false)),
    }
}

/// Take the lock of a vault directory that is about to be filled, creating it if needed.
fn lock_new_vault(vault_dir: &str) -> Result<Vault, CliError> {
    let mp = meta_path(vault_dir);
    if exists(&lock_path(vault_dir))? {
        Vault::acquire(&mp, false)
    } else {
        Vault::acquire(&mp, true)
    }
}

fn retired() -> CliError {
    CliError::state("ShareInvalidated: this quorum vault was retired by a dynamic reshare")
}

// ---------------------------------------------------------------------------------------
// Passphrase Envelope (cshake256-iterated-v1)
// ---------------------------------------------------------------------------------------

#[derive(Clone)]
struct HemEnvelopeMeta {
    salt: [u8; 32],
    nonce: [u8; 32],
    tag: [u8; 32],
    encrypted_latch_seed: [u8; 32],
}

struct HemEnvelopeKeys {
    salt: [u8; 32],
    enc: Secret32,
    mac: Secret32,
}

impl HemEnvelopeKeys {
    fn derive_fresh(pass: &[u8]) -> Result<Self, CliError> {
        if pass.is_empty() {
            return Err(CliError::input("empty passphrase"));
        }
        let salt = os_random_32()?;
        let (enc, mac) = derive_hem_envelope_keys(pass, &salt);
        Ok(Self { salt, enc, mac })
    }

    fn from_salt(pass: &[u8], salt: [u8; 32]) -> Result<Self, CliError> {
        if pass.is_empty() {
            return Err(CliError::input("empty passphrase"));
        }
        let (enc, mac) = derive_hem_envelope_keys(pass, &salt);
        Ok(Self { salt, enc, mac })
    }
}

fn derive_hem_envelope_keys(pass: &[u8], salt: &[u8; 32]) -> (Secret32, Secret32) {
    let mut state = Secret32::new([0u8; 32]);
    cshake256_framed_xof(
        b"QSAG.ENVELOPE.KDF.V1",
        &[pass, salt, HEM_SCHEME_NAME.as_bytes()],
        &mut state.0,
    );
    for i in 0..crate::envelope::KDF_ROUNDS {
        let mut next = Secret32::new([0u8; 32]);
        cshake256_framed_xof(
            b"QSAG.ENVELOPE.ITER.V1",
            &[&state.0, salt, &i.to_le_bytes()],
            &mut next.0,
        );
        state = next;
    }
    let mut enc = Secret32::new([0u8; 32]);
    cshake256_framed_xof(
        b"QSAG.ENVELOPE.ENC.V1",
        &[&state.0, salt, HEM_SCHEME_NAME.as_bytes()],
        &mut enc.0,
    );
    let mut mac = Secret32::new([0u8; 32]);
    cshake256_framed_xof(
        b"QSAG.ENVELOPE.MAC.V1",
        &[&state.0, salt, HEM_SCHEME_NAME.as_bytes()],
        &mut mac.0,
    );
    (enc, mac)
}

fn crypt_latch_seed(
    buf: &mut [u8; 32],
    enc: &Secret32,
    salt: &[u8; 32],
    nonce: &[u8; 32],
    generation: u64,
) {
    let mut stream = Secret32::new([0u8; 32]);
    cshake256_framed_xof(
        b"QSAG.HEM.LATCH.STREAM.V1",
        &[
            &enc.0,
            salt,
            nonce,
            HEM_SCHEME_NAME.as_bytes(),
            &generation.to_le_bytes(),
        ],
        &mut stream.0,
    );
    for (a, b) in buf.iter_mut().zip(stream.0.iter()) {
        *a ^= *b;
    }
}

fn crypt_share_payload(
    bytes: &mut [u8],
    enc: &Secret32,
    salt: &[u8; 32],
    nonce: &[u8; 32],
    generation: u64,
    party: usize,
) {
    let party_le = (party as u64).to_le_bytes();
    let gen_le = generation.to_le_bytes();
    for (blk_idx, block) in bytes.chunks_mut(32).enumerate() {
        let mut stream = Secret32::new([0u8; 32]);
        cshake256_framed_xof(
            b"QSAG.HEM.SHARE.STREAM.V1",
            &[
                &enc.0,
                salt,
                nonce,
                HEM_SCHEME_NAME.as_bytes(),
                &gen_le,
                &party_le,
                &(blk_idx as u64).to_le_bytes(),
            ],
            &mut stream.0,
        );
        for (a, b) in block.iter_mut().zip(stream.0.iter()) {
            *a ^= *b;
        }
    }
}

fn compute_share_seal_tag(
    mac: &Secret32,
    pk: &[u8; HEM_JORTS_PK_BYTES],
    salt: &[u8; 32],
    nonce: &[u8; 32],
    generation: u64,
    party: usize,
    ciphertext: &[u8],
) -> [u8; 32] {
    cshake256_framed_32(
        b"QSAG.HEM.SHARE.TAG.V1",
        &[
            &mac.0,
            HEM_SHARE_SEAL_MAGIC,
            pk,
            salt,
            nonce,
            &generation.to_le_bytes(),
            &(party as u64).to_le_bytes(),
            ciphertext,
        ],
    )
}

fn seal_share_bytes(
    plain: &[u8],
    keys: &HemEnvelopeKeys,
    pk: &[u8; HEM_JORTS_PK_BYTES],
    nonce: &[u8; 32],
    generation: u64,
    party: usize,
) -> ZeroizingBuf {
    let mut ct = ZeroizingBuf::new(plain.to_vec());
    crypt_share_payload(&mut ct.0, &keys.enc, &keys.salt, nonce, generation, party);
    let tag = compute_share_seal_tag(&keys.mac, pk, &keys.salt, nonce, generation, party, &ct.0);
    let mut out = Vec::with_capacity(HEM_SHARE_SEAL_HEADER_BYTES + ct.0.len());
    out.extend_from_slice(HEM_SHARE_SEAL_MAGIC);
    out.extend_from_slice(&(party as u64).to_le_bytes());
    out.extend_from_slice(&generation.to_le_bytes());
    out.extend_from_slice(nonce);
    out.extend_from_slice(&tag);
    out.extend_from_slice(&ct.0);
    ZeroizingBuf::new(out)
}

fn open_sealed_share_bytes(
    sealed: &[u8],
    keys: &HemEnvelopeKeys,
    pk: &[u8; HEM_JORTS_PK_BYTES],
    expected_nonce: &[u8; 32],
    generation: u64,
    party: usize,
) -> Result<ZeroizingBuf, CliError> {
    if sealed.len() <= HEM_SHARE_SEAL_HEADER_BYTES || &sealed[..24] != HEM_SHARE_SEAL_MAGIC {
        return Err(CliError::state("CorruptSealedHemShareHeader"));
    }
    let rec_party = u64::from_le_bytes(sealed[24..32].try_into().unwrap());
    let rec_gen = u64::from_le_bytes(sealed[32..40].try_into().unwrap());
    if rec_party != party as u64 || rec_gen != generation {
        return Err(CliError::state("HemSealedShareBindingMismatch"));
    }
    let rec_nonce: &[u8; 32] = sealed[40..72].try_into().unwrap();
    if !qsag_accel::ct::ct_eq_bytes(rec_nonce, expected_nonce) {
        return Err(CliError::state("HemSealedShareNonceMismatch"));
    }
    let rec_tag: &[u8; 32] = sealed[72..104].try_into().unwrap();
    let ct = &sealed[104..];
    let expected_tag = compute_share_seal_tag(
        &keys.mac,
        pk,
        &keys.salt,
        expected_nonce,
        generation,
        party,
        ct,
    );
    if !qsag_accel::ct::ct_eq_bytes(rec_tag, &expected_tag) {
        return Err(CliError::input(
            "wrong passphrase or damaged sealed Hem quorum share",
        ));
    }
    let mut plain = ZeroizingBuf::new(ct.to_vec());
    crypt_share_payload(
        &mut plain.0,
        &keys.enc,
        &keys.salt,
        expected_nonce,
        generation,
        party,
    );
    Ok(plain)
}

// ---------------------------------------------------------------------------------------
// Meta
// ---------------------------------------------------------------------------------------

struct PendingReshare {
    /// Absolute path of the vault being created.
    target: String,
    /// The quorum epoch the new vault starts at.
    quorum_epoch: u64,
    /// Identifies only this attempt's uncommitted fork-guard target and external anchor.
    anchor_key_id: Option<[u8; 32]>,
    anchor_dir: Option<String>,
}

/// The committed state of a v2 vault.
struct Meta {
    t: usize,
    n: usize,
    quorum_epoch: u64,
    high_water_leaf: usize,
    active_leaves: usize,
    invalidated: bool,
    pk: [u8; HEM_JORTS_PK_BYTES],
    directory_digest: [u8; 32],
    latch_seed: Secret32,
    generation: u64,
    share_digests: Vec<[u8; 32]>,
    lock_id: (u64, u64),
    pending: Option<PendingReshare>,
    envelope: Option<HemEnvelopeMeta>,
    anchor_info: Option<([u8; 24], [u8; 32])>,
    // Absent for older vaults whose anchor identity used only the lock inode.
    anchor_key_id: Option<[u8; 32]>,
}

const HEM_ANCHOR_DOMAIN: &str = "hem_quorum";

fn hem_anchor_key_id(pk: &[u8; HEM_JORTS_PK_BYTES], lock_id: (u64, u64)) -> [u8; 32] {
    cshake256_framed_32(
        b"QSAG.CLI.HEM.ANCHOR.KEYID.V1",
        &[pk, &lock_id.0.to_le_bytes(), &lock_id.1.to_le_bytes()],
    )
}

fn hem_anchor_mac(anchor_nonce: &[u8; 32], key_id: &[u8; 32]) -> Secret32 {
    Secret32::new(cshake256_framed_32(
        b"QSAG.CLI.HEM.ANCHOR.MAC.V1",
        &[anchor_nonce, key_id],
    ))
}

fn share_digest(party: usize, bytes: &[u8]) -> [u8; 32] {
    cshake256_framed_32(
        b"QSAG.CLI.HEM.SHARE_DIGEST.V1",
        &[&(party as u64).to_le_bytes(), bytes],
    )
}

fn directory_digest(bytes: &[u8]) -> [u8; 32] {
    cshake256_framed_32(b"QSAG.CLI.HEM.DIR_DIGEST.V1", &[bytes])
}

impl Meta {
    /// Meta for `quorum` before its first generation is written.
    fn new(quorum: &HemDynamicShamirQuorum, latch_seed: Secret32, lock_id: (u64, u64)) -> Self {
        let (t, n) = quorum.threshold_and_size();
        Self {
            t,
            n,
            quorum_epoch: quorum.quorum_epoch(),
            high_water_leaf: quorum.high_water_leaf(),
            active_leaves: quorum.public_directory().active_leaves,
            invalidated: false,
            pk: quorum.public_key().to_bytes(),
            directory_digest: directory_digest(&quorum.public_directory().to_bytes()),
            latch_seed,
            generation: 0,
            share_digests: Vec::new(),
            lock_id,
            pending: None,
            envelope: None,
            anchor_info: None,
            anchor_key_id: None,
        }
    }

    fn latch_seed_on_disk(&self) -> &[u8; 32] {
        match &self.envelope {
            Some(env) => &env.encrypted_latch_seed,
            None => &self.latch_seed.0,
        }
    }

    fn compute_envelope_tag(
        &self,
        salt: &[u8; 32],
        nonce: &[u8; 32],
        encrypted_latch_seed: &[u8; 32],
        mac: &Secret32,
    ) -> [u8; 32] {
        let mut flat_shares = Vec::with_capacity(self.share_digests.len() * 32);
        for d in &self.share_digests {
            flat_shares.extend_from_slice(d);
        }
        cshake256_framed_32(
            b"QSAG.HEM.META.TAG.V1",
            &[
                &mac.0,
                HEM_ENVELOPE_FORMAT.as_bytes(),
                HEM_SCHEME_NAME.as_bytes(),
                &(self.t as u64).to_le_bytes(),
                &(self.n as u64).to_le_bytes(),
                &self.quorum_epoch.to_le_bytes(),
                &(self.high_water_leaf as u64).to_le_bytes(),
                &(self.active_leaves as u64).to_le_bytes(),
                &self.pk,
                &self.directory_digest,
                &self.generation.to_le_bytes(),
                salt,
                nonce,
                encrypted_latch_seed,
                &flat_shares,
            ],
        )
    }

    /// Digest over every on-disk field, so an edited or damaged meta is refused.
    /// For unsealed vaults (`self.envelope.is_none()`), the frame sequence is 100%
    /// byte-identical to unsealed v2 vaults.
    fn digest(&self) -> [u8; 32] {
        let mut frames: Vec<Vec<u8>> = vec![
            (self.t as u64).to_le_bytes().to_vec(),
            (self.n as u64).to_le_bytes().to_vec(),
            self.quorum_epoch.to_le_bytes().to_vec(),
            (self.high_water_leaf as u64).to_le_bytes().to_vec(),
            (self.active_leaves as u64).to_le_bytes().to_vec(),
            vec![u8::from(self.invalidated)],
            self.pk.to_vec(),
            self.directory_digest.to_vec(),
            self.latch_seed_on_disk().to_vec(),
            self.generation.to_le_bytes().to_vec(),
            self.lock_id.0.to_le_bytes().to_vec(),
            self.lock_id.1.to_le_bytes().to_vec(),
            (self.share_digests.len() as u64).to_le_bytes().to_vec(),
        ];
        frames.extend(self.share_digests.iter().map(|d| d.to_vec()));
        match &self.pending {
            None => frames.push(vec![0]),
            Some(pending) => {
                frames.push(vec![1]);
                frames.push(pending.target.as_bytes().to_vec());
                frames.push(pending.quorum_epoch.to_le_bytes().to_vec());
                if let Some(key_id) = pending.anchor_key_id {
                    frames.push(b"QSAG.HEM.PENDING.ANCHOR.KEYID.V2".to_vec());
                    frames.push(key_id.to_vec());
                }
                if let Some(dir) = &pending.anchor_dir {
                    frames.push(b"QSAG.HEM.PENDING.ANCHOR.DIR.V2".to_vec());
                    frames.push(dir.as_bytes().to_vec());
                }
            }
        }
        if let Some(env) = &self.envelope {
            frames.push(HEM_ENVELOPE_FORMAT.as_bytes().to_vec());
            frames.push(env.salt.to_vec());
            frames.push(env.nonce.to_vec());
            frames.push(env.tag.to_vec());
        }
        if let Some((seal, anchor_nonce)) = &self.anchor_info {
            frames.push(b"QSAG.HEM.ANCHOR.V1".to_vec());
            frames.push(seal.to_vec());
            frames.push(anchor_nonce.to_vec());
        }
        if let Some(key_id) = self.anchor_key_id {
            frames.push(b"QSAG.HEM.ANCHOR.KEYID.V2".to_vec());
            frames.push(key_id.to_vec());
        }
        let refs: Vec<&[u8]> = frames.iter().map(Vec::as_slice).collect();
        let digest = cshake256_framed_32(b"QSAG.CLI.HEM.META_DIGEST.V2", &refs);
        for frame in &mut frames {
            qsag_accel::ct::ct_zeroize_bytes(frame);
        }
        digest
    }

    fn checkpoint(&self) -> LedgerCheckpoint {
        let mut flat_shares = Vec::with_capacity(self.share_digests.len() * 32);
        for d in &self.share_digests {
            flat_shares.extend_from_slice(d);
        }
        let (seal_bytes, nonce_bytes) = match &self.anchor_info {
            Some((s, n)) => (&s[..], &n[..]),
            None => (&[][..], &[][..]),
        };
        let tag = cshake256_framed_32(
            b"QSAG.CLI.HEM.ANCHOR_CKPT.V1",
            &[
                &(self.t as u64).to_le_bytes(),
                &(self.n as u64).to_le_bytes(),
                &self.quorum_epoch.to_le_bytes(),
                &(self.high_water_leaf as u64).to_le_bytes(),
                &(self.active_leaves as u64).to_le_bytes(),
                &[u8::from(self.invalidated)],
                &self.pk,
                &self.directory_digest,
                &self.generation.to_le_bytes(),
                &self.lock_id.0.to_le_bytes(),
                &self.lock_id.1.to_le_bytes(),
                &flat_shares,
                seal_bytes,
                nonce_bytes,
            ],
        );
        LedgerCheckpoint {
            generation: self.generation,
            tag,
        }
    }

    fn to_json(&self) -> Json {
        let mut members = vec![
            ("format", Json::str(HEM_META_FORMAT)),
            ("scheme", Json::str(HEM_SCHEME_NAME)),
            ("threshold", Json::num(self.t)),
            ("parties", Json::num(self.n)),
            ("quorum_epoch", Json::num(self.quorum_epoch)),
            ("high_water_leaf", Json::num(self.high_water_leaf)),
            ("active_leaves", Json::num(self.active_leaves)),
            ("invalidated", Json::Bool(self.invalidated)),
            ("validator_public_key", Json::hex(&self.pk)),
            ("directory_digest", Json::hex(&self.directory_digest)),
            ("latch_seed", Json::hex(self.latch_seed_on_disk())),
            ("generation", Json::num(self.generation)),
            (
                "share_digests",
                Json::Array(self.share_digests.iter().map(|d| Json::hex(d)).collect()),
            ),
            ("vault_device", Json::num(self.lock_id.0)),
            ("vault_inode", Json::num(self.lock_id.1)),
        ];
        if let Some((seal, anchor_nonce)) = &self.anchor_info {
            members.push(("anchor_required", Json::Bool(true)));
            members.push(("anchor_ceremony_seal", Json::hex(seal)));
            members.push(("anchor_nonce", Json::hex(anchor_nonce)));
        }
        if let Some(key_id) = self.anchor_key_id {
            members.push(("anchor_key_id", Json::hex(&key_id)));
        }
        if let Some(env) = &self.envelope {
            members.push(("envelope", Json::str(HEM_ENVELOPE_FORMAT)));
            members.push(("envelope_salt", Json::hex(&env.salt)));
            members.push(("envelope_nonce", Json::hex(&env.nonce)));
            members.push(("envelope_tag", Json::hex(&env.tag)));
        }
        if let Some(pending) = &self.pending {
            members.push(("pending_reshare_target", Json::str(pending.target.clone())));
            members.push(("pending_reshare_epoch", Json::num(pending.quorum_epoch)));
            if let Some(key_id) = pending.anchor_key_id {
                members.push(("pending_reshare_anchor_key_id", Json::hex(&key_id)));
            }
            if let Some(dir) = &pending.anchor_dir {
                members.push(("pending_reshare_anchor_dir", Json::str(dir.clone())));
            }
        }
        members.push(("meta_digest", Json::hex(&self.digest())));
        Json::object(members)
    }

    fn from_json(json: &Json) -> Result<Self, CliError> {
        let corrupt = || CliError::state("CorruptHemQuorumMeta");
        if json.field_str("format")? != HEM_META_FORMAT
            || json.field_str("scheme")? != HEM_SCHEME_NAME
        {
            return Err(corrupt());
        }
        let share_digests = json
            .get("share_digests")
            .and_then(Json::as_array)
            .ok_or_else(corrupt)?
            .iter()
            .map(|d| from_hex_exact(d.as_str().ok_or_else(corrupt)?, "share_digests"))
            .collect::<Result<Vec<[u8; 32]>, CliError>>()?;
        let pending = match json.get("pending_reshare_target") {
            None => None,
            Some(target) => Some(PendingReshare {
                target: target.as_str().ok_or_else(corrupt)?.to_owned(),
                quorum_epoch: json.field_u64("pending_reshare_epoch")?,
                anchor_key_id: json
                    .get("pending_reshare_anchor_key_id")
                    .map(|value| {
                        from_hex_exact(
                            value.as_str().ok_or_else(corrupt)?,
                            "pending_reshare_anchor_key_id",
                        )
                    })
                    .transpose()?,
                anchor_dir: json
                    .get("pending_reshare_anchor_dir")
                    .map(|value| value.as_str().ok_or_else(corrupt).map(str::to_owned))
                    .transpose()?,
            }),
        };
        let latch_disk: [u8; 32] = from_hex_exact(json.field_str("latch_seed")?, "latch_seed")?;
        let has_any_env = json.get("envelope").is_some()
            || json.get("envelope_salt").is_some()
            || json.get("envelope_nonce").is_some()
            || json.get("envelope_tag").is_some();
        let envelope = if has_any_env {
            if json.get("envelope").is_none() {
                return Err(CliError::input("damaged sealed Hem quorum envelope header"));
            }
            if json.field_str("envelope")? != HEM_ENVELOPE_FORMAT {
                return Err(CliError::input("unsupported sealed Hem quorum envelope"));
            }
            Some(HemEnvelopeMeta {
                salt: from_hex_exact(json.field_str("envelope_salt")?, "envelope_salt")?,
                nonce: from_hex_exact(json.field_str("envelope_nonce")?, "envelope_nonce")?,
                tag: from_hex_exact(json.field_str("envelope_tag")?, "envelope_tag")?,
                encrypted_latch_seed: latch_disk,
            })
        } else {
            None
        };
        let latch_seed = if envelope.is_some() {
            Secret32::new([0u8; 32])
        } else {
            Secret32::new(latch_disk)
        };
        let anchor_info = match json.get("anchor_required") {
            None | Some(Json::Bool(false)) => None,
            Some(Json::Bool(true)) => {
                let seal: [u8; 24] = from_hex_exact(
                    json.field_str("anchor_ceremony_seal")
                        .map_err(|_| corrupt())?,
                    "anchor_ceremony_seal",
                )?;
                let nonce: [u8; 32] = from_hex_exact(
                    json.field_str("anchor_nonce").map_err(|_| corrupt())?,
                    "anchor_nonce",
                )?;
                Some((seal, nonce))
            }
            Some(_) => return Err(corrupt()),
        };
        let meta = Self {
            t: usize::try_from(json.field_u64("threshold")?)
                .map_err(|_| CliError::input("threshold out of range"))?,
            n: usize::try_from(json.field_u64("parties")?)
                .map_err(|_| CliError::input("parties out of range"))?,
            quorum_epoch: json.field_u64("quorum_epoch")?,
            high_water_leaf: usize::try_from(json.field_u64("high_water_leaf")?)
                .map_err(|_| CliError::input("high_water_leaf out of range"))?,
            active_leaves: usize::try_from(json.field_u64("active_leaves")?)
                .map_err(|_| CliError::input("active_leaves out of range"))?,
            invalidated: json
                .get("invalidated")
                .and_then(Json::as_bool)
                .ok_or_else(corrupt)?,
            pk: from_hex_exact(
                json.field_str("validator_public_key")?,
                "validator_public_key",
            )?,
            directory_digest: from_hex_exact(
                json.field_str("directory_digest")?,
                "directory_digest",
            )?,
            latch_seed,
            generation: json.field_u64("generation")?,
            share_digests,
            lock_id: (
                json.field_u64("vault_device")?,
                json.field_u64("vault_inode")?,
            ),
            pending,
            envelope,
            anchor_info,
            anchor_key_id: json
                .get("anchor_key_id")
                .map(|value| from_hex_exact(value.as_str().ok_or_else(corrupt)?, "anchor_key_id"))
                .transpose()?,
        };
        let recorded: [u8; 32] = from_hex_exact(json.field_str("meta_digest")?, "meta_digest")?;
        if !qsag_accel::ct::ct_eq_bytes(&recorded, &meta.digest()) {
            return Err(CliError::state("HemQuorumMetaDigestMismatch"));
        }
        if !meta.invalidated && meta.share_digests.len() != meta.n {
            return Err(corrupt());
        }
        Ok(meta)
    }

    fn unlock_with_passphrase(
        &mut self,
        pass: Option<&[u8]>,
    ) -> Result<Option<HemEnvelopeKeys>, CliError> {
        match (&self.envelope, pass) {
            (None, None) => Ok(None),
            (None, Some(_)) => Err(CliError::input(
                "passphrase supplied for unencrypted Hem quorum vault",
            )),
            (Some(_), None) => Err(CliError::usage(
                "sealed Hem quorum vault requires --passphrase-env or --passphrase-file",
            )),
            (Some(env), Some(pass_bytes)) => {
                let keys = HemEnvelopeKeys::from_salt(pass_bytes, env.salt)?;
                let expected_tag = self.compute_envelope_tag(
                    &env.salt,
                    &env.nonce,
                    &env.encrypted_latch_seed,
                    &keys.mac,
                );
                if !qsag_accel::ct::ct_eq_bytes(&expected_tag, &env.tag) {
                    return Err(CliError::input(
                        "wrong passphrase or damaged sealed Hem quorum vault",
                    ));
                }
                let mut seed = Secret32::new(env.encrypted_latch_seed);
                crypt_latch_seed(
                    &mut seed.0,
                    &keys.enc,
                    &env.salt,
                    &env.nonce,
                    self.generation,
                );
                self.latch_seed = seed;
                Ok(Some(keys))
            }
        }
    }

    fn read(vault_dir: &str) -> Result<Self, CliError> {
        Self::from_json(&Json::parse(&read_text(&meta_path(vault_dir))?)?)
    }

    /// Put this meta on disk. Replacing an existing meta is one atomic rename.
    fn write(&self, vault_dir: &str, fresh: bool) -> Result<(), CliError> {
        let bytes = ZeroizingBuf::new(self.to_json().to_pretty().into_bytes());
        if fresh {
            write_new(&meta_path(vault_dir), &bytes.0, true)
        } else {
            replace_secret(&meta_path(vault_dir), &bytes.0)
        }
    }
}

// ---------------------------------------------------------------------------------------
// Generations
// ---------------------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq)]
enum Keep {
    /// The vault is still in the old format: keep `custodian-<p>.share`.
    Legacy,
    /// Keep the share files of this generation only.
    Generation(u64),
    /// The vault is retired or was never committed: keep no share file.
    Nothing,
}

/// Overwrite a superseded share file with zeros and remove it. Overwriting in place is
/// best effort: a copy-on-write or flash-translated disk may keep the old blocks.
fn wipe_and_remove(path: &str) -> Result<(), CliError> {
    let meta = std::fs::symlink_metadata(path)
        .map_err(|e| CliError::io(format_args!("inspecting {path}"), e))?;
    if !meta.is_file() {
        return Err(CliError::state(format!("{path} is not a regular file")));
    }
    let mut options = std::fs::OpenOptions::new();
    options.write(true);
    crate::cli::set_nofollow_nonblocking(&mut options)?;
    let wiped = options.open(path).and_then(|mut file| {
        use std::io::Write;
        let zeros = vec![0u8; 64 * 1024];
        let mut left = meta.len();
        while left > 0 {
            let chunk = usize::try_from(left.min(zeros.len() as u64)).map_err(|_| {
                std::io::Error::new(std::io::ErrorKind::InvalidData, "wipe chunk out of range")
            })?;
            file.write_all(&zeros[..chunk])?;
            left -= chunk as u64;
        }
        file.sync_all()
    });
    wiped.map_err(|e| CliError::io(format_args!("wiping {path}"), e))?;
    std::fs::remove_file(path).map_err(|e| CliError::io(format_args!("removing {path}"), e))
}

/// Remove every share file the committed state does not name, and temporary files left by
/// an interrupted meta replacement. The caller holds the vault's lock. Files that are not
/// this vault's share or temporary files are never touched.
fn remove_stale(vault_dir: &str, keep: Keep) -> Result<(), CliError> {
    let mut removed = false;
    for name in vault_file_names(vault_dir)? {
        let stale = match parse_share_name(&name) {
            Some((_, None)) => keep != Keep::Legacy,
            Some((_, Some(generation))) => keep != Keep::Generation(generation),
            None => is_stale_temporary(&name),
        };
        if stale {
            wipe_and_remove(&join(vault_dir, &name))?;
            removed = true;
        }
    }
    if removed {
        sync_parent(&meta_path(vault_dir))?;
    }
    Ok(())
}

/// Make `quorum` the vault's state as generation `meta.generation + 1`.
///
/// The share files are written beside the current generation; replacing the meta commits
/// them; the generation they replace is wiped afterwards. `fresh` is for a vault that has
/// no meta yet. On error before the meta is replaced the vault is still its old state.
fn commit(
    vault_dir: &str,
    quorum: &HemDynamicShamirQuorum,
    meta: &mut Meta,
    keys: Option<&HemEnvelopeKeys>,
    fresh: bool,
    hook: Hook<'_>,
) -> Result<(), CliError> {
    commit_anchored(vault_dir, quorum, meta, keys, None, fresh, hook)
}

fn commit_anchored(
    vault_dir: &str,
    quorum: &HemDynamicShamirQuorum,
    meta: &mut Meta,
    keys: Option<&HemEnvelopeKeys>,
    anchor: Option<&FsExternalMountAnchor>,
    fresh: bool,
    hook: Hook<'_>,
) -> Result<(), CliError> {
    let generation = meta
        .generation
        .checked_add(1)
        .ok_or_else(|| CliError::state("HemQuorumGenerationExhausted"))?;
    let seal_nonce = if keys.is_some() {
        Some(os_random_32()?)
    } else {
        None
    };
    let mut digests = Vec::with_capacity(quorum.custodian_shares().len());
    for (party, share) in quorum.custodian_shares().iter().enumerate() {
        let raw = ZeroizingBuf::new(share.to_vault_bytes().map_err(map_quorum_err)?);
        let on_disk = match (keys, &seal_nonce) {
            (Some(k), Some(nonce)) => {
                seal_share_bytes(&raw.0, k, &meta.pk, nonce, generation, party)
            }
            _ => raw,
        };
        write_new(&share_path(vault_dir, party, generation), &on_disk.0, true)?;
        digests.push(share_digest(party, &on_disk.0));
        hook(Step::ShareStaged)?;
    }
    let (t, n) = quorum.threshold_and_size();
    meta.t = t;
    meta.n = n;
    meta.quorum_epoch = quorum.quorum_epoch();
    meta.high_water_leaf = quorum.high_water_leaf();
    meta.generation = generation;
    meta.share_digests = digests;
    meta.envelope = match (keys, seal_nonce) {
        (Some(k), Some(nonce)) => {
            let mut enc_latch = meta.latch_seed.0;
            crypt_latch_seed(&mut enc_latch, &k.enc, &k.salt, &nonce, generation);
            let tag = meta.compute_envelope_tag(&k.salt, &nonce, &enc_latch, &k.mac);
            Some(HemEnvelopeMeta {
                salt: k.salt,
                nonce,
                tag,
                encrypted_latch_seed: enc_latch,
            })
        }
        _ => None,
    };
    meta.write(vault_dir, fresh)?;
    if let Some(ext_anchor) = anchor {
        ext_anchor
            .advance(meta.checkpoint())
            .map_err(|e| CliError::state(format!("ExternalAnchorAdvanceFailed: {e}")))?;
    }
    hook(Step::MetaCommitted)?;
    remove_stale(vault_dir, Keep::Generation(generation))?;
    hook(Step::StaleRemoved)
}

/// Retire the vault: the meta and external anchor say so first, then every share file is wiped.
fn retire_anchored(
    vault_dir: &str,
    meta: &mut Meta,
    anchor: Option<&FsExternalMountAnchor>,
    hook: Hook<'_>,
) -> Result<(), CliError> {
    meta.invalidated = true;
    meta.pending = None;
    meta.envelope = None;
    meta.latch_seed = Secret32::new([0u8; 32]);
    meta.share_digests = Vec::new();
    meta.generation = meta
        .generation
        .checked_add(1)
        .ok_or_else(|| CliError::state("HemQuorumGenerationExhausted"))?;
    meta.write(vault_dir, false)?;
    if let Some(ext_anchor) = anchor {
        ext_anchor
            .advance(meta.checkpoint())
            .map_err(|e| CliError::state(format!("ExternalAnchorAdvanceFailed: {e}")))?;
    }
    hook(Step::MetaCommitted)?;
    remove_stale(vault_dir, Keep::Nothing)?;
    hook(Step::StaleRemoved)
}

// ---------------------------------------------------------------------------------------
// Opening a vault
// ---------------------------------------------------------------------------------------

/// A vault held under its lock, with its state loaded and nothing left over on disk.
struct OpenVault {
    _lock: Vault,
    quorum: HemDynamicShamirQuorum,
    meta: Meta,
    envelope_keys: Option<HemEnvelopeKeys>,
    anchor: Option<FsExternalMountAnchor>,
}

fn read_directory(
    vault_dir: &str,
    expected_digest: &[u8; 32],
) -> Result<HemQuorumPublicDirectory, CliError> {
    let raw = read_bounded_file(&directory_path(vault_dir), MAX_VAULT_FILE_BYTES)?;
    if !qsag_accel::ct::ct_eq_bytes(&directory_digest(&raw.0), expected_digest) {
        return Err(CliError::state("HemQuorumDirectoryDigestMismatch"));
    }
    HemQuorumPublicDirectory::from_bytes_canonical(&raw.0).map_err(map_quorum_err)
}

/// Load a vault in the old format: `custodian-<p>.share` files replaced one by one, then
/// the meta.
fn load_legacy(
    vault_dir: &str,
    json: &Json,
) -> Result<(HemDynamicShamirQuorum, Secret32), CliError> {
    if json.field_str("scheme")? != HEM_SCHEME_NAME {
        return Err(CliError::state("CorruptHemQuorumMeta"));
    }
    if json
        .get("invalidated")
        .and_then(Json::as_bool)
        .unwrap_or(false)
    {
        return Err(retired());
    }
    let t = usize::try_from(json.field_u64("threshold")?)
        .map_err(|_| CliError::input("threshold out of range"))?;
    let n = usize::try_from(json.field_u64("parties")?)
        .map_err(|_| CliError::input("parties out of range"))?;
    if t < 2 || t > n || n >= MAX_HEM_QUORUM_PARTIES {
        return Err(CliError::input(
            "invalid legacy Hem threshold or party count",
        ));
    }
    let expected_qe = json.field_u64("quorum_epoch")?;
    let meta_hw = usize::try_from(json.field_u64("high_water_leaf")?)
        .map_err(|_| CliError::input("high_water_leaf out of range"))?;
    let expected_pk: [u8; HEM_JORTS_PK_BYTES] = from_hex_exact(
        json.field_str("validator_public_key")?,
        "validator_public_key",
    )?;
    let expected_dir_digest: [u8; 32] =
        from_hex_exact(json.field_str("directory_digest")?, "directory_digest")?;
    let latch_seed = Secret32::new(from_hex_exact(json.field_str("latch_seed")?, "latch_seed")?);

    let public_dir = read_directory(vault_dir, &expected_dir_digest)?;
    if public_dir.pk.to_bytes() != expected_pk {
        return Err(CliError::state("HemQuorumPublicKeyMismatch"));
    }
    let mut shares = Vec::with_capacity(n);
    for p in 0..n {
        let raw = read_bounded_file(&legacy_share_path(vault_dir, p), MAX_VAULT_FILE_BYTES)?;
        shares.push(HemShamirCustodianShare::from_vault_bytes(&raw.0).map_err(map_quorum_err)?);
    }
    let high_water = shares
        .iter()
        .map(|s| s.high_water_leaf)
        .fold(meta_hw, usize::max);
    for share in &mut shares {
        if share.active_leaves != public_dir.active_leaves {
            return Err(CliError::state("HemQuorumHeaderStateMismatch"));
        }
        share.burn_leaves_below(high_water);
    }
    let quorum = HemDynamicShamirQuorum::from_persisted_shares(public_dir, shares, latch_seed.0)
        .map_err(map_quorum_err)?;
    if quorum.quorum_epoch() != expected_qe
        || quorum.high_water_leaf() != high_water
        || quorum.threshold_and_size() != (t, n)
    {
        return Err(CliError::state("HemQuorumHeaderStateMismatch"));
    }
    Ok((quorum, latch_seed))
}

fn load_generation(
    vault_dir: &str,
    meta: &Meta,
    keys: Option<&HemEnvelopeKeys>,
) -> Result<HemDynamicShamirQuorum, CliError> {
    let public_dir = read_directory(vault_dir, &meta.directory_digest)?;
    if public_dir.pk.to_bytes() != meta.pk {
        return Err(CliError::state("HemQuorumPublicKeyMismatch"));
    }
    let mut shares = Vec::with_capacity(meta.n);
    for (p, expected) in meta.share_digests.iter().enumerate() {
        let raw = read_bounded_file(
            &share_path(vault_dir, p, meta.generation),
            MAX_VAULT_FILE_BYTES,
        )?;
        if !qsag_accel::ct::ct_eq_bytes(&share_digest(p, &raw.0), expected) {
            return Err(CliError::state("HemQuorumShareDigestMismatch"));
        }
        let plain = match (&meta.envelope, keys) {
            (Some(env), Some(k)) => {
                open_sealed_share_bytes(&raw.0, k, &meta.pk, &env.nonce, meta.generation, p)?
            }
            (None, None) => raw,
            _ => return Err(CliError::state("HemQuorumEnvelopeStateMismatch")),
        };
        shares.push(HemShamirCustodianShare::from_vault_bytes(&plain.0).map_err(map_quorum_err)?);
    }
    let quorum =
        HemDynamicShamirQuorum::from_persisted_shares(public_dir, shares, meta.latch_seed.0)
            .map_err(map_quorum_err)?;
    if quorum.quorum_epoch() != meta.quorum_epoch
        || quorum.high_water_leaf() != meta.high_water_leaf
        || quorum.threshold_and_size() != (meta.t, meta.n)
        || quorum.public_directory().active_leaves != meta.active_leaves
    {
        return Err(CliError::state("HemQuorumHeaderStateMismatch"));
    }
    Ok(quorum)
}

/// Settle a reshare that stopped after the old vault recorded its intent.
fn settle_interrupted_reshare(
    vault_dir: &str,
    meta: &mut Meta,
    anchor: Option<&FsExternalMountAnchor>,
    hook: Hook<'_>,
) -> Result<(), CliError> {
    let Some(pending) = &meta.pending else {
        return Ok(());
    };
    let target = pending.target.clone();
    let unknown = |why: &str| {
        CliError::state(format!(
            "HemReshareInterrupted: a reshare of this vault into {target} did not finish and {why};              this vault stays closed so that it and its successor can never both sign"
        ))
    };
    if !exists(&target)? {
        return Err(unknown("that directory is missing"));
    }
    private_dir(&target, false)?;
    if exists(&meta_path(&target))? {
        let successor = Meta::read(&target).map_err(|_| unknown("its meta cannot be read"))?;
        if successor.pk != meta.pk || successor.quorum_epoch < pending.quorum_epoch {
            return Err(unknown("it holds a different vault"));
        }
        retire_anchored(vault_dir, meta, anchor, hook)?;
        return Err(retired());
    }
    // Never committed. The staged shares are shares of this vault's key: wipe them.
    {
        let _target_lock = if exists(&lock_path(&target))? {
            Some(Vault::acquire(&meta_path(&target), false)?)
        } else {
            None
        };
        remove_stale(&target, Keep::Nothing)?;
        let target_anchor_key_id = match (pending.anchor_key_id, &_target_lock) {
            (Some(key_id), _) => Some(key_id),
            (None, Some(lock)) => Some(hem_anchor_key_id(&meta.pk, lock_identity(lock)?)),
            (None, None) => None,
        };
        if let Some(key_id) = target_anchor_key_id {
            crate::anchor::remove_uncommitted_guarded_target(
                &target,
                pending.anchor_dir.as_deref(),
                HEM_ANCHOR_DOMAIN,
                &key_id,
            )?;
        }
        for leftover in [directory_path(&target), lock_path(&target)] {
            if exists(&leftover)? {
                std::fs::remove_file(&leftover)
                    .map_err(|e| CliError::io(format_args!("removing {leftover}"), e))?;
            }
        }
        sync_parent(&meta_path(&target))?;
    }
    meta.pending = None;
    meta.write(vault_dir, false)?;
    hook(Step::IntentCleared)
}

/// Lock a vault and load its committed state, finishing whatever an interrupted command
/// left: stale generations are wiped, an old-format vault is converted, an interrupted
/// reshare is settled.
#[cfg_attr(not(test), allow(dead_code))]
fn open_vault(vault_dir: &str, pass: Option<&[u8]>, hook: Hook<'_>) -> Result<OpenVault, CliError> {
    open_vault_anchored(vault_dir, pass, None, hook)
}

fn open_vault_anchored(
    vault_dir: &str,
    pass: Option<&[u8]>,
    anchor_cfg: Option<&AnchorConfig>,
    hook: Hook<'_>,
) -> Result<OpenVault, CliError> {
    let (lock, lock_created) = lock_existing_vault(vault_dir)?;
    let lock_id = lock_identity(&lock)?;
    let json = Json::parse(&read_text(&meta_path(vault_dir))?)?;

    if json.field_str("format")? == HEM_META_FORMAT_V1 {
        if anchor_cfg.is_some() {
            return Err(CliError::state(
                "legacy Hem quorum vault was not enrolled with an external monotone anchor",
            ));
        }
        if pass.is_some() {
            return Err(CliError::input(
                "passphrase supplied for unencrypted Hem quorum vault",
            ));
        }
        let (quorum, latch_seed) = load_legacy(vault_dir, &json)?;
        remove_stale(vault_dir, Keep::Legacy)?;
        let mut meta = Meta::new(&quorum, latch_seed, lock_id);
        commit(vault_dir, &quorum, &mut meta, None, false, hook)?;
        return Ok(OpenVault {
            _lock: lock,
            quorum,
            meta,
            envelope_keys: None,
            anchor: None,
        });
    }

    let mut meta = Meta::from_json(&json)?;
    if lock_created || meta.lock_id != lock_id {
        return Err(crate::vault::corrupt());
    }
    let anchor = match (meta.anchor_info, anchor_cfg) {
        (Some(_), None) => {
            return Err(CliError::state(
                "Hem quorum vault requires an external monotone anchor (--anchor-dir, --anchor-tpm-nv, or --anchor-vmgenid)",
            ));
        }
        (None, Some(_)) => {
            return Err(CliError::state(
                "Hem quorum vault was not enrolled with an external monotone anchor",
            ));
        }
        (None, None) => None,
        (Some((expected_seal, anchor_nonce)), Some(cfg)) => {
            let key_id = meta
                .anchor_key_id
                .unwrap_or_else(|| hem_anchor_key_id(&meta.pk, meta.lock_id));
            let mac = hem_anchor_mac(&anchor_nonce, &key_id);
            let ext_anchor = FsExternalMountAnchor::open_existing(
                cfg,
                &[&meta_path(vault_dir)],
                &[vault_dir],
                HEM_ANCHOR_DOMAIN,
                key_id,
                mac.0,
            )?;
            if !qsag_accel::ct::ct_eq_bytes(&ext_anchor.lock_identity_seal(), &expected_seal) {
                return Err(CliError::state("ExternalAnchorIdentitySealMismatch"));
            }
            let ext_ckpt = ext_anchor
                .load()
                .map_err(|e| CliError::state(format!("ExternalAnchorRollbackOrCorrupt: {e}")))?
                .ok_or_else(|| CliError::state("ExternalAnchorMissingFloorState"))?;
            let local_ckpt = meta.checkpoint();
            if local_ckpt.generation < ext_ckpt.generation
                || (local_ckpt.generation == ext_ckpt.generation
                    && !qsag_accel::ct::ct_eq_bytes(&local_ckpt.tag, &ext_ckpt.tag))
            {
                return Err(CliError::state(
                    "ExternalAnchorDetectedRollback: Hem quorum vault rolled back behind external anchor",
                ));
            }
            Some(ext_anchor)
        }
    };

    if meta.invalidated {
        remove_stale(vault_dir, Keep::Nothing)?;
        return Err(retired());
    }
    let envelope_keys = meta.unlock_with_passphrase(pass)?;
    settle_interrupted_reshare(vault_dir, &mut meta, anchor.as_ref(), &mut *hook)?;
    let quorum = load_generation(vault_dir, &meta, envelope_keys.as_ref())?;
    remove_stale(vault_dir, Keep::Generation(meta.generation))?;
    Ok(OpenVault {
        _lock: lock,
        quorum,
        meta,
        envelope_keys,
        anchor,
    })
}

// ---------------------------------------------------------------------------------------
// Transactions
// ---------------------------------------------------------------------------------------

/// Create a vault for a freshly staged quorum. The directory must hold no vault file.
#[cfg_attr(not(test), allow(dead_code))]
fn create_vault(
    vault_dir: &str,
    quorum: &HemDynamicShamirQuorum,
    latch_seed: Secret32,
    pass: Option<&[u8]>,
    hook: Hook<'_>,
) -> Result<(), CliError> {
    create_vault_anchored(vault_dir, quorum, latch_seed, pass, None, hook)
}

fn create_vault_anchored(
    vault_dir: &str,
    quorum: &HemDynamicShamirQuorum,
    latch_seed: Secret32,
    pass: Option<&[u8]>,
    anchor_cfg: Option<&AnchorConfig>,
    hook: Hook<'_>,
) -> Result<(), CliError> {
    let keys = match pass {
        Some(p) => Some(HemEnvelopeKeys::derive_fresh(p)?),
        None => None,
    };
    ensure_no_vault_files(vault_dir)?;
    private_dir(vault_dir, true)?;
    let lock = lock_new_vault(vault_dir)?;
    ensure_no_vault_files(vault_dir)?;
    let lock_id = lock_identity(&lock)?;
    let mut meta = Meta::new(quorum, latch_seed, lock_id);
    let anchor = match anchor_cfg {
        Some(cfg) => {
            let anchor_nonce = os_random_32()?;
            let key_id = cshake256_framed_32(
                b"QSAG.CLI.HEM.ANCHOR.KEYID.V2",
                &[&hem_anchor_key_id(&meta.pk, lock_id), &anchor_nonce],
            );
            meta.anchor_key_id = Some(key_id);
            let mac = hem_anchor_mac(&anchor_nonce, &key_id);
            let ext_anchor = FsExternalMountAnchor::provision_fresh(
                cfg,
                &[&meta_path(vault_dir)],
                &[vault_dir],
                HEM_ANCHOR_DOMAIN,
                key_id,
                mac.0,
            )?;
            meta.anchor_info = Some((ext_anchor.lock_identity_seal(), anchor_nonce));
            Some(ext_anchor)
        }
        None => None,
    };
    write_new(
        &directory_path(vault_dir),
        &quorum.public_directory().to_bytes(),
        false,
    )?;
    commit_anchored(
        vault_dir,
        quorum,
        &mut meta,
        keys.as_ref(),
        anchor.as_ref(),
        true,
        hook,
    )
}

struct Signed {
    leaf_epoch: u64,
    sig: HemJortsSignature,
    vault: OpenVault,
}

/// Sign `message`: reserve the leaf, commit the vault without it, then use it.
#[cfg_attr(not(test), allow(dead_code))]
fn sign_tx(
    vault_dir: &str,
    signers: Option<&str>,
    ackers: Option<&str>,
    requested_epoch: Option<u64>,
    message: &[u8],
    pass: Option<&[u8]>,
    hook: Hook<'_>,
) -> Result<Signed, CliError> {
    sign_tx_anchored(
        vault_dir,
        signers,
        ackers,
        requested_epoch,
        message,
        pass,
        None,
        hook,
    )
}

#[allow(clippy::too_many_arguments)]
fn sign_tx_anchored(
    vault_dir: &str,
    signers: Option<&str>,
    ackers: Option<&str>,
    requested_epoch: Option<u64>,
    message: &[u8],
    pass: Option<&[u8]>,
    anchor_cfg: Option<&AnchorConfig>,
    hook: Hook<'_>,
) -> Result<Signed, CliError> {
    let mut vault = open_vault_anchored(vault_dir, pass, anchor_cfg, &mut *hook)?;
    let (t, n) = vault.quorum.threshold_and_size();
    let signers = match signers {
        Some(s) => parse_party_list(s, "signers", n)?,
        None => (0..t).collect(),
    };
    let ackers = match ackers {
        Some(a) => parse_party_list(a, "ackers", n)?,
        None => (0..n).collect(),
    };
    if let Some(req_epoch) = requested_epoch
        && req_epoch != vault.quorum.high_water_leaf() as u64
    {
        return Err(CliError::state(format!(
            "requested --epoch {req_epoch} does not match monotone high-water leaf {}",
            vault.quorum.high_water_leaf()
        )));
    }

    let reserved = vault
        .quorum
        .reserve_leaf(&signers, &ackers, message)
        .map_err(map_quorum_err)?;
    commit_anchored(
        vault_dir,
        &vault.quorum,
        &mut vault.meta,
        vault.envelope_keys.as_ref(),
        vault.anchor.as_ref(),
        false,
        &mut *hook,
    )?;
    hook(Step::LeafBurned)?;

    let (leaf_epoch, sig) = vault
        .quorum
        .sign_reserved(reserved, message)
        .map_err(map_quorum_err)?;
    Ok(Signed {
        leaf_epoch,
        sig,
        vault,
    })
}

#[cfg_attr(not(test), allow(dead_code))]
fn refresh_tx(
    vault_dir: &str,
    deterministic: bool,
    pass: Option<&[u8]>,
    hook: Hook<'_>,
) -> Result<OpenVault, CliError> {
    refresh_tx_anchored(vault_dir, deterministic, pass, None, hook)
}

fn refresh_tx_anchored(
    vault_dir: &str,
    deterministic: bool,
    pass: Option<&[u8]>,
    anchor_cfg: Option<&AnchorConfig>,
    hook: Hook<'_>,
) -> Result<OpenVault, CliError> {
    let mut vault = open_vault_anchored(vault_dir, pass, anchor_cfg, &mut *hook)?;
    let pk_before = vault.quorum.public_key();
    let sid = if deterministic {
        cshake256_framed_32(
            b"QSAG.CLI.HEM.REFRESH.DET.V1",
            &[
                &pk_before.to_bytes(),
                &vault.quorum.quorum_epoch().to_le_bytes(),
                &vault.meta.latch_seed.0,
            ],
        )
    } else {
        os_random_32()?
    };
    let mut party_rngs = fresh_party_rngs(vault.quorum.threshold_and_size().1)?;
    vault
        .quorum
        .proactive_refresh(sid, &mut party_rngs)
        .map_err(map_quorum_err)?;
    if vault.quorum.public_key() != pk_before {
        return Err(CliError::verify(
            "proactive refresh mutated validator pubkey",
        ));
    }
    vault.meta.latch_seed = Secret32::new(os_random_32()?);
    commit_anchored(
        vault_dir,
        &vault.quorum,
        &mut vault.meta,
        vault.envelope_keys.as_ref(),
        vault.anchor.as_ref(),
        false,
        hook,
    )?;
    Ok(vault)
}

struct Reshared {
    old_t: usize,
    old_n: usize,
    quorum: HemDynamicShamirQuorum,
}

/// Move custody from the vault in `old_vault_dir` to a new vault in `new_vault_dir`.
#[cfg_attr(not(test), allow(dead_code))]
#[allow(clippy::too_many_arguments)]
fn reshare_tx(
    old_vault_dir: &str,
    new_vault_dir: &str,
    signers: Option<&str>,
    new_t: usize,
    new_n: usize,
    deterministic: bool,
    old_pass: Option<&[u8]>,
    new_pass: Option<&[u8]>,
    hook: Hook<'_>,
) -> Result<Reshared, CliError> {
    reshare_tx_anchored(
        old_vault_dir,
        new_vault_dir,
        signers,
        new_t,
        new_n,
        deterministic,
        old_pass,
        new_pass,
        None,
        None,
        hook,
    )
}

#[allow(clippy::too_many_arguments)]
fn reshare_tx_anchored(
    old_vault_dir: &str,
    new_vault_dir: &str,
    signers: Option<&str>,
    new_t: usize,
    new_n: usize,
    deterministic: bool,
    old_pass: Option<&[u8]>,
    new_pass: Option<&[u8]>,
    old_anchor_cfg: Option<&AnchorConfig>,
    new_anchor_cfg: Option<&AnchorConfig>,
    hook: Hook<'_>,
) -> Result<Reshared, CliError> {
    if new_t < 2 || new_t > new_n || new_n >= MAX_HEM_QUORUM_PARTIES {
        return Err(CliError::usage(
            "--new-threshold must be >= 2 and <= --new-parties (<= 255 nonzero GF(256) evaluation points)",
        ));
    }
    ensure_no_vault_files(new_vault_dir)?;
    let old = open_vault_anchored(old_vault_dir, old_pass, old_anchor_cfg, &mut *hook)?;
    let effective_new_pass = new_pass.or(old_pass);
    let new_keys = match effective_new_pass {
        Some(p) => Some(HemEnvelopeKeys::derive_fresh(p)?),
        None => None,
    };
    let (old_t, old_n) = old.quorum.threshold_and_size();
    let old_signers = match signers {
        Some(s) => parse_party_list(s, "signers", old_n)?,
        None => (0..old_t).collect(),
    };
    let pk_before = old.quorum.public_key();
    let sid = if deterministic {
        cshake256_framed_32(
            b"QSAG.CLI.HEM.RESHARE.DET.V1",
            &[
                &pk_before.to_bytes(),
                &old.quorum.quorum_epoch().to_le_bytes(),
                &(new_t as u64).to_le_bytes(),
                &(new_n as u64).to_le_bytes(),
                &old.meta.latch_seed.0,
            ],
        )
    } else {
        os_random_32()?
    };
    let new_latch_seed = Secret32::new(os_random_32()?);

    let mut old_party_rngs = fresh_party_rngs(old_n)?;
    let mut new_party_rngs = fresh_party_rngs(new_n)?;
    let OpenVault {
        _lock: old_lock,
        mut quorum,
        meta: mut old_meta,
        envelope_keys: _,
        anchor: old_anchor,
    } = old;
    quorum
        .reshare_quorum(
            sid,
            &old_signers,
            new_t,
            new_n,
            &mut old_party_rngs,
            &mut new_party_rngs,
        )
        .map_err(map_quorum_err)?;
    if quorum.public_key() != pk_before {
        return Err(CliError::verify(
            "dynamic reshare mutated validator public key",
        ));
    }

    private_dir(new_vault_dir, true)?;
    let target = std::fs::canonicalize(new_vault_dir)
        .map_err(|e| CliError::io(format_args!("resolving {new_vault_dir}"), e))?
        .to_str()
        .ok_or_else(|| CliError::usage("--out-vault-dir must be a UTF-8 path"))?
        .to_owned();
    let new_lock = lock_new_vault(&target)?;
    ensure_no_vault_files(&target)?;
    let new_lock_id = lock_identity(&new_lock)?;
    let mut new_meta = Meta::new(&quorum, new_latch_seed, new_lock_id);
    let anchor_nonce = os_random_32()?;
    let key_id = cshake256_framed_32(
        b"QSAG.CLI.HEM.ANCHOR.KEYID.V2",
        &[&hem_anchor_key_id(&new_meta.pk, new_lock_id), &anchor_nonce],
    );
    // Record recovery information before provisioning any external state.
    old_meta.pending = Some(PendingReshare {
        target: target.clone(),
        quorum_epoch: quorum.quorum_epoch(),
        anchor_key_id: new_anchor_cfg.map(|_| key_id),
        anchor_dir: new_anchor_cfg.and_then(|cfg| cfg.anchor_dir.clone()),
    });
    old_meta.write(old_vault_dir, false)?;
    hook(Step::IntentRecorded)?;
    let new_anchor = match new_anchor_cfg {
        Some(cfg) => {
            new_meta.anchor_key_id = Some(key_id);
            let mac = hem_anchor_mac(&anchor_nonce, &key_id);
            let ext_anchor = FsExternalMountAnchor::provision_fresh(
                cfg,
                &[&meta_path(&target)],
                &[&target],
                HEM_ANCHOR_DOMAIN,
                key_id,
                mac.0,
            )?;
            new_meta.anchor_info = Some((ext_anchor.lock_identity_seal(), anchor_nonce));
            Some(ext_anchor)
        }
        None => None,
    };
    hook(Step::TargetPrepared)?;

    write_new(
        &directory_path(&target),
        &quorum.public_directory().to_bytes(),
        false,
    )?;
    commit_anchored(
        &target,
        &quorum,
        &mut new_meta,
        new_keys.as_ref(),
        new_anchor.as_ref(),
        true,
        &mut *hook,
    )?;

    retire_anchored(old_vault_dir, &mut old_meta, old_anchor.as_ref(), hook)?;
    drop(old_lock);
    Ok(Reshared {
        old_t,
        old_n,
        quorum,
    })
}

// ---------------------------------------------------------------------------------------
// Commands
// ---------------------------------------------------------------------------------------

pub fn keygen(args: &Args) -> Result<(), CliError> {
    let vault_dir = args.require("vault-dir")?;
    let public_out = args.require("public-out")?;
    let passphrase = crate::envelope::passphrase(args)?;
    let anchor_cfg = AnchorConfig::from_quorum_args(args, vault_dir)?;
    require_anchor_or_waiver(
        anchor_cfg.is_some(),
        args.flag("ephemeral-unanchored"),
        "anchor-dir",
    )?;
    ensure_absent(public_out)?;

    let t = usize::try_from(args.get_u64("threshold")?.unwrap_or(2))
        .map_err(|_| CliError::usage("--threshold out of range"))?;
    let n = usize::try_from(args.get_u64("parties")?.unwrap_or(3))
        .map_err(|_| CliError::usage("--parties out of range"))?;
    let active_leaves = usize::try_from(args.get_u64("leaves")?.unwrap_or(8))
        .map_err(|_| CliError::usage("--leaves out of range"))?;
    if t < 2 || t > n || n >= MAX_HEM_QUORUM_PARTIES {
        return Err(CliError::usage(
            "--threshold must be >= 2 and <= --parties (<= 255 nonzero GF(256) evaluation points)",
        ));
    }
    if active_leaves == 0 || active_leaves > HEM_JORTS_MAX_LEAVES {
        return Err(CliError::usage(format!(
            "--leaves must be between 1 and {HEM_JORTS_MAX_LEAVES}"
        )));
    }
    ensure_no_vault_files(vault_dir)?;

    let ceremony_seed = if let Some(seed_file) = args.get("seed-file") {
        let raw = read_bounded_file(seed_file, MAX_KEY_FILE_BYTES)?;
        if raw.0.len() < 32 {
            return Err(CliError::usage("--seed-file must hold at least 32 bytes"));
        }
        Secret32::new(cshake256_framed_32(
            b"QSAG.CLI.HEM.QUORUM.SEED_FILE.V1",
            &[&raw.0],
        ))
    } else {
        Secret32::new(os_random_32()?)
    };
    let latch_seed = Secret32::new(cshake256_framed_32(
        b"QSAG.CLI.HEM.QUORUM.LATCH_SEED.V1",
        &[&ceremony_seed.0],
    ));

    let quorum = HemDynamicShamirQuorum::stage(ceremony_seed.0, t, n, active_leaves)
        .map_err(map_quorum_err)?;
    create_vault_anchored(
        vault_dir,
        &quorum,
        latch_seed,
        passphrase.as_deref().map(Vec::as_slice),
        anchor_cfg.as_ref(),
        &mut no_crash,
    )?;

    let public = write_public_json(&quorum.public_key(), t, n, 0, active_leaves);
    write_new(public_out, public.to_pretty().as_bytes(), false)?;

    if args.flag("json") {
        print!("{}", public.to_pretty());
    } else {
        println!(
            "enrolled ({t}, {n}) {HEM_SCHEME_NAME} quorum ({active_leaves} leaves) in {vault_dir} -> {public_out}"
        );
    }
    Ok(())
}

pub fn sign(args: &Args) -> Result<(), CliError> {
    let vault_dir = args.require("vault-dir")?;
    let out_path = args.require("out")?;
    let passphrase = crate::envelope::passphrase(args)?;
    let anchor_cfg = AnchorConfig::from_quorum_args(args, vault_dir)?;
    require_anchor_or_waiver(
        anchor_cfg.is_some(),
        args.flag("ephemeral-unanchored"),
        "anchor-dir",
    )?;
    ensure_absent(out_path)?;
    if args.get("in").is_some() && args.get("message").is_some() {
        return Err(CliError::usage("pass either --message or --in, not both"));
    }
    let msg_arg = args
        .get("message")
        .or_else(|| args.get("in"))
        .ok_or_else(|| CliError::usage("missing required option --message (or --in)"))?;
    let message = read_input(msg_arg)?;

    let Signed {
        leaf_epoch,
        sig,
        vault,
    } = sign_tx_anchored(
        vault_dir,
        args.get("signers"),
        args.get("ackers"),
        args.get_u64("epoch")?,
        &message,
        passphrase.as_deref().map(Vec::as_slice),
        anchor_cfg.as_ref(),
        &mut no_crash,
    )?;
    let quorum = &vault.quorum;
    let (t, n) = quorum.threshold_and_size();

    let pk = quorum.public_key();
    let pk_bytes = pk.to_bytes();
    let sig_bytes = sig.to_bytes();
    let agg_pk = ValidatorPublicKey::from_bytes_canonical(&pk_bytes)
        .ok_or_else(|| CliError::verify("quorum public key failed canonical Hem decode"))?;
    let agg_sig =
        ValidatorSignature::from_bytes_canonical(AggSigProfile::JortsPoseidon2, &sig_bytes)
            .map_err(|_| CliError::verify("quorum signature failed canonical Hem decode"))?;
    if !verify_hem_jorts_signature(&pk, &message, &sig)
        || !verify_individual_signature(&agg_pk, &message, &agg_sig)
    {
        return Err(CliError::verify(
            "verify-before-release rejected Hem quorum signature",
        ));
    }

    let sig_json = Json::object(vec![
        ("format", Json::str(SIG_FORMAT)),
        ("scheme", Json::str(HEM_SCHEME_NAME)),
        ("epoch", Json::num(leaf_epoch)),
        ("quorum_epoch", Json::num(quorum.quorum_epoch())),
        ("threshold", Json::num(t)),
        ("parties", Json::num(n)),
        ("validator_public_key", Json::hex(&pk_bytes)),
        ("signature_bytes", Json::num(HEM_JORTS_SIG_BYTES)),
        ("signature", Json::hex(&sig_bytes)),
    ]);
    write_new(out_path, sig_json.to_pretty().as_bytes(), false)?;

    if args.flag("json") {
        let report = Json::object(vec![
            ("scheme", Json::str(HEM_SCHEME_NAME)),
            ("epoch", Json::num(leaf_epoch)),
            ("quorum_epoch", Json::num(quorum.quorum_epoch())),
            ("signature_bytes", Json::num(HEM_JORTS_SIG_BYTES)),
            ("out", Json::str(out_path)),
        ]);
        print!("{}", report.to_pretty());
    } else {
        println!(
            "signed {HEM_SCHEME_NAME} leaf epoch {leaf_epoch} (quorum_epoch {}, {} bytes) -> {out_path}",
            quorum.quorum_epoch(),
            HEM_JORTS_SIG_BYTES
        );
    }
    Ok(())
}

pub fn refresh(raw: &[String]) -> Result<(), CliError> {
    let mut opts = vec!["vault-dir", "passphrase-env", "passphrase-file"];
    opts.extend_from_slice(ANCHOR_NO_VAULT_VALUE_OPTIONS);
    let mut flags = vec!["deterministic", "json", "help"];
    flags.extend_from_slice(ANCHOR_FLAG_OPTIONS);
    let args = Args::parse(raw, &opts, &flags)?;
    if args.flag("help") {
        print!("{HEM_REFRESH_HELP}");
        return Ok(());
    }
    args.no_positionals()?;
    let vault_dir = args.require("vault-dir")?;
    let anchor_cfg = AnchorConfig::from_quorum_args(&args, vault_dir)?;
    require_anchor_or_waiver(
        anchor_cfg.is_some(),
        args.flag("ephemeral-unanchored"),
        "anchor-dir",
    )?;
    let passphrase = crate::envelope::passphrase(&args)?;
    let vault = refresh_tx_anchored(
        vault_dir,
        args.flag("deterministic"),
        passphrase.as_deref().map(Vec::as_slice),
        anchor_cfg.as_ref(),
        &mut no_crash,
    )?;
    let quorum = &vault.quorum;

    let (t, n) = quorum.threshold_and_size();
    if args.flag("json") {
        let report = Json::object(vec![
            ("scheme", Json::str(HEM_SCHEME_NAME)),
            ("threshold", Json::num(t)),
            ("parties", Json::num(n)),
            ("quorum_epoch", Json::num(quorum.quorum_epoch())),
            ("high_water_leaf", Json::num(quorum.high_water_leaf())),
            (
                "validator_public_key",
                Json::hex(&quorum.public_key().to_bytes()),
            ),
        ]);
        print!("{}", report.to_pretty());
    } else {
        println!(
            "refreshed ({t}, {n}) {HEM_SCHEME_NAME} shares in {vault_dir} -> quorum_epoch {}",
            quorum.quorum_epoch()
        );
    }
    Ok(())
}

pub fn reshare(raw: &[String]) -> Result<(), CliError> {
    let mut opts = vec![
        "vault-dir",
        "signers",
        "new-threshold",
        "new-parties",
        "out-vault-dir",
        "out-anchor-dir",
        "public-out",
        "passphrase-env",
        "passphrase-file",
        "new-passphrase-env",
        "new-passphrase-file",
    ];
    opts.extend_from_slice(ANCHOR_NO_VAULT_VALUE_OPTIONS);
    let mut flags = vec![
        "deterministic",
        "out-allow-single-disk-anchor",
        "out-ephemeral-unanchored",
        "json",
        "help",
    ];
    flags.extend_from_slice(ANCHOR_FLAG_OPTIONS);
    let args = Args::parse(raw, &opts, &flags)?;
    if args.flag("help") {
        print!("{HEM_RESHARE_HELP}");
        return Ok(());
    }
    args.no_positionals()?;
    let old_vault_dir = args.require("vault-dir")?;
    let new_vault_dir = args.require("out-vault-dir")?;
    let old_anchor_cfg = AnchorConfig::from_quorum_args(&args, old_vault_dir)?;
    require_anchor_or_waiver(
        old_anchor_cfg.is_some(),
        args.flag("ephemeral-unanchored"),
        "anchor-dir",
    )?;
    let new_anchor_cfg = if args.get("out-anchor-dir").is_some()
        || args.flag("out-allow-single-disk-anchor")
        || args.flag("out-ephemeral-unanchored")
    {
        let cfg = AnchorConfig::for_vault(
            &args,
            new_vault_dir,
            "out-anchor-dir",
            "out-allow-single-disk-anchor",
        )?;
        require_anchor_or_waiver(
            cfg.is_some(),
            args.flag("out-ephemeral-unanchored"),
            "out-anchor-dir",
        )?;
        cfg
    } else {
        old_anchor_cfg.clone().map(|mut cfg| {
            cfg.vault_dir = Some(new_vault_dir.to_owned());
            cfg
        })
    };
    let old_passphrase = crate::envelope::passphrase(&args)?;
    let new_passphrase =
        crate::envelope::passphrase_named(&args, "new-passphrase-env", "new-passphrase-file")?;
    let new_t = usize::try_from(
        args.get_u64("new-threshold")?
            .ok_or_else(|| CliError::usage("missing required option --new-threshold"))?,
    )
    .map_err(|_| CliError::usage("--new-threshold out of range"))?;
    let new_n = usize::try_from(
        args.get_u64("new-parties")?
            .ok_or_else(|| CliError::usage("missing required option --new-parties"))?,
    )
    .map_err(|_| CliError::usage("--new-parties out of range"))?;
    if let Some(pub_out) = args.get("public-out") {
        ensure_absent(pub_out)?;
    }

    let Reshared {
        old_t,
        old_n,
        quorum,
    } = reshare_tx_anchored(
        old_vault_dir,
        new_vault_dir,
        args.get("signers"),
        new_t,
        new_n,
        args.flag("deterministic"),
        old_passphrase.as_deref().map(Vec::as_slice),
        new_passphrase.as_deref().map(Vec::as_slice),
        old_anchor_cfg.as_ref(),
        new_anchor_cfg.as_ref(),
        &mut no_crash,
    )?;
    let pk = quorum.public_key();

    if let Some(pub_out) = args.get("public-out") {
        let public = write_public_json(
            &pk,
            new_t,
            new_n,
            quorum.quorum_epoch(),
            quorum.public_directory().active_leaves,
        );
        write_new(pub_out, public.to_pretty().as_bytes(), false)?;
    }

    if args.flag("json") {
        let report = Json::object(vec![
            ("scheme", Json::str(HEM_SCHEME_NAME)),
            ("old_threshold", Json::num(old_t)),
            ("old_parties", Json::num(old_n)),
            ("new_threshold", Json::num(new_t)),
            ("new_parties", Json::num(new_n)),
            ("quorum_epoch", Json::num(quorum.quorum_epoch())),
            ("high_water_leaf", Json::num(quorum.high_water_leaf())),
            ("validator_public_key", Json::hex(&pk.to_bytes())),
            ("out_vault_dir", Json::str(new_vault_dir)),
        ]);
        print!("{}", report.to_pretty());
    } else {
        println!(
            "reshared ({old_t}, {old_n}) -> ({new_t}, {new_n}) {HEM_SCHEME_NAME} (quorum_epoch {}, pubkey preserved) -> {new_vault_dir}",
            quorum.quorum_epoch()
        );
    }
    Ok(())
}

pub fn verify(
    pub_json: &Json,
    message: &[u8],
    sig_path: &str,
    json_flag: bool,
) -> Result<(), CliError> {
    let pk_bytes: [u8; HEM_JORTS_PK_BYTES] = from_hex_exact(
        pub_json.field_str("validator_public_key")?,
        "validator_public_key",
    )?;
    let pk = HemJortsPublicKey::from_bytes_canonical(&pk_bytes)
        .ok_or_else(|| CliError::input("non-canonical Hem quorum public key"))?;

    let sig_raw = read_bounded_file(sig_path, MAX_SIG_PROOF_BYTES)?;
    let sig_str = std::str::from_utf8(&sig_raw.0)
        .map_err(|_| CliError::input(format!("{sig_path} is not UTF-8 text")))?;
    let sig_json = Json::parse(sig_str)?;
    if sig_json.field_str("format")? != SIG_FORMAT
        || sig_json.field_str("scheme")? != HEM_SCHEME_NAME
    {
        return Err(CliError::input("unexpected Hem quorum signature format"));
    }
    let sig_bytes = sig_json.field_hex("signature")?;
    let sig = HemJortsSignature::from_bytes_canonical(&sig_bytes)
        .ok_or_else(|| CliError::verify("non-canonical Hem quorum signature"))?;
    if u64::from(sig.stateful_leaf_idx) != sig_json.field_u64("epoch")? {
        return Err(CliError::verify("quorum signature epoch header mismatch"));
    }
    if !verify_hem_jorts_signature(&pk, message, &sig) {
        return Err(CliError::verify("quorum signature verification failed"));
    }

    if json_flag {
        let report = Json::object(vec![
            ("valid", Json::Bool(true)),
            ("scheme", Json::str(HEM_SCHEME_NAME)),
            ("epoch", Json::num(sig.stateful_leaf_idx)),
        ]);
        print!("{}", report.to_pretty());
    } else {
        println!("VALID ({HEM_SCHEME_NAME}, epoch {})", sig.stateful_leaf_idx);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    //! Crash boundaries, old-format vaults and file substitution. A "crash" is a transaction
    //! stopped at one of its [`Step`]s: every write before the step is on disk and nothing
    //! after it happened. (What a real power loss does to writes that were not yet synced is
    //! the file system's contract with `fsync` and `rename`, which these tests cannot reach.)

    use super::*;
    use crate::codec::to_hex;

    struct Scratch(String);

    impl Scratch {
        fn new(name: &str) -> Self {
            let dir = std::env::temp_dir()
                .join(format!("qsag-hem-vault-{name}-{}", std::process::id()))
                .to_str()
                .unwrap()
                .to_owned();
            let _ = std::fs::remove_dir_all(&dir);
            private_dir(&dir, true).unwrap();
            Self(dir)
        }
        fn path(&self, name: &str) -> String {
            join(&self.0, name)
        }
    }

    impl Drop for Scratch {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn interrupted_anchored_reshares_use_fresh_identities_and_remove_targets() {
        let scratch = Scratch::new("anchored-reshare-retry");
        let old = scratch.path("old");
        let target = scratch.path("target");
        let anchor_dir = scratch.path("anchor");
        private_dir(&anchor_dir, true).unwrap();
        let cfg = AnchorConfig::dir_only(&anchor_dir, Some(target.clone()), true);
        let pk = new_vault(&old, 2);
        // Reproduce the old failure: provisioning left an external record while
        // the destination lock inode survived and no reshare intent was recorded.
        private_dir(&target, true).unwrap();
        let leftover_lock = lock_new_vault(&target).unwrap();
        let leftover_id = hem_anchor_key_id(&pk.to_bytes(), lock_identity(&leftover_lock).unwrap());
        drop(
            FsExternalMountAnchor::provision_fresh(
                &cfg,
                &[&meta_path(&target)],
                &[&target],
                HEM_ANCHOR_DOMAIN,
                leftover_id,
                [0x42; 32],
            )
            .unwrap(),
        );
        drop(leftover_lock);
        let mut previous_id = Some(leftover_id);
        // Interrupt twice on the same target after provisioning. Both attempts must
        // provision distinct identities, and recovery must remove only their targets.
        for _ in 0..2 {
            let mut stop = |step| {
                if step == Step::TargetPrepared {
                    Err(CliError::state("simulated interruption"))
                } else {
                    Ok(())
                }
            };
            let stopped = reshare_tx_anchored(
                &old,
                &target,
                None,
                2,
                3,
                false,
                None,
                None,
                None,
                Some(&cfg),
                &mut stop,
            );
            assert!(matches!(stopped, Err(err) if err.message == "simulated interruption"));
            let meta = Meta::read(&old).unwrap();
            let key_id = meta.pending.as_ref().unwrap().anchor_key_id.unwrap();
            assert_ne!(Some(key_id), previous_id);
            previous_id = Some(key_id);
            // Model the VMGenID artifact without depending on host hypervisor support.
            let digest = cshake256_framed_32(
                b"QSAG.CLI.ANCHOR.SLOT.V1",
                &[HEM_ANCHOR_DOMAIN.as_bytes(), &key_id],
            );
            let stem = format!("hem_quorum-{}", to_hex(&digest));
            let artifact = join(&target, &format!(".qsag-{stem}.target"));
            let ext_anchor_lock = join(&anchor_dir, &format!("{stem}.anchor.lock"));
            let ext_mirror_dir = join(&anchor_dir, &format!("{stem}.mirror"));
            assert!(exists(&ext_anchor_lock).unwrap());
            assert!(exists(&ext_mirror_dir).unwrap());
            std::fs::write(&artifact, b"uncommitted target").unwrap();
            drop(open_vault(&old, None, &mut no_crash).unwrap());
            assert!(!exists(&artifact).unwrap());
            assert!(!exists(&ext_anchor_lock).unwrap());
            assert!(!exists(&ext_mirror_dir).unwrap());
            assert!(!exists(&meta_path(&target)).unwrap());
        }
        // Legacy pre-existing unrecorded external anchor remains untouched, while
        // the successor commits cleanly under its own fresh identity.
        let leftover_digest = cshake256_framed_32(
            b"QSAG.CLI.ANCHOR.SLOT.V1",
            &[HEM_ANCHOR_DOMAIN.as_bytes(), &leftover_id],
        );
        assert!(
            exists(&join(
                &anchor_dir,
                &format!("hem_quorum-{}.anchor.lock", to_hex(&leftover_digest)),
            ))
            .unwrap()
        );
        reshare_tx_anchored(
            &old,
            &target,
            None,
            2,
            3,
            false,
            None,
            None,
            None,
            Some(&cfg),
            &mut no_crash,
        )
        .unwrap();
        drop(open_vault_anchored(&target, None, Some(&cfg), &mut no_crash).unwrap());
    }

    #[test]
    fn gf256_party_limit_rejects_256_before_keygen_or_reshare() {
        let scratch = Scratch::new("party-limit");
        // An occupied vault stops the accepted boundary before expensive key generation.
        std::fs::write(meta_path(&scratch.0), b"occupied").unwrap();
        for n in [255usize, 256, 257] {
            let raw = vec![
                "--vault-dir".into(),
                scratch.0.clone(),
                "--public-out".into(),
                scratch.path("public"),
                "--parties".into(),
                n.to_string(),
                "--threshold".into(),
                "2".into(),
                "--ephemeral-unanchored".into(),
            ];
            let args = Args::parse(
                &raw,
                &["vault-dir", "public-out", "parties", "threshold"],
                &["ephemeral-unanchored"],
            )
            .unwrap();
            let keygen_error = keygen(&args).unwrap_err();
            let reshare_error = match reshare_tx(
                &scratch.path("missing"),
                &scratch.0,
                None,
                2,
                n,
                true,
                None,
                None,
                &mut no_crash,
            ) {
                Err(e) => e,
                Ok(_) => panic!("occupied vault must reject"),
            };
            for error in [keygen_error, reshare_error] {
                if n == 255 {
                    assert!(error.message.contains("already exists"), "{error}");
                } else {
                    assert!(
                        error
                            .message
                            .contains("<= 255 nonzero GF(256) evaluation points"),
                        "{error}"
                    );
                }
            }
            assert_eq!(std::fs::read(meta_path(&scratch.0)).unwrap(), b"occupied");
            assert!(!std::path::Path::new(&scratch.path("public")).exists());
        }
    }

    /// Stops a transaction at its `at`-th boundary (counting from zero).
    struct Crash {
        at: usize,
        seen: Vec<Step>,
    }

    impl Crash {
        fn at(at: usize) -> Self {
            Self {
                at,
                seen: Vec::new(),
            }
        }
        fn hook(&mut self) -> impl FnMut(Step) -> Result<(), CliError> + '_ {
            move |step| {
                self.seen.push(step);
                if self.seen.len() > self.at {
                    Err(CliError::state("simulated crash"))
                } else {
                    Ok(())
                }
            }
        }
        fn boundary(&self) -> Step {
            *self.seen.last().unwrap()
        }
    }

    fn stage(leaves: usize) -> HemDynamicShamirQuorum {
        HemDynamicShamirQuorum::stage([0x5a; 32], 2, 3, leaves).unwrap()
    }

    fn new_vault(dir: &str, leaves: usize) -> HemJortsPublicKey {
        let quorum = stage(leaves);
        create_vault(dir, &quorum, Secret32::new([0x33; 32]), None, &mut no_crash).unwrap();
        quorum.public_key()
    }

    fn files(dir: &str) -> Vec<String> {
        let mut names = vault_file_names(dir).unwrap();
        names.sort();
        names
    }

    fn snapshot(dir: &str) -> Vec<(String, Vec<u8>)> {
        files(dir)
            .into_iter()
            .map(|name| {
                let bytes = std::fs::read(join(dir, &name)).unwrap();
                (name, bytes)
            })
            .collect()
    }

    /// Exactly the files of a settled v2 vault at its committed generation.
    fn settled_files(dir: &str, parties: usize) -> Vec<String> {
        let generation = Meta::read(dir).unwrap().generation;
        let mut names: Vec<String> = (0..parties)
            .map(|p| format!("custodian-{p}.g{generation}.share"))
            .collect();
        names.extend(
            [
                "directory.bin",
                "quorum-meta.json",
                "quorum-meta.json.vault.lock",
            ]
            .map(str::to_owned),
        );
        names.sort();
        names
    }

    fn sign_ok(dir: &str, pk: &HemJortsPublicKey, message: &[u8]) -> u64 {
        let signed = sign_tx(dir, None, None, None, message, None, &mut no_crash).unwrap();
        assert!(verify_hem_jorts_signature(pk, message, &signed.sig));
        signed.leaf_epoch
    }

    /// A vault exactly as the previous format's writer left it: no lock, no generations.
    fn write_legacy(
        dir: &str,
        quorum: &HemDynamicShamirQuorum,
        shares: &[Vec<u8>],
        meta_hw: usize,
    ) {
        let (t, n) = quorum.threshold_and_size();
        let dir_bytes = quorum.public_directory().to_bytes();
        let meta = Json::object(vec![
            ("format", Json::str(HEM_META_FORMAT_V1)),
            ("scheme", Json::str(HEM_SCHEME_NAME)),
            ("threshold", Json::num(t)),
            ("parties", Json::num(n)),
            ("quorum_epoch", Json::num(quorum.quorum_epoch())),
            ("high_water_leaf", Json::num(meta_hw)),
            (
                "active_leaves",
                Json::num(quorum.public_directory().active_leaves),
            ),
            ("invalidated", Json::Bool(false)),
            (
                "validator_public_key",
                Json::hex(&quorum.public_key().to_bytes()),
            ),
            ("directory_digest", Json::hex(&directory_digest(&dir_bytes))),
            ("latch_seed", Json::hex(&[0x44; 32])),
        ]);
        private_dir(dir, true).unwrap();
        write_new(&directory_path(dir), &dir_bytes, false).unwrap();
        for (p, bytes) in shares.iter().enumerate() {
            write_new(&legacy_share_path(dir, p), bytes, true).unwrap();
        }
        write_new(&meta_path(dir), meta.to_pretty().as_bytes(), true).unwrap();
    }

    fn share_bytes(quorum: &HemDynamicShamirQuorum) -> Vec<Vec<u8>> {
        quorum
            .custodian_shares()
            .iter()
            .map(|s| s.to_vault_bytes().unwrap())
            .collect()
    }

    #[test]
    fn sign_stopped_at_any_boundary_leaves_a_vault_that_opens_and_never_reuses_a_leaf() {
        let scratch = Scratch::new("sign");
        let vault = scratch.path("vault");
        let pk = new_vault(&vault, 6);
        let mut high_water = 0usize;
        let mut boundaries = Vec::new();

        for at in 0.. {
            let mut crash = Crash::at(at);
            let message = format!("message {at}");
            let outcome = sign_tx(
                &vault,
                None,
                None,
                None,
                message.as_bytes(),
                None,
                &mut crash.hook(),
            );
            match outcome {
                Ok(signed) => {
                    // The burn is committed and swept before the leaf is used.
                    assert_eq!(
                        crash.seen,
                        [
                            Step::ShareStaged,
                            Step::ShareStaged,
                            Step::ShareStaged,
                            Step::MetaCommitted,
                            Step::StaleRemoved,
                            Step::LeafBurned,
                        ]
                    );
                    assert_eq!(usize::try_from(signed.leaf_epoch).unwrap(), high_water);
                    assert!(verify_hem_jorts_signature(
                        &pk,
                        message.as_bytes(),
                        &signed.sig
                    ));
                    high_water += 1;
                    break;
                }
                Err(_) => {
                    // No signature left the transaction. The leaf is spent exactly when
                    // the meta naming the generation without it was committed.
                    boundaries.push(crash.boundary());
                    let committed = crash.seen.contains(&Step::MetaCommitted);
                    assert_eq!(
                        Meta::read(&vault).unwrap().high_water_leaf,
                        high_water + usize::from(committed)
                    );
                    let opened = open_vault(&vault, None, &mut no_crash).unwrap();
                    high_water += usize::from(committed);
                    assert_eq!(opened.quorum.high_water_leaf(), high_water);
                    drop(opened);
                    assert_eq!(files(&vault), settled_files(&vault, 3));
                }
            }
        }
        assert_eq!(
            boundaries,
            [
                Step::ShareStaged,
                Step::ShareStaged,
                Step::ShareStaged,
                Step::MetaCommitted,
                Step::StaleRemoved,
                Step::LeafBurned,
            ]
        );
        // Three attempts stopped after the commit and one succeeded: four leaves are gone.
        assert_eq!(high_water, 4);
        assert_eq!(sign_ok(&vault, &pk, b"after"), 4);
        assert_eq!(files(&vault), settled_files(&vault, 3));
    }

    #[test]
    fn refresh_stopped_at_any_boundary_is_either_the_old_or_the_new_sharing() {
        let scratch = Scratch::new("refresh");
        let vault = scratch.path("vault");
        let pk = new_vault(&vault, 2);
        let mut epoch = 0u64;

        for at in 0.. {
            let mut crash = Crash::at(at);
            let done = refresh_tx(&vault, false, None, &mut crash.hook()).is_ok();
            epoch += u64::from(crash.seen.contains(&Step::MetaCommitted));
            let opened = open_vault(&vault, None, &mut no_crash).unwrap();
            assert_eq!(opened.quorum.quorum_epoch(), epoch);
            assert_eq!(opened.quorum.public_key(), pk);
            drop(opened);
            assert_eq!(files(&vault), settled_files(&vault, 3));
            if done {
                break;
            }
        }
        assert!(epoch >= 3);
        assert_eq!(sign_ok(&vault, &pk, b"after refreshes"), 0);
    }

    #[test]
    fn reshare_stopped_at_any_boundary_leaves_exactly_one_live_vault() {
        let scratch = Scratch::new("reshare");
        let mut old = scratch.path("v0");
        let pk = new_vault(&old, 2);
        let mut epoch = 0u64;
        let mut round = 0usize;
        let mut boundaries = Vec::new();

        for at in 0.. {
            let new = scratch.path(&format!("v{}", round + 1));
            let mut crash = Crash::at(at);
            let done =
                reshare_tx(&old, &new, None, 2, 3, false, None, None, &mut crash.hook()).is_ok();
            if !done {
                boundaries.push(crash.boundary());
            }
            match open_vault(&old, None, &mut no_crash) {
                Ok(opened) => {
                    // The old vault is live: the reshare was undone and nothing of the
                    // new vault remains.
                    assert!(!done);
                    assert_eq!(opened.quorum.quorum_epoch(), epoch);
                    assert!(opened.meta.pending.is_none());
                    drop(opened);
                    assert_eq!(files(&old), settled_files(&old, 3));
                    assert!(
                        !exists(&new).unwrap()
                            || files(&new)
                                .iter()
                                .all(|name| name == "quorum-meta.json.vault.lock")
                    );
                }
                Err(err) => {
                    // The old vault is retired: the new one is live, and only it.
                    assert!(err.message.contains("ShareInvalidated"), "{}", err.message);
                    assert_eq!(
                        files(&old),
                        [
                            "directory.bin",
                            "quorum-meta.json",
                            "quorum-meta.json.vault.lock"
                        ]
                    );
                    epoch += 1;
                    let opened = open_vault(&new, None, &mut no_crash).unwrap();
                    assert_eq!(opened.quorum.quorum_epoch(), epoch);
                    assert_eq!(opened.quorum.public_key(), pk);
                    drop(opened);
                    assert_eq!(files(&new), settled_files(&new, 3));
                    old = new;
                    round += 1;
                }
            }
            if done {
                break;
            }
        }
        assert_eq!(
            boundaries,
            [
                Step::IntentRecorded,
                Step::TargetPrepared,
                Step::ShareStaged,
                Step::ShareStaged,
                Step::ShareStaged,
                Step::MetaCommitted,
                Step::StaleRemoved,
                Step::MetaCommitted,
                Step::StaleRemoved,
            ]
        );
        assert_eq!(sign_ok(&old, &pk, b"after reshares"), 0);
    }

    /// Run a reshare of `old` into `new` and stop it at the first `boundary`.
    fn reshare_stopped_at(old: &str, new: &str, boundary: Step) {
        for at in 0.. {
            let mut crash = Crash::at(at);
            assert!(
                reshare_tx(old, new, None, 2, 3, false, None, None, &mut crash.hook()).is_err()
            );
            if crash.boundary() == boundary {
                return;
            }
            // Stopped earlier: opening the old vault undoes the attempt.
            drop(open_vault(old, None, &mut no_crash).unwrap());
        }
    }

    #[test]
    fn old_vault_does_not_sign_while_its_reshare_is_unsettled() {
        let scratch = Scratch::new("reshare-unsettled");
        let (old, new, moved) = (
            scratch.path("old"),
            scratch.path("new"),
            scratch.path("moved"),
        );
        let pk = new_vault(&old, 3);

        // Stopped with staged new shares on disk and no new meta.
        reshare_stopped_at(&old, &new, Step::ShareStaged);
        assert!(Meta::read(&old).unwrap().pending.is_some());
        assert!(files(&new).iter().any(|n| parse_share_name(n).is_some()));

        // If the new vault's directory cannot be found the outcome is unknown: refuse.
        std::fs::rename(&new, &moved).unwrap();
        let before = snapshot(&old);
        let err = sign_tx(&old, None, None, None, b"m", None, &mut no_crash)
            .err()
            .unwrap();
        assert!(
            err.message.contains("HemReshareInterrupted"),
            "{}",
            err.message
        );
        assert_eq!(snapshot(&old), before);
        std::fs::rename(&moved, &new).unwrap();

        // Found again and never committed: undone, even if the undo itself is interrupted.
        let mut crash = Crash::at(0);
        assert!(open_vault(&old, None, &mut crash.hook()).is_err());
        assert_eq!(crash.boundary(), Step::IntentCleared);
        assert!(files(&new).is_empty());
        assert_eq!(sign_ok(&old, &pk, b"old is live"), 0);

        // Stopped right after the new vault committed: the new vault is live at once, and
        // the old one retires itself instead of signing, however far the new one has moved.
        reshare_stopped_at(&old, &new, Step::MetaCommitted);
        assert_eq!(sign_ok(&new, &pk, b"new is live"), 1);
        drop(refresh_tx(&new, false, None, &mut no_crash).unwrap());
        let err = sign_tx(&old, None, None, None, b"m", None, &mut no_crash)
            .err()
            .unwrap();
        assert!(err.message.contains("ShareInvalidated"), "{}", err.message);
        assert!(Meta::read(&old).unwrap().invalidated);
        assert!(!files(&old).iter().any(|n| parse_share_name(n).is_some()));
        assert_eq!(sign_ok(&new, &pk, b"new still live"), 2);
    }

    #[test]
    fn old_format_vault_is_converted_in_place_and_conversion_survives_a_crash() {
        let scratch = Scratch::new("legacy");
        let quorum = stage(3);
        let pk = quorum.public_key();
        let shares = share_bytes(&quorum);

        // Stop the conversion at each boundary, then open normally.
        for at in 0.. {
            let vault = scratch.path(&format!("crash-{at}"));
            write_legacy(&vault, &quorum, &shares, 0);
            let mut crash = Crash::at(at);
            let converted = open_vault(&vault, None, &mut crash.hook()).is_ok();
            let opened = open_vault(&vault, None, &mut no_crash).unwrap();
            assert_eq!(opened.quorum.high_water_leaf(), 0);
            assert_eq!(opened.quorum.quorum_epoch(), 0);
            assert_eq!(opened.meta.generation, 1);
            drop(opened);
            assert_eq!(files(&vault), settled_files(&vault, 3));
            assert_eq!(sign_ok(&vault, &pk, b"converted"), 0);
            if converted {
                assert!(at >= 5);
                break;
            }
        }

        // A vault that already has a lock file (written between the two formats).
        let locked = scratch.path("locked");
        write_legacy(&locked, &quorum, &shares, 0);
        drop(Vault::acquire(&meta_path(&locked), true).unwrap());
        assert_eq!(sign_ok(&locked, &pk, b"locked"), 0);
        assert_eq!(files(&locked), settled_files(&locked, 3));
    }

    #[test]
    fn old_format_vault_torn_by_its_writer_is_recovered_only_when_that_is_safe() {
        let scratch = Scratch::new("legacy-torn");
        let mut quorum = stage(3);
        let pk = quorum.public_key();
        let before = share_bytes(&quorum);

        // The old writer was interrupted while recording a signature at leaf 0: two shares
        // are past the leaf, one share and the meta are not. Recovery burns forward.
        quorum.sign_quorum(&[0, 1], &[0, 1, 2], b"lost").unwrap();
        let after_sign = share_bytes(&quorum);
        let torn_sign = scratch.path("torn-sign");
        let mixed = [
            after_sign[0].clone(),
            after_sign[1].clone(),
            before[2].clone(),
        ];
        write_legacy(&torn_sign, &stage(3), &mixed, 0);
        let opened = open_vault(&torn_sign, None, &mut no_crash).unwrap();
        assert_eq!(opened.quorum.high_water_leaf(), 1);
        drop(opened);
        assert_eq!(sign_ok(&torn_sign, &pk, b"next"), 1);

        // Interrupted during a refresh: shares of two sharings. Refused, files untouched.
        let mut refreshed = stage(3);
        let mut rngs = fresh_party_rngs(3).unwrap();
        refreshed.proactive_refresh([0x61; 32], &mut rngs).unwrap();
        let after_refresh = share_bytes(&refreshed);
        let torn_refresh = scratch.path("torn-refresh");
        let mixed = [
            after_refresh[0].clone(),
            before[1].clone(),
            before[2].clone(),
        ];
        write_legacy(&torn_refresh, &stage(3), &mixed, 0);
        let on_disk = snapshot(&torn_refresh);
        assert!(open_vault(&torn_refresh, None, &mut no_crash).is_err());
        let mut now = snapshot(&torn_refresh);
        now.retain(|(name, _)| name != "quorum-meta.json.vault.lock");
        assert_eq!(now, on_disk);

        // A retired old-format vault stays retired and gets no lock file.
        let retired_dir = scratch.path("retired");
        write_legacy(&retired_dir, &stage(3), &before, 0);
        let meta = std::fs::read_to_string(meta_path(&retired_dir)).unwrap();
        let meta = meta.replace("\"invalidated\": false", "\"invalidated\": true");
        replace_secret(&meta_path(&retired_dir), meta.as_bytes()).unwrap();
        let on_disk = snapshot(&retired_dir);
        let err = open_vault(&retired_dir, None, &mut no_crash).err().unwrap();
        assert!(err.message.contains("ShareInvalidated"), "{}", err.message);
        assert_eq!(snapshot(&retired_dir), on_disk);
    }

    #[test]
    fn substituted_lock_meta_share_or_copied_vault_is_refused_without_changing_anything() {
        let scratch = Scratch::new("substitution");
        let vault = scratch.path("vault");
        let pk = new_vault(&vault, 2);
        assert_eq!(sign_ok(&vault, &pk, b"first"), 0);
        let good = snapshot(&vault);
        let restore = |name: &str| {
            let bytes = &good.iter().find(|(n, _)| n == name).unwrap().1;
            replace_secret(&join(&vault, name), bytes).unwrap();
        };
        let refused = |why: &str| {
            let err = open_vault(&vault, None, &mut no_crash).err().unwrap();
            assert!(err.message.contains(why), "{}", err.message);
        };
        let share = settled_files(&vault, 3)[0].clone();

        // A damaged share: caught by the digest in the meta before any leaf is touched.
        let mut bytes = std::fs::read(join(&vault, &share)).unwrap();
        bytes[60] ^= 1;
        replace_secret(&join(&vault, &share), &bytes).unwrap();
        refused("HemQuorumShareDigestMismatch");
        restore(&share);

        // An edited meta.
        let meta = std::fs::read_to_string(meta_path(&vault)).unwrap();
        let edited = meta.replace("\"high_water_leaf\": 1", "\"high_water_leaf\": 0");
        assert_ne!(edited, meta);
        replace_secret(&meta_path(&vault), edited.as_bytes()).unwrap();
        refused("HemQuorumMetaDigestMismatch");

        // The meta of an old-format vault put over a current one: the generation files
        // must survive, so that putting the right meta back recovers the vault.
        let downgraded = meta
            .replace(HEM_META_FORMAT, HEM_META_FORMAT_V1)
            .replace("\"high_water_leaf\": 1", "\"high_water_leaf\": 0");
        replace_secret(&meta_path(&vault), downgraded.as_bytes()).unwrap();
        assert!(open_vault(&vault, None, &mut no_crash).is_err());
        restore("quorum-meta.json");
        assert_eq!(snapshot(&vault), good);
        drop(open_vault(&vault, None, &mut no_crash).unwrap());

        // The whole vault copied elsewhere: its lock is a different file, so the copy is
        // refused. Two copies signing would use the same leaves for different messages.
        let copy = scratch.path("copy");
        private_dir(&copy, true).unwrap();
        for (name, bytes) in &good {
            write_new(&join(&copy, name), bytes, true).unwrap();
        }
        assert!(open_vault(&copy, None, &mut no_crash).is_err());
        assert_eq!(snapshot(&copy), good);

        // The lock replaced by another file, then removed.
        let lock = lock_path(&vault);
        std::fs::write(format!("{lock}.new"), [0u8; 32]).unwrap();
        std::fs::rename(format!("{lock}.new"), &lock).unwrap();
        assert!(open_vault(&vault, None, &mut no_crash).is_err());
        std::fs::remove_file(&lock).unwrap();
        assert!(open_vault(&vault, None, &mut no_crash).is_err());
        let mut now = snapshot(&vault);
        now.retain(|(name, _)| name != "quorum-meta.json.vault.lock");
        let mut expected = good.clone();
        expected.retain(|(name, _)| name != "quorum-meta.json.vault.lock");
        assert_eq!(now, expected);
    }

    #[test]
    fn passphrase_sealed_vault_roundtrips_sign_refresh_reshare_and_rejects_wrong_passphrase() {
        let scratch = Scratch::new("sealed-envelope");
        let v1 = scratch.path("v1");
        let v2 = scratch.path("v2");
        let v3 = scratch.path("v3");
        let pass_a = b"correct-horse-battery-staple-hem-a";
        let pass_b = b"rotated-custody-passphrase-hem-b";

        let quorum = stage(6);
        let raw_latch = [0x7a; 32];
        let raw_share0 = quorum.custodian_shares()[0].to_vault_bytes().unwrap();
        let pk = quorum.public_key();
        create_vault(
            &v1,
            &quorum,
            Secret32::new(raw_latch),
            Some(pass_a),
            &mut no_crash,
        )
        .unwrap();

        // Verify on-disk encryption: neither plaintext latch_seed nor plaintext share magic appears.
        let meta_text = std::fs::read_to_string(meta_path(&v1)).unwrap();
        assert!(meta_text.contains(HEM_ENVELOPE_FORMAT));
        assert!(!meta_text.contains(&crate::codec::to_hex(&raw_latch)));
        let disk_share0 = std::fs::read(share_path(&v1, 0, 1)).unwrap();
        assert_eq!(&disk_share0[..24], HEM_SHARE_SEAL_MAGIC);
        assert!(
            !disk_share0
                .windows(raw_share0.len().min(32))
                .any(|w| w == &raw_share0[..raw_share0.len().min(32)])
        );

        // Missing or wrong passphrase fails closed without advancing generation or burning leaves.
        let before = snapshot(&v1);
        let err_missing = sign_tx(&v1, None, None, None, b"m0", None, &mut no_crash)
            .err()
            .unwrap();
        assert_eq!(err_missing.code, 1);
        assert!(err_missing.message.contains("requires --passphrase-env"));
        let err_wrong = sign_tx(&v1, None, None, None, b"m0", Some(b"wrong"), &mut no_crash)
            .err()
            .unwrap();
        assert_eq!(err_wrong.code, 1);
        assert!(err_wrong.message.contains("wrong passphrase"));
        assert_eq!(snapshot(&v1), before);

        // Sign, refresh, reshare (inheriting pass_a), and reshare (rotating to pass_b).
        let s0 = sign_tx(&v1, None, None, None, b"m0", Some(pass_a), &mut no_crash).unwrap();
        assert_eq!(s0.leaf_epoch, 0);
        assert!(verify_hem_jorts_signature(&pk, b"m0", &s0.sig));
        drop(s0);

        drop(refresh_tx(&v1, false, Some(pass_a), &mut no_crash).unwrap());
        let s1 = sign_tx(&v1, None, None, None, b"m1", Some(pass_a), &mut no_crash).unwrap();
        assert_eq!(s1.leaf_epoch, 1);
        assert!(verify_hem_jorts_signature(&pk, b"m1", &s1.sig));
        drop(s1);

        // Reshare without --new-passphrase-* preserves sealing under pass_a (never strips encryption).
        reshare_tx(
            &v1,
            &v2,
            None,
            2,
            4,
            false,
            Some(pass_a),
            None,
            &mut no_crash,
        )
        .unwrap();
        assert!(sign_tx(&v2, None, None, None, b"m2", None, &mut no_crash).is_err());
        let s2 = sign_tx(&v2, None, None, None, b"m2", Some(pass_a), &mut no_crash).unwrap();
        assert_eq!(s2.leaf_epoch, 2);
        assert!(verify_hem_jorts_signature(&pk, b"m2", &s2.sig));
        drop(s2);

        // Reshare with explicit new passphrase rotates encryption to pass_b; even if interrupted
        // right after new meta commits, opening old vault with pass_a settles cleanly.
        for at in 0.. {
            let mut crash = Crash::at(at);
            let res = reshare_tx(
                &v2,
                &v3,
                None,
                3,
                5,
                false,
                Some(pass_a),
                Some(pass_b),
                &mut crash.hook(),
            );
            assert!(res.is_err());
            if crash.boundary() == Step::MetaCommitted {
                break;
            }
            drop(open_vault(&v2, Some(pass_a), &mut no_crash).unwrap());
        }
        let err_retired = open_vault(&v2, Some(pass_a), &mut no_crash).err().unwrap();
        assert!(err_retired.message.contains("ShareInvalidated"));
        assert!(sign_tx(&v3, None, None, None, b"m3", Some(pass_a), &mut no_crash).is_err());
        let s3 = sign_tx(&v3, None, None, None, b"m3", Some(pass_b), &mut no_crash).unwrap();
        assert_eq!(s3.leaf_epoch, 3);
        assert!(verify_hem_jorts_signature(&pk, b"m3", &s3.sig));

        // Supplying a passphrase to an unsealed vault also fails closed.
        let unsealed = scratch.path("unsealed");
        let _ = new_vault(&unsealed, 2);
        let err_unsolicited = open_vault(&unsealed, Some(pass_a), &mut no_crash)
            .err()
            .unwrap();
        assert_eq!(err_unsolicited.code, 1);
        assert!(err_unsolicited.message.contains("unencrypted"));
    }
}
