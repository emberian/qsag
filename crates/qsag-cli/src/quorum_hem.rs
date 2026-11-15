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

use qsag_accel::keccak::cshake256_framed_32;
use qsag_agg::{
    AggSigProfile, ValidatorPublicKey, ValidatorSignature, verify_individual_signature,
};
use qsag_core::preprocessing::PartyPrivateRng;
use qsag_quorum::hem_quorum::{
    HEM_JORTS_MAX_LEAVES, HEM_JORTS_PK_BYTES, HEM_JORTS_SIG_BYTES, HemDynamicShamirQuorum,
    HemJortsPublicKey, HemJortsSignature, HemQuorumError, HemQuorumPublicDirectory,
    HemShamirCustodianShare, verify_hem_jorts_signature,
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

pub const HEM_REFRESH_HELP: &str = "\
qsag quorum refresh --vault-dir <dir> [--deterministic] [--json]

Execute proactive share refresh (Π_refresh) across all (t, n) custodians in --vault-dir,
advancing quorum_epoch and overwriting custodian share files in place while preserving
the exact 65-byte validator public key and monotone leaf high-water mark.
--deterministic fixes only the session ID; private ceremony entropy remains fresh.
";

pub const HEM_RESHARE_HELP: &str = "\
qsag quorum reshare --vault-dir <old_dir> [--signers <i,j,..>] --new-threshold <t'> --new-parties <n'> --out-vault-dir <new_dir> [--public-out <path>] [--deterministic] [--json]

Execute dynamic (t, n) -> (t', n') quorum-switching (Π_reshare) using >= t custodians from
--vault-dir, writing the new (t', n') custodian vault into --out-vault-dir WITHOUT changing
the 65-byte validator public key, and permanently invalidating/wiping the retired vault.
--deterministic fixes only the session ID; private ceremony entropy remains fresh.
";

// The local vault CLI hosts all custodians, but each protocol stream still needs
// independent private entropy; deterministic session identifiers are only context.
fn fresh_party_rngs(n: usize) -> Result<Vec<PartyPrivateRng>, CliError> {
    (0..n)
        .map(|_| {
            let seed = Secret32(os_random_32()?);
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
// Meta
// ---------------------------------------------------------------------------------------

struct PendingReshare {
    /// Absolute path of the vault being created.
    target: String,
    /// The quorum epoch the new vault starts at.
    quorum_epoch: u64,
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
        }
    }

    /// Digest over every field, so an edited or damaged meta is refused.
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
            self.latch_seed.0.to_vec(),
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
            }
        }
        let refs: Vec<&[u8]> = frames.iter().map(Vec::as_slice).collect();
        let digest = cshake256_framed_32(b"QSAG.CLI.HEM.META_DIGEST.V2", &refs);
        for frame in &mut frames {
            qsag_accel::ct::ct_zeroize_bytes(frame);
        }
        digest
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
            ("latch_seed", Json::hex(&self.latch_seed.0)),
            ("generation", Json::num(self.generation)),
            (
                "share_digests",
                Json::Array(self.share_digests.iter().map(|d| Json::hex(d)).collect()),
            ),
            ("vault_device", Json::num(self.lock_id.0)),
            ("vault_inode", Json::num(self.lock_id.1)),
        ];
        if let Some(pending) = &self.pending {
            members.push(("pending_reshare_target", Json::str(pending.target.clone())));
            members.push(("pending_reshare_epoch", Json::num(pending.quorum_epoch)));
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
            }),
        };
        let meta = Self {
            t: json.field_u64("threshold")? as usize,
            n: json.field_u64("parties")? as usize,
            quorum_epoch: json.field_u64("quorum_epoch")?,
            high_water_leaf: json.field_u64("high_water_leaf")? as usize,
            active_leaves: json.field_u64("active_leaves")? as usize,
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
            latch_seed: Secret32(from_hex_exact(json.field_str("latch_seed")?, "latch_seed")?),
            generation: json.field_u64("generation")?,
            share_digests,
            lock_id: (
                json.field_u64("vault_device")?,
                json.field_u64("vault_inode")?,
            ),
            pending,
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

    fn read(vault_dir: &str) -> Result<Self, CliError> {
        Self::from_json(&Json::parse(&read_text(&meta_path(vault_dir))?)?)
    }

    /// Put this meta on disk. Replacing an existing meta is one atomic rename.
    fn write(&self, vault_dir: &str, fresh: bool) -> Result<(), CliError> {
        let bytes = ZeroizingBuf(self.to_json().to_pretty().into_bytes());
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
            let chunk = left.min(zeros.len() as u64) as usize;
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
    fresh: bool,
    hook: Hook<'_>,
) -> Result<(), CliError> {
    let generation = meta
        .generation
        .checked_add(1)
        .ok_or_else(|| CliError::state("HemQuorumGenerationExhausted"))?;
    let mut digests = Vec::with_capacity(quorum.custodian_shares().len());
    for (party, share) in quorum.custodian_shares().iter().enumerate() {
        let raw = ZeroizingBuf(share.to_vault_bytes().map_err(map_quorum_err)?);
        write_new(&share_path(vault_dir, party, generation), &raw.0, true)?;
        digests.push(share_digest(party, &raw.0));
        hook(Step::ShareStaged)?;
    }
    let (t, n) = quorum.threshold_and_size();
    meta.t = t;
    meta.n = n;
    meta.quorum_epoch = quorum.quorum_epoch();
    meta.high_water_leaf = quorum.high_water_leaf();
    meta.generation = generation;
    meta.share_digests = digests;
    meta.write(vault_dir, fresh)?;
    hook(Step::MetaCommitted)?;
    remove_stale(vault_dir, Keep::Generation(generation))?;
    hook(Step::StaleRemoved)
}

/// Retire the vault: the meta says so first, then every share file is wiped.
fn retire(vault_dir: &str, meta: &mut Meta, hook: Hook<'_>) -> Result<(), CliError> {
    meta.invalidated = true;
    meta.pending = None;
    meta.latch_seed = Secret32([0u8; 32]);
    meta.share_digests = Vec::new();
    meta.generation = meta
        .generation
        .checked_add(1)
        .ok_or_else(|| CliError::state("HemQuorumGenerationExhausted"))?;
    meta.write(vault_dir, false)?;
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
///
/// An old writer interrupted while recording a signature left some shares one leaf ahead of
/// the others and of the meta. Those vaults are brought forward to the highest mark any file
/// recorded, which only burns leaves. One interrupted during a refresh has shares of two
/// different sharings; that cannot be repaired and is refused as before.
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
    let t = json.field_u64("threshold")? as usize;
    let n = json.field_u64("parties")? as usize;
    let expected_qe = json.field_u64("quorum_epoch")?;
    let meta_hw = json.field_u64("high_water_leaf")? as usize;
    let expected_pk: [u8; HEM_JORTS_PK_BYTES] = from_hex_exact(
        json.field_str("validator_public_key")?,
        "validator_public_key",
    )?;
    let expected_dir_digest: [u8; 32] =
        from_hex_exact(json.field_str("directory_digest")?, "directory_digest")?;
    let latch_seed = Secret32(from_hex_exact(json.field_str("latch_seed")?, "latch_seed")?);

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

fn load_generation(vault_dir: &str, meta: &Meta) -> Result<HemDynamicShamirQuorum, CliError> {
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
        shares.push(HemShamirCustodianShare::from_vault_bytes(&raw.0).map_err(map_quorum_err)?);
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
///
/// `Ok` means the new vault was never committed: what was staged for it is gone and the old
/// vault is live again. If the new vault was committed, the old one is retired here and
/// the retired error is returned. If the new vault's directory cannot be found the outcome
/// is unknown and the old vault stays closed.
fn settle_interrupted_reshare(
    vault_dir: &str,
    meta: &mut Meta,
    hook: Hook<'_>,
) -> Result<(), CliError> {
    let Some(pending) = &meta.pending else {
        return Ok(());
    };
    let target = pending.target.clone();
    let unknown = |why: &str| {
        CliError::state(format!(
            "HemReshareInterrupted: a reshare of this vault into {target} did not finish and {why}; \
             this vault stays closed so that it and its successor can never both sign"
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
        retire(vault_dir, meta, hook)?;
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
fn open_vault(vault_dir: &str, hook: Hook<'_>) -> Result<OpenVault, CliError> {
    let (lock, lock_created) = lock_existing_vault(vault_dir)?;
    let lock_id = lock_identity(&lock)?;
    let json = Json::parse(&read_text(&meta_path(vault_dir))?)?;

    if json.field_str("format")? == HEM_META_FORMAT_V1 {
        let (quorum, latch_seed) = load_legacy(vault_dir, &json)?;
        // The old-format shares loaded, so any generation file is an unfinished conversion.
        remove_stale(vault_dir, Keep::Legacy)?;
        let mut meta = Meta::new(&quorum, latch_seed, lock_id);
        commit(vault_dir, &quorum, &mut meta, false, hook)?;
        return Ok(OpenVault {
            _lock: lock,
            quorum,
            meta,
        });
    }

    let mut meta = Meta::from_json(&json)?;
    if lock_created || meta.lock_id != lock_id {
        return Err(crate::vault::corrupt());
    }
    if meta.invalidated {
        // Finish wiping if retirement was interrupted after its commit.
        remove_stale(vault_dir, Keep::Nothing)?;
        return Err(retired());
    }
    settle_interrupted_reshare(vault_dir, &mut meta, &mut *hook)?;
    let quorum = load_generation(vault_dir, &meta)?;
    remove_stale(vault_dir, Keep::Generation(meta.generation))?;
    Ok(OpenVault {
        _lock: lock,
        quorum,
        meta,
    })
}

// ---------------------------------------------------------------------------------------
// Transactions
// ---------------------------------------------------------------------------------------

/// Create a vault for a freshly staged quorum. The directory must hold no vault file.
fn create_vault(
    vault_dir: &str,
    quorum: &HemDynamicShamirQuorum,
    latch_seed: Secret32,
    hook: Hook<'_>,
) -> Result<(), CliError> {
    ensure_no_vault_files(vault_dir)?;
    private_dir(vault_dir, true)?;
    let lock = lock_new_vault(vault_dir)?;
    ensure_no_vault_files(vault_dir)?;
    let mut meta = Meta::new(quorum, latch_seed, lock_identity(&lock)?);
    write_new(
        &directory_path(vault_dir),
        &quorum.public_directory().to_bytes(),
        false,
    )?;
    commit(vault_dir, quorum, &mut meta, true, hook)
}

struct Signed {
    leaf_epoch: u64,
    sig: HemJortsSignature,
    vault: OpenVault,
}

/// Sign `message`: reserve the leaf, commit the vault without it, then use it.
fn sign_tx(
    vault_dir: &str,
    signers: Option<&str>,
    ackers: Option<&str>,
    requested_epoch: Option<u64>,
    message: &[u8],
    hook: Hook<'_>,
) -> Result<Signed, CliError> {
    let mut vault = open_vault(vault_dir, &mut *hook)?;
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

    // Nothing is written if the reservation is refused.
    let reserved = vault
        .quorum
        .reserve_leaf(&signers, &ackers, message)
        .map_err(map_quorum_err)?;
    // The leaf is out of the quorum; record that before its shares are combined.
    commit(vault_dir, &vault.quorum, &mut vault.meta, false, &mut *hook)?;
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

fn refresh_tx(vault_dir: &str, deterministic: bool, hook: Hook<'_>) -> Result<OpenVault, CliError> {
    let mut vault = open_vault(vault_dir, &mut *hook)?;
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
    vault.meta.latch_seed = Secret32(os_random_32()?);
    commit(vault_dir, &vault.quorum, &mut vault.meta, false, hook)?;
    Ok(vault)
}

struct Reshared {
    old_t: usize,
    old_n: usize,
    quorum: HemDynamicShamirQuorum,
}

/// Move custody from the vault in `old_vault_dir` to a new vault in `new_vault_dir`.
///
/// Order on disk: the old vault records the reshare; the new vault is written and
/// committed; the old vault is retired. Stopped before the new vault's commit, the old
/// vault undoes the reshare when next opened; stopped after it, the old vault retires
/// itself when next opened. See [`settle_interrupted_reshare`].
fn reshare_tx(
    old_vault_dir: &str,
    new_vault_dir: &str,
    signers: Option<&str>,
    new_t: usize,
    new_n: usize,
    deterministic: bool,
    hook: Hook<'_>,
) -> Result<Reshared, CliError> {
    if new_t < 2 || new_t > new_n || new_n > 64 {
        return Err(CliError::usage(
            "--new-threshold must be >= 2 and <= --new-parties (<= 64)",
        ));
    }
    ensure_no_vault_files(new_vault_dir)?;
    let old = open_vault(old_vault_dir, &mut *hook)?;
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
    let new_latch_seed = Secret32(os_random_32()?);

    // The ceremony runs in memory. The old vault's files are untouched by it.
    let mut old_party_rngs = fresh_party_rngs(old_n)?;
    let mut new_party_rngs = fresh_party_rngs(new_n)?;
    let OpenVault {
        _lock: old_lock,
        mut quorum,
        meta: mut old_meta,
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
    hook(Step::TargetPrepared)?;

    old_meta.pending = Some(PendingReshare {
        target: target.clone(),
        quorum_epoch: quorum.quorum_epoch(),
    });
    old_meta.write(old_vault_dir, false)?;
    hook(Step::IntentRecorded)?;

    let mut new_meta = Meta::new(&quorum, new_latch_seed, lock_identity(&new_lock)?);
    write_new(
        &directory_path(&target),
        &quorum.public_directory().to_bytes(),
        false,
    )?;
    commit(&target, &quorum, &mut new_meta, true, &mut *hook)?;

    retire(old_vault_dir, &mut old_meta, hook)?;
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
    ensure_absent(public_out)?;

    let t = args.get_u64("threshold")?.unwrap_or(2) as usize;
    let n = args.get_u64("parties")?.unwrap_or(3) as usize;
    let active_leaves = args.get_u64("leaves")?.unwrap_or(8) as usize;
    if t < 2 || t > n || n > 64 {
        return Err(CliError::usage(
            "--threshold must be >= 2 and <= --parties (<= 64)",
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
        Secret32(cshake256_framed_32(
            b"QSAG.CLI.HEM.QUORUM.SEED_FILE.V1",
            &[&raw.0],
        ))
    } else {
        Secret32(os_random_32()?)
    };
    let latch_seed = Secret32(cshake256_framed_32(
        b"QSAG.CLI.HEM.QUORUM.LATCH_SEED.V1",
        &[&ceremony_seed.0],
    ));

    let quorum = HemDynamicShamirQuorum::stage(ceremony_seed.0, t, n, active_leaves)
        .map_err(map_quorum_err)?;
    create_vault(vault_dir, &quorum, latch_seed, &mut no_crash)?;

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
    ensure_absent(out_path)?;
    if args.get("in").is_some() && args.get("message").is_some() {
        return Err(CliError::usage("pass either --message or --in, not both"));
    }
    let msg_arg = args
        .get("message")
        .or_else(|| args.get("in"))
        .ok_or_else(|| CliError::usage("missing required option --message (or --in)"))?;
    let message = read_input(msg_arg)?;

    // The vault stays locked until the signature file is written.
    let Signed {
        leaf_epoch,
        sig,
        vault,
    } = sign_tx(
        vault_dir,
        args.get("signers"),
        args.get("ackers"),
        args.get_u64("epoch")?,
        &message,
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
    let args = Args::parse(raw, &["vault-dir"], &["deterministic", "json", "help"])?;
    if args.flag("help") {
        print!("{HEM_REFRESH_HELP}");
        return Ok(());
    }
    args.no_positionals()?;
    let vault_dir = args.require("vault-dir")?;
    let vault = refresh_tx(vault_dir, args.flag("deterministic"), &mut no_crash)?;
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
    let args = Args::parse(
        raw,
        &[
            "vault-dir",
            "signers",
            "new-threshold",
            "new-parties",
            "out-vault-dir",
            "public-out",
        ],
        &["deterministic", "json", "help"],
    )?;
    if args.flag("help") {
        print!("{HEM_RESHARE_HELP}");
        return Ok(());
    }
    args.no_positionals()?;
    let old_vault_dir = args.require("vault-dir")?;
    let new_vault_dir = args.require("out-vault-dir")?;
    let new_t = args
        .get_u64("new-threshold")?
        .ok_or_else(|| CliError::usage("missing required option --new-threshold"))?
        as usize;
    let new_n = args
        .get_u64("new-parties")?
        .ok_or_else(|| CliError::usage("missing required option --new-parties"))?
        as usize;
    if let Some(pub_out) = args.get("public-out") {
        ensure_absent(pub_out)?;
    }

    let Reshared {
        old_t,
        old_n,
        quorum,
    } = reshare_tx(
        old_vault_dir,
        new_vault_dir,
        args.get("signers"),
        new_t,
        new_n,
        args.flag("deterministic"),
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
        create_vault(dir, &quorum, Secret32([0x33; 32]), &mut no_crash).unwrap();
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
        let signed = sign_tx(dir, None, None, None, message, &mut no_crash).unwrap();
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
                    assert_eq!(signed.leaf_epoch as usize, high_water);
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
                    let opened = open_vault(&vault, &mut no_crash).unwrap();
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
            let done = refresh_tx(&vault, false, &mut crash.hook()).is_ok();
            epoch += u64::from(crash.seen.contains(&Step::MetaCommitted));
            let opened = open_vault(&vault, &mut no_crash).unwrap();
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
            let done = reshare_tx(&old, &new, None, 2, 3, false, &mut crash.hook()).is_ok();
            if !done {
                boundaries.push(crash.boundary());
            }
            match open_vault(&old, &mut no_crash) {
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
                    let opened = open_vault(&new, &mut no_crash).unwrap();
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
                Step::TargetPrepared,
                Step::IntentRecorded,
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
            assert!(reshare_tx(old, new, None, 2, 3, false, &mut crash.hook()).is_err());
            if crash.boundary() == boundary {
                return;
            }
            // Stopped earlier: opening the old vault undoes the attempt.
            drop(open_vault(old, &mut no_crash).unwrap());
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
        let err = sign_tx(&old, None, None, None, b"m", &mut no_crash)
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
        assert!(open_vault(&old, &mut crash.hook()).is_err());
        assert_eq!(crash.boundary(), Step::IntentCleared);
        assert!(files(&new).is_empty());
        assert_eq!(sign_ok(&old, &pk, b"old is live"), 0);

        // Stopped right after the new vault committed: the new vault is live at once, and
        // the old one retires itself instead of signing, however far the new one has moved.
        reshare_stopped_at(&old, &new, Step::MetaCommitted);
        assert_eq!(sign_ok(&new, &pk, b"new is live"), 1);
        drop(refresh_tx(&new, false, &mut no_crash).unwrap());
        let err = sign_tx(&old, None, None, None, b"m", &mut no_crash)
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
            let converted = open_vault(&vault, &mut crash.hook()).is_ok();
            let opened = open_vault(&vault, &mut no_crash).unwrap();
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
        let opened = open_vault(&torn_sign, &mut no_crash).unwrap();
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
        assert!(open_vault(&torn_refresh, &mut no_crash).is_err());
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
        let err = open_vault(&retired_dir, &mut no_crash).err().unwrap();
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
            let err = open_vault(&vault, &mut no_crash).err().unwrap();
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
        assert!(open_vault(&vault, &mut no_crash).is_err());
        restore("quorum-meta.json");
        assert_eq!(snapshot(&vault), good);
        drop(open_vault(&vault, &mut no_crash).unwrap());

        // The whole vault copied elsewhere: its lock is a different file, so the copy is
        // refused. Two copies signing would use the same leaves for different messages.
        let copy = scratch.path("copy");
        private_dir(&copy, true).unwrap();
        for (name, bytes) in &good {
            write_new(&join(&copy, name), bytes, true).unwrap();
        }
        assert!(open_vault(&copy, &mut no_crash).is_err());
        assert_eq!(snapshot(&copy), good);

        // The lock replaced by another file, then removed.
        let lock = lock_path(&vault);
        std::fs::write(format!("{lock}.new"), [0u8; 32]).unwrap();
        std::fs::rename(format!("{lock}.new"), &lock).unwrap();
        assert!(open_vault(&vault, &mut no_crash).is_err());
        std::fs::remove_file(&lock).unwrap();
        assert!(open_vault(&vault, &mut no_crash).is_err());
        let mut now = snapshot(&vault);
        now.retain(|(name, _)| name != "quorum-meta.json.vault.lock");
        let mut expected = good.clone();
        expected.retain(|(name, _)| name != "quorum-meta.json.vault.lock");
        assert_eq!(now, expected);
    }
}
