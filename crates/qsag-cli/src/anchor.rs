//! External monotone anchor backend (`FsExternalMountAnchor`) for CLI custody state.
//!
//! Defends local stateful signing against full vault-directory snapshot rollback when
//! `--anchor-dir` points to an independently mounted filesystem or hardware-backed directory.
//! Each resource slot holds a permanent `0600` `.lock` sidecar (`QSAGLCK1`) whose 24-byte
//! `dev_le64 || ino_le64 || seal8` identity (`lock_identity_seal`) is authenticated inside the
//! `QSAGANC1` checkpoint record MAC, paired with single-use ceremony ticket consumption.

use std::fs::File;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};

use qsag_accel::ct::{ct_eq_bytes, ct_zeroize_bytes};
use qsag_accel::keccak::cshake256_framed_32;
use qsag_core::ceremony_journal::CeremonyContext;
use qsag_core::{ExternalMonotoneAnchor, LedgerCheckpoint};

use crate::cli::{Args, CliError, Secret32, ZeroizingBuf, os_random_32};
use crate::codec::{Json, from_hex_exact, to_hex};
use crate::persist::{self, file_identity, parent_dir, private_dir};

const LOCK_MAGIC: &[u8; 8] = b"QSAGLCK1";
const ANCHOR_MAGIC: &[u8; 8] = b"QSAGANC1";
const ANCHOR_PAYLOAD_LEN: usize = 8 + 32 + 32 + 8 + 32 + 1 + 8 + 32;
const ANCHOR_RECORD_LEN: usize = ANCHOR_PAYLOAD_LEN + 32;

/// Parsed `--anchor-dir`, `--vault-dir`, and `--allow-single-disk-anchor` CLI options.
#[derive(Clone, Debug)]
pub struct AnchorConfig {
    pub anchor_dir: String,
    pub vault_dir: Option<String>,
    pub allow_single_disk: bool,
}

impl AnchorConfig {
    pub fn from_args(args: &Args) -> Result<Option<Self>, CliError> {
        let anchor_dir = args.get("anchor-dir").map(str::to_owned);
        let vault_dir = args.get("vault-dir").map(str::to_owned);
        let allow_single_disk = args.flag("allow-single-disk-anchor");
        if anchor_dir.is_none() && (vault_dir.is_some() || allow_single_disk) {
            return Err(CliError::usage(
                "--vault-dir and --allow-single-disk-anchor require --anchor-dir",
            ));
        }
        Ok(anchor_dir.map(|anchor_dir| Self {
            anchor_dir,
            vault_dir,
            allow_single_disk,
        }))
    }

    pub fn from_quorum_args(args: &Args, vault_dir: &str) -> Result<Option<Self>, CliError> {
        Self::for_vault(args, vault_dir, "anchor-dir", "allow-single-disk-anchor")
    }

    /// The anchor of a vault directory the command already names, read from the option
    /// `dir_option` and the flag `single_disk_flag`.
    pub fn for_vault(
        args: &Args,
        vault_dir: &str,
        dir_option: &str,
        single_disk_flag: &str,
    ) -> Result<Option<Self>, CliError> {
        let anchor_dir = args.get(dir_option).map(str::to_owned);
        let allow_single_disk = args.flag(single_disk_flag);
        if anchor_dir.is_none() && allow_single_disk {
            return Err(CliError::usage(format!(
                "--{single_disk_flag} requires --{dir_option}"
            )));
        }
        Ok(anchor_dir.map(|anchor_dir| Self {
            anchor_dir,
            vault_dir: Some(vault_dir.to_owned()),
            allow_single_disk,
        }))
    }

    /// Validate `--anchor-dir` permissions, non-symlink status, and mount/inode separation
    /// from all local custody directories (`custody_files` parents and `explicit_dirs`).
    pub fn validate_isolation(
        &self,
        custody_files: &[&str],
        explicit_dirs: &[&str],
        create_anchor_dir: bool,
    ) -> Result<(), CliError> {
        let anchor = Location {
            id: private_dir(&self.anchor_dir, create_anchor_dir)?,
            canon: canonical(&self.anchor_dir)?,
        };
        if Location::of(&anchor.canon)?.id != anchor.id {
            return Err(CliError::state(
                "--anchor-dir changed identity during validation",
            ));
        }

        let explicit_vault = match &self.vault_dir {
            Some(vd) => {
                let vault = Location {
                    id: private_dir(vd, create_anchor_dir)?,
                    canon: canonical(vd)?,
                };
                self.refuse_overlap(&anchor, &vault, "--vault-dir")?;
                self.refuse_shared_device(&anchor, &vault, "--vault-dir")?;
                Some(vault)
            }
            None => None,
        };

        for file_path in custody_files {
            let parent = Location::of(parent_dir(Path::new(file_path)))?;
            // Without --vault-dir the custody directory is the key file's own directory. An
            // anchor inside it (or around it) travels with any snapshot of that directory.
            self.refuse_overlap(&anchor, &parent, "the directory holding custody state")?;
            if let Some(vault) = &explicit_vault
                && !parent.canon.starts_with(&vault.canon)
            {
                return Err(CliError::state(format!(
                    "custody file {file_path} does not reside inside --vault-dir"
                )));
            }
            self.refuse_shared_device(&anchor, &parent, "custody state")?;
        }

        for dir_path in explicit_dirs {
            let dir = Location::of(Path::new(dir_path))?;
            self.refuse_overlap(&anchor, &dir, "custody directory")?;
            self.refuse_shared_device(&anchor, &dir, "custody directory")?;
        }
        Ok(())
    }

    /// The anchor may be neither the directory `other`, nor inside it, nor around it. No
    /// option waives this: such an anchor travels with every snapshot of `other`.
    fn refuse_overlap(
        &self,
        anchor: &Location,
        other: &Location,
        what: &str,
    ) -> Result<(), CliError> {
        if other.id == anchor.id {
            return Err(CliError::state(format!(
                "--anchor-dir resolves to the same directory/inode as {what}"
            )));
        }
        if anchor.canon.starts_with(&other.canon) || other.canon.starts_with(&anchor.canon) {
            return Err(CliError::state(format!(
                "--anchor-dir must not overlap or nest with {what}"
            )));
        }
        Ok(())
    }

    fn refuse_shared_device(
        &self,
        anchor: &Location,
        other: &Location,
        what: &str,
    ) -> Result<(), CliError> {
        if other.id.0 == anchor.id.0 && !self.allow_single_disk {
            return Err(CliError::state(format!(
                "--anchor-dir resides on the same filesystem device as {what}; mount an independent device or pass --allow-single-disk-anchor"
            )));
        }
        Ok(())
    }
}

/// A directory as the isolation rules see it: `(device, inode)` and resolved path.
struct Location {
    id: (u64, u64),
    canon: PathBuf,
}

fn canonical(path: impl AsRef<Path>) -> Result<PathBuf, CliError> {
    let path = path.as_ref();
    std::fs::canonicalize(path)
        .map_err(|e| CliError::io(format_args!("resolving {}", path.display()), e))
}

impl Location {
    /// A custody directory wherever it lives: unlike the anchor and `--vault-dir`, it is
    /// not required to be private, and a symlink to it is resolved.
    fn of(path: &Path) -> Result<Self, CliError> {
        let meta = std::fs::metadata(path)
            .map_err(|e| CliError::io(format_args!("inspecting {}", path.display()), e))?;
        Ok(Self {
            id: file_identity(&meta),
            canon: canonical(path)?,
        })
    }
}

/// Parse optional `--policy-id-hex` and `--spend-amount` CLI ceremony context options.
pub fn parse_ceremony_context(
    args: &Args,
    mpc_nonce_epoch: u64,
) -> Result<CeremonyContext, CliError> {
    let policy_id = match args.get("policy-id-hex") {
        Some(hex) => from_hex_exact(hex, "policy-id-hex")?,
        None => [0u8; 32],
    };
    let spend_amount = args.get_u64("spend-amount")?.unwrap_or(0);
    Ok(CeremonyContext {
        policy_id,
        spend_amount,
        mpc_nonce_epoch,
    })
}

/// How the `"anchor_required"` field of a custody file disagrees with the options given.
pub enum AnchorRequirementError {
    /// The field is present but is not a boolean.
    Malformed,
    /// The file was enrolled with an external anchor and none was supplied.
    AnchorMissing,
    /// An anchor was supplied for a file enrolled without one.
    NotEnrolled,
}

/// Whether `file` was enrolled with an external anchor, checked against whether one was
/// `supplied`. Enrollment and the anchor options must agree in both directions.
pub fn anchor_requirement(file: &Json, supplied: bool) -> Result<bool, AnchorRequirementError> {
    let required = match file.get("anchor_required") {
        None => false,
        Some(Json::Bool(flag)) => *flag,
        Some(_) => return Err(AnchorRequirementError::Malformed),
    };
    match (required, supplied) {
        (true, false) => Err(AnchorRequirementError::AnchorMissing),
        (false, true) => Err(AnchorRequirementError::NotEnrolled),
        (flag, _) => Ok(flag),
    }
}

/// Enforce that `"anchor_required"` in `secret_json` matches whether `--anchor-dir` was supplied.
pub fn enforce_anchor_requirement(
    secret: &Json,
    anchor_cfg: Option<&AnchorConfig>,
) -> Result<bool, CliError> {
    anchor_requirement(secret, anchor_cfg.is_some()).map_err(|e| match e {
        AnchorRequirementError::Malformed => crate::vault::corrupt(),
        AnchorRequirementError::AnchorMissing => {
            CliError::state("key requires --anchor-dir external monotone anchor")
        }
        AnchorRequirementError::NotEnrolled => {
            CliError::state("key was not enrolled with --anchor-dir")
        }
    })
}

/// Compute a deterministic 256-bit monotonic floor checkpoint tag for integer watermarks.
pub fn floor_checkpoint(domain: &[u8], key_id: &[u8; 32], floor_value: u64) -> LedgerCheckpoint {
    let generation = floor_value.saturating_add(1);
    let tag = cshake256_framed_32(
        b"QSAG.CLI.ANCHOR.FLOOR.V1",
        &[
            domain,
            key_id,
            &generation.to_be_bytes(),
            &floor_value.to_be_bytes(),
        ],
    );
    LedgerCheckpoint { generation, tag }
}

fn invalid_anchor(msg: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, msg)
}

fn side_path(path: &Path, suffix: &str) -> PathBuf {
    let mut os = path.as_os_str().to_os_string();
    os.push(suffix);
    PathBuf::from(os)
}

/// Safe-Rust exclusive lock sidecar binding `dev_le64 || ino_le64 || seal8`.
struct AnchorLockedRecord {
    path: PathBuf,
    lock_file: File,
    seal: [u8; 8],
    inode: [u8; 16],
    poisoned: AtomicBool,
}

impl AnchorLockedRecord {
    #[cfg(not(unix))]
    fn acquire(_path: PathBuf, _must_create: bool) -> io::Result<Self> {
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "external anchor locking requires Unix",
        ))
    }

    #[cfg(unix)]
    fn acquire(path: PathBuf, must_create: bool) -> io::Result<Self> {
        use std::os::unix::fs::FileExt;

        if must_create {
            match std::fs::symlink_metadata(&path) {
                Ok(_) => {
                    return Err(io::Error::new(
                        io::ErrorKind::AlreadyExists,
                        "external anchor record already exists",
                    ));
                }
                Err(e) if e.kind() == io::ErrorKind::NotFound => {}
                Err(e) => return Err(e),
            }
        } else if persist::regular_metadata(&path)?.is_none() {
            return Err(io::Error::new(
                io::ErrorKind::NotFound,
                "provisioned external anchor record is missing",
            ));
        }

        let lock_path = side_path(&path, ".lock");
        let (mut lock_file, held_meta) =
            persist::acquire_lock(&lock_path, must_create).map_err(|e| match e.kind() {
                io::ErrorKind::NotFound if !must_create => {
                    invalid_anchor("external anchor lock sidecar missing")
                }
                io::ErrorKind::WouldBlock => {
                    io::Error::new(io::ErrorKind::WouldBlock, "external anchor lock unavailable")
                }
                _ => e,
            })?;
        let inode = persist::identity_bytes(&held_meta);
        let mut header = [0u8; 32];
        if must_create {
            let rand = os_random_32().map_err(|e| io::Error::other(e.message))?;
            header[..8].copy_from_slice(LOCK_MAGIC);
            header[8..16].copy_from_slice(&rand[..8]);
            header[16..32].copy_from_slice(&inode);
            lock_file.write_all(&header)?;
            lock_file.sync_all()?;
            persist::sync_parent_dir(&lock_path)?;
        } else {
            if held_meta.len() != 32 {
                return Err(invalid_anchor("external anchor lock header truncated"));
            }
            lock_file.read_exact_at(&mut header, 0)?;
            if &header[..8] != LOCK_MAGIC || header[16..32] != inode {
                return Err(invalid_anchor("external anchor lock identity mismatch"));
            }
        }

        if must_create && persist::regular_metadata(&path)?.is_some() {
            return Err(io::Error::new(
                io::ErrorKind::AlreadyExists,
                "external anchor record appeared concurrently",
            ));
        }

        let mut seal = [0u8; 8];
        seal.copy_from_slice(&header[8..16]);
        let this = Self {
            path,
            lock_file,
            seal,
            inode,
            poisoned: AtomicBool::new(false),
        };
        this.check_lock()?;
        persist::remove_interrupted_replacements(&this.path);
        Ok(this)
    }

    /// Canonical 24-byte `dev_le64 || ino_le64 || nonce8` lock identity seal.
    fn lock_identity_seal(&self) -> [u8; 24] {
        let mut out = [0u8; 24];
        out[..16].copy_from_slice(&self.inode);
        out[16..24].copy_from_slice(&self.seal);
        out
    }

    fn poison<T>(&self, err: io::Error) -> io::Result<T> {
        self.poisoned.store(true, Ordering::SeqCst);
        Err(err)
    }

    fn check_not_poisoned(&self) -> io::Result<()> {
        if self.poisoned.load(Ordering::SeqCst) {
            return Err(io::Error::other("external anchor handle poisoned"));
        }
        Ok(())
    }

    #[cfg(unix)]
    fn check_lock(&self) -> io::Result<()> {
        use std::os::unix::fs::FileExt;
        let lock_path = side_path(&self.path, ".lock");
        let meta = persist::verify_held(&self.lock_file, &lock_path, true)?;
        if meta.len() != 32 || persist::identity_bytes(&meta) != self.inode {
            return Err(invalid_anchor("external anchor lock sidecar replaced"));
        }
        let mut header = [0u8; 32];
        self.lock_file.read_exact_at(&mut header, 0)?;
        if &header[..8] != LOCK_MAGIC || header[8..16] != self.seal || header[16..32] != self.inode
        {
            return Err(invalid_anchor("external anchor lock header altered"));
        }
        Ok(())
    }

    #[cfg(not(unix))]
    fn check_lock(&self) -> io::Result<()> {
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "external anchor requires Unix",
        ))
    }

    #[cfg(unix)]
    fn read_optional(&self) -> io::Result<Option<ZeroizingBuf>> {
        use std::io::Read;
        self.check_not_poisoned()?;
        if let Err(e) = self.check_lock() {
            return self.poison(e);
        }
        if persist::regular_metadata(&self.path)?.is_none() {
            return Ok(None);
        }
        let result = (|| -> io::Result<ZeroizingBuf> {
            let mut file = persist::no_follow()?.read(true).open(&self.path)?;
            let meta = persist::verify_held(&file, &self.path, true)?;
            if meta.len() != ANCHOR_RECORD_LEN as u64 {
                return Err(invalid_anchor("external anchor record length invalid"));
            }
            let mut buf = ZeroizingBuf(vec![0u8; ANCHOR_RECORD_LEN]);
            file.read_exact(&mut buf.0)?;
            let mut extra = [0u8; 1];
            if file.read(&mut extra)? != 0 {
                return Err(invalid_anchor("external anchor record grew concurrently"));
            }
            self.check_lock()?;
            Ok(buf)
        })();
        match result {
            Ok(buf) => Ok(Some(buf)),
            Err(e) => self.poison(e),
        }
    }

    #[cfg(not(unix))]
    fn read_optional(&self) -> io::Result<Option<ZeroizingBuf>> {
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "external anchor requires Unix",
        ))
    }

    #[cfg(unix)]
    fn replace(&self, contents: &[u8]) -> io::Result<()> {
        self.check_not_poisoned()?;
        if let Err(e) = self.check_lock() {
            return self.poison(e);
        }
        persist::replace(&self.path, contents, || self.check_lock())
            .and_then(|()| self.check_lock())
            .or_else(|e| self.poison(e))
    }

    #[cfg(not(unix))]
    fn replace(&self, _contents: &[u8]) -> io::Result<()> {
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "external anchor requires Unix",
        ))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct AnchorRecordState {
    checkpoint: LedgerCheckpoint,
    consumed: Option<(u64, [u8; 32])>,
}

struct AnchorInner {
    record: AnchorLockedRecord,
    domain_hash: [u8; 32],
    key_id: [u8; 32],
    mac_key: [u8; 32],
    state: Mutex<Option<AnchorRecordState>>,
    /// Set once a record is known to exist: by opening an enrolled slot or by the first
    /// write of a fresh one. From then on a missing record is a rollback, never a genesis.
    written: AtomicBool,
}

impl Drop for AnchorInner {
    fn drop(&mut self) {
        ct_zeroize_bytes(&mut self.mac_key);
    }
}

impl AnchorInner {
    fn compute_mac(&self, payload: &[u8; ANCHOR_PAYLOAD_LEN]) -> [u8; 32] {
        let seal = self.record.lock_identity_seal();
        cshake256_framed_32(
            b"QSAG.CLI.EXTERNAL_ANCHOR.MAC.V1",
            &[&self.mac_key, &seal, payload],
        )
    }

    fn encode(&self, state: &AnchorRecordState) -> [u8; ANCHOR_RECORD_LEN] {
        let mut payload = [0u8; ANCHOR_PAYLOAD_LEN];
        payload[..8].copy_from_slice(ANCHOR_MAGIC);
        payload[8..40].copy_from_slice(&self.domain_hash);
        payload[40..72].copy_from_slice(&self.key_id);
        payload[72..80].copy_from_slice(&state.checkpoint.generation.to_be_bytes());
        payload[80..112].copy_from_slice(&state.checkpoint.tag);
        match state.consumed {
            Some((consumed_gen, ceremony_id)) => {
                payload[112] = 1;
                payload[113..121].copy_from_slice(&consumed_gen.to_be_bytes());
                payload[121..153].copy_from_slice(&ceremony_id);
            }
            None => {
                payload[112] = 0;
            }
        }
        let mac = self.compute_mac(&payload);
        let mut out = [0u8; ANCHOR_RECORD_LEN];
        out[..ANCHOR_PAYLOAD_LEN].copy_from_slice(&payload);
        out[ANCHOR_PAYLOAD_LEN..].copy_from_slice(&mac);
        out
    }

    fn decode(&self, bytes: &[u8]) -> io::Result<AnchorRecordState> {
        if bytes.len() != ANCHOR_RECORD_LEN {
            return Err(invalid_anchor("external anchor record wrong length"));
        }
        let payload: &[u8; ANCHOR_PAYLOAD_LEN] = bytes[..ANCHOR_PAYLOAD_LEN]
            .try_into()
            .map_err(|_| invalid_anchor("external anchor payload slice"))?;
        let stored_mac = &bytes[ANCHOR_PAYLOAD_LEN..];
        let expected_mac = Secret32(self.compute_mac(payload));
        if !ct_eq_bytes(stored_mac, &expected_mac.0) {
            return Err(invalid_anchor("external anchor MAC verification failed"));
        }
        if &payload[..8] != ANCHOR_MAGIC
            || !ct_eq_bytes(&payload[8..40], &self.domain_hash)
            || !ct_eq_bytes(&payload[40..72], &self.key_id)
        {
            return Err(invalid_anchor("external anchor header binding mismatch"));
        }
        let generation = u64::from_be_bytes(payload[72..80].try_into().unwrap());
        let mut tag = [0u8; 32];
        tag.copy_from_slice(&payload[80..112]);
        let consumed_gen = u64::from_be_bytes(payload[113..121].try_into().unwrap());
        let mut ceremony_id = [0u8; 32];
        ceremony_id.copy_from_slice(&payload[121..153]);
        let consumed = match payload[112] {
            0 => {
                if consumed_gen != 0 || ceremony_id != [0u8; 32] {
                    return Err(invalid_anchor("external anchor unconsumed fields non-zero"));
                }
                None
            }
            1 => {
                if consumed_gen > generation {
                    return Err(invalid_anchor(
                        "external anchor consumed generation ahead of checkpoint",
                    ));
                }
                Some((consumed_gen, ceremony_id))
            }
            _ => return Err(invalid_anchor("external anchor invalid consumed flag")),
        };
        Ok(AnchorRecordState {
            checkpoint: LedgerCheckpoint { generation, tag },
            consumed,
        })
    }

    fn read_verified_disk_state(&self) -> io::Result<Option<AnchorRecordState>> {
        match self.record.read_optional()? {
            None if self.written.load(Ordering::SeqCst) => self
                .record
                .poison(invalid_anchor("external anchor record vanished")),
            None => Ok(None),
            Some(bytes) => match self.decode(&bytes) {
                Ok(state) => Ok(Some(state)),
                Err(e) => self.record.poison(e),
            },
        }
    }

    fn write_state(&self, state: &AnchorRecordState) -> io::Result<()> {
        self.record.replace(&self.encode(state))?;
        self.written.store(true, Ordering::SeqCst);
        Ok(())
    }
}

/// Production filesystem-backed [`ExternalMonotoneAnchor`] with `O_NOFOLLOW` `0600` locking,
/// 24-byte `lock_identity_seal` MAC binding, rollback refusal, and single-use ticket fencing.
#[derive(Clone)]
pub struct FsExternalMountAnchor {
    inner: Arc<AnchorInner>,
}

fn sanitize_domain_prefix(domain: &str) -> String {
    let mut prefix: String = domain
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() {
                c.to_ascii_lowercase()
            } else {
                '_'
            }
        })
        .take(24)
        .collect();
    if prefix.is_empty() {
        prefix.push_str("slot");
    }
    prefix
}

fn anchor_record_path(anchor_dir: &str, domain: &str, key_id: &[u8; 32]) -> PathBuf {
    let slot_digest = cshake256_framed_32(b"QSAG.CLI.ANCHOR.SLOT.V1", &[domain.as_bytes(), key_id]);
    let filename = format!(
        "{}-{}.anchor",
        sanitize_domain_prefix(domain),
        to_hex(&slot_digest)
    );
    Path::new(anchor_dir).join(filename)
}

impl FsExternalMountAnchor {
    /// Provision a brand-new external anchor slot inside `--anchor-dir` (`load()` initially `None`).
    pub fn provision_fresh(
        config: &AnchorConfig,
        custody_files: &[&str],
        explicit_dirs: &[&str],
        domain: &str,
        key_id: [u8; 32],
        mac_key: [u8; 32],
    ) -> Result<Self, CliError> {
        config.validate_isolation(custody_files, explicit_dirs, true)?;
        let path = anchor_record_path(&config.anchor_dir, domain, &key_id);
        let record = AnchorLockedRecord::acquire(path, true)
            .map_err(|e| CliError::state(format!("enrolling external anchor ({domain}): {e}")))?;
        let domain_hash = cshake256_framed_32(b"QSAG.CLI.ANCHOR.DOMAIN.V1", &[domain.as_bytes()]);
        Ok(Self {
            inner: Arc::new(AnchorInner {
                record,
                domain_hash,
                key_id,
                mac_key,
                state: Mutex::new(None),
                written: AtomicBool::new(false),
            }),
        })
    }

    /// Open and authenticate an existing external anchor slot inside `--anchor-dir`.
    pub fn open_existing(
        config: &AnchorConfig,
        custody_files: &[&str],
        explicit_dirs: &[&str],
        domain: &str,
        key_id: [u8; 32],
        mac_key: [u8; 32],
    ) -> Result<Self, CliError> {
        config.validate_isolation(custody_files, explicit_dirs, false)?;
        let path = anchor_record_path(&config.anchor_dir, domain, &key_id);
        let record = AnchorLockedRecord::acquire(path, false).map_err(|e| {
            CliError::state(format!(
                "ExternalAnchorUnavailableOrCorrupt ({domain}): {e}"
            ))
        })?;
        let domain_hash = cshake256_framed_32(b"QSAG.CLI.ANCHOR.DOMAIN.V1", &[domain.as_bytes()]);
        let inner = Arc::new(AnchorInner {
            record,
            domain_hash,
            key_id,
            mac_key,
            state: Mutex::new(None),
            written: AtomicBool::new(true),
        });
        let loaded = inner
            .read_verified_disk_state()
            .map_err(|e| {
                CliError::state(format!(
                    "ExternalAnchorUnavailableOrCorrupt ({domain}): {e}"
                ))
            })?
            .ok_or_else(|| {
                CliError::state(format!(
                    "ExternalAnchorUnavailableOrCorrupt ({domain}): missing state"
                ))
            })?;
        *inner
            .state
            .lock()
            .map_err(|_| CliError::state("external anchor mutex poisoned"))? = Some(loaded);
        Ok(Self { inner })
    }

    /// 24-byte `dev_le64 || ino_le64 || seal8` lock identity authenticated by this anchor.
    pub fn lock_identity_seal(&self) -> [u8; 24] {
        self.inner.record.lock_identity_seal()
    }

    /// Verify that this anchor's 24-byte `.lock` identity seal matches the seal pinned in `secret`.
    pub fn verify_expected_seal(&self, secret: &Json, field: &str) -> Result<(), CliError> {
        let expected: [u8; 24] = from_hex_exact(
            secret
                .field_str(field)
                .map_err(|_| CliError::state("MissingExternalAnchorIdentitySeal"))?,
            field,
        )
        .map_err(|_| CliError::state("CorruptExternalAnchorIdentitySeal"))?;
        if !ct_eq_bytes(&self.lock_identity_seal(), &expected) {
            return Err(CliError::state("ExternalAnchorIdentitySealMismatch"));
        }
        Ok(())
    }

    /// Atomically consume the single-use ceremony ticket at `expected.generation`.
    /// Rejects replay if `consumed_generation >= expected.generation` (post-issuance clone fence).
    pub fn consume_ceremony_ticket(
        &self,
        expected: LedgerCheckpoint,
        ceremony_id: &[u8; 32],
    ) -> io::Result<()> {
        let mut guard = self
            .inner
            .state
            .lock()
            .map_err(|_| io::Error::other("external anchor mutex poisoned"))?;
        let disk = self
            .inner
            .read_verified_disk_state()?
            .ok_or_else(|| invalid_anchor("external anchor uninitialized on consume"))?;
        if let Some(mem) = *guard
            && mem != disk
        {
            return self
                .inner
                .record
                .poison(invalid_anchor("external anchor disk diverged from memory"));
        }
        if disk.checkpoint.generation != expected.generation
            || !ct_eq_bytes(&disk.checkpoint.tag, &expected.tag)
        {
            return self.inner.record.poison(invalid_anchor(
                "external anchor checkpoint mismatch on ticket consume",
            ));
        }
        if let Some((consumed_gen, _)) = disk.consumed
            && consumed_gen >= expected.generation
        {
            return self.inner.record.poison(io::Error::new(
                io::ErrorKind::PermissionDenied,
                "CeremonyTicketAlreadyConsumed",
            ));
        }
        let next = AnchorRecordState {
            checkpoint: disk.checkpoint,
            consumed: Some((expected.generation, *ceremony_id)),
        };
        self.inner.write_state(&next)?;
        *guard = Some(next);
        Ok(())
    }

    /// Verify that a monotonic integer floor has not regressed below the externally anchored value.
    pub fn verify_floor_at_least(
        &self,
        domain: &[u8],
        observed_floor: u64,
    ) -> Result<(), CliError> {
        let current = self
            .load()
            .map_err(|e| CliError::state(format!("ExternalAnchorRollbackOrCorrupt: {e}")))?
            .ok_or_else(|| CliError::state("ExternalAnchorMissingFloorState"))?;
        let min_floor = current
            .generation
            .checked_sub(1)
            .ok_or_else(|| CliError::state("ExternalAnchorInvalidFloorGeneration"))?;
        if observed_floor < min_floor {
            return Err(CliError::state("ExternalAnchorDetectedRollback"));
        }
        if observed_floor == min_floor {
            let expected = floor_checkpoint(domain, &self.inner.key_id, min_floor);
            if !ct_eq_bytes(&current.tag, &expected.tag) {
                return Err(CliError::state("ExternalAnchorFloorTagMismatch"));
            }
        }
        Ok(())
    }

    /// Ratchet a monotonic integer floor forward on the external anchor.
    pub fn advance_floor(&self, domain: &[u8], next_floor: u64) -> Result<(), CliError> {
        let ckpt = floor_checkpoint(domain, &self.inner.key_id, next_floor);
        self.advance(ckpt)
            .map_err(|e| CliError::state(format!("ExternalAnchorAdvanceFailed: {e}")))
    }
}

impl ExternalMonotoneAnchor for FsExternalMountAnchor {
    fn load(&self) -> io::Result<Option<LedgerCheckpoint>> {
        let mut guard = self
            .inner
            .state
            .lock()
            .map_err(|_| io::Error::other("external anchor mutex poisoned"))?;
        let disk = self.inner.read_verified_disk_state()?;
        if let (Some(mem), Some(on_disk)) = (*guard, disk)
            && (on_disk.checkpoint.generation < mem.checkpoint.generation
                || (on_disk.checkpoint.generation == mem.checkpoint.generation
                    && !ct_eq_bytes(&on_disk.checkpoint.tag, &mem.checkpoint.tag)))
        {
            return self.inner.record.poison(io::Error::other(
                "external anchor rolled back underneath live handle",
            ));
        }
        *guard = disk;
        Ok(disk.map(|s| s.checkpoint))
    }

    fn advance(&self, checkpoint: LedgerCheckpoint) -> io::Result<()> {
        let mut guard = self
            .inner
            .state
            .lock()
            .map_err(|_| io::Error::other("external anchor mutex poisoned"))?;
        let disk = self.inner.read_verified_disk_state()?;
        if let Some(prev) = disk {
            if checkpoint.generation < prev.checkpoint.generation {
                return self.inner.record.poison(io::Error::other(
                    "external anchor rejects rolled-back generation",
                ));
            }
            if checkpoint.generation == prev.checkpoint.generation {
                if !ct_eq_bytes(&checkpoint.tag, &prev.checkpoint.tag) {
                    return self.inner.record.poison(io::Error::other(
                        "external anchor rejects mismatched tag at equal generation",
                    ));
                }
                *guard = Some(prev);
                return Ok(());
            }
        }
        let next = AnchorRecordState {
            checkpoint,
            consumed: disk.and_then(|d| d.consumed),
        };
        self.inner.write_state(&next)?;
        *guard = Some(next);
        Ok(())
    }
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;
    use std::fs::OpenOptions;

    fn temp_root(label: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "qsag-anchor-{label}-{}",
            to_hex(&os_random_32().unwrap()[..16])
        ));
        private_dir(dir.to_str().unwrap(), true).unwrap();
        dir
    }

    #[test]
    fn rejects_same_inode_nested_dirs_and_unapproved_single_disk() {
        let root = temp_root("isolation");
        let vault = root.join("vault");
        let anchor = root.join("anchor");
        private_dir(vault.to_str().unwrap(), true).unwrap();
        private_dir(anchor.to_str().unwrap(), true).unwrap();
        let sk = vault.join("sk");

        // 1. Same directory/inode is refused EVEN when allow_single_disk is true.
        let same_cfg = AnchorConfig {
            anchor_dir: vault.to_str().unwrap().to_owned(),
            vault_dir: Some(vault.to_str().unwrap().to_owned()),
            allow_single_disk: true,
        };
        assert!(
            same_cfg
                .validate_isolation(&[sk.to_str().unwrap()], &[], true)
                .is_err()
        );

        // 2. Alias via `vault/.` or symlink to `vault` is also refused unconditionally.
        let dot_cfg = AnchorConfig {
            anchor_dir: vault.join(".").to_str().unwrap().to_owned(),
            vault_dir: None,
            allow_single_disk: true,
        };
        assert!(
            dot_cfg
                .validate_isolation(&[sk.to_str().unwrap()], &[], false)
                .is_err()
        );
        let link = root.join("anchor-link");
        std::os::unix::fs::symlink(&anchor, &link).unwrap();
        let link_cfg = AnchorConfig {
            anchor_dir: link.to_str().unwrap().to_owned(),
            vault_dir: Some(vault.to_str().unwrap().to_owned()),
            allow_single_disk: true,
        };
        assert!(
            link_cfg
                .validate_isolation(&[sk.to_str().unwrap()], &[], false)
                .is_err()
        );

        // 3. Nested anchor inside `--vault-dir` is refused even with allow_single_disk.
        let nested = vault.join("nested-anchor");
        let nested_cfg = AnchorConfig {
            anchor_dir: nested.to_str().unwrap().to_owned(),
            vault_dir: Some(vault.to_str().unwrap().to_owned()),
            allow_single_disk: true,
        };
        assert!(
            nested_cfg
                .validate_isolation(&[sk.to_str().unwrap()], &[], true)
                .is_err()
        );

        // 4. Decoy `--vault-dir` while `sk` lives outside it is refused.
        let outside_sk = root.join("outside.sk");
        let decoy_cfg = AnchorConfig {
            anchor_dir: anchor.to_str().unwrap().to_owned(),
            vault_dir: Some(vault.to_str().unwrap().to_owned()),
            allow_single_disk: true,
        };
        assert!(
            decoy_cfg
                .validate_isolation(&[outside_sk.to_str().unwrap()], &[], false)
                .is_err()
        );

        // 5. Same filesystem device without `allow_single_disk` is refused; with it, accepted.
        let strict_cfg = AnchorConfig {
            anchor_dir: anchor.to_str().unwrap().to_owned(),
            vault_dir: Some(vault.to_str().unwrap().to_owned()),
            allow_single_disk: false,
        };
        assert!(
            strict_cfg
                .validate_isolation(&[sk.to_str().unwrap()], &[], false)
                .is_err()
        );
        let single_disk_cfg = AnchorConfig {
            anchor_dir: anchor.to_str().unwrap().to_owned(),
            vault_dir: Some(vault.to_str().unwrap().to_owned()),
            allow_single_disk: true,
        };
        single_disk_cfg
            .validate_isolation(&[sk.to_str().unwrap()], &[], false)
            .unwrap();

        std::fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn monotone_advance_lock_identity_seal_and_single_use_ticket_fence() {
        let root = temp_root("ops");
        let vault = root.join("vault");
        let anchor_dir = root.join("anchor");
        private_dir(vault.to_str().unwrap(), true).unwrap();
        let sk_path = vault.join("sk");
        let cfg = AnchorConfig {
            anchor_dir: anchor_dir.to_str().unwrap().to_owned(),
            vault_dir: Some(vault.to_str().unwrap().to_owned()),
            allow_single_disk: true,
        };
        let key_id = [0x11; 32];
        let mac_key = [0x22; 32];

        let anchor = FsExternalMountAnchor::provision_fresh(
            &cfg,
            &[sk_path.to_str().unwrap()],
            &[],
            "ceremony",
            key_id,
            mac_key,
        )
        .unwrap();
        assert_ne!(anchor.lock_identity_seal(), [0u8; 24]);
        assert_eq!(anchor.load().unwrap(), None);

        let ckpt1 = LedgerCheckpoint {
            generation: 1,
            tag: [0xAA; 32],
        };
        let ckpt2 = LedgerCheckpoint {
            generation: 2,
            tag: [0xBB; 32],
        };
        anchor.advance(ckpt1).unwrap();
        assert_eq!(anchor.load().unwrap(), Some(ckpt1));
        // Idempotent at equal generation + equal tag.
        anchor.advance(ckpt1).unwrap();
        anchor.advance(ckpt2).unwrap();
        assert_eq!(anchor.load().unwrap(), Some(ckpt2));

        // Single-use ceremony ticket consumption succeeds once and refuses replay.
        anchor.consume_ceremony_ticket(ckpt2, &[0x99; 32]).unwrap();
        assert!(anchor.consume_ceremony_ticket(ckpt2, &[0x99; 32]).is_err());

        // Reopening from disk recovers state; advancing to generation 3 allows a fresh ticket.
        drop(anchor);
        let reopened = FsExternalMountAnchor::open_existing(
            &cfg,
            &[sk_path.to_str().unwrap()],
            &[],
            "ceremony",
            key_id,
            mac_key,
        )
        .unwrap();
        assert_eq!(reopened.load().unwrap(), Some(ckpt2));
        // Replay at generation 2 is still refused across process restarts!
        assert!(
            reopened
                .consume_ceremony_ticket(ckpt2, &[0x99; 32])
                .is_err()
        );
        drop(reopened);

        let reopened = FsExternalMountAnchor::open_existing(
            &cfg,
            &[sk_path.to_str().unwrap()],
            &[],
            "ceremony",
            key_id,
            mac_key,
        )
        .unwrap();
        let ckpt3 = LedgerCheckpoint {
            generation: 3,
            tag: [0xCC; 32],
        };
        reopened.advance(ckpt3).unwrap();
        reopened
            .consume_ceremony_ticket(ckpt3, &[0x77; 32])
            .unwrap();

        // Older generation rollback is rejected and poisons the handle.
        assert!(reopened.advance(ckpt2).is_err());
        assert!(reopened.load().is_err());
        drop(reopened);

        // Replacing the `.anchor.lock` sidecar with a copy at a new inode fails `lock_identity_seal`!
        let rec_path = anchor_record_path(cfg.anchor_dir.as_str(), "ceremony", &key_id);
        let lock_path = side_path(&rec_path, ".lock");
        let saved_lock = std::fs::read(&lock_path).unwrap();
        let _keep_old_ino = File::open(&lock_path).unwrap();
        std::fs::remove_file(&lock_path).unwrap();
        let mut recreated = OpenOptions::new();
        {
            use std::os::unix::fs::OpenOptionsExt;
            recreated.write(true).create_new(true).mode(0o600);
        }
        recreated
            .open(&lock_path)
            .unwrap()
            .write_all(&saved_lock)
            .unwrap();
        assert!(
            FsExternalMountAnchor::open_existing(
                &cfg,
                &[sk_path.to_str().unwrap()],
                &[],
                "ceremony",
                key_id,
                mac_key,
            )
            .is_err()
        );

        std::fs::remove_dir_all(root).unwrap();
    }

    struct Slot {
        root: PathBuf,
        cfg: AnchorConfig,
        sk: String,
    }

    impl Slot {
        fn new(label: &str) -> Self {
            let root = temp_root(label);
            let vault = root.join("vault");
            private_dir(vault.to_str().unwrap(), true).unwrap();
            Self {
                cfg: AnchorConfig {
                    anchor_dir: root.join("anchor").to_str().unwrap().to_owned(),
                    vault_dir: Some(vault.to_str().unwrap().to_owned()),
                    allow_single_disk: true,
                },
                sk: vault.join("sk").to_str().unwrap().to_owned(),
                root,
            }
        }
        fn provision(&self, domain: &str, key_id: [u8; 32]) -> FsExternalMountAnchor {
            FsExternalMountAnchor::provision_fresh(
                &self.cfg,
                &[&self.sk],
                &[],
                domain,
                key_id,
                [0x22; 32],
            )
            .unwrap()
        }
        fn open(&self, domain: &str, key_id: [u8; 32]) -> Result<FsExternalMountAnchor, CliError> {
            FsExternalMountAnchor::open_existing(
                &self.cfg,
                &[&self.sk],
                &[],
                domain,
                key_id,
                [0x22; 32],
            )
        }
        fn record(&self, domain: &str, key_id: &[u8; 32]) -> PathBuf {
            anchor_record_path(&self.cfg.anchor_dir, domain, key_id)
        }
    }

    impl Drop for Slot {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.root);
        }
    }

    fn ckpt(generation: u64, fill: u8) -> LedgerCheckpoint {
        LedgerCheckpoint {
            generation,
            tag: [fill; 32],
        }
    }

    #[test]
    fn anchor_nested_in_the_custody_directory_is_refused_without_vault_dir() {
        let root = temp_root("nested-custody");
        let custody = root.join("custody");
        private_dir(custody.to_str().unwrap(), true).unwrap();
        let sk = custody.join("sk");
        for anchor in [custody.join("anchor"), root.clone()] {
            let cfg = AnchorConfig {
                anchor_dir: anchor.to_str().unwrap().to_owned(),
                vault_dir: None,
                allow_single_disk: true,
            };
            let err = cfg
                .validate_isolation(&[sk.to_str().unwrap()], &[], true)
                .err()
                .unwrap();
            assert!(err.message.contains("overlap or nest"), "{}", err.message);
        }
        let sibling = AnchorConfig {
            anchor_dir: root.join("anchor").to_str().unwrap().to_owned(),
            vault_dir: None,
            allow_single_disk: true,
        };
        sibling
            .validate_isolation(&[sk.to_str().unwrap()], &[], true)
            .unwrap();
        std::fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn truncated_corrupt_and_foreign_records_fail_closed() {
        let slot = Slot::new("corrupt");
        let key_id = [0x11; 32];
        let other_id = [0x12; 32];
        let anchor = slot.provision("ceremony", key_id);
        anchor.advance(ckpt(1, 0xAA)).unwrap();
        anchor.advance(ckpt(2, 0xBB)).unwrap();
        drop(anchor);
        let other = slot.provision("ceremony", other_id);
        other.advance(ckpt(9, 0xCC)).unwrap();
        drop(other);
        let seedburn = slot.provision("seedburn", key_id);
        seedburn.advance(ckpt(9, 0xCC)).unwrap();
        drop(seedburn);

        let path = slot.record("ceremony", &key_id);
        let good = std::fs::read(&path).unwrap();
        assert_eq!(good.len(), ANCHOR_RECORD_LEN);
        let refused = |bytes: &[u8]| {
            std::fs::write(&path, bytes).unwrap();
            let err = slot.open("ceremony", key_id).err().unwrap();
            assert_eq!(
                err.code,
                crate::cli::exit::STATE_CONFLICT,
                "{}",
                err.message
            );
        };
        // Truncated at every length, extended, and empty.
        for len in [0, 1, 8, ANCHOR_PAYLOAD_LEN, ANCHOR_RECORD_LEN - 1] {
            refused(&good[..len]);
        }
        refused(&[&good[..], &[0u8]].concat());
        // One flipped bit in every field: magic, domain, key, generation, tag, consumed
        // flag, consumed generation, ceremony id, MAC.
        for at in [
            0,
            8,
            40,
            79,
            80,
            112,
            120,
            121,
            ANCHOR_PAYLOAD_LEN,
            ANCHOR_RECORD_LEN - 1,
        ] {
            let mut bytes = good.clone();
            bytes[at] ^= 1;
            refused(&bytes);
        }
        // A higher-generation record of another key, and of another domain of the same key:
        // each carries a valid MAC for its own slot only.
        refused(&std::fs::read(slot.record("ceremony", &other_id)).unwrap());
        refused(&std::fs::read(slot.record("seedburn", &key_id)).unwrap());
        // The wrong MAC key.
        std::fs::write(&path, &good).unwrap();
        assert!(
            FsExternalMountAnchor::open_existing(
                &slot.cfg,
                &[&slot.sk],
                &[],
                "ceremony",
                key_id,
                [0x23; 32],
            )
            .is_err()
        );
        assert_eq!(
            slot.open("ceremony", key_id).unwrap().load().unwrap(),
            Some(ckpt(2, 0xBB))
        );

        // A truncated or foreign lock sidecar.
        let lock = side_path(&path, ".lock");
        let header = std::fs::read(&lock).unwrap();
        std::fs::write(&lock, &header[..31]).unwrap();
        assert!(slot.open("ceremony", key_id).is_err());
        let mut altered = header.clone();
        altered[9] ^= 1;
        std::fs::write(&lock, &altered).unwrap();
        assert!(slot.open("ceremony", key_id).is_err());
        std::fs::write(&lock, &header).unwrap();
        slot.open("ceremony", key_id).unwrap();
    }

    #[test]
    fn symlinked_record_and_lock_are_not_followed() {
        let slot = Slot::new("symlink");
        let key_id = [0x31; 32];
        let anchor = slot.provision("ceremony", key_id);
        anchor.advance(ckpt(1, 0xAA)).unwrap();
        drop(anchor);
        let path = slot.record("ceremony", &key_id);
        let lock = side_path(&path, ".lock");
        for target in [&path, &lock] {
            let aside = side_path(target, ".aside");
            std::fs::rename(target, &aside).unwrap();
            std::os::unix::fs::symlink(&aside, target).unwrap();
            assert!(slot.open("ceremony", key_id).is_err());
            std::fs::remove_file(target).unwrap();
            std::fs::rename(&aside, target).unwrap();
            slot.open("ceremony", key_id).unwrap();
        }
        // Enrollment does not follow a planted lock symlink either, and leaves its target alone.
        let fresh_id = [0x32; 32];
        let fresh_lock = side_path(&slot.record("ceremony", &fresh_id), ".lock");
        let decoy = slot.root.join("decoy");
        std::fs::write(&decoy, b"untouched").unwrap();
        std::os::unix::fs::symlink(&decoy, &fresh_lock).unwrap();
        assert!(
            FsExternalMountAnchor::provision_fresh(
                &slot.cfg,
                &[&slot.sk],
                &[],
                "ceremony",
                fresh_id,
                [0x22; 32],
            )
            .is_err()
        );
        assert_eq!(std::fs::read(&decoy).unwrap(), b"untouched");
    }

    /// Write an owner-only record file, replacing whatever is at `path`.
    fn put_back(path: &Path, bytes: &[u8]) {
        use std::os::unix::fs::OpenOptionsExt;
        let _ = std::fs::remove_file(path);
        OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(path)
            .unwrap()
            .write_all(bytes)
            .unwrap();
    }

    #[test]
    fn vanished_or_rewound_record_under_a_live_handle_poisons_it() {
        let slot = Slot::new("vanish");
        let key_id = [0x41; 32];
        let path = slot.record("ceremony", &key_id);

        // A fresh slot has no record until its first write; after that, absence is a rollback.
        let anchor = slot.provision("ceremony", key_id);
        assert_eq!(anchor.load().unwrap(), None);
        anchor.advance(ckpt(1, 0xAA)).unwrap();
        let first = std::fs::read(&path).unwrap();
        anchor.advance(ckpt(2, 0xBB)).unwrap();
        std::fs::remove_file(&path).unwrap();
        assert!(anchor.load().is_err());
        // Poisoning is sticky: restoring the record does not revive the handle.
        put_back(&path, &first);
        assert!(anchor.load().is_err());
        assert!(anchor.advance(ckpt(3, 0xCC)).is_err());
        drop(anchor);

        // An enrolled slot whose record is deleted mid-session can not be re-created at a
        // generation of the caller's choosing.
        put_back(&path, &first);
        let anchor = slot.open("ceremony", key_id).unwrap();
        std::fs::remove_file(&path).unwrap();
        assert!(anchor.advance(ckpt(1, 0xAA)).is_err());
        assert!(!path.exists());
        assert!(
            anchor
                .consume_ceremony_ticket(ckpt(1, 0xAA), &[7; 32])
                .is_err()
        );
        drop(anchor);
        // A record put back with permissions wider than its owner's is refused as well.
        put_back(&path, &first);
        {
            use std::os::unix::fs::PermissionsExt;
            std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o640)).unwrap();
        }
        let err = slot.open("ceremony", key_id).err().unwrap();
        assert!(err.message.contains("permissions"), "{}", err.message);
        std::fs::remove_file(&path).unwrap();
        // With the record gone the slot does not open at all.
        assert!(slot.open("ceremony", key_id).is_err());

        // A record rewound underneath a live handle is refused by every operation.
        put_back(&path, &first);
        let anchor = slot.open("ceremony", key_id).unwrap();
        anchor.advance(ckpt(2, 0xBB)).unwrap();
        put_back(&path, &first);
        assert!(anchor.load().is_err());
        assert!(anchor.advance(ckpt(3, 0xCC)).is_err());
    }

    #[test]
    fn ticket_is_single_use_per_generation_and_bound_to_the_checkpoint() {
        let slot = Slot::new("ticket");
        let key_id = [0x51; 32];
        let anchor = slot.provision("ceremony", key_id);
        // No ticket exists before the first checkpoint.
        assert!(
            anchor
                .consume_ceremony_ticket(ckpt(1, 0xAA), &[1; 32])
                .is_err()
        );
        anchor.advance(ckpt(2, 0xBB)).unwrap();
        drop(anchor);
        // A ticket names the exact checkpoint on disk; a refusal poisons the handle.
        for wrong in [ckpt(1, 0xBB), ckpt(3, 0xBB), ckpt(2, 0xBC)] {
            let anchor = slot.open("ceremony", key_id).unwrap();
            assert!(anchor.consume_ceremony_ticket(wrong, &[1; 32]).is_err());
            assert!(anchor.load().is_err());
        }
        let anchor = slot.open("ceremony", key_id).unwrap();
        anchor
            .consume_ceremony_ticket(ckpt(2, 0xBB), &[1; 32])
            .unwrap();
        drop(anchor);
        // Replay under the same or another ceremony id, from a new handle, is refused.
        for id in [[1u8; 32], [2u8; 32]] {
            let anchor = slot.open("ceremony", key_id).unwrap();
            assert!(anchor.consume_ceremony_ticket(ckpt(2, 0xBB), &id).is_err());
        }
        // A new generation issues exactly one new ticket and voids the earlier one.
        let anchor = slot.open("ceremony", key_id).unwrap();
        anchor.advance(ckpt(3, 0xCC)).unwrap();
        anchor
            .consume_ceremony_ticket(ckpt(3, 0xCC), &[3; 32])
            .unwrap();
        assert!(
            anchor
                .consume_ceremony_ticket(ckpt(3, 0xCC), &[3; 32])
                .is_err()
        );
        drop(anchor);
        let anchor = slot.open("ceremony", key_id).unwrap();
        assert!(
            anchor
                .consume_ceremony_ticket(ckpt(2, 0xBB), &[4; 32])
                .is_err()
        );
    }

    #[test]
    fn interrupted_write_leftovers_are_removed_on_the_next_open() {
        let slot = Slot::new("leftover");
        let key_id = [0x61; 32];
        let anchor = slot.provision("ceremony", key_id);
        anchor.advance(ckpt(1, 0xAA)).unwrap();
        drop(anchor);
        let path = slot.record("ceremony", &key_id);
        let leftover = side_path(&path, &format!(".{}.tmp", "ab".repeat(16)));
        let unrelated = side_path(&path, ".note.tmp");
        std::fs::write(&leftover, b"half a record").unwrap();
        std::fs::write(&unrelated, b"keep").unwrap();
        let anchor = slot.open("ceremony", key_id).unwrap();
        assert!(!leftover.exists());
        assert!(unrelated.exists());
        assert_eq!(anchor.load().unwrap(), Some(ckpt(1, 0xAA)));
    }
}
