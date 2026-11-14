//! External monotone anchor backend (`FsExternalMountAnchor`) for CLI custody state.
//!
//! Defends local stateful signing against full vault-directory snapshot rollback when
//! `--anchor-dir` points to an independently mounted filesystem or hardware-backed directory.
//! Each resource slot holds a permanent `0600` `.lock` sidecar (`QSAGLCK1`) whose 24-byte
//! `dev_le64 || ino_le64 || seal8` identity (`lock_identity_seal`) is authenticated inside the
//! `QSAGANC1` checkpoint record MAC, paired with single-use ceremony ticket consumption.

use std::fs::{File, OpenOptions};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};

use qsag_accel::ct::{ct_eq_bytes, ct_zeroize_bytes};
use qsag_accel::keccak::cshake256_framed_32;
use qsag_core::ceremony_journal::CeremonyContext;
use qsag_core::{ExternalMonotoneAnchor, LedgerCheckpoint};

use crate::cli::{Args, CliError, Secret32, ZeroizingBuf, os_random_32, private_dir};
use crate::codec::{Json, from_hex_exact, to_hex};

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
        let anchor_dir = args.get("anchor-dir").map(str::to_owned);
        let allow_single_disk = args.flag("allow-single-disk-anchor");
        if anchor_dir.is_none() && allow_single_disk {
            return Err(CliError::usage(
                "--allow-single-disk-anchor requires --anchor-dir",
            ));
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
        private_dir(&self.anchor_dir, create_anchor_dir)?;
        let (anchor_dev, anchor_ino) = open_verified_dir_identity(Path::new(&self.anchor_dir))?;
        let anchor_canon = std::fs::canonicalize(&self.anchor_dir)
            .map_err(|e| CliError::io(format_args!("resolving {}", self.anchor_dir), e))?;
        let anchor_canon_meta = std::fs::metadata(&anchor_canon)
            .map_err(|e| CliError::io(format_args!("inspecting {}", self.anchor_dir), e))?;
        if metadata_identity(&anchor_canon_meta) != (anchor_dev, anchor_ino) {
            return Err(CliError::state(
                "--anchor-dir changed identity during validation",
            ));
        }

        let explicit_vault_canon = if let Some(vd) = &self.vault_dir {
            private_dir(vd, create_anchor_dir)?;
            let (vd_dev, vd_ino) = open_verified_dir_identity(Path::new(vd))?;
            if (vd_dev, vd_ino) == (anchor_dev, anchor_ino) {
                return Err(CliError::state(
                    "--anchor-dir resolves to the same directory/inode as --vault-dir",
                ));
            }
            let vd_canon = std::fs::canonicalize(vd)
                .map_err(|e| CliError::io(format_args!("resolving {vd}"), e))?;
            if anchor_canon.starts_with(&vd_canon) || vd_canon.starts_with(&anchor_canon) {
                return Err(CliError::state(
                    "--anchor-dir must not overlap or nest with --vault-dir",
                ));
            }
            if vd_dev == anchor_dev && !self.allow_single_disk {
                return Err(CliError::state(
                    "--anchor-dir resides on the same filesystem device as --vault-dir; mount an independent device or pass --allow-single-disk-anchor",
                ));
            }
            Some(vd_canon)
        } else {
            None
        };

        for file_path in custody_files {
            let parent = Path::new(file_path)
                .parent()
                .filter(|p| !p.as_os_str().is_empty())
                .unwrap_or(Path::new("."));
            let meta = std::fs::metadata(parent)
                .map_err(|e| CliError::io(format_args!("inspecting {}", parent.display()), e))?;
            let (c_dev, c_ino) = metadata_identity(&meta);
            if (c_dev, c_ino) == (anchor_dev, anchor_ino) {
                return Err(CliError::state(
                    "--anchor-dir resolves to the same directory/inode as custody state",
                ));
            }
            let parent_canon = std::fs::canonicalize(parent)
                .map_err(|e| CliError::io(format_args!("resolving {}", parent.display()), e))?;
            // Without --vault-dir the custody directory is the key file's own directory. An
            // anchor inside it (or around it) travels with any snapshot of that directory.
            if anchor_canon.starts_with(&parent_canon) || parent_canon.starts_with(&anchor_canon) {
                return Err(CliError::state(
                    "--anchor-dir must not overlap or nest with the directory holding custody state",
                ));
            }
            if let Some(vd_canon) = &explicit_vault_canon
                && !parent_canon.starts_with(vd_canon)
            {
                return Err(CliError::state(format!(
                    "custody file {file_path} does not reside inside --vault-dir"
                )));
            }
            if c_dev == anchor_dev && !self.allow_single_disk {
                return Err(CliError::state(
                    "--anchor-dir resides on the same filesystem device as custody state; mount an independent device or pass --allow-single-disk-anchor",
                ));
            }
        }

        for dir_path in explicit_dirs {
            let meta = std::fs::metadata(dir_path)
                .map_err(|e| CliError::io(format_args!("inspecting {dir_path}"), e))?;
            let (d_dev, d_ino) = metadata_identity(&meta);
            if (d_dev, d_ino) == (anchor_dev, anchor_ino) {
                return Err(CliError::state(
                    "--anchor-dir resolves to the same directory/inode as custody directory",
                ));
            }
            let dir_canon = std::fs::canonicalize(dir_path)
                .map_err(|e| CliError::io(format_args!("resolving {dir_path}"), e))?;
            if anchor_canon.starts_with(&dir_canon) || dir_canon.starts_with(&anchor_canon) {
                return Err(CliError::state(
                    "--anchor-dir must not overlap or nest with custody directory",
                ));
            }
            if d_dev == anchor_dev && !self.allow_single_disk {
                return Err(CliError::state(
                    "--anchor-dir resides on the same filesystem device as custody directory; mount an independent device or pass --allow-single-disk-anchor",
                ));
            }
        }
        Ok(())
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

/// Enforce that `"anchor_required"` in `secret_json` matches whether `--anchor-dir` was supplied.
pub fn enforce_anchor_requirement(
    secret: &Json,
    anchor_cfg: Option<&AnchorConfig>,
) -> Result<bool, CliError> {
    let required = match secret.get("anchor_required") {
        None => false,
        Some(Json::Bool(flag)) => *flag,
        Some(_) => return Err(crate::vault::corrupt()),
    };
    match (required, anchor_cfg.is_some()) {
        (true, false) => Err(CliError::state(
            "key requires --anchor-dir external monotone anchor",
        )),
        (false, true) => Err(CliError::state("key was not enrolled with --anchor-dir")),
        (flag, _) => Ok(flag),
    }
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

#[cfg(unix)]
fn metadata_identity(meta: &std::fs::Metadata) -> (u64, u64) {
    use std::os::unix::fs::MetadataExt;
    (meta.dev(), meta.ino())
}

#[cfg(not(unix))]
fn metadata_identity(_meta: &std::fs::Metadata) -> (u64, u64) {
    (0, 0)
}

#[cfg(unix)]
fn identity_bytes16(meta: &std::fs::Metadata) -> [u8; 16] {
    let (dev, ino) = metadata_identity(meta);
    let mut out = [0u8; 16];
    out[..8].copy_from_slice(&dev.to_le_bytes());
    out[8..].copy_from_slice(&ino.to_le_bytes());
    out
}

#[cfg(not(unix))]
fn identity_bytes16(_meta: &std::fs::Metadata) -> [u8; 16] {
    [0u8; 16]
}

#[cfg(unix)]
fn open_verified_dir_identity(path: &Path) -> Result<(u64, u64), CliError> {
    use std::os::unix::fs::PermissionsExt;
    let lstat = std::fs::symlink_metadata(path)
        .map_err(|e| CliError::io(format_args!("inspecting {}", path.display()), e))?;
    if !lstat.is_dir() || lstat.permissions().mode() & 0o077 != 0 {
        return Err(CliError::state(format!(
            "{} must be a private 0700 directory, not a symlink",
            path.display()
        )));
    }
    let mut opts = OpenOptions::new();
    opts.read(true);
    crate::cli::set_nofollow_nonblocking(&mut opts)?;
    let dir_file = opts
        .open(path)
        .map_err(|e| CliError::io(format_args!("opening directory {}", path.display()), e))?;
    let fstat = dir_file
        .metadata()
        .map_err(|e| CliError::io(format_args!("inspecting {}", path.display()), e))?;
    if !fstat.is_dir()
        || fstat.permissions().mode() & 0o077 != 0
        || metadata_identity(&lstat) != metadata_identity(&fstat)
    {
        return Err(CliError::state(format!(
            "{} failed directory identity or 0700 permission verification",
            path.display()
        )));
    }
    Ok(metadata_identity(&fstat))
}

#[cfg(not(unix))]
fn open_verified_dir_identity(path: &Path) -> Result<(u64, u64), CliError> {
    Err(CliError::state(format!(
        "{}: external anchor directories require Unix file identity support",
        path.display()
    )))
}

fn sync_parent_io(path: &Path) -> io::Result<()> {
    let parent = path
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    File::open(parent)?.sync_all()
}

fn side_path(path: &Path, suffix: &str) -> PathBuf {
    let mut os = path.as_os_str().to_os_string();
    os.push(suffix);
    PathBuf::from(os)
}

fn regular_metadata_io(path: &Path) -> io::Result<Option<std::fs::Metadata>> {
    match std::fs::symlink_metadata(path) {
        Ok(meta) if meta.is_file() => Ok(Some(meta)),
        Ok(_) => Err(invalid_anchor("anchor path is not a regular file")),
        Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(None),
        Err(e) => Err(e),
    }
}

fn verify_file_identity(file: &File, path: &Path) -> io::Result<std::fs::Metadata> {
    let held = file.metadata()?;
    let named = regular_metadata_io(path)?
        .ok_or_else(|| invalid_anchor("anchor sidecar or record vanished"))?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        if held.permissions().mode() & 0o077 != 0 {
            return Err(invalid_anchor("anchor file permissions exceed 0600"));
        }
    }
    if !held.is_file() || identity_bytes16(&held) != identity_bytes16(&named) {
        return Err(invalid_anchor("anchor file inode mismatch"));
    }
    Ok(held)
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
        use std::os::unix::fs::{FileExt, OpenOptionsExt};

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
        } else if regular_metadata_io(&path)?.is_none() {
            return Err(io::Error::new(
                io::ErrorKind::NotFound,
                "provisioned external anchor record is missing",
            ));
        }

        let lock_path = side_path(&path, ".lock");
        regular_metadata_io(&lock_path)?;

        let mut opts = OpenOptions::new();
        opts.read(true)
            .write(true)
            .create_new(must_create)
            .mode(0o600);
        crate::cli::set_nofollow_nonblocking(&mut opts)
            .map_err(|e| io::Error::new(io::ErrorKind::Unsupported, e.message))?;

        let mut lock_file = opts.open(&lock_path).map_err(|e| {
            if !must_create && e.kind() == io::ErrorKind::NotFound {
                invalid_anchor("external anchor lock sidecar missing")
            } else {
                e
            }
        })?;

        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(5);
        loop {
            match lock_file.try_lock() {
                Ok(()) => break,
                Err(std::fs::TryLockError::WouldBlock) if std::time::Instant::now() < deadline => {
                    std::thread::sleep(std::time::Duration::from_millis(10));
                }
                Err(_) => {
                    return Err(io::Error::new(
                        io::ErrorKind::WouldBlock,
                        "external anchor lock unavailable",
                    ));
                }
            }
        }

        let held_meta = verify_file_identity(&lock_file, &lock_path)?;
        let inode = identity_bytes16(&held_meta);
        let mut header = [0u8; 32];
        if must_create {
            let rand = os_random_32().map_err(|e| io::Error::other(e.message))?;
            header[..8].copy_from_slice(LOCK_MAGIC);
            header[8..16].copy_from_slice(&rand[..8]);
            header[16..32].copy_from_slice(&inode);
            lock_file.write_all(&header)?;
            lock_file.sync_all()?;
            sync_parent_io(&lock_path)?;
        } else {
            if held_meta.len() != 32 {
                return Err(invalid_anchor("external anchor lock header truncated"));
            }
            lock_file.read_exact_at(&mut header, 0)?;
            if &header[..8] != LOCK_MAGIC || header[16..32] != inode {
                return Err(invalid_anchor("external anchor lock identity mismatch"));
            }
        }

        if must_create && regular_metadata_io(&path)?.is_some() {
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
        this.remove_interrupted_writes();
        Ok(this)
    }

    /// Unlink the temporary files of writes that were interrupted before their rename. The
    /// exclusive lock is held, so no live writer owns one. Best effort: a leftover is inert.
    #[cfg(unix)]
    fn remove_interrupted_writes(&self) {
        let (Some(dir), Some(name)) = (
            self.path.parent(),
            self.path.file_name().and_then(|n| n.to_str()),
        ) else {
            return;
        };
        let Ok(entries) = std::fs::read_dir(dir) else {
            return;
        };
        for entry in entries.flatten() {
            let file_name = entry.file_name();
            let stale = file_name
                .to_str()
                .and_then(|n| n.strip_prefix(name))
                .and_then(|n| n.strip_prefix('.'))
                .and_then(|n| n.strip_suffix(".tmp"))
                .is_some_and(|hex| hex.len() == 32 && hex.bytes().all(|b| b.is_ascii_hexdigit()));
            if stale && entry.file_type().is_ok_and(|t| t.is_file()) {
                let _ = std::fs::remove_file(entry.path());
            }
        }
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
        let meta = verify_file_identity(&self.lock_file, &lock_path)?;
        if meta.len() != 32 || identity_bytes16(&meta) != self.inode {
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
        if regular_metadata_io(&self.path)?.is_none() {
            return Ok(None);
        }
        let result = (|| -> io::Result<ZeroizingBuf> {
            let mut opts = OpenOptions::new();
            opts.read(true);
            crate::cli::set_nofollow_nonblocking(&mut opts)
                .map_err(|e| io::Error::new(io::ErrorKind::Unsupported, e.message))?;
            let mut file = opts.open(&self.path)?;
            let meta = verify_file_identity(&file, &self.path)?;
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
        use std::os::unix::fs::OpenOptionsExt;
        self.check_not_poisoned()?;
        if let Err(e) = self.check_lock() {
            return self.poison(e);
        }
        let rand = os_random_32().map_err(|e| io::Error::other(e.message))?;
        let tmp_suffix = format!(".{}.tmp", to_hex(&rand[..16]));
        let tmp_path = side_path(&self.path, &tmp_suffix);
        let result = (|| -> io::Result<()> {
            let mut opts = OpenOptions::new();
            opts.write(true).create_new(true).mode(0o600);
            crate::cli::set_nofollow_nonblocking(&mut opts)
                .map_err(|e| io::Error::new(io::ErrorKind::Unsupported, e.message))?;
            let mut tmp = opts.open(&tmp_path)?;
            verify_file_identity(&tmp, &tmp_path)?;
            tmp.write_all(contents)?;
            tmp.sync_all()?;
            drop(tmp);
            self.check_lock()?;
            std::fs::rename(&tmp_path, &self.path)?;
            sync_parent_io(&self.path)?;
            self.check_lock()
        })();
        if let Err(e) = result {
            let _ = std::fs::remove_file(&tmp_path);
            return self.poison(e);
        }
        Ok(())
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
