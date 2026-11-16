//! External monotone anchor backend (`FsExternalMountAnchor`) for CLI custody state.
//!
//! Defends local stateful signing against full vault-directory snapshot rollback and VM/volume
//! forks by composing up to three independent anti-rollback authorities via
//! [`CompositeAntiRollbackAnchor`]:
//! 1. `--anchor-dir <dir>`: a `LockedRecord` single-use ceremony ticket seal (`QSAGANC1`) paired
//!    with a mirrored dual-slot [`FsDirectoryMonotoneAnchor`] (`TwoSlotRecord` surviving loss of
//!    either slot).
//! 2. `--anchor-tpm-nv <nv-index>`: hardware TPM 2.0 `TPM_NT_COUNTER` NV index accessed directly
//!    through `/dev/tpmrm0` ([`Tpm2NvMonotoneAnchor<DevTpmRm0>`]).
//! 3. `--anchor-vmgenid`: hypervisor generation-ID + kernel `boot_id` + inode continuity fence
//!    ([`HypervisorGenerationAnchor<LinuxSysfsVmGenSource>`]).

use std::io;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};

use qsag_accel::ct::{ct_eq_bytes, ct_zeroize_bytes};
use qsag_accel::keccak::cshake256_framed_32;
use qsag_asm::durable::LockedRecord;
use qsag_core::anti_rollback::{
    CompositeAntiRollbackAnchor, DevTpmRm0, HypervisorGenerationAnchor, LinuxSysfsVmGenSource,
    Tpm2NvMonotoneAnchor, Tpm2Transport, VmGenPolicy, is_valid_tpm2_nv_index,
};
use qsag_core::ceremony_journal::CeremonyContext;
use qsag_core::{ExternalMonotoneAnchor, LedgerCheckpoint};
use qsag_quorum::FsDirectoryMonotoneAnchor;

use crate::cli::{Args, CliError, Secret32, ZeroizingBuf};
use crate::codec::{Json, from_hex_exact, to_hex};
use crate::persist::{file_identity, parent_dir, private_dir};

const ANCHOR_MAGIC: &[u8; 8] = b"QSAGANC1";
const ANCHOR_PAYLOAD_LEN: usize = 8 + 32 + 32 + 8 + 32 + 1 + 8 + 32;
const ANCHOR_RECORD_LEN: usize = ANCHOR_PAYLOAD_LEN + 32;

/// Value options shared across CLI subcommands that accept external monotone anchors.
pub const ANCHOR_VALUE_OPTIONS: &[&str] = &[
    "anchor-dir",
    "vault-dir",
    "anchor-tpm-nv",
    "anchor-tpm-device",
    "anchor-tpm-auth-env",
];

/// Value options for CLI subcommands that already declare `"vault-dir"` directly.
pub const ANCHOR_NO_VAULT_VALUE_OPTIONS: &[&str] = &[
    "anchor-dir",
    "anchor-tpm-nv",
    "anchor-tpm-device",
    "anchor-tpm-auth-env",
];

/// Flag options shared across CLI subcommands that accept external monotone anchors.
pub const ANCHOR_FLAG_OPTIONS: &[&str] = &[
    "allow-single-disk-anchor",
    "anchor-vmgenid",
    "anchor-vmgenid-strict",
    "ephemeral-unanchored",
];

/// Parsed `--anchor-dir`, `--anchor-tpm-nv`, `--anchor-vmgenid`, `--vault-dir`, and
/// `--allow-single-disk-anchor` CLI options.
#[derive(Clone, Debug, Default)]
pub struct AnchorConfig {
    pub anchor_dir: Option<String>,
    pub vault_dir: Option<String>,
    pub allow_single_disk: bool,
    pub tpm_nv_index: Option<u32>,
    pub tpm_device_path: Option<String>,
    pub tpm_auth_env: Option<String>,
    pub vmgenid: bool,
    pub vmgenid_strict: bool,
}

pub fn parse_tpm_nv_index(raw: &str) -> Result<u32, CliError> {
    let trimmed = raw.trim();
    let parsed = if let Some(hex) = trimmed
        .strip_prefix("0x")
        .or_else(|| trimmed.strip_prefix("0X"))
    {
        u32::from_str_radix(hex, 16)
    } else {
        trimmed.parse::<u32>()
    }
    .map_err(|_| {
        CliError::usage("--anchor-tpm-nv must be a 32-bit NV index (e.g. 0x01800001)")
    })?;
    if !is_valid_tpm2_nv_index(parsed) {
        return Err(CliError::usage(
            "--anchor-tpm-nv must lie in TPM_HT_NV_INDEX (0x01000000..=0x01FFFFFF)",
        ));
    }
    Ok(parsed)
}

fn read_tpm_password(auth_env: Option<&str>) -> Result<ZeroizingBuf, CliError> {
    let Some(var) = auth_env else {
        return Ok(ZeroizingBuf::new(Vec::new()));
    };
    let val = std::env::var(var).map_err(|_| {
        CliError::usage(format!(
            "TPM2 auth environment variable {var} is not set or not valid UTF-8"
        ))
    })?;
    let buf = ZeroizingBuf::new(val.into_bytes());
    if buf.len() > 64 {
        return Err(CliError::usage(
            "--anchor-tpm-auth-env value exceeds 64-byte TPM2B_AUTH limit",
        ));
    }
    Ok(buf)
}

impl AnchorConfig {
    #[cfg(test)]
    pub fn dir_only(
        anchor_dir: impl Into<String>,
        vault_dir: Option<String>,
        allow_single_disk: bool,
    ) -> Self {
        Self {
            anchor_dir: Some(anchor_dir.into()),
            vault_dir,
            allow_single_disk,
            ..Self::default()
        }
    }

    pub fn from_args(args: &Args) -> Result<Option<Self>, CliError> {
        let anchor_dir = args.get("anchor-dir").map(str::to_owned);
        let vault_dir = args.get("vault-dir").map(str::to_owned);
        let allow_single_disk = args.flag("allow-single-disk-anchor");
        let tpm_nv_index = args.get("anchor-tpm-nv").map(parse_tpm_nv_index).transpose()?;
        let tpm_device_path = args.get("anchor-tpm-device").map(str::to_owned);
        let tpm_auth_env = args.get("anchor-tpm-auth-env").map(str::to_owned);
        let vmgenid = args.flag("anchor-vmgenid");
        let vmgenid_strict = args.flag("anchor-vmgenid-strict");

        if tpm_nv_index.is_none() && (tpm_device_path.is_some() || tpm_auth_env.is_some()) {
            return Err(CliError::usage(
                "--anchor-tpm-device and --anchor-tpm-auth-env require --anchor-tpm-nv",
            ));
        }
        if vmgenid_strict && !vmgenid {
            return Err(CliError::usage(
                "--anchor-vmgenid-strict requires --anchor-vmgenid",
            ));
        }
        if anchor_dir.is_none() && allow_single_disk {
            return Err(CliError::usage(
                "--allow-single-disk-anchor requires --anchor-dir",
            ));
        }
        let any_anchor = anchor_dir.is_some() || tpm_nv_index.is_some() || vmgenid;
        if !any_anchor && vault_dir.is_some() {
            return Err(CliError::usage(
                "--vault-dir requires an anchor (--anchor-dir, --anchor-tpm-nv, or --anchor-vmgenid)",
            ));
        }
        if !any_anchor {
            return Ok(None);
        }
        Ok(Some(Self {
            anchor_dir,
            vault_dir,
            allow_single_disk,
            tpm_nv_index,
            tpm_device_path,
            tpm_auth_env,
            vmgenid,
            vmgenid_strict,
        }))
    }

    pub fn from_quorum_args(args: &Args, vault_dir: &str) -> Result<Option<Self>, CliError> {
        Self::for_vault(args, vault_dir, "anchor-dir", "allow-single-disk-anchor")
    }

    /// The anchor of a vault directory the command already names, read from the option
    /// `dir_option` and the flag `single_disk_flag` (plus hardware TPM2/VMGENID options when
    /// `dir_option == "anchor-dir"`).
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
        let (tpm_nv_index, tpm_device_path, tpm_auth_env, vmgenid, vmgenid_strict) =
            if dir_option == "anchor-dir" {
                let tpm_nv = args
                    .get("anchor-tpm-nv")
                    .map(parse_tpm_nv_index)
                    .transpose()?;
                let tpm_dev = args.get("anchor-tpm-device").map(str::to_owned);
                let tpm_auth = args.get("anchor-tpm-auth-env").map(str::to_owned);
                let vmg = args.flag("anchor-vmgenid");
                let vmg_strict = args.flag("anchor-vmgenid-strict");
                if tpm_nv.is_none() && (tpm_dev.is_some() || tpm_auth.is_some()) {
                    return Err(CliError::usage(
                        "--anchor-tpm-device and --anchor-tpm-auth-env require --anchor-tpm-nv",
                    ));
                }
                if vmg_strict && !vmg {
                    return Err(CliError::usage(
                        "--anchor-vmgenid-strict requires --anchor-vmgenid",
                    ));
                }
                (tpm_nv, tpm_dev, tpm_auth, vmg, vmg_strict)
            } else {
                (None, None, None, false, false)
            };

        if anchor_dir.is_none() && tpm_nv_index.is_none() && !vmgenid {
            return Ok(None);
        }
        Ok(Some(Self {
            anchor_dir,
            vault_dir: Some(vault_dir.to_owned()),
            allow_single_disk,
            tpm_nv_index,
            tpm_device_path,
            tpm_auth_env,
            vmgenid,
            vmgenid_strict,
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
        let explicit_vault = match &self.vault_dir {
            Some(vd) => {
                let vault = Location {
                    id: private_dir(vd, create_anchor_dir)?,
                    canon: canonical(vd)?,
                };
                Some(vault)
            }
            None => None,
        };

        if let Some(anchor_dir) = &self.anchor_dir {
            let anchor = Location {
                id: private_dir(anchor_dir, create_anchor_dir)?,
                canon: canonical(anchor_dir)?,
            };
            if Location::of(&anchor.canon)?.id != anchor.id {
                return Err(CliError::state(
                    "--anchor-dir changed identity during validation",
                ));
            }

            if let Some(vault) = &explicit_vault {
                self.refuse_overlap(&anchor, vault, "--vault-dir")?;
                self.refuse_shared_device(&anchor, vault, "--vault-dir")?;
            }

            for file_path in custody_files {
                let parent = Location::of(parent_dir(Path::new(file_path)))?;
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
        } else if let Some(vault) = &explicit_vault {
            for file_path in custody_files {
                let parent = Location::of(parent_dir(Path::new(file_path)))?;
                if !parent.canon.starts_with(&vault.canon) {
                    return Err(CliError::state(format!(
                        "custody file {file_path} does not reside inside --vault-dir"
                    )));
                }
            }
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

/// Parse optional `--policy-id-hex` and `--spend-amount` (`u128`) CLI ceremony context options.
pub fn parse_ceremony_context(
    args: &Args,
    mpc_nonce_epoch: u64,
) -> Result<CeremonyContext, CliError> {
    let policy_id = match args.get("policy-id-hex") {
        Some(hex) => from_hex_exact(hex, "policy-id-hex")?,
        None => [0u8; 32],
    };
    let spend_amount = args.get_u128("spend-amount")?.unwrap_or(0);
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

/// Enforce that `"anchor_required"` in `secret_json` matches whether an external anchor was supplied.
pub fn enforce_anchor_requirement(
    secret: &Json,
    anchor_cfg: Option<&AnchorConfig>,
) -> Result<bool, CliError> {
    anchor_requirement(secret, anchor_cfg.is_some()).map_err(|e| match e {
        AnchorRequirementError::Malformed => crate::vault::corrupt(),
        AnchorRequirementError::AnchorMissing => CliError::state(
            "key requires an external monotone anchor (--anchor-dir, --anchor-tpm-nv, or --anchor-vmgenid)",
        ),
        AnchorRequirementError::NotEnrolled => {
            CliError::state("key was not enrolled with an external monotone anchor")
        }
    })
}

/// Rollback-sensitive custody state names its external anchor (`--{dir_option}`) or
/// waives rollback protection by name (`--ephemeral-unanchored`). Naming both is a
/// contradiction, not a preference.
pub fn require_anchor_or_waiver(
    anchored: bool,
    waived: bool,
    dir_option: &str,
) -> Result<(), CliError> {
    match (anchored, waived) {
        (true, true) => Err(CliError::usage(format!(
            "--ephemeral-unanchored waives rollback protection and cannot be combined with --{dir_option}"
        ))),
        (false, false) => Err(CliError::usage(format!(
            "stateful custody requires --{dir_option}; disposable tests must explicitly use --ephemeral-unanchored"
        ))),
        _ => Ok(()),
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct AnchorRecordState {
    checkpoint: LedgerCheckpoint,
    consumed: Option<(u64, [u8; 32])>,
}

struct AnchorInner {
    record: LockedRecord,
    /// Set by any refused read, write or consistency check; never cleared.
    poisoned: AtomicBool,
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
        let expected_mac = Secret32::new(self.compute_mac(payload));
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
        self.check_not_poisoned()?;
        match self.record.read_bounded(ANCHOR_RECORD_LEN) {
            Ok(bytes) => match self.decode(&bytes) {
                Ok(state) => Ok(Some(state)),
                Err(e) => self.poison(e),
            },
            // A slot has no record between its enrollment and its first write.
            Err(e) if e.kind() == io::ErrorKind::NotFound => {
                if self.written.load(Ordering::SeqCst) {
                    self.poison(invalid_anchor("external anchor record vanished"))
                } else {
                    Ok(None)
                }
            }
            Err(e) => self.poison(e),
        }
    }

    fn write_state(&self, state: &AnchorRecordState) -> io::Result<()> {
        self.check_not_poisoned()?;
        if let Err(e) = self.record.replace(&self.encode(state)) {
            return self.poison(e);
        }
        self.written.store(true, Ordering::SeqCst);
        Ok(())
    }
}

/// Production composite [`ExternalMonotoneAnchor`] combining:
/// - `O_NOFOLLOW` `0600` [`LockedRecord`] single-use ticket seal (`lock_identity_seal`),
/// - mirrored dual-slot [`FsDirectoryMonotoneAnchor`] (`--anchor-dir`),
/// - hardware TPM 2.0 NV counter [`Tpm2NvMonotoneAnchor<DevTpmRm0>`] (`--anchor-tpm-nv`), and
/// - hypervisor generation-ID + `boot_id` + inode continuity [`HypervisorGenerationAnchor`] (`--anchor-vmgenid`)
///   via [`CompositeAntiRollbackAnchor`].
#[derive(Clone)]
pub struct FsExternalMountAnchor {
    inner: Arc<AnchorInner>,
    composite: Arc<dyn ExternalMonotoneAnchor>,
}

struct CoreTicketAnchor(Arc<AnchorInner>);

impl ExternalMonotoneAnchor for CoreTicketAnchor {
    fn load(&self) -> io::Result<Option<LedgerCheckpoint>> {
        let mut guard = self
            .0
            .state
            .lock()
            .map_err(|_| io::Error::other("external anchor mutex poisoned"))?;
        let disk = self.0.read_verified_disk_state()?;
        if let (Some(mem), Some(on_disk)) = (*guard, disk)
            && (on_disk.checkpoint.generation < mem.checkpoint.generation
                || (on_disk.checkpoint.generation == mem.checkpoint.generation
                    && !ct_eq_bytes(&on_disk.checkpoint.tag, &mem.checkpoint.tag)))
        {
            return self.0.poison(io::Error::other(
                "external anchor rolled back underneath live handle",
            ));
        }
        *guard = disk;
        Ok(disk.map(|s| s.checkpoint))
    }

    fn advance(&self, checkpoint: LedgerCheckpoint) -> io::Result<()> {
        let mut guard = self
            .0
            .state
            .lock()
            .map_err(|_| io::Error::other("external anchor mutex poisoned"))?;
        let disk = self.0.read_verified_disk_state()?;
        if let Some(prev) = disk {
            if checkpoint.generation < prev.checkpoint.generation {
                return self.0.poison(io::Error::other(
                    "external anchor rejects rolled-back generation",
                ));
            }
            if checkpoint.generation == prev.checkpoint.generation {
                if !ct_eq_bytes(&checkpoint.tag, &prev.checkpoint.tag) {
                    return self.0.poison(io::Error::other(
                        "external anchor rejects mismatched tag at equal generation",
                    ));
                }
                *guard = Some(prev);
                return Ok(());
            }
        }
        let next = AnchorRecordState {
            checkpoint,
            // A strictly newer checkpoint retires the previous generation's latch.
            // Equal-generation advances return above and preserve its consumption.
            consumed: None,
        };
        self.0.write_state(&next)?;
        *guard = Some(next);
        Ok(())
    }
}

struct DynExternalAnchor(Arc<dyn ExternalMonotoneAnchor>);

impl ExternalMonotoneAnchor for DynExternalAnchor {
    fn load(&self) -> io::Result<Option<LedgerCheckpoint>> {
        self.0.load()
    }
    fn advance(&self, checkpoint: LedgerCheckpoint) -> io::Result<()> {
        self.0.advance(checkpoint)
    }
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

fn slot_stem(domain: &str, key_id: &[u8; 32]) -> String {
    let slot_digest = cshake256_framed_32(b"QSAG.CLI.ANCHOR.SLOT.V1", &[domain.as_bytes(), key_id]);
    format!("{}-{}", sanitize_domain_prefix(domain), to_hex(&slot_digest))
}

fn anchor_record_path(anchor_dir: &str, domain: &str, key_id: &[u8; 32]) -> PathBuf {
    Path::new(anchor_dir).join(format!("{}.anchor", slot_stem(domain, key_id)))
}

fn anchor_mirror_dir_path(anchor_dir: &str, domain: &str, key_id: &[u8; 32]) -> PathBuf {
    Path::new(anchor_dir).join(format!("{}.mirror", slot_stem(domain, key_id)))
}

fn resolve_custody_dir(
    config: &AnchorConfig,
    custody_files: &[&str],
    explicit_dirs: &[&str],
) -> Result<PathBuf, CliError> {
    if let Some(d) = explicit_dirs.first() {
        return Ok(PathBuf::from(d));
    }
    if let Some(f) = custody_files.first() {
        return Ok(parent_dir(Path::new(f)).to_path_buf());
    }
    if let Some(vd) = &config.vault_dir {
        return Ok(PathBuf::from(vd));
    }
    Err(CliError::state(
        "cannot resolve custody directory for external anchor",
    ))
}

fn derive_sub_mac(
    root_mac: &[u8; 32],
    backend_tag: &[u8],
    domain: &str,
    key_id: &[u8; 32],
) -> Secret32 {
    Secret32::new(cshake256_framed_32(
        b"QSAG.CLI.ANCHOR.SUBKEY.V1",
        &[root_mac, backend_tag, domain.as_bytes(), key_id],
    ))
}

fn ensure_seal_state(path: &Path, fresh: bool, label: &str) -> Result<(), CliError> {
    let exists = match std::fs::symlink_metadata(path) {
        Ok(_) => true,
        Err(e) if e.kind() == io::ErrorKind::NotFound => false,
        Err(e) => return Err(CliError::io(format_args!("inspecting {label} seal"), e)),
    };
    if fresh && exists {
        return Err(CliError::state(format!(
            "{label} anchor seal already exists at {}",
            path.display()
        )));
    }
    if !fresh && !exists {
        return Err(CliError::state(format!(
            "ExternalAnchorUnavailableOrCorrupt ({label}): missing seal {}",
            path.display()
        )));
    }
    Ok(())
}

impl FsExternalMountAnchor {
    /// Provision a brand-new external anchor slot (`load()` initially `None`).
    pub fn provision_fresh(
        config: &AnchorConfig,
        custody_files: &[&str],
        explicit_dirs: &[&str],
        domain: &str,
        key_id: [u8; 32],
        mac_key: [u8; 32],
    ) -> Result<Self, CliError> {
        Self::open_composite::<DevTpmRm0>(
            config,
            custody_files,
            explicit_dirs,
            domain,
            key_id,
            mac_key,
            true,
            None,
        )
    }

    /// Open and authenticate an existing external anchor slot.
    pub fn open_existing(
        config: &AnchorConfig,
        custody_files: &[&str],
        explicit_dirs: &[&str],
        domain: &str,
        key_id: [u8; 32],
        mac_key: [u8; 32],
    ) -> Result<Self, CliError> {
        Self::open_composite::<DevTpmRm0>(
            config,
            custody_files,
            explicit_dirs,
            domain,
            key_id,
            mac_key,
            false,
            None,
        )
    }

    #[cfg(test)]
    pub(crate) fn provision_fresh_with_tpm<T: Tpm2Transport + 'static>(
        config: &AnchorConfig,
        custody_files: &[&str],
        explicit_dirs: &[&str],
        domain: &str,
        key_id: [u8; 32],
        mac_key: [u8; 32],
        transport: T,
    ) -> Result<Self, CliError> {
        Self::open_composite(
            config,
            custody_files,
            explicit_dirs,
            domain,
            key_id,
            mac_key,
            true,
            Some(transport),
        )
    }

    #[cfg(test)]
    pub(crate) fn open_existing_with_tpm<T: Tpm2Transport + 'static>(
        config: &AnchorConfig,
        custody_files: &[&str],
        explicit_dirs: &[&str],
        domain: &str,
        key_id: [u8; 32],
        mac_key: [u8; 32],
        transport: T,
    ) -> Result<Self, CliError> {
        Self::open_composite(
            config,
            custody_files,
            explicit_dirs,
            domain,
            key_id,
            mac_key,
            false,
            Some(transport),
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn open_composite<T: Tpm2Transport + 'static>(
        config: &AnchorConfig,
        custody_files: &[&str],
        explicit_dirs: &[&str],
        domain: &str,
        key_id: [u8; 32],
        mac_key: [u8; 32],
        fresh: bool,
        injected_tpm: Option<T>,
    ) -> Result<Self, CliError> {
        let root_mac = Secret32::new(mac_key);
        config.validate_isolation(custody_files, explicit_dirs, fresh)?;

        let stem = slot_stem(domain, &key_id);
        let seal_base_dir = match &config.anchor_dir {
            Some(dir) => PathBuf::from(dir),
            None => resolve_custody_dir(config, custody_files, explicit_dirs)?,
        };
        let record_path = match &config.anchor_dir {
            Some(dir) => anchor_record_path(dir, domain, &key_id),
            None => seal_base_dir.join(format!(".qsag-{stem}.anchor")),
        };

        let record = if fresh {
            LockedRecord::create_new(&record_path).map_err(|e| {
                CliError::state(format!("enrolling external anchor ({domain}): {e}"))
            })?
        } else {
            LockedRecord::open_existing(&record_path).map_err(|e| {
                CliError::state(format!(
                    "ExternalAnchorUnavailableOrCorrupt ({domain}): {e}"
                ))
            })?
        };

        let domain_hash = cshake256_framed_32(b"QSAG.CLI.ANCHOR.DOMAIN.V1", &[domain.as_bytes()]);
        let inner = Arc::new(AnchorInner {
            record,
            poisoned: AtomicBool::new(false),
            domain_hash,
            key_id,
            mac_key: root_mac.0,
            state: Mutex::new(None),
            written: AtomicBool::new(!fresh),
        });

        if !fresh {
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
        }

        let mut chain: DynExternalAnchor =
            DynExternalAnchor(Arc::new(CoreTicketAnchor(Arc::clone(&inner))));

        if let Some(anchor_dir) = &config.anchor_dir {
            let mirror_path = anchor_mirror_dir_path(anchor_dir, domain, &key_id);
            let dir_mac = derive_sub_mac(&root_mac.0, b"dir_mirror", domain, &key_id);
            let dir_anchor = if fresh {
                FsDirectoryMonotoneAnchor::create_new(&mirror_path, dir_mac.0).map_err(|e| {
                    CliError::state(format!(
                        "enrolling mirrored directory anchor ({domain}): {e}"
                    ))
                })?
            } else {
                FsDirectoryMonotoneAnchor::open_existing(&mirror_path, dir_mac.0).map_err(|e| {
                    CliError::state(format!(
                        "ExternalAnchorUnavailableOrCorrupt (mirrored {domain}): {e}"
                    ))
                })?
            };
            chain = DynExternalAnchor(Arc::new(CompositeAntiRollbackAnchor::new(
                chain, dir_anchor,
            )));
        }

        if let Some(nv_index) = config.tpm_nv_index {
            let tpm_seal_path = if config.anchor_dir.is_some() {
                seal_base_dir.join(format!("{stem}.tpm"))
            } else {
                seal_base_dir.join(format!(".qsag-{stem}.tpm"))
            };
            ensure_seal_state(&tpm_seal_path, fresh, "TPM2 NV")?;
            let password = read_tpm_password(config.tpm_auth_env.as_deref())?;
            let tpm_mac = derive_sub_mac(&root_mac.0, b"tpm2_nv", domain, &key_id);
            if let Some(transport) = injected_tpm {
                let tpm_anchor = Tpm2NvMonotoneAnchor::open_with_transport(
                    transport,
                    &tpm_seal_path,
                    nv_index,
                    nv_index,
                    &password,
                    tpm_mac.0,
                )
                .map_err(|e| {
                    CliError::state(format!(
                        "ExternalAnchorUnavailableOrCorrupt (TPM2 NV {domain}): {}",
                        e.into_io_error()
                    ))
                })?;
                chain = DynExternalAnchor(Arc::new(CompositeAntiRollbackAnchor::new(
                    chain, tpm_anchor,
                )));
            } else {
                let dev_path = config
                    .tpm_device_path
                    .as_deref()
                    .unwrap_or(DevTpmRm0::DEFAULT_DEVICE_PATH);
                let dev = DevTpmRm0::open_path(dev_path).map_err(|e| {
                    CliError::state(format!(
                        "opening TPM2 resource manager {dev_path} ({domain}): {}",
                        e.into_io_error()
                    ))
                })?;
                let tpm_anchor = Tpm2NvMonotoneAnchor::open_with_transport(
                    dev,
                    &tpm_seal_path,
                    nv_index,
                    nv_index,
                    &password,
                    tpm_mac.0,
                )
                .map_err(|e| {
                    CliError::state(format!(
                        "ExternalAnchorUnavailableOrCorrupt (TPM2 NV {domain}): {}",
                        e.into_io_error()
                    ))
                })?;
                chain = DynExternalAnchor(Arc::new(CompositeAntiRollbackAnchor::new(
                    chain, tpm_anchor,
                )));
            }
        }

        if config.vmgenid {
            let vmgen_seal_path = if config.anchor_dir.is_some() {
                seal_base_dir.join(format!("{stem}.vmgen"))
            } else {
                seal_base_dir.join(format!(".qsag-{stem}.vmgen"))
            };
            ensure_seal_state(&vmgen_seal_path, fresh, "VMGENID")?;
            let guarded_dir = resolve_custody_dir(config, custody_files, explicit_dirs)?;
            let guarded_target = guarded_dir.join(format!(".qsag-{stem}.target"));
            if fresh {
                crate::cli::write_new(&guarded_target.to_string_lossy(), &domain_hash, true)?;
            } else if !std::fs::symlink_metadata(&guarded_target)
                .map(|m| m.is_file())
                .unwrap_or(false)
            {
                return Err(CliError::state(format!(
                    "ExternalAnchorUnavailableOrCorrupt (VMGENID {domain}): missing guarded custody target {}",
                    guarded_target.display()
                )));
            }
            let policy = if config.vmgenid_strict {
                VmGenPolicy::STRICT_HYPERVISOR
            } else {
                VmGenPolicy::PINNED_BOOT_SESSION
            };
            let vmgen_mac = derive_sub_mac(&root_mac.0, b"vmgenid", domain, &key_id);
            let vmgen_anchor =
                HypervisorGenerationAnchor::<LinuxSysfsVmGenSource>::open_or_create(
                    &vmgen_seal_path,
                    &guarded_target,
                    vmgen_mac.0,
                    policy,
                )
                .map_err(|e| {
                    CliError::state(format!(
                        "ExternalAnchorUnavailableOrCorrupt (VMGENID {domain}): {}",
                        e.into_io_error()
                    ))
                })?;
            chain = DynExternalAnchor(Arc::new(CompositeAntiRollbackAnchor::new(
                chain,
                vmgen_anchor,
            )));
        }

        Ok(Self {
            inner,
            composite: chain.0,
        })
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
    #[cfg(test)]
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
                .poison(invalid_anchor("external anchor disk diverged from memory"));
        }
        if disk.checkpoint.generation != expected.generation
            || !ct_eq_bytes(&disk.checkpoint.tag, &expected.tag)
        {
            return self.inner.poison(invalid_anchor(
                "external anchor checkpoint mismatch on ticket consume",
            ));
        }
        if let Some((consumed_gen, _)) = disk.consumed
            && consumed_gen >= expected.generation
        {
            return self.inner.poison(io::Error::new(
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
        self.composite.load()
    }

    fn advance(&self, checkpoint: LedgerCheckpoint) -> io::Result<()> {
        self.composite.advance(checkpoint)
    }
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;
    use crate::cli::os_random_32;
    use qsag_asm::durable::RECORD_HEADER_BYTES;
    use std::fs::{File, OpenOptions};
    use std::io::Write;

    fn side_path(path: &Path, suffix: &str) -> PathBuf {
        let mut os = path.as_os_str().to_os_string();
        os.push(suffix);
        PathBuf::from(os)
    }

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
        let same_cfg = AnchorConfig::dir_only(
            vault.to_str().unwrap(),
            Some(vault.to_str().unwrap().to_owned()),
            true,
        );
        assert!(
            same_cfg
                .validate_isolation(&[sk.to_str().unwrap()], &[], true)
                .is_err()
        );

        // 2. Alias via `vault/.` or symlink to `vault` is also refused unconditionally.
        let dot_cfg = AnchorConfig::dir_only(vault.join(".").to_str().unwrap(), None, true);
        assert!(
            dot_cfg
                .validate_isolation(&[sk.to_str().unwrap()], &[], false)
                .is_err()
        );
        let link = root.join("anchor-link");
        std::os::unix::fs::symlink(&anchor, &link).unwrap();
        let link_cfg = AnchorConfig::dir_only(
            link.to_str().unwrap(),
            Some(vault.to_str().unwrap().to_owned()),
            true,
        );
        assert!(
            link_cfg
                .validate_isolation(&[sk.to_str().unwrap()], &[], false)
                .is_err()
        );

        // 3. Nested anchor inside `--vault-dir` is refused even with allow_single_disk.
        let nested = vault.join("nested-anchor");
        let nested_cfg = AnchorConfig::dir_only(
            nested.to_str().unwrap(),
            Some(vault.to_str().unwrap().to_owned()),
            true,
        );
        assert!(
            nested_cfg
                .validate_isolation(&[sk.to_str().unwrap()], &[], true)
                .is_err()
        );

        // 4. Decoy `--vault-dir` while `sk` lives outside it is refused.
        let outside_sk = root.join("outside.sk");
        let decoy_cfg = AnchorConfig::dir_only(
            anchor.to_str().unwrap(),
            Some(vault.to_str().unwrap().to_owned()),
            true,
        );
        assert!(
            decoy_cfg
                .validate_isolation(&[outside_sk.to_str().unwrap()], &[], false)
                .is_err()
        );

        // 5. Same filesystem device without `allow_single_disk` is refused; with it, accepted.
        let strict_cfg = AnchorConfig::dir_only(
            anchor.to_str().unwrap(),
            Some(vault.to_str().unwrap().to_owned()),
            false,
        );
        assert!(
            strict_cfg
                .validate_isolation(&[sk.to_str().unwrap()], &[], false)
                .is_err()
        );
        let single_disk_cfg = AnchorConfig::dir_only(
            anchor.to_str().unwrap(),
            Some(vault.to_str().unwrap().to_owned()),
            true,
        );
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
        let cfg = AnchorConfig::dir_only(
            anchor_dir.to_str().unwrap(),
            Some(vault.to_str().unwrap().to_owned()),
            true,
        );
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
        let rec_path =
            anchor_record_path(cfg.anchor_dir.as_deref().unwrap(), "ceremony", &key_id);
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
                cfg: AnchorConfig::dir_only(
                    root.join("anchor").to_str().unwrap(),
                    Some(vault.to_str().unwrap().to_owned()),
                    true,
                ),
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
            anchor_record_path(self.cfg.anchor_dir.as_deref().unwrap(), domain, key_id)
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
            let cfg = AnchorConfig::dir_only(anchor.to_str().unwrap(), None, true);
            let err = cfg
                .validate_isolation(&[sk.to_str().unwrap()], &[], true)
                .err()
                .unwrap();
            assert!(err.message.contains("overlap or nest"), "{}", err.message);
        }
        let sibling = AnchorConfig::dir_only(root.join("anchor").to_str().unwrap(), None, true);
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
        assert_eq!(good.len(), RECORD_HEADER_BYTES + ANCHOR_RECORD_LEN);
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
        for len in [
            0,
            1,
            RECORD_HEADER_BYTES,
            RECORD_HEADER_BYTES + 8,
            RECORD_HEADER_BYTES + ANCHOR_PAYLOAD_LEN,
            good.len() - 1,
        ] {
            refused(&good[..len]);
        }
        refused(&[&good[..], &[0u8]].concat());
        // One flipped bit in the record header (magic, lock seal) and in every field:
        // magic, domain, key, generation, tag, consumed flag, consumed generation,
        // ceremony id, MAC.
        for at in [0, 8] {
            let mut bytes = good.clone();
            bytes[at] ^= 1;
            refused(&bytes);
        }
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
            bytes[RECORD_HEADER_BYTES + at] ^= 1;
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
        assert_eq!(
            anchor
                .inner
                .read_verified_disk_state()
                .unwrap()
                .unwrap()
                .consumed,
            None
        );
        // Reopening cannot resurrect a latch from the retired ceremony generation.
        drop(anchor);
        let anchor = slot.open("ceremony", key_id).unwrap();
        assert_eq!(
            anchor
                .inner
                .read_verified_disk_state()
                .unwrap()
                .unwrap()
                .consumed,
            None
        );
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
    fn interrupted_write_leftover_does_not_block_the_next_write() {
        let slot = Slot::new("leftover");
        let key_id = [0x61; 32];
        let anchor = slot.provision("ceremony", key_id);
        anchor.advance(ckpt(1, 0xAA)).unwrap();
        drop(anchor);
        let path = slot.record("ceremony", &key_id);
        let leftover = side_path(&path, ".tmp");
        let unrelated = side_path(&path, ".note.tmp");
        use std::io::Write;
        qsag_asm::durable::no_follow_options()
            .unwrap()
            .write(true)
            .create_new(true)
            .open(&leftover)
            .unwrap()
            .write_all(b"half a record")
            .unwrap();
        std::fs::write(&unrelated, b"keep").unwrap();
        let anchor = slot.open("ceremony", key_id).unwrap();
        assert_eq!(anchor.load().unwrap(), Some(ckpt(1, 0xAA)));
        anchor.advance(ckpt(2, 0xBB)).unwrap();
        assert!(!leftover.exists());
        assert!(unrelated.exists());
        assert_eq!(anchor.load().unwrap(), Some(ckpt(2, 0xBB)));
    }

    #[test]
    fn mirrored_directory_anchor_survives_loss_of_either_slot() {
        for lost in ["slot_a", "slot_b"] {
            let slot = Slot::new(&format!("mirror-{lost}"));
            let key_id = [0x71; 32];
            let anchor = slot.provision("ceremony", key_id);
            anchor.advance(ckpt(1, 0x11)).unwrap();
            anchor.advance(ckpt(4, 0x44)).unwrap();
            drop(anchor);

            let mirror_dir = anchor_mirror_dir_path(
                slot.cfg.anchor_dir.as_deref().unwrap(),
                "ceremony",
                &key_id,
            );
            std::fs::write(mirror_dir.join(lost), b"corrupt-slot").unwrap();

            let reopened = slot.open("ceremony", key_id).unwrap();
            assert_eq!(reopened.load().unwrap(), Some(ckpt(4, 0x44)));
            assert!(reopened.advance(ckpt(3, 0x33)).is_err());
            drop(reopened);

            let reopened = slot.open("ceremony", key_id).unwrap();
            reopened.advance(ckpt(5, 0x55)).unwrap();
            assert_eq!(reopened.load().unwrap(), Some(ckpt(5, 0x55)));
        }
    }

    #[derive(Clone)]
    struct TestTpm2Device {
        nv_index: u32,
        counter: Arc<Mutex<u64>>,
    }

    impl Tpm2Transport for TestTpm2Device {
        fn transmit(
            &self,
            cmd: &[u8],
        ) -> Result<Vec<u8>, qsag_core::anti_rollback::AntiRollbackError> {
            use qsag_core::anti_rollback::{
                AntiRollbackError, TPM_CC_NV_INCREMENT, TPM_CC_NV_READ, TPM_RC_SUCCESS,
                TPM_ST_SESSIONS,
            };
            if cmd.len() < 18 {
                return Err(AntiRollbackError::ProtocolFramingError("short cmd"));
            }
            let cc = u32::from_be_bytes([cmd[6], cmd[7], cmd[8], cmd[9]]);
            let nv = u32::from_be_bytes([cmd[14], cmd[15], cmd[16], cmd[17]]);
            if nv != self.nv_index {
                return Err(AntiRollbackError::Tpm2ResponseError(0x0000_018B));
            }
            let params: Vec<u8> = match cc {
                TPM_CC_NV_READ => {
                    let val = *self.counter.lock().unwrap();
                    let mut p = Vec::with_capacity(10);
                    p.extend_from_slice(&8u16.to_be_bytes());
                    p.extend_from_slice(&val.to_be_bytes());
                    p
                }
                TPM_CC_NV_INCREMENT => {
                    *self.counter.lock().unwrap() += 1;
                    Vec::new()
                }
                _ => return Err(AntiRollbackError::Tpm2ResponseError(0x0000_0143)),
            };
            let total_len = (10 + 4 + params.len() + 5) as u32;
            let mut rsp = Vec::with_capacity(total_len as usize);
            rsp.extend_from_slice(&TPM_ST_SESSIONS.to_be_bytes());
            rsp.extend_from_slice(&total_len.to_be_bytes());
            rsp.extend_from_slice(&TPM_RC_SUCCESS.to_be_bytes());
            rsp.extend_from_slice(&(params.len() as u32).to_be_bytes());
            rsp.extend_from_slice(&params);
            rsp.extend_from_slice(&0u16.to_be_bytes());
            rsp.push(0x01);
            rsp.extend_from_slice(&0u16.to_be_bytes());
            Ok(rsp)
        }
    }

    #[test]
    fn composite_tpm2_vmgenid_and_u128_ceremony_context_roundtrip_and_detect_rollback() {
        let args = Args::parse(
            &[
                "--anchor-tpm-nv".into(),
                "0x01800007".into(),
                "--anchor-vmgenid".into(),
                "--spend-amount".into(),
                "340282366920938463463374607431768211455".into(),
            ],
            &["anchor-tpm-nv", "spend-amount"],
            &["anchor-vmgenid"],
        )
        .unwrap();
        let ctx = parse_ceremony_context(&args, 9).unwrap();
        assert_eq!(ctx.spend_amount, u128::MAX);
        assert_eq!(ctx.mpc_nonce_epoch, 9);

        let parsed_cfg = AnchorConfig::from_args(&args).unwrap().unwrap();
        assert_eq!(parsed_cfg.tpm_nv_index, Some(0x0180_0007));
        assert!(parsed_cfg.vmgenid);
        assert!(parsed_cfg.anchor_dir.is_none());

        let root = temp_root("tpm-vmgen");
        let vault = root.join("vault");
        private_dir(vault.to_str().unwrap(), true).unwrap();
        let sk_path = vault.join("sk");
        let sk_str = sk_path.to_str().unwrap();

        let tpm = TestTpm2Device {
            nv_index: 0x0180_0007,
            counter: Arc::new(Mutex::new(41)),
        };
        let key_id = [0x88; 32];
        let mac_key = [0x99; 32];

        let anchor = FsExternalMountAnchor::provision_fresh_with_tpm(
            &parsed_cfg,
            &[sk_str],
            &[],
            "ceremony",
            key_id,
            mac_key,
            tpm.clone(),
        )
        .unwrap();
        assert_eq!(anchor.load().unwrap(), None);
        anchor.advance(ckpt(1, 0xA1)).unwrap();
        assert_eq!(*tpm.counter.lock().unwrap(), 42);
        anchor.advance(ckpt(2, 0xB2)).unwrap();
        assert_eq!(*tpm.counter.lock().unwrap(), 43);
        drop(anchor);

        let reopened = FsExternalMountAnchor::open_existing_with_tpm(
            &parsed_cfg,
            &[sk_str],
            &[],
            "ceremony",
            key_id,
            mac_key,
            tpm.clone(),
        )
        .unwrap();
        assert_eq!(reopened.load().unwrap(), Some(ckpt(2, 0xB2)));
        drop(reopened);

        // Simulate local disk snapshot rollback while hardware TPM2 counter remains at 43:
        // bump hardware counter to 44 (as if another signature occurred before snapshot restore).
        *tpm.counter.lock().unwrap() = 44;
        assert!(
            FsExternalMountAnchor::open_existing_with_tpm(
                &parsed_cfg,
                &[sk_str],
                &[],
                "ceremony",
                key_id,
                mac_key,
                tpm,
            )
            .is_err()
        );
        std::fs::remove_dir_all(root).unwrap();
    }
}
