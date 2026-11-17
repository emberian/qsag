//! External monotone anchor backend (`FsExternalMountAnchor`) for CLI custody state.
//!
//! Defends local stateful signing against vault-directory rollback using independent
//! monotone storage, optionally composed with VM snapshot/clone detection via
//! [`CompositeAntiRollbackAnchor`]:
//! 1. `--anchor-dir <dir>`: a `LockedRecord` single-use ceremony ticket seal (`QSAGANC1`) paired
//!    with a mirrored dual-slot [`FsDirectoryMonotoneAnchor`] (`TwoSlotRecord` surviving loss of
//!    either slot).
//! 2. `--anchor-tpm-nv <nv-index>`: hardware TPM 2.0 `TPM_NT_COUNTER` NV index accessed directly
//!    through `/dev/tpmrm0` ([`Tpm2NvMonotoneAnchor<DevTpmRm0>`]). Multi-domain workflows
//!    treat this index as a range base: RSS quorum party `p` uses `base + 2*p` for its
//!    belt and `base + 2*p + 1` for its ceremony (six counters); committee validator
//!    `i` uses `base + i`, with `base + validators` for the ceremony. All indices must
//!    be defined (`tpm2_nvdefine <index> -C o -s 8 -a "authread|authwrite|no_da|nt=counter"`)
//!    and never written before enrollment. Do not undefine enrolled counters.
//!    Every index is a counter of its own, and the TPM is asked to prove it: an
//!    enrolling command reads each index's public area (`TPM2_NV_ReadPublic`) before it
//!    writes anything and refuses one that is not a plain `TPM_NT_COUNTER` or that has
//!    ever been incremented. So an index already used by another key, vault or policy
//!    ledger, or one inside this command's own `--policy-anchor-tpm-nv`, is refused at
//!    enrollment rather than surfacing later as a false rollback.
//!
//!    Enrollments made while all anchors of a quorum or committee shared one index
//!    cannot open. `quorum sign` and `aggregate` recognise them and name the repair:
//!    `quorum reanchor-tpm` / `aggregate --reanchor-tpm-nv`
//!    ([`AnchorConfig::reanchor_shared_tpm_index`]), which proves the disk is the
//!    newest state the shared counter has seen and moves each anchor to a new counter.
//! 3. `--anchor-vmgenid`: hypervisor generation-ID + kernel `boot_id` + inode continuity fence
//!    ([`HypervisorGenerationAnchor<LinuxSysfsVmGenSource>`]). This is snapshot/clone detection
//!    only, not protection against in-guest file restore. It requires a disjoint-device
//!    directory anchor or TPM counter. Without hypervisor VMGENID, it only pins boot/file identity.
//!    A vault enrolled with this guard alone has no re-anchoring path: it kept no
//!    monotone record outside its own disk, so its current state cannot be told from a
//!    restored one. Such a key is retired and a new one enrolled.

use std::io;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};

use qsag_accel::ct::{ct_eq_bytes, ct_zeroize_bytes};
use qsag_accel::keccak::cshake256_framed_32;
use qsag_asm::durable::LockedRecord;
use qsag_core::anti_rollback::{
    CompositeAntiRollbackAnchor, DevTpmRm0, HypervisorGenerationAnchor, LinuxSysfsVmGenSource,
    Tpm2NvMonotoneAnchor, Tpm2Transport, VmGenPolicy, inspect_tpm2_seal, is_valid_tpm2_nv_index,
    tpm2_nv_read_counter, tpm2_nv_read_public,
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
    .map_err(|_| CliError::usage("--anchor-tpm-nv must be a 32-bit NV index (e.g. 0x01800001)"))?;
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
    /// Select an independent counter from a workflow's contiguous NV range. The CLI
    /// never defines or resets NV indices: the operator must provision every counter
    /// in this exclusive range, with the same authorization, before enrollment.
    /// Checking the entire range on every selection prevents overflow/aliasing and
    /// keeps enrollment and recovery on the same deterministic allocation.
    pub fn tpm_slot(&self, offset: u32, slots: u32) -> Result<Self, CliError> {
        if slots == 0 || offset >= slots {
            return Err(CliError::state("invalid TPM2 anchor domain allocation"));
        }
        let mut scoped = self.clone();
        if let Some(base) = self.tpm_nv_index {
            let last = base
                .checked_add(slots - 1)
                .filter(|n| is_valid_tpm2_nv_index(*n));
            if !is_valid_tpm2_nv_index(base) || last.is_none() {
                return Err(CliError::usage(format!(
                    "TPM2 anchor range starting at {base:#010x} needs {slots} distinct NV indices within 0x01000000..=0x01ffffff"
                )));
            }
            scoped.tpm_nv_index = Some(base + offset);
        }
        Ok(scoped)
    }

    /// Validate a workflow's whole NV range against the TPM before any state of the
    /// command exists. Every index must be a counter an anchor can use
    /// (`Tpm2NvPublic::check_anchor_counter`). For [`TpmUse::Enroll`] every counter
    /// must never have been incremented: a written counter backs another anchor (in
    /// this vault, another vault, or the policy ledger) or an abandoned enrollment,
    /// and two seals on one counter invalidate each other. For [`TpmUse::Reopen`]
    /// every counter must be written and readable with the configured authorization.
    pub fn check_tpm_range(&self, slots: u32, purpose: TpmUse) -> Result<(), CliError> {
        self.tpm_slot(0, slots)?;
        let Some(base) = self.tpm_nv_index else {
            return Ok(());
        };
        let password = read_tpm_password(self.tpm_auth_env.as_deref())?;
        self.with_tpm(|tpm| probe_tpm_range(tpm, base, slots, &password, purpose))
    }

    /// Run `f` against the configured TPM (the test thread's model when one is installed).
    fn with_tpm<R>(
        &self,
        f: impl FnOnce(&dyn Tpm2Transport) -> Result<R, CliError>,
    ) -> Result<R, CliError> {
        #[cfg(all(test, unix))]
        if let Some(tpm) = tpm_model::active() {
            return f(&tpm);
        }
        let dev_path = self
            .tpm_device_path
            .as_deref()
            .unwrap_or(DevTpmRm0::DEFAULT_DEVICE_PATH);
        let dev = DevTpmRm0::open_path(dev_path).map_err(|e| {
            CliError::state(format!(
                "opening TPM2 resource manager {dev_path}: {}",
                e.into_io_error()
            ))
        })?;
        f(&dev)
    }

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
        let tpm_nv_index = args
            .get("anchor-tpm-nv")
            .map(parse_tpm_nv_index)
            .transpose()?;
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
        require_vmgenid_backing(vmgenid, anchor_dir.is_some(), tpm_nv_index.is_some())?;
        let any_anchor = anchor_dir.is_some() || tpm_nv_index.is_some();
        if !any_anchor && vault_dir.is_some() {
            return Err(CliError::usage(
                "--vault-dir requires an anchor (--anchor-dir or --anchor-tpm-nv)",
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
    /// `dir_option` is "anchor-dir" or "policy-anchor-dir").
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
        // An independently named output anchor has no hardware options of its own.
        let hardware_options = match dir_option {
            "policy-anchor-dir" => Some((
                "policy-anchor-tpm-nv",
                "policy-anchor-tpm-device",
                "policy-anchor-tpm-auth-env",
                "policy-vmgenid",
                "policy-vmgenid-strict",
            )),
            "anchor-dir" => Some((
                "anchor-tpm-nv",
                "anchor-tpm-device",
                "anchor-tpm-auth-env",
                "anchor-vmgenid",
                "anchor-vmgenid-strict",
            )),
            _ => None,
        };
        let (tpm_nv_index, tpm_device_path, tpm_auth_env, vmgenid, vmgenid_strict) =
            match hardware_options {
                Some((nv_option, device_option, auth_option, vmgenid_flag, strict_flag)) => {
                    let tpm_nv = args.get(nv_option).map(parse_tpm_nv_index).transpose()?;
                    let tpm_dev = args.get(device_option).map(str::to_owned);
                    let tpm_auth = args.get(auth_option).map(str::to_owned);
                    let vmg = args.flag(vmgenid_flag);
                    let vmg_strict = args.flag(strict_flag);
                    if tpm_nv.is_none() && (tpm_dev.is_some() || tpm_auth.is_some()) {
                        return Err(CliError::usage(format!(
                            "--{device_option} and --{auth_option} require --{nv_option}"
                        )));
                    }
                    if vmg_strict && !vmg {
                        return Err(CliError::usage(format!(
                            "--{strict_flag} requires --{vmgenid_flag}"
                        )));
                    }
                    (tpm_nv, tpm_dev, tpm_auth, vmg, vmg_strict)
                }
                None => (None, None, None, false, false),
            };

        require_vmgenid_backing(vmgenid, anchor_dir.is_some(), tpm_nv_index.is_some())?;
        if anchor_dir.is_none() && tpm_nv_index.is_none() {
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
        require_vmgenid_backing(
            self.vmgenid,
            self.anchor_dir.is_some(),
            self.tpm_nv_index.is_some(),
        )?;
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
        if other.id.0 == anchor.id.0 && self.vmgenid && self.tpm_nv_index.is_none() {
            return Err(CliError::state(
                "VMGENID provides snapshot/clone detection only; --anchor-dir must be on a disjoint device unless --anchor-tpm-nv is also supplied; --allow-single-disk-anchor cannot waive this requirement",
            ));
        }
        if other.id.0 == anchor.id.0 && !self.allow_single_disk {
            return Err(CliError::state(format!(
                "--anchor-dir resides on the same filesystem device as {what}; mount an independent device or pass --allow-single-disk-anchor"
            )));
        }
        Ok(())
    }
}

// VM/file identities attest continuity, not a signing-state floor. In particular,
// restoring authenticated local records in place leaves these identities intact.
fn require_vmgenid_backing(vmgenid: bool, directory: bool, tpm: bool) -> Result<(), CliError> {
    if vmgenid && !directory && !tpm {
        return Err(CliError::usage(
            "VMGENID provides snapshot/clone detection only; combine with --anchor-dir on a disjoint device or --anchor-tpm-nv (policy vaults use the corresponding policy options). A vault that was enrolled with VMGENID alone cannot be re-anchored: it kept no monotone record outside its own disk, so nothing distinguishes its current state from a restored one and its one-time leaves may already have been spent twice. Retire that key and enroll a new one with a monotone anchor",
        ));
    }
    Ok(())
}

/// Refuse a `--policy-anchor-tpm-nv` index inside the `slots` counters this command
/// reserves from `--anchor-tpm-nv`: the policy ledger's anchor and a key anchor would
/// share a counter. Reads only the options, so commands call it before anything else.
pub fn refuse_policy_tpm_overlap(args: &Args, slots: u32) -> Result<(), CliError> {
    let index = |option: &str| args.get(option).map(parse_tpm_nv_index).transpose();
    let (Some(base), Some(policy)) = (index("anchor-tpm-nv")?, index("policy-anchor-tpm-nv")?)
    else {
        return Ok(());
    };
    if policy >= base && policy - base < slots {
        return Err(CliError::usage(format!(
            "--policy-anchor-tpm-nv {policy:#010x} lies inside the {slots} counter(s) reserved from --anchor-tpm-nv {base:#010x}; every anchor needs its own TPM2 NV counter"
        )));
    }
    Ok(())
}

/// The TPM checks every enrolling command makes right after parsing its options and
/// before it writes anything: the `slots` counters reserved from `--anchor-tpm-nv`
/// exist, can back an anchor and have never been used, and the policy ledger's
/// counter (if this command names one) is not among them.
pub fn preflight_tpm_enrollment(
    cfg: Option<&AnchorConfig>,
    args: &Args,
    slots: u32,
) -> Result<(), CliError> {
    let Some(cfg) = cfg else {
        return Ok(());
    };
    refuse_policy_tpm_overlap(args, slots)?;
    cfg.check_tpm_range(slots, TpmUse::Enroll)
}

/// What a command is about to do with its TPM2 NV counters.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TpmUse {
    /// Bind new anchors: the counters must never have been incremented.
    Enroll,
    /// Open existing anchors: the counters must be in use.
    Reopen,
}

/// How to create a counter the anchor accepts, for error messages.
const TPM_DEFINE_HINT: &str = "define it with: tpm2_nvdefine <index> -C o -s 8 -a \"authread|authwrite|no_da|nt=counter\" [-p <auth>]";

fn probe_tpm_range(
    transport: &dyn Tpm2Transport,
    base: u32,
    slots: u32,
    password: &[u8],
    purpose: TpmUse,
) -> Result<(), CliError> {
    for index in base..base + slots {
        let slot = format!(
            "TPM2 NV counter {index:#010x} (slot {} of the {slots} reserved from {base:#010x})",
            index - base
        );
        let public = tpm2_nv_read_public(transport, index).map_err(|e| {
            CliError::state(format!(
                "{slot} is not defined or cannot be read: {}; {TPM_DEFINE_HINT}",
                e.into_io_error()
            ))
        })?;
        public.check_anchor_counter(index).map_err(|e| {
            CliError::state(format!("{slot}: {}; {TPM_DEFINE_HINT}", e.into_io_error()))
        })?;
        match (purpose, public.is_written()) {
            (TpmUse::Enroll, true) => {
                return Err(CliError::state(format!(
                    "{slot} has already been incremented: it backs another anchor (another key, vault or policy ledger) or an abandoned enrollment. Two anchors on one counter invalidate each other, so enrollment needs counters that were never written: choose unused indices, or undefine and define this one again (tpm2_nvundefine {index:#010x} -C o; {TPM_DEFINE_HINT})"
                )));
            }
            (TpmUse::Reopen, false) => {
                return Err(CliError::state(format!(
                    "{slot} was never incremented, so no anchor was enrolled on it: wrong index or range base, another TPM, or the index was redefined"
                )));
            }
            (TpmUse::Enroll, false) => {}
            (TpmUse::Reopen, true) => {
                tpm2_nv_read_counter(transport, index, password).map_err(|e| {
                    CliError::state(format!(
                        "{slot} cannot be read with the configured authorization: {}",
                        e.into_io_error()
                    ))
                })?;
            }
        }
    }
    Ok(())
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
            "key requires an external monotone anchor (--anchor-dir or --anchor-tpm-nv)",
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
pub fn floor_checkpoint(
    domain: &[u8],
    key_id: &[u8; 32],
    floor_value: u64,
) -> Result<LedgerCheckpoint, CliError> {
    let generation = floor_value
        .checked_add(1)
        .ok_or_else(|| CliError::state("external anchor floor exhausted"))?;
    let tag = cshake256_framed_32(
        b"QSAG.CLI.ANCHOR.FLOOR.V1",
        &[
            domain,
            key_id,
            &generation.to_be_bytes(),
            &floor_value.to_be_bytes(),
        ],
    );
    Ok(LedgerCheckpoint { generation, tag })
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
        let (domain_hash, state) = self.decode_any_backend_binding(bytes)?;
        if !ct_eq_bytes(&domain_hash, &self.domain_hash) {
            return Err(invalid_anchor("external anchor header binding mismatch"));
        }
        Ok(state)
    }

    /// Authenticate a record for this key and return the domain/backend binding it was
    /// written under along with its state, whatever that binding is.
    fn decode_any_backend_binding(
        &self,
        bytes: &[u8],
    ) -> io::Result<([u8; 32], AnchorRecordState)> {
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
        if &payload[..8] != ANCHOR_MAGIC || !ct_eq_bytes(&payload[40..72], &self.key_id) {
            return Err(invalid_anchor("external anchor header binding mismatch"));
        }
        let domain_hash: [u8; 32] = payload[8..40].try_into().unwrap();
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
        Ok((
            domain_hash,
            AnchorRecordState {
                checkpoint: LedgerCheckpoint { generation, tag },
                consumed,
            },
        ))
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
/// - optional hypervisor generation-ID + `boot_id` + inode continuity fork guard
///   [`HypervisorGenerationAnchor`] (`--anchor-vmgenid`), requiring independent monotone backing
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
    format!(
        "{}-{}",
        sanitize_domain_prefix(domain),
        to_hex(&slot_digest)
    )
}

fn remove_file_if_present(path: &Path, label: &'static str) -> Result<(), CliError> {
    match std::fs::remove_file(path) {
        Ok(()) => Ok(()),
        Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(()),
        Err(e) => Err(CliError::io(label, e)),
    }
}

/// Remove the local uncommitted `.target` fork-guard marker for a never-committed enrollment
/// attempt. The caller must hold the destination vault lock and verify that it has no
/// committed meta. External anti-rollback `.anchor` / `.mirror` state and `.lock` sidecars are
/// intentionally NEVER unlinked from local recovery metadata (`pending_*` in local vault JSON is
/// untrusted under the external-anchor threat model); fresh per-attempt `anchor_key_id` nonces
/// isolate retries without deleting external state.
pub fn remove_uncommitted_guarded_target(
    vault_dir: &str,
    domain: &str,
    key_id: &[u8; 32],
) -> Result<(), CliError> {
    let local = Path::new(vault_dir).join(format!(".qsag-{}.target", slot_stem(domain, key_id)));
    remove_file_if_present(&local, "removing uncommitted fork-guard target")
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

/// The domain and enrolled backends a ticket record is bound to. Authenticating the
/// hardware and fork-guard requirements in the record header stops a TPM+directory
/// anchor from being reopened with only `--anchor-dir`, which would silently drop the
/// hardware fence. The directory-only encoding is the original one.
fn backend_binding_hash(config: &AnchorConfig, domain: &str) -> [u8; 32] {
    if config.tpm_nv_index.is_none() && !config.vmgenid {
        return cshake256_framed_32(b"QSAG.CLI.ANCHOR.DOMAIN.V1", &[domain.as_bytes()]);
    }
    let backend_flags = [
        u8::from(config.anchor_dir.is_some()),
        u8::from(config.tpm_nv_index.is_some()),
        u8::from(config.vmgenid),
        u8::from(config.vmgenid_strict),
    ];
    cshake256_framed_32(
        b"QSAG.CLI.ANCHOR.DOMAIN.V1",
        &[
            domain.as_bytes(),
            &backend_flags,
            &config.tpm_nv_index.unwrap_or_default().to_be_bytes(),
        ],
    )
}

/// Where a domain's ticket record and TPM seal live under `config`.
fn domain_record_paths(
    config: &AnchorConfig,
    custody_files: &[&str],
    explicit_dirs: &[&str],
    domain: &str,
    key_id: &[u8; 32],
) -> Result<(PathBuf, PathBuf), CliError> {
    let stem = slot_stem(domain, key_id);
    Ok(match &config.anchor_dir {
        Some(dir) => (
            anchor_record_path(dir, domain, key_id),
            Path::new(dir).join(format!("{stem}.tpm")),
        ),
        None => {
            let dir = resolve_custody_dir(config, custody_files, explicit_dirs)?;
            (
                dir.join(format!(".qsag-{stem}.anchor")),
                dir.join(format!(".qsag-{stem}.tpm")),
            )
        }
    })
}

/// One anchor domain of a multi-anchor workflow, with its slot in the workflow's
/// TPM2 NV counter range.
pub struct TpmDomain<'a> {
    pub slot: u32,
    pub domain: &'a str,
    pub key_id: [u8; 32],
    pub mac_key: [u8; 32],
}

impl Drop for TpmDomain<'_> {
    fn drop(&mut self) {
        ct_zeroize_bytes(&mut self.mac_key);
    }
}

/// A domain's ticket record, authenticated, with the binding it was written under.
struct TicketView {
    inner: AnchorInner,
    binding: [u8; 32],
    state: AnchorRecordState,
}

fn open_ticket(
    config: &AnchorConfig,
    record_path: &Path,
    domain: &TpmDomain<'_>,
) -> Result<TicketView, CliError> {
    let unavailable = |e: io::Error| {
        CliError::state(format!(
            "ExternalAnchorUnavailableOrCorrupt ({}): {e}",
            domain.domain
        ))
    };
    let inner = AnchorInner {
        record: LockedRecord::open_existing(record_path).map_err(unavailable)?,
        poisoned: AtomicBool::new(false),
        domain_hash: backend_binding_hash(config, domain.domain),
        key_id: domain.key_id,
        mac_key: domain.mac_key,
        state: Mutex::new(None),
        written: AtomicBool::new(true),
    };
    let bytes = inner
        .record
        .read_bounded(ANCHOR_RECORD_LEN)
        .map_err(unavailable)?;
    let (binding, state) = inner
        .decode_any_backend_binding(&bytes)
        .map_err(unavailable)?;
    Ok(TicketView {
        inner,
        binding,
        state,
    })
}

impl AnchorConfig {
    /// Whether these `domains` were enrolled before each domain had its own counter:
    /// more than one of their ticket records is bound to the single index
    /// `--anchor-tpm-nv` names. Such a vault cannot open (every seal but the newest
    /// lags the shared counter); [`Self::reanchor_shared_tpm_index`] repairs it.
    pub fn shared_tpm_index_enrollment(
        &self,
        custody_files: &[&str],
        explicit_dirs: &[&str],
        domains: &[TpmDomain<'_>],
    ) -> Result<bool, CliError> {
        if self.tpm_nv_index.is_none() {
            return Ok(false);
        }
        let mut shared = 0;
        for domain in domains {
            let (record_path, _) = domain_record_paths(
                self,
                custody_files,
                explicit_dirs,
                domain.domain,
                &domain.key_id,
            )?;
            let Ok(ticket) = open_ticket(self, &record_path, domain) else {
                continue;
            };
            if ct_eq_bytes(&ticket.binding, &backend_binding_hash(self, domain.domain)) {
                shared += 1;
            }
        }
        Ok(shared > 1)
    }

    /// Move every domain of a shared-index enrollment (`self` names the shared index)
    /// onto its own never-written counter in the range starting at `new_base`, keeping
    /// each domain's checkpoint.
    ///
    /// # Why this is safe against a rolled-back disk
    /// On a shared counter a domain can only be opened, and so only advanced, while
    /// its seal equals the counter, and advancing keeps it equal. So at any time
    /// exactly one domain's seal equals the live counter (the last one to advance) and
    /// every other domain is still in the single state it was enrolled in, which a
    /// rollback cannot change. The domains not yet moved are therefore all current
    /// if and only if the largest count among their seals equals the live counter.
    /// That is checked before anything is written; a vault whose newest seal is
    /// behind the counter is refused as rolled back or foreign.
    ///
    /// Domains are moved in ascending order of their sealed count, the one that
    /// matches the counter last, so an interrupted run leaves the proof intact for
    /// the domains that remain and can simply be run again. A domain already moved
    /// is verified against its own new counter instead.
    pub fn reanchor_shared_tpm_index(
        &self,
        new_base: u32,
        slots: u32,
        custody_files: &[&str],
        explicit_dirs: &[&str],
        domains: &[TpmDomain<'_>],
    ) -> Result<(), CliError> {
        let shared_index = self.tpm_nv_index.ok_or_else(|| {
            CliError::usage("re-anchoring needs the shared index as --anchor-tpm-nv")
        })?;
        let new_cfg = AnchorConfig {
            tpm_nv_index: Some(new_base),
            ..self.clone()
        };
        new_cfg.tpm_slot(0, slots)?;
        if shared_index >= new_base && shared_index - new_base < slots {
            return Err(CliError::usage(format!(
                "the new counter range starting at {new_base:#010x} contains the shared index {shared_index:#010x}"
            )));
        }
        if domains.len() as u64 != u64::from(slots) {
            return Err(CliError::state(
                "re-anchoring needs every domain of the enrollment",
            ));
        }
        self.validate_isolation(custody_files, explicit_dirs, false)?;
        let password = read_tpm_password(self.tpm_auth_env.as_deref())?;
        let refused = |why: String| {
            CliError::state(format!(
                "shared TPM2 NV index {shared_index:#010x} cannot be re-anchored: {why}"
            ))
        };

        // Phase 1: authenticate every domain and establish that the old state is current.
        struct Pending<'a> {
            domain: &'a TpmDomain<'a>,
            ticket: TicketView,
            seal_path: PathBuf,
            new_index: u32,
            new_binding: [u8; 32],
            // The count of a seal still on the shared index; `None` once it has moved.
            shared_count: Option<u64>,
        }
        let mut pending = Vec::with_capacity(domains.len());
        for domain in domains {
            let scoped = new_cfg.tpm_slot(domain.slot, slots)?;
            let new_index = scoped.tpm_nv_index.unwrap_or(new_base);
            let new_binding = backend_binding_hash(&scoped, domain.domain);
            let (record_path, seal_path) = domain_record_paths(
                self,
                custody_files,
                explicit_dirs,
                domain.domain,
                &domain.key_id,
            )?;
            let ticket = open_ticket(self, &record_path, domain)?;
            let ticket_moved = ct_eq_bytes(&ticket.binding, &new_binding);
            if !ticket_moved
                && !ct_eq_bytes(&ticket.binding, &backend_binding_hash(self, domain.domain))
            {
                return Err(refused(format!(
                    "the {} anchor record is bound to neither that index nor its new counter {new_index:#010x}",
                    domain.domain
                )));
            }
            let tpm_mac =
                derive_sub_mac(&domain.mac_key, b"tpm2_nv", domain.domain, &domain.key_id);
            let shared_count = match inspect_tpm2_seal(&seal_path, shared_index, tpm_mac.0) {
                Ok(seal) if !ticket_moved => {
                    if seal.commit_in_flight
                        || seal.checkpoint.generation != ticket.state.checkpoint.generation
                        || !ct_eq_bytes(&seal.checkpoint.tag, &ticket.state.checkpoint.tag)
                    {
                        return Err(refused(format!(
                            "the {} TPM seal and anchor record disagree or hold an interrupted commit",
                            domain.domain
                        )));
                    }
                    Some(seal.sealed_count)
                }
                Ok(_) => {
                    return Err(refused(format!(
                        "the {} anchor record was moved but its TPM seal was not",
                        domain.domain
                    )));
                }
                Err(_) => {
                    inspect_tpm2_seal(&seal_path, new_index, tpm_mac.0).map_err(|e| {
                        refused(format!(
                            "the {} TPM seal is bound to neither that index nor {new_index:#010x}: {}",
                            domain.domain,
                            e.into_io_error()
                        ))
                    })?;
                    None
                }
            };
            pending.push(Pending {
                domain,
                ticket,
                seal_path,
                new_index,
                new_binding,
                shared_count,
            });
        }
        if let Some(newest) = pending.iter().filter_map(|p| p.shared_count).max() {
            let live = self.with_tpm(|tpm| {
                tpm2_nv_read_counter(tpm, shared_index, &password).map_err(|e| {
                    refused(format!("the counter cannot be read: {}", e.into_io_error()))
                })
            })?;
            if newest != live {
                return Err(refused(format!(
                    "the newest seal on disk was written at count {newest} but the counter is at {live}: the disk is older than the TPM (rolled back), or something else used this index"
                )));
            }
        }

        // Phase 2: move the seals, the one that matches the counter last, then rebind
        // each ticket record. Each step is safe to repeat.
        pending.sort_by_key(|p| p.shared_count.unwrap_or(0));
        for p in &mut pending {
            let tpm_mac = derive_sub_mac(
                &p.domain.mac_key,
                b"tpm2_nv",
                p.domain.domain,
                &p.domain.key_id,
            );
            self.rebind_seal(
                &p.seal_path,
                shared_index,
                p.new_index,
                &password,
                tpm_mac.0,
            )
            .map_err(|e| {
                refused(format!(
                    "moving the {} seal to {:#010x}: {}",
                    p.domain.domain,
                    p.new_index,
                    e.into_io_error()
                ))
            })?;
            // The record keeps its lock identity (the seal pinned in the custody file);
            // only the backend binding in its authenticated header changes.
            p.ticket.inner.domain_hash = p.new_binding;
            p.ticket
                .inner
                .write_state(&p.ticket.state)
                .map_err(|e| refused(format!("rebinding the {} record: {e}", p.domain.domain)))?;
        }
        drop(pending);

        // Phase 3: every domain opens under the new layout.
        for domain in domains {
            let anchor = FsExternalMountAnchor::open_existing(
                &new_cfg.tpm_slot(domain.slot, slots)?,
                custody_files,
                explicit_dirs,
                domain.domain,
                domain.key_id,
                domain.mac_key,
            )?;
            anchor
                .load()
                .map_err(|e| refused(format!("verifying {} after the move: {e}", domain.domain)))?;
        }
        Ok(())
    }

    fn rebind_seal(
        &self,
        seal_path: &Path,
        shared_index: u32,
        new_index: u32,
        password: &[u8],
        mac_key: [u8; 32],
    ) -> Result<(), qsag_core::anti_rollback::AntiRollbackError> {
        #[cfg(all(test, unix))]
        if let Some(tpm) = tpm_model::active() {
            return Tpm2NvMonotoneAnchor::rebind_to_new_counter(
                tpm,
                seal_path,
                shared_index,
                new_index,
                password,
                mac_key,
            )
            .map(drop);
        }
        let dev_path = self
            .tpm_device_path
            .as_deref()
            .unwrap_or(DevTpmRm0::DEFAULT_DEVICE_PATH);
        Tpm2NvMonotoneAnchor::rebind_to_new_counter(
            DevTpmRm0::open_path(dev_path)?,
            seal_path,
            shared_index,
            new_index,
            password,
            mac_key,
        )
        .map(drop)
    }
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
        #[cfg(all(test, unix))]
        if let Some(tpm) = tpm_model::active() {
            return Self::open_composite(
                config,
                custody_files,
                explicit_dirs,
                domain,
                key_id,
                mac_key,
                true,
                Some(tpm),
            );
        }
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
        #[cfg(all(test, unix))]
        if let Some(tpm) = tpm_model::active() {
            return Self::open_composite(
                config,
                custody_files,
                explicit_dirs,
                domain,
                key_id,
                mac_key,
                false,
                Some(tpm),
            );
        }
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

        let domain_hash = backend_binding_hash(config, domain);
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
                crate::cli::write_new(
                    guarded_target.to_str().ok_or_else(|| {
                        CliError::usage("guarded custody target must be a UTF-8 path")
                    })?,
                    &domain_hash,
                    true,
                )?;
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
            let vmgen_anchor = HypervisorGenerationAnchor::<LinuxSysfsVmGenSource>::open_or_create(
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
            let expected = floor_checkpoint(domain, &self.inner.key_id, min_floor)?;
            if !ct_eq_bytes(&current.tag, &expected.tag) {
                return Err(CliError::state("ExternalAnchorFloorTagMismatch"));
            }
        }
        Ok(())
    }

    /// Ratchet a monotonic integer floor forward on the external anchor.
    pub fn advance_floor(&self, domain: &[u8], next_floor: u64) -> Result<(), CliError> {
        let ckpt = floor_checkpoint(domain, &self.inner.key_id, next_floor)?;
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

/// Installs the software TPM model (`qsag_core::anti_rollback::tpm2_model`) for
/// tests that drive the real CLI call chains, which open their own transport.
#[cfg(all(test, unix))]
pub(crate) mod tpm_model {
    use super::*;
    pub(crate) use qsag_core::anti_rollback::tpm2_model::ModelTpm2;
    use std::cell::RefCell;

    thread_local! {
        static ACTIVE: RefCell<Option<ModelTpm2>> = const { RefCell::new(None) };
    }

    /// The model this test thread installed, used in place of `/dev/tpmrm0`.
    pub(crate) fn active() -> Option<ModelTpm2> {
        ACTIVE.with(|t| t.borrow().clone())
    }

    /// Keeps a model installed for the current test thread.
    pub(crate) struct Installed(pub(crate) ModelTpm2);

    /// A TPM whose counters have reached `history`, with never-written anchor counters
    /// `first..first + count` (empty index authorization) defined.
    pub(crate) fn install(first: u32, count: u32, history: u64) -> Installed {
        let tpm = ModelTpm2::with_history(history);
        for nv_index in first..first + count {
            tpm.define_counter(nv_index, b"");
        }
        ACTIVE.with(|t| {
            assert!(t.borrow().is_none(), "one model TPM per test thread");
            *t.borrow_mut() = Some(tpm.clone());
        });
        Installed(tpm)
    }

    impl Drop for Installed {
        fn drop(&mut self) {
            ACTIVE.with(|t| *t.borrow_mut() = None);
        }
    }

    /// Rewrite a workflow enrolled under `layout` (one counter per domain) into the
    /// on-disk shape releases before per-domain counters produced: every ticket record
    /// and every seal bound to the one index `shared`, each seal holding the count the
    /// shared counter had right after that domain's own increment.
    pub(crate) fn make_shared_index_enrollment(
        tpm: &ModelTpm2,
        layout: &AnchorConfig,
        shared: u32,
        slots: u32,
        custody_files: &[&str],
        explicit_dirs: &[&str],
        domains: &[TpmDomain<'_>],
    ) {
        let legacy = AnchorConfig {
            tpm_nv_index: Some(shared),
            ..layout.clone()
        };
        for domain in domains {
            let scoped = layout.tpm_slot(domain.slot, slots).unwrap();
            let (record_path, seal_path) = domain_record_paths(
                layout,
                custody_files,
                explicit_dirs,
                domain.domain,
                &domain.key_id,
            )
            .unwrap();
            let mut ticket = open_ticket(&scoped, &record_path, domain).unwrap();
            assert_eq!(ticket.binding, backend_binding_hash(&scoped, domain.domain));
            ticket.inner.domain_hash = backend_binding_hash(&legacy, domain.domain);
            ticket.inner.write_state(&ticket.state).unwrap();
            Tpm2NvMonotoneAnchor::fixture_reseal_on_shared_counter(
                tpm.clone(),
                &seal_path,
                scoped.tpm_nv_index.unwrap(),
                shared,
                b"",
                derive_sub_mac(&domain.mac_key, b"tpm2_nv", domain.domain, &domain.key_id).0,
            )
            .unwrap();
        }
    }

    /// One enrolled anchor domain: honest storage reopens; an advance moves only its
    /// own counter `nv_index`; restoring every local record of the domain in place
    /// (ticket and TPM seal, inodes kept) is refused; the current records reopen.
    pub(crate) fn assert_domain_reopens_and_refuses_rollback(
        tpm: &ModelTpm2,
        config: &AnchorConfig,
        dir: &str,
        nv_index: u32,
        domain: &str,
        key_id: [u8; 32],
        mac_key: [u8; 32],
    ) {
        let scoped = AnchorConfig {
            tpm_nv_index: Some(nv_index),
            ..config.clone()
        };
        let stem = slot_stem(domain, &key_id);
        let files: Vec<PathBuf> = ["anchor", "tpm"]
            .iter()
            .map(|ext| Path::new(dir).join(format!(".qsag-{stem}.{ext}")))
            .collect();
        let read_all = || -> Vec<Vec<u8>> {
            files
                .iter()
                .map(|p| {
                    std::fs::read(p).unwrap_or_else(|e| panic!("{domain} {}: {e}", p.display()))
                })
                .collect()
        };
        let write_all = |contents: &[Vec<u8>]| {
            for (path, bytes) in files.iter().zip(contents) {
                std::fs::write(path, bytes).unwrap();
            }
        };
        let open =
            || FsExternalMountAnchor::open_existing(&scoped, &[], &[dir], domain, key_id, mac_key);

        let anchor = open()
            .unwrap_or_else(|e| panic!("honest {domain} at {nv_index:#x} must reopen: {e:?}"));
        let checkpoint = anchor.load().unwrap().expect("enrolled checkpoint");
        let before_records = read_all();
        let before_counters = tpm.counts();
        anchor
            .advance(LedgerCheckpoint {
                generation: checkpoint.generation + 1,
                tag: [0x9b; 32],
            })
            .unwrap();
        drop(anchor);
        let mut expected = before_counters.clone();
        *expected.get_mut(&nv_index).unwrap().as_mut().unwrap() += 1;
        assert_eq!(
            tpm.counts(),
            expected,
            "{domain} owns exactly {nv_index:#x}"
        );

        let current_records = read_all();
        write_all(&before_records);
        let err = match open() {
            Ok(_) => panic!("rolled-back {domain} reopened"),
            Err(e) => format!("{e:?}"),
        };
        assert!(err.contains("lags TPM2 NV monotonic counter"), "{err}");
        write_all(&current_records);
        drop(open().unwrap_or_else(|e| panic!("current {domain} must reopen: {e:?}")));
    }
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;

    #[test]
    fn vmgenid_requires_an_independent_monotone_backend() {
        let raw = vec!["--anchor-vmgenid".to_owned()];
        let args = Args::parse(&raw, ANCHOR_VALUE_OPTIONS, ANCHOR_FLAG_OPTIONS).unwrap();
        assert!(AnchorConfig::from_args(&args).is_err());
        assert!(AnchorConfig::from_quorum_args(&args, "/vault").is_err());
        let raw = vec!["--policy-vmgenid".to_owned()];
        let args = Args::parse(&raw, &[], &["policy-vmgenid"]).unwrap();
        assert!(
            AnchorConfig::for_vault(
                &args,
                "/vault",
                "policy-anchor-dir",
                "policy-allow-single-disk-anchor"
            )
            .is_err()
        );
        // Direct users of the configuration cannot bypass the parser's requirement.
        let config = AnchorConfig {
            vmgenid: true,
            ..AnchorConfig::default()
        };
        assert!(config.validate_isolation(&[], &[], false).is_err());
    }

    #[test]
    fn vmgenid_same_device_waiver_cannot_supply_monotonicity() {
        let root = temp_root("vmgenid-disjoint-device");
        let vault = root.join("vault");
        let anchor_dir = root.join("anchor");
        private_dir(vault.to_str().unwrap(), true).unwrap();
        private_dir(anchor_dir.to_str().unwrap(), true).unwrap();
        let mut config = AnchorConfig {
            anchor_dir: Some(anchor_dir.to_string_lossy().into_owned()),
            vault_dir: Some(vault.to_string_lossy().into_owned()),
            allow_single_disk: true,
            vmgenid: true,
            ..AnchorConfig::default()
        };
        assert!(config.validate_isolation(&[], &[], false).is_err());
        // A TPM counter supplies the independent monotone state even on one disk.
        config.tpm_nv_index = Some(0x01800001);
        config.validate_isolation(&[], &[], false).unwrap();
        std::fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn floor_checkpoint_rejects_generation_overflow() {
        assert_eq!(
            floor_checkpoint(b"test", &[1; 32], u64::MAX - 1)
                .unwrap()
                .generation,
            u64::MAX
        );
        assert!(floor_checkpoint(b"test", &[1; 32], u64::MAX).is_err());
    }

    #[test]
    fn policy_hardware_anchor_options_reach_vault_config() {
        let raw: Vec<String> = [
            "--policy-anchor-tpm-nv",
            "0x01800001",
            "--policy-anchor-tpm-device",
            "/dev/test-tpm",
            "--policy-anchor-tpm-auth-env",
            "TEST_AUTH",
            "--policy-vmgenid",
            "--policy-vmgenid-strict",
        ]
        .into_iter()
        .map(str::to_owned)
        .collect();
        let args = Args::parse(
            &raw,
            &crate::policy_ledger::GATE_VALUE_OPTIONS,
            &crate::policy_ledger::GATE_FLAG_OPTIONS,
        )
        .unwrap();
        let config = AnchorConfig::for_vault(
            &args,
            "/vault",
            "policy-anchor-dir",
            "policy-allow-single-disk-anchor",
        )
        .unwrap()
        .unwrap();
        assert_eq!(config.tpm_nv_index, Some(0x01800001));
        assert_eq!(config.tpm_device_path.as_deref(), Some("/dev/test-tpm"));
        assert_eq!(config.tpm_auth_env.as_deref(), Some("TEST_AUTH"));
        assert!(config.vmgenid && config.vmgenid_strict);
        for raw in [
            vec!["--policy-vmgenid-strict"],
            vec!["--policy-anchor-tpm-device", "/dev/test-tpm"],
        ] {
            let raw: Vec<_> = raw.into_iter().map(str::to_owned).collect();
            let args = Args::parse(
                &raw,
                &crate::policy_ledger::GATE_VALUE_OPTIONS,
                &crate::policy_ledger::GATE_FLAG_OPTIONS,
            )
            .unwrap();
            assert!(
                AnchorConfig::for_vault(
                    &args,
                    "/vault",
                    "policy-anchor-dir",
                    "policy-allow-single-disk-anchor"
                )
                .is_err()
            );
        }
    }

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
        let rec_path = anchor_record_path(cfg.anchor_dir.as_deref().unwrap(), "ceremony", &key_id);
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

    use super::tpm_model::ModelTpm2;

    fn model_tpm(nv_index: u32) -> ModelTpm2 {
        let tpm = ModelTpm2::with_history(41);
        tpm.define_counter(nv_index, b"");
        tpm
    }

    fn strings(args: &[&str]) -> Vec<String> {
        args.iter().map(|s| (*s).to_owned()).collect()
    }

    /// Every command that binds a new anchor, with the options that carry it to its
    /// TPM preflight. `{dir}` is a scratch directory that must stay empty.
    fn enrolling_commands(dir: &str, tpm_nv: &str) -> Vec<(&'static str, Vec<String>)> {
        let path = |name: &str| format!("{dir}/{name}");
        let (out, pk, vault) = (path("out"), path("pk"), path("vault"));
        let hem = crate::quorum_hem::HEM_SCHEME_NAME;
        let table: Vec<(&'static str, Vec<&str>)> = vec![
            (
                "keygen (single key)",
                vec![
                    "keygen",
                    "--scheme",
                    "fts-frontier-2338",
                    "--secret-out",
                    &out,
                    "--public-out",
                    &pk,
                ],
            ),
            (
                "keygen (committee)",
                vec![
                    "keygen",
                    "--scheme",
                    "agg-jorts-poseidon2",
                    "--secret-out",
                    &out,
                    "--public-out",
                    &pk,
                    "--wal-dir",
                    &vault,
                    "--validators",
                    "2",
                ],
            ),
            (
                "quorum keygen",
                vec![
                    "quorum",
                    "keygen",
                    "--vault-dir",
                    &vault,
                    "--public-out",
                    &pk,
                    "--tree-height",
                    "1",
                ],
            ),
            (
                "quorum keygen (Hem)",
                vec![
                    "quorum",
                    "keygen",
                    "--scheme",
                    hem,
                    "--vault-dir",
                    &vault,
                    "--public-out",
                    &pk,
                ],
            ),
            (
                "cred voprf-keygen",
                vec![
                    "cred",
                    "voprf-keygen",
                    "--vault-dir",
                    &vault,
                    "--public-out",
                    &pk,
                ],
            ),
            (
                "cred mldsa-keygen",
                vec![
                    "cred",
                    "mldsa-keygen",
                    "--vault-dir",
                    &vault,
                    "--public-out",
                    &pk,
                ],
            ),
            (
                "hd keygen",
                vec!["hd", "keygen", "--vault-dir", &vault, "--watch-out", &pk],
            ),
            (
                "policy init",
                vec![
                    "policy",
                    "init",
                    "--ledger-dir",
                    &vault,
                    "--accept-single-host-custody",
                ],
            ),
            (
                "policy biscuit keygen",
                vec![
                    "policy",
                    "biscuit",
                    "keygen",
                    "--secret-out",
                    &out,
                    "--public-out",
                    &pk,
                ],
            ),
        ];
        table
            .into_iter()
            .map(|(name, mut args)| {
                args.extend_from_slice(&["--anchor-tpm-nv", tpm_nv]);
                (name, strings(&args))
            })
            .collect()
    }

    fn dispatch(args: &[String]) -> Result<(), CliError> {
        let rest = &args[1..];
        match args[0].as_str() {
            "keygen" => crate::keys::keygen(rest),
            "quorum" => crate::quorum::run(rest),
            "cred" => crate::cred::run(rest),
            "hd" => crate::hd::run(rest),
            "policy" => crate::policy::run(rest),
            other => panic!("{other}"),
        }
    }

    // A counter that anything has incremented (a key, a vault, a policy ledger, an
    // abandoned enrollment) is refused by every enrolling command before it creates
    // a file or touches the TPM. Before, the second anchor on an index enrolled, and
    // both it and the first then failed later as "rolled back".
    #[test]
    fn every_enrolling_command_refuses_a_used_tpm_counter_before_writing() {
        let root = temp_root("tpm-used-counter");
        // 0x01800200 backs another vault's anchor; the committee and the quorum also
        // need the following counters, which are unused, so only the overlap refuses.
        // The counters below it are defined and unused, so a range that starts below it
        // is refused for the overlap and for nothing else.
        let installed = tpm_model::install(0x0180_01f8, 16, 41);
        let tpm = &installed.0;
        let other_vault = root.join("other");
        private_dir(other_vault.to_str().unwrap(), true).unwrap();
        let other_cfg = AnchorConfig {
            tpm_nv_index: Some(0x0180_0200),
            ..AnchorConfig::default()
        };
        let other = FsExternalMountAnchor::provision_fresh(
            &other_cfg,
            &[],
            &[other_vault.to_str().unwrap()],
            "ceremony",
            [0x31; 32],
            [0x32; 32],
        )
        .unwrap();
        other.advance(ckpt(1, 0x33)).unwrap();
        let counts = tpm.counts();
        let scratch = root.join("scratch");
        private_dir(scratch.to_str().unwrap(), true).unwrap();
        let scratch_s = scratch.to_str().unwrap();
        for (name, args) in enrolling_commands(scratch_s, "0x01800200") {
            let err = dispatch(&args).expect_err(name);
            assert!(
                err.message.contains("0x01800200")
                    && err.message.contains("has already been incremented"),
                "{name}: {err:?}"
            );
            assert_eq!(
                std::fs::read_dir(&scratch).unwrap().count(),
                0,
                "{name} wrote before its TPM preflight"
            );
            assert_eq!(tpm.counts(), counts, "{name} touched a counter");
        }
        // Multi-anchor ranges that reach the used counter from below are refused too.
        for (name, base) in [
            ("quorum keygen", "0x018001fb"),
            ("keygen (committee)", "0x018001fe"),
        ] {
            let args = enrolling_commands(scratch_s, base)
                .into_iter()
                .find(|(n, _)| *n == name)
                .unwrap()
                .1;
            let err = dispatch(&args).expect_err(name);
            assert!(
                err.message.contains("0x01800200")
                    && err.message.contains("has already been incremented"),
                "{name}: {err:?}"
            );
            assert_eq!(std::fs::read_dir(&scratch).unwrap().count(), 0);
            assert_eq!(tpm.counts(), counts, "{name} touched a counter");
        }
        // The other vault's anchor is untouched and still opens.
        assert_eq!(other.load().unwrap(), Some(ckpt(1, 0x33)));
        drop(other);
        std::fs::remove_dir_all(root).unwrap();
    }

    // The policy ledger has its own anchor. Naming its counter inside the counters a
    // key reserves would bind two anchors to one counter.
    #[test]
    fn policy_ledger_counter_inside_a_key_range_is_refused_before_writing() {
        let root = temp_root("tpm-policy-overlap");
        let dir = root.to_str().unwrap();
        let installed = tpm_model::install(0x0180_0300, 8, 41);
        // (command, the policy counter that collides with it, one just outside its range)
        for (name, inside, outside) in [
            ("keygen (single key)", "0x01800300", "0x01800301"),
            ("keygen (committee)", "0x01800302", "0x01800303"),
            ("quorum keygen", "0x01800305", "0x01800306"),
            ("quorum keygen", "0x01800300", "0x018002ff"),
        ] {
            let mut args = enrolling_commands(dir, "0x01800300")
                .into_iter()
                .find(|(n, _)| *n == name)
                .unwrap()
                .1;
            args.extend(strings(&["--policy-anchor-tpm-nv", inside]));
            let err = dispatch(&args).expect_err(name);
            assert!(err.message.contains("lies inside"), "{name}: {err:?}");
            assert!(err.message.contains(&inside[2..]), "{name}: {err:?}");
            // Outside the range the overlap check passes; the command then stops at a
            // later requirement (the policy ledger these options belong to).
            let len = args.len();
            args[len - 1] = outside.to_owned();
            let err = dispatch(&args).expect_err(name);
            assert!(!err.message.contains("lies inside"), "{name}: {err:?}");
            assert!(installed.0.counts().values().all(Option::is_none));
            let _ = std::fs::remove_dir_all(format!("{dir}/vault"));
            let _ = std::fs::remove_file(format!("{dir}/out"));
            let _ = std::fs::remove_file(format!("{dir}/pk"));
        }
        // Signing with a quorum checks the same thing before it opens the vault.
        let err = crate::quorum::run(&strings(&[
            "sign",
            "--vault-dir",
            &format!("{dir}/vault"),
            "--epoch",
            "0",
            "--in",
            &format!("{dir}/no-such-message"),
            "--out",
            &format!("{dir}/sig"),
            "--anchor-tpm-nv",
            "0x01800300",
            "--policy-anchor-tpm-nv",
            "0x01800303",
        ]))
        .unwrap_err();
        assert!(err.message.contains("lies inside"), "{err:?}");
        std::fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn hardware_anchor_cannot_be_reopened_with_weaker_backend_requirements() {
        let slot = Slot::new("hardware-no-downgrade");
        let config = AnchorConfig {
            tpm_nv_index: Some(0x0180_0007),
            vmgenid: true,
            ..slot.cfg.clone()
        };
        let tpm = model_tpm(0x0180_0007);
        let key_id = [0x87; 32];
        let mac_key = [0x98; 32];
        let anchor = FsExternalMountAnchor::provision_fresh_with_tpm(
            &config,
            &[&slot.sk],
            &[],
            "ceremony",
            key_id,
            mac_key,
            tpm.clone(),
        )
        .unwrap();
        anchor.advance(ckpt(1, 0xA1)).unwrap();
        drop(anchor);
        for (nv, vmgenid) in [(None, false), (None, true), (config.tpm_nv_index, false)] {
            let weaker = AnchorConfig {
                tpm_nv_index: nv,
                vmgenid,
                ..config.clone()
            };
            let result = FsExternalMountAnchor::open_existing_with_tpm(
                &weaker,
                &[&slot.sk],
                &[],
                "ceremony",
                key_id,
                mac_key,
                tpm.clone(),
            );
            assert!(
                result.is_err(),
                "removing an enrolled backend must fail closed"
            );
            assert_eq!(tpm.count(0x0180_0007), Some(42));
        }
        let reopened = FsExternalMountAnchor::open_existing_with_tpm(
            &config,
            &[&slot.sk],
            &[],
            "ceremony",
            key_id,
            mac_key,
            tpm.clone(),
        )
        .unwrap();
        assert_eq!(reopened.load().unwrap(), Some(ckpt(1, 0xA1)));
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

        let tpm = model_tpm(0x0180_0007);
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
        assert_eq!(tpm.count(0x0180_0007), Some(42));
        anchor.advance(ckpt(2, 0xB2)).unwrap();
        assert_eq!(tpm.count(0x0180_0007), Some(43));
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

        // The counter moves on without this seal, as it would if the seal on disk were
        // an older one than the TPM last saw.
        tpm.transmit(
            &qsag_core::anti_rollback::marshal_tpm2_nv_increment_cmd(0x0180_0007, 0x0180_0007, b"")
                .unwrap(),
        )
        .unwrap();
        assert_eq!(tpm.count(0x0180_0007), Some(44));
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
