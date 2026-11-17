//! Hardware and hypervisor anti-rollback anchors for stateful post-quantum custody
//! (`FrontierSumFts`, `DurableFtsWal`, `JortsPoseidon2`, and `DurableQueryBudget`).
//!
//! Two orthogonal rollback/fork surfaces threaten stateful hash-based signers (`XMSS`,
//! `LMS/HSS`, `Jorts`, `FTS`):
//!
//! 1. **VM snapshot restore / clone:** [`VmGenIdForkGuard`] and
//!    [`HypervisorGenerationAnchor`] bind checkpoints to hypervisor ACPI `VMGENID`,
//!    Linux `boot_id`, and a guarded file's `(st_dev, st_ino, st_ctime)` tuple. A changed
//!    hypervisor generation detects whole-VM snapshot restore or cloning when the
//!    hypervisor exposes and updates it. Boot/file identity checks add continuity fences.
//!    These are **not independently monotone signing state**: restoring the local seal
//!    and custody bytes in place can preserve every checked identity. Always combine
//!    this guard with an independent monotone authority for storage rollback protection.
//! 2. **Offline disk image rollback across host reboots:**
//!    [`Tpm2NvMonotoneAnchor`] speaks raw big-endian ISO/IEC 11889 TPM 2.0 command/response
//!    packets (`TPM2_NV_Increment = 0x00000134`, `TPM2_NV_Read = 0x0000014E` under
//!    `TPM_ST_SESSIONS = 0x8002` / `TPM_RS_PW = 0x40000009`) directly over `/dev/tpmrm0` in pure
//!    safe Rust (`#![forbid(unsafe_code)]`, zero C library dependencies), binding [`LedgerCheckpoint`]
//!    monotonicity to a hardware 64-bit `TPM_NT_COUNTER` NVRAM index via a crash-safe two-phase
//!    `(committed, pending)` seal.

use alloc::{vec, vec::Vec};
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use std::sync::Mutex;

use qsag_asm::durable::LockedRecord;

use crate::durable_ledger::{ExternalMonotoneAnchor, LedgerCheckpoint};
use crate::sponge::Cshake256Xof;
use crate::wipe::{SecretBuffer, ct_eq_bytes, ct_eq_bytes32, wipe_bytes, wipe_bytes32};

/// TPM 2.0 command/response structure tag without authorization sessions (`0x8001`).
pub const TPM_ST_NO_SESSIONS: u16 = 0x8001;
/// TPM 2.0 command/response structure tag carrying an authorization area (`0x8002`).
pub const TPM_ST_SESSIONS: u16 = 0x8002;
// Section numbers below are those of the TCG "Trusted Platform Module Library, Family
// 2.0, Level 00 Revision 01.59" (ISO/IEC 11889:2015 is the earlier revision): Part 2
// (Structures) and Part 3 (Commands).

/// `TPM_CC_NV_Increment` (Part 3 §31.8).
pub const TPM_CC_NV_INCREMENT: u32 = 0x0000_0134;
/// `TPM_CC_NV_Read` (Part 3 §31.13).
pub const TPM_CC_NV_READ: u32 = 0x0000_014E;
/// `TPM_CC_NV_ReadPublic` (Part 3 §31.6): no authorization, no sessions.
pub const TPM_CC_NV_READ_PUBLIC: u32 = 0x0000_0169;

/// `TPM_RC_NV_UNINITIALIZED` (Part 2 §6.6.3, `RC_VER1 + 0x04A`): the index is defined
/// and `TPMA_NV_WRITTEN` is CLEAR (Part 3 §31.13).
pub const TPM_RC_NV_UNINITIALIZED: u32 = 0x0000_014A;
/// `TPM_RC_NV_LOCKED` (`RC_VER1 + 0x048`).
pub const TPM_RC_NV_LOCKED: u32 = 0x0000_0148;
/// `TPM_RC_NV_AUTHORIZATION` (`RC_VER1 + 0x049`): the index does not allow this
/// access with its own authorization value.
pub const TPM_RC_NV_AUTHORIZATION: u32 = 0x0000_0149;
/// `TPM_RC_NV_RANGE` (`RC_VER1 + 0x046`).
pub const TPM_RC_NV_RANGE: u32 = 0x0000_0146;
/// `TPM_RC_COMMAND_CODE` (`RC_VER1 + 0x043`).
pub const TPM_RC_COMMAND_CODE: u32 = 0x0000_0143;
/// `TPM_RC_HANDLE` (`RC_FMT1 + 0x00B`) for the first handle: the index does not exist.
pub const TPM_RC_HANDLE_1: u32 = 0x0000_018B;
/// `TPM_RC_ATTRIBUTES` (`RC_FMT1 + 0x002`) for the second handle (`nvIndex`).
pub const TPM_RC_ATTRIBUTES_HANDLE_2: u32 = 0x0000_0282;
/// `TPM_RC_BAD_AUTH` (`RC_FMT1 + 0x022`) for the first session.
pub const TPM_RC_BAD_AUTH_SESSION_1: u32 = 0x0000_09A2;

/// `TPMA_NV` bits (Part 2 §13.4, Table 214).
pub const TPMA_NV_AUTHWRITE: u32 = 1 << 2;
/// `TPM_NT` is bits 7:4 of `TPMA_NV`; `TPM_NT_COUNTER = 0x1` (Part 2 §13.2).
pub const TPMA_NV_TPM_NT_MASK: u32 = 0xF << 4;
pub const TPMA_NV_TPM_NT_COUNTER: u32 = 0x1 << 4;
pub const TPMA_NV_WRITELOCKED: u32 = 1 << 11;
pub const TPMA_NV_AUTHREAD: u32 = 1 << 18;
pub const TPMA_NV_NO_DA: u32 = 1 << 25;
pub const TPMA_NV_ORDERLY: u32 = 1 << 26;
pub const TPMA_NV_CLEAR_STCLEAR: u32 = 1 << 27;
pub const TPMA_NV_READLOCKED: u32 = 1 << 28;
pub const TPMA_NV_WRITTEN: u32 = 1 << 29;
/// TPM 2.0 password authorization session handle (`TPM_RS_PW = 0x4000_0009`).
pub const TPM_RS_PW: u32 = 0x4000_0009;
/// TPM 2.0 `TPM_RH_OWNER` permanent hierarchy handle (`0x4000_0001`).
pub const TPM_RH_OWNER: u32 = 0x4000_0001;
/// TPM 2.0 `TPM_RC_SUCCESS` response code (`0x0000_0000`).
pub const TPM_RC_SUCCESS: u32 = 0x0000_0000;

const MAX_TPM2_AUTH_BYTES: usize = 64;
const MAX_TPM2_RSP_BYTES: usize = 4096;

/// Typed anti-rollback and fork-detection failure modes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AntiRollbackError {
    /// A VM snapshot restore, volume clone, container fork, or NVRAM counter regression was
    /// detected; callers MUST permanently halt signing until manual operator re-keying.
    RollbackOrForkDetected(&'static str),
    /// The TPM 2.0 resource manager returned a non-zero `TPM_RC` status code.
    Tpm2ResponseError(u32),
    /// Malformed TPM 2.0 packet header, handle range, or parameter framing.
    ProtocolFramingError(&'static str),
    /// Local anchor record failed CSHAKE256 MAC verification or magic/length validation.
    AuthenticationFailed,
    /// The NV index cannot back an anchor: wrong type or attributes, or (for a new
    /// anchor) a counter that has already been incremented by something else.
    UnsuitableCounterIndex(&'static str),
    /// Underlying OS/filesystem/device I/O failure.
    Io(io::ErrorKind),
}

impl core::fmt::Display for AntiRollbackError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::RollbackOrForkDetected(msg) => {
                write!(
                    f,
                    "anti-rollback halt (rollback or VM fork detected): {msg}"
                )
            }
            Self::Tpm2ResponseError(rc) => {
                write!(f, "TPM 2.0 command failed with response code 0x{rc:08x}")
            }
            Self::ProtocolFramingError(msg) => write!(f, "TPM 2.0 protocol framing error: {msg}"),
            Self::AuthenticationFailed => {
                write!(f, "anti-rollback anchor record authentication failed")
            }
            Self::UnsuitableCounterIndex(msg) => {
                write!(f, "TPM 2.0 NV index cannot back an anchor: {msg}")
            }
            Self::Io(kind) => write!(f, "anti-rollback anchor I/O error: {kind:?}"),
        }
    }
}

impl std::error::Error for AntiRollbackError {}

impl AntiRollbackError {
    /// Convert into [`std::io::Error`] while preserving this typed error as the inner payload
    /// so [`ExternalMonotoneAnchor`] callers can downcast or inspect `io::ErrorKind`.
    pub fn into_io_error(self) -> io::Error {
        let kind = match &self {
            Self::RollbackOrForkDetected(_) | Self::AuthenticationFailed => {
                io::ErrorKind::InvalidData
            }
            Self::ProtocolFramingError(_)
            | Self::Tpm2ResponseError(_)
            | Self::UnsuitableCounterIndex(_) => io::ErrorKind::Other,
            Self::Io(k) => *k,
        };
        io::Error::new(kind, self)
    }
}

impl From<io::Error> for AntiRollbackError {
    fn from(err: io::Error) -> Self {
        Self::Io(err.kind())
    }
}

// ============================================================================
// 1. Hypervisor VMGENID + Linux boot_id + Inode Identity Fork Guard
// ============================================================================

/// Sampled host/hypervisor generation identity and target WAL inode metadata.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VmGenSnapshot {
    /// 128-bit hypervisor VM Generation ID (`ACPI VMGENID`), if exposed by the guest OS.
    pub vmgenid: Option<[u8; 16]>,
    /// 128-bit Linux kernel boot session UUID (`/proc/sys/kernel/random/boot_id`), if exposed.
    pub boot_id: Option<[u8; 16]>,
    /// Block device ID (`st_dev`) of the guarded WAL / custody state file.
    pub target_dev: u64,
    /// Inode number (`st_ino`) of the guarded WAL / custody state file.
    pub target_ino: u64,
    /// Inode status-change timestamp seconds (`st_ctime`) of the guarded file at observation.
    pub target_ctime_sec: i64,
}

/// Policy controlling how [`VmGenIdForkGuard`] treats missing `VMGENID` devices and reboots.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VmGenPolicy {
    /// Require a hardware/hypervisor `VMGENID` device (`/sys/devices/virtual/misc/vmgenid` or
    /// ACPI `vmgenid`) to be present; fail closed on bare-metal/unconfigured VMs when `true`.
    pub require_vmgenid: bool,
    /// Pin `/proc/sys/kernel/random/boot_id` so even a reboot or container restart halts signing
    /// until explicit operator re-attestation.
    pub pin_boot_id: bool,
    /// When `vmgenid` is absent (`None`), halt if `boot_id` changes across opens (since without
    /// `VMGENID` or a hardware TPM2 anchor, a host reboot cannot be distinguished from an offline
    /// VM snapshot restore).
    pub halt_reboot_without_vmgenid: bool,
}

impl VmGenPolicy {
    /// Strict cloud/VM production policy: requires hypervisor `VMGENID` exposure and halts on
    /// any `VMGENID` mutation or `(dev, ino)` volume clone while permitting normal guest reboots
    /// whose `VMGENID` and `(dev, ino)` remain invariant.
    pub const STRICT_HYPERVISOR: Self = Self {
        require_vmgenid: true,
        pin_boot_id: false,
        halt_reboot_without_vmgenid: true,
    };

    /// Ephemeral/container fork-guard policy: does not require ACPI `VMGENID`, but pins both
    /// `boot_id` and `(dev, ino)` (and `vmgenid` if present), halting when those identities
    /// change. Without hypervisor VMGENID, a restore preserving them is undetectable.
    pub const PINNED_BOOT_SESSION: Self = Self {
        require_vmgenid: false,
        pin_boot_id: true,
        halt_reboot_without_vmgenid: true,
    };
}

impl Default for VmGenPolicy {
    fn default() -> Self {
        Self::PINNED_BOOT_SESSION
    }
}

/// Pluggable probe for hypervisor `VMGENID`, kernel `boot_id`, and guarded file identity.
pub trait VmGenSource: Send + Sync {
    fn sample(&self, guarded_target: &Path) -> Result<VmGenSnapshot, AntiRollbackError>;
}

/// Production Linux sysfs/procfs probe reading `/sys/devices/virtual/misc/vmgenid`, ACPI
/// `QEMU0002:00` / `VM_Gen_Counter:00`, `/proc/sys/kernel/random/boot_id`, and `lstat` metadata.
#[derive(Clone, Copy, Debug, Default)]
pub struct LinuxSysfsVmGenSource;

const VMGENID_SYSFS_CANDIDATES: &[&str] = &[
    "/sys/devices/virtual/misc/vmgenid/generation",
    "/sys/devices/virtual/misc/vmgenid/raw",
    "/sys/bus/acpi/devices/QEMU0002:00/vmgenid",
    "/sys/bus/acpi/devices/VM_Gen_Counter:00/vmgenid",
    "/sys/devices/virtual/misc/vmgenid",
];

const LINUX_BOOT_ID_PATH: &str = "/proc/sys/kernel/random/boot_id";

/// Parse either a 16-byte raw binary generation ID or an ASCII UUID / 32-nibble hex string
/// (`xxxxxxxx-xxxx-xxxx-xxxx-xxxxxxxxxxxx` or `32` hex chars, with optional trailing newline).
pub fn parse_id128_bytes(raw: &[u8]) -> Result<[u8; 16], AntiRollbackError> {
    if raw.len() == 16 {
        let mut out = [0u8; 16];
        out.copy_from_slice(raw);
        return Ok(out);
    }
    let trimmed = trim_ascii_whitespace(raw);
    let mut nibbles = [0u8; 32];
    let mut n = 0usize;
    for &b in trimmed {
        if b == b'-' {
            continue;
        }
        let val = match b {
            b'0'..=b'9' => b - b'0',
            b'a'..=b'f' => b - b'a' + 10,
            b'A'..=b'F' => b - b'A' + 10,
            _ => {
                return Err(AntiRollbackError::ProtocolFramingError(
                    "invalid hex byte in 128-bit generation identifier",
                ));
            }
        };
        if n >= 32 {
            return Err(AntiRollbackError::ProtocolFramingError(
                "oversized 128-bit generation identifier",
            ));
        }
        nibbles[n] = val;
        n += 1;
    }
    if n != 32 {
        return Err(AntiRollbackError::ProtocolFramingError(
            "truncated 128-bit generation identifier",
        ));
    }
    let mut out = [0u8; 16];
    for i in 0..16 {
        out[i] = (nibbles[2 * i] << 4) | nibbles[2 * i + 1];
    }
    Ok(out)
}

fn trim_ascii_whitespace(mut s: &[u8]) -> &[u8] {
    while let Some((&first, rest)) = s.split_first() {
        if first.is_ascii_whitespace() {
            s = rest;
        } else {
            break;
        }
    }
    while let Some((&last, rest)) = s.split_last() {
        if last.is_ascii_whitespace() {
            s = rest;
        } else {
            break;
        }
    }
    s
}

fn read_bounded_sysfs_id(path: &Path) -> Result<Option<[u8; 16]>, AntiRollbackError> {
    let meta = match fs::symlink_metadata(path) {
        Ok(m) => m,
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(e) => return Err(AntiRollbackError::Io(e.kind())),
    };
    if meta.is_dir() || meta.file_type().is_symlink() {
        return Ok(None);
    }
    let mut f = match OpenOptions::new().read(true).open(path) {
        Ok(f) => f,
        Err(e)
            if e.kind() == io::ErrorKind::NotFound
                || e.kind() == io::ErrorKind::PermissionDenied =>
        {
            return Ok(None);
        }
        Err(e) => return Err(AntiRollbackError::Io(e.kind())),
    };
    let mut buf = [0u8; 64];
    let mut total = 0usize;
    while total < buf.len() {
        match f.read(&mut buf[total..]) {
            Ok(0) => break,
            Ok(n) => total += n,
            Err(e) if e.kind() == io::ErrorKind::Interrupted => continue,
            Err(e) => return Err(AntiRollbackError::Io(e.kind())),
        }
    }
    if total == 0 {
        return Ok(None);
    }
    parse_id128_bytes(&buf[..total]).map(Some)
}

impl VmGenSource for LinuxSysfsVmGenSource {
    fn sample(&self, guarded_target: &Path) -> Result<VmGenSnapshot, AntiRollbackError> {
        let mut vmgenid = None;
        for candidate in VMGENID_SYSFS_CANDIDATES {
            if let Some(id) = read_bounded_sysfs_id(Path::new(candidate))? {
                vmgenid = Some(id);
                break;
            }
        }
        let boot_id = read_bounded_sysfs_id(Path::new(LINUX_BOOT_ID_PATH))?;

        let meta = fs::symlink_metadata(guarded_target)?;
        if !meta.is_file() {
            return Err(AntiRollbackError::RollbackOrForkDetected(
                "guarded custody target is not a regular file",
            ));
        }
        #[cfg(unix)]
        let (target_dev, target_ino, target_ctime_sec) = {
            use std::os::unix::fs::MetadataExt;
            (meta.dev(), meta.ino(), meta.ctime())
        };
        #[cfg(not(unix))]
        let (target_dev, target_ino, target_ctime_sec) = (0u64, 0u64, 0i64);

        Ok(VmGenSnapshot {
            vmgenid,
            boot_id,
            target_dev,
            target_ino,
            target_ctime_sec,
        })
    }
}

/// Stateless verifier comparing a previously sealed [`VmGenSnapshot`] against a live probe.
#[derive(Clone, Copy, Debug)]
pub struct VmGenIdForkGuard {
    policy: VmGenPolicy,
}

impl VmGenIdForkGuard {
    pub const fn new(policy: VmGenPolicy) -> Self {
        Self { policy }
    }

    /// Validate that a live [`VmGenSnapshot`] satisfies initial provisioning requirements.
    pub fn validate_initial(&self, live: &VmGenSnapshot) -> Result<(), AntiRollbackError> {
        if self.policy.require_vmgenid && live.vmgenid.is_none() {
            return Err(AntiRollbackError::RollbackOrForkDetected(
                "hypervisor VMGENID device missing under require_vmgenid policy",
            ));
        }
        Ok(())
    }

    /// Verify continuity between a sealed [`VmGenSnapshot`] and a freshly sampled `live` snapshot.
    /// Any VM snapshot restore (`vmgenid` drift), volume/file clone (`(dev, ino)` drift), or
    /// disallowed `boot_id` drift returns `Err(AntiRollbackError::RollbackOrForkDetected)`.
    pub fn verify_continuity(
        &self,
        sealed: &VmGenSnapshot,
        live: &VmGenSnapshot,
    ) -> Result<(), AntiRollbackError> {
        self.validate_initial(live)?;

        if sealed.target_dev != live.target_dev || sealed.target_ino != live.target_ino {
            return Err(AntiRollbackError::RollbackOrForkDetected(
                "guarded WAL device/inode identity changed (EBS volume clone or file copy)",
            ));
        }
        if live.target_ctime_sec < sealed.target_ctime_sec {
            return Err(AntiRollbackError::RollbackOrForkDetected(
                "guarded WAL inode ctime regressed (snapshot or backup restore)",
            ));
        }

        match (sealed.vmgenid, live.vmgenid) {
            (Some(old_id), Some(cur_id)) => {
                if !ct_eq_bytes(&old_id, &cur_id) {
                    return Err(AntiRollbackError::RollbackOrForkDetected(
                        "hypervisor VMGENID mutated (VM snapshot restore or live fork)",
                    ));
                }
            }
            (Some(_), None) => {
                return Err(AntiRollbackError::RollbackOrForkDetected(
                    "previously present hypervisor VMGENID disappeared",
                ));
            }
            (None, Some(_)) => {
                return Err(AntiRollbackError::RollbackOrForkDetected(
                    "unexpected hypervisor VMGENID appeared on previously bare-metal seal",
                ));
            }
            (None, None) => {}
        }

        match (sealed.boot_id, live.boot_id) {
            (Some(old_boot), Some(cur_boot)) => {
                if !ct_eq_bytes(&old_boot, &cur_boot) {
                    if self.policy.pin_boot_id {
                        return Err(AntiRollbackError::RollbackOrForkDetected(
                            "kernel boot_id changed under pinned session policy",
                        ));
                    }
                    if live.vmgenid.is_none() && self.policy.halt_reboot_without_vmgenid {
                        return Err(AntiRollbackError::RollbackOrForkDetected(
                            "kernel boot_id changed without hardware VMGENID continuity witness",
                        ));
                    }
                }
            }
            (Some(_), None) => {
                return Err(AntiRollbackError::RollbackOrForkDetected(
                    "previously present kernel boot_id disappeared",
                ));
            }
            _ => {}
        }

        Ok(())
    }
}

const VMGEN_RECORD_MAGIC: &[u8; 8] = b"QSVMGEN1";
const VMGEN_RECORD_LEN: usize = 146;
// Layout (146 bytes):
//   [0..8]     magic "QSVMGEN1"
//   [8]        flags: bit0 = has_vmgenid, bit1 = has_boot_id
//   [9]        reserved (0)
//   [10..26]   vmgenid ([u8; 16], zero if absent)
//   [26..42]   boot_id ([u8; 16], zero if absent)
//   [42..50]   target_dev (u64 LE)
//   [50..58]   target_ino (u64 LE)
//   [58..66]   target_ctime_sec (i64 LE)
//   [66..74]   checkpoint.generation (u64 LE)
//   [74..106]  checkpoint.tag ([u8; 32])
//   [106..114] monotonic_update_seq (u64 LE)
//   [114..146] CSHAKE256 MAC ([u8; 32])

/// VM snapshot/clone continuity guard implementing [`ExternalMonotoneAnchor`] for composition.
/// Seals [`LedgerCheckpoint`] alongside hypervisor `VMGENID`, Linux `boot_id`, and guarded
/// file `(dev, ino, ctime)` continuity. This guard alone cannot detect in-place restoration
/// of custody and seal bytes: its checkpoint and sequence are on the same rollbackable
/// storage. Pair with an independently monotone anchor to protect stateful signing.
pub struct HypervisorGenerationAnchor<S: VmGenSource = LinuxSysfsVmGenSource> {
    record: LockedRecord,
    guarded_target: PathBuf,
    mac_key: [u8; 32],
    guard: VmGenIdForkGuard,
    source: S,
}

impl<S: VmGenSource> Drop for HypervisorGenerationAnchor<S> {
    fn drop(&mut self) {
        wipe_bytes32(&mut self.mac_key);
    }
}

impl HypervisorGenerationAnchor<LinuxSysfsVmGenSource> {
    /// Acquire or create a [`HypervisorGenerationAnchor`] at `anchor_path` watching
    /// `guarded_target` using the production Linux sysfs/procfs probe.
    pub fn open_or_create(
        anchor_path: impl Into<PathBuf>,
        guarded_target: impl Into<PathBuf>,
        mut mac_key: [u8; 32],
        policy: VmGenPolicy,
    ) -> Result<Self, AntiRollbackError> {
        // The by-value argument is the callee's to wipe; `key_arg` wipes this frame's copy.
        let key_arg = SecretBuffer(&mut mac_key);
        Self::open_or_create_with_source(
            anchor_path,
            guarded_target,
            **key_arg,
            policy,
            LinuxSysfsVmGenSource,
        )
    }
}

impl<S: VmGenSource> HypervisorGenerationAnchor<S> {
    /// Acquire or create a [`HypervisorGenerationAnchor`] with an explicit [`VmGenSource`].
    pub fn open_or_create_with_source(
        anchor_path: impl Into<PathBuf>,
        guarded_target: impl Into<PathBuf>,
        mut mac_key: [u8; 32],
        policy: VmGenPolicy,
        source: S,
    ) -> Result<Self, AntiRollbackError> {
        // Wipes the by-value key argument on every return, `?` and unwind; the key is
        // copied straight into the anchor (whose `Drop` wipes it), not via a temporary.
        let key_arg = SecretBuffer(&mut mac_key);
        let record = LockedRecord::acquire(anchor_path)?;
        let guarded_target = guarded_target.into();
        let guard = VmGenIdForkGuard::new(policy);
        let mut this = Self {
            record,
            guarded_target,
            mac_key: [0u8; 32],
            guard,
            source,
        };
        this.mac_key.copy_from_slice(key_arg.as_slice());
        drop(key_arg);
        // Immediately verify existing state (if already sealed) so fork/rollback fails on open.
        let _ = this.load_checked()?;
        Ok(this)
    }

    fn compute_mac(&self, body_without_mac: &[u8]) -> [u8; 32] {
        let mut xof = Cshake256Xof::new(b"QSAG.VMGENID.ANCHOR.MAC/v1");
        xof.absorb(&self.mac_key);
        xof.absorb(&self.record.lock_seal());
        xof.absorb(&(body_without_mac.len() as u64).to_le_bytes());
        xof.absorb(body_without_mac);
        let mut out = [0u8; 32];
        xof.squeeze(&mut out);
        out
    }

    fn decode_sealed(
        &self,
        raw: &[u8],
    ) -> Result<(VmGenSnapshot, LedgerCheckpoint, u64), AntiRollbackError> {
        if raw.len() != VMGEN_RECORD_LEN || &raw[..8] != VMGEN_RECORD_MAGIC {
            return Err(AntiRollbackError::AuthenticationFailed);
        }
        let expected_mac = self.compute_mac(&raw[..114]);
        let stored_mac: [u8; 32] = raw[114..146]
            .try_into()
            .map_err(|_| AntiRollbackError::AuthenticationFailed)?;
        if !ct_eq_bytes32(&stored_mac, &expected_mac) {
            return Err(AntiRollbackError::AuthenticationFailed);
        }
        let flags = raw[8];
        if (flags & !0b11) != 0 || raw[9] != 0 {
            return Err(AntiRollbackError::AuthenticationFailed);
        }
        let vmgenid_bytes: [u8; 16] = raw[10..26]
            .try_into()
            .map_err(|_| AntiRollbackError::AuthenticationFailed)?;
        let boot_bytes: [u8; 16] = raw[26..42]
            .try_into()
            .map_err(|_| AntiRollbackError::AuthenticationFailed)?;
        if (flags & 0b01) == 0 && vmgenid_bytes != [0u8; 16] {
            return Err(AntiRollbackError::AuthenticationFailed);
        }
        if (flags & 0b10) == 0 && boot_bytes != [0u8; 16] {
            return Err(AntiRollbackError::AuthenticationFailed);
        }
        let target_dev = u64::from_le_bytes(raw[42..50].try_into().unwrap());
        let target_ino = u64::from_le_bytes(raw[50..58].try_into().unwrap());
        let target_ctime_sec = i64::from_le_bytes(raw[58..66].try_into().unwrap());
        let generation = u64::from_le_bytes(raw[66..74].try_into().unwrap());
        let tag: [u8; 32] = raw[74..106].try_into().unwrap();
        let seq = u64::from_le_bytes(raw[106..114].try_into().unwrap());

        let snap = VmGenSnapshot {
            vmgenid: if (flags & 0b01) != 0 {
                Some(vmgenid_bytes)
            } else {
                None
            },
            boot_id: if (flags & 0b10) != 0 {
                Some(boot_bytes)
            } else {
                None
            },
            target_dev,
            target_ino,
            target_ctime_sec,
        };
        Ok((snap, LedgerCheckpoint { generation, tag }, seq))
    }

    fn encode_sealed(
        &self,
        snap: &VmGenSnapshot,
        cp: LedgerCheckpoint,
        seq: u64,
    ) -> [u8; VMGEN_RECORD_LEN] {
        let mut buf = [0u8; VMGEN_RECORD_LEN];
        buf[..8].copy_from_slice(VMGEN_RECORD_MAGIC);
        let mut flags = 0u8;
        if let Some(id) = snap.vmgenid {
            flags |= 0b01;
            buf[10..26].copy_from_slice(&id);
        }
        if let Some(boot) = snap.boot_id {
            flags |= 0b10;
            buf[26..42].copy_from_slice(&boot);
        }
        buf[8] = flags;
        buf[42..50].copy_from_slice(&snap.target_dev.to_le_bytes());
        buf[50..58].copy_from_slice(&snap.target_ino.to_le_bytes());
        buf[58..66].copy_from_slice(&snap.target_ctime_sec.to_le_bytes());
        buf[66..74].copy_from_slice(&cp.generation.to_le_bytes());
        buf[74..106].copy_from_slice(&cp.tag);
        buf[106..114].copy_from_slice(&seq.to_le_bytes());
        let mac = self.compute_mac(&buf[..114]);
        buf[114..146].copy_from_slice(&mac);
        buf
    }

    /// Authenticate the anchor and verify live `VMGENID` + `boot_id` + `(dev, ino)` continuity.
    pub fn load_checked(&self) -> Result<Option<LedgerCheckpoint>, AntiRollbackError> {
        let raw = match self.record.read_bounded(VMGEN_RECORD_LEN) {
            Ok(bytes) => bytes,
            Err(e) if e.kind() == io::ErrorKind::NotFound && self.record.is_fresh() => {
                if self.guarded_target.exists() {
                    let live = self.source.sample(&self.guarded_target)?;
                    self.guard.validate_initial(&live)?;
                }
                return Ok(None);
            }
            Err(e) => return Err(AntiRollbackError::Io(e.kind())),
        };
        let (sealed_snap, cp, _seq) = self.decode_sealed(&raw)?;
        let live_snap = self.source.sample(&self.guarded_target)?;
        self.guard.verify_continuity(&sealed_snap, &live_snap)?;
        Ok(Some(cp))
    }

    /// Verify live continuity and advance the sealed checkpoint monotonically.
    pub fn advance_checked(&self, checkpoint: LedgerCheckpoint) -> Result<(), AntiRollbackError> {
        let live_snap = self.source.sample(&self.guarded_target)?;
        self.guard.validate_initial(&live_snap)?;

        let next_seq = match self.record.read_bounded(VMGEN_RECORD_LEN) {
            Ok(raw) => {
                let (sealed_snap, old_cp, old_seq) = self.decode_sealed(&raw)?;
                self.guard.verify_continuity(&sealed_snap, &live_snap)?;
                if checkpoint.generation < old_cp.generation {
                    return Err(AntiRollbackError::RollbackOrForkDetected(
                        "checkpoint generation regressed below sealed VMGENID anchor",
                    ));
                }
                if checkpoint.generation == old_cp.generation {
                    if !ct_eq_bytes32(&checkpoint.tag, &old_cp.tag) {
                        return Err(AntiRollbackError::RollbackOrForkDetected(
                            "divergent checkpoint tag at equal generation (split-brain fork)",
                        ));
                    }
                    if sealed_snap == live_snap {
                        return Ok(());
                    }
                }
                old_seq
                    .checked_add(1)
                    .ok_or(AntiRollbackError::ProtocolFramingError(
                        "anchor sequence counter overflow",
                    ))?
            }
            Err(e) if e.kind() == io::ErrorKind::NotFound && self.record.is_fresh() => 1,
            Err(e) => return Err(AntiRollbackError::Io(e.kind())),
        };

        let encoded = self.encode_sealed(&live_snap, checkpoint, next_seq);
        self.record.replace(&encoded)?;
        Ok(())
    }
}

impl<S: VmGenSource> ExternalMonotoneAnchor for HypervisorGenerationAnchor<S> {
    fn load(&self) -> io::Result<Option<LedgerCheckpoint>> {
        self.load_checked()
            .map_err(AntiRollbackError::into_io_error)
    }

    fn advance(&self, checkpoint: LedgerCheckpoint) -> io::Result<()> {
        self.advance_checked(checkpoint)
            .map_err(AntiRollbackError::into_io_error)
    }
}

// ============================================================================
// 2. Hardware TPM 2.0 Monotonic NV Counter Anchor (`/dev/tpmrm0`)
// ============================================================================

/// Validate that `nv_index` lies in the normative TCG NV index handle range
/// (`0x0100_0000 ..= 0x01FF_FFFF`, `TPM_HT_NV_INDEX = 0x01`).
#[inline]
pub const fn is_valid_tpm2_nv_index(nv_index: u32) -> bool {
    (nv_index >> 24) == 0x01
}

fn marshal_pw_auth_area(out: &mut Vec<u8>, auth_value: &[u8]) -> Result<(), AntiRollbackError> {
    if auth_value.len() > MAX_TPM2_AUTH_BYTES {
        return Err(AntiRollbackError::ProtocolFramingError(
            "TPM2 password authorization exceeds 64-byte TPM2B_AUTH limit",
        ));
    }
    // TPMS_AUTH_COMMAND:
    //   sessionHandle:     TPM_RS_PW (4B BE)
    //   nonce:             TPM2B_NONCE { size = 0 } (2B BE)
    //   sessionAttributes: TPMA_SESSION { continueSession = 1 } (1B = 0x01)
    //   hmac:              TPM2B_AUTH { size = auth_value.len(), buffer = auth_value }
    let auth_size = (9 + auth_value.len()) as u32;
    out.extend_from_slice(&auth_size.to_be_bytes());
    out.extend_from_slice(&TPM_RS_PW.to_be_bytes());
    out.extend_from_slice(&0u16.to_be_bytes());
    out.push(0x01);
    out.extend_from_slice(&(auth_value.len() as u16).to_be_bytes());
    out.extend_from_slice(auth_value);
    Ok(())
}

/// Marshal an exact big-endian `TPM2_NV_Increment` (`0x0000_0134`) command packet carrying
/// a `TPM_ST_SESSIONS` (`0x8002`) password authorization area (`TPM_RS_PW = 0x4000_0009`).
pub fn marshal_tpm2_nv_increment_cmd(
    auth_handle: u32,
    nv_index: u32,
    auth_value: &[u8],
) -> Result<Vec<u8>, AntiRollbackError> {
    if !is_valid_tpm2_nv_index(nv_index) {
        return Err(AntiRollbackError::ProtocolFramingError(
            "nv_index handle outside TPM_HT_NV_INDEX (0x01000000..=0x01FFFFFF)",
        ));
    }
    if auth_value.len() > MAX_TPM2_AUTH_BYTES {
        return Err(AntiRollbackError::ProtocolFramingError(
            "TPM2 password authorization exceeds 64-byte TPM2B_AUTH limit",
        ));
    }
    let cmd_size = (31 + auth_value.len()) as u32;
    let mut pkt = Vec::with_capacity(cmd_size as usize);
    pkt.extend_from_slice(&TPM_ST_SESSIONS.to_be_bytes());
    pkt.extend_from_slice(&cmd_size.to_be_bytes());
    pkt.extend_from_slice(&TPM_CC_NV_INCREMENT.to_be_bytes());
    pkt.extend_from_slice(&auth_handle.to_be_bytes());
    pkt.extend_from_slice(&nv_index.to_be_bytes());
    marshal_pw_auth_area(&mut pkt, auth_value)?;
    debug_assert_eq!(pkt.len(), cmd_size as usize);
    Ok(pkt)
}

/// Marshal an exact big-endian `TPM2_NV_Read` (`0x0000_014E`) command packet reading an
/// 8-byte (`size = 8, offset = 0`) 64-bit monotonic counter from `nv_index`.
pub fn marshal_tpm2_nv_read_u64_cmd(
    auth_handle: u32,
    nv_index: u32,
    auth_value: &[u8],
) -> Result<Vec<u8>, AntiRollbackError> {
    if !is_valid_tpm2_nv_index(nv_index) {
        return Err(AntiRollbackError::ProtocolFramingError(
            "nv_index handle outside TPM_HT_NV_INDEX (0x01000000..=0x01FFFFFF)",
        ));
    }
    if auth_value.len() > MAX_TPM2_AUTH_BYTES {
        return Err(AntiRollbackError::ProtocolFramingError(
            "TPM2 password authorization exceeds 64-byte TPM2B_AUTH limit",
        ));
    }
    let cmd_size = (35 + auth_value.len()) as u32;
    let mut pkt = Vec::with_capacity(cmd_size as usize);
    pkt.extend_from_slice(&TPM_ST_SESSIONS.to_be_bytes());
    pkt.extend_from_slice(&cmd_size.to_be_bytes());
    pkt.extend_from_slice(&TPM_CC_NV_READ.to_be_bytes());
    pkt.extend_from_slice(&auth_handle.to_be_bytes());
    pkt.extend_from_slice(&nv_index.to_be_bytes());
    marshal_pw_auth_area(&mut pkt, auth_value)?;
    // Parameters: size = 8 (u16 BE), offset = 0 (u16 BE)
    pkt.extend_from_slice(&8u16.to_be_bytes());
    pkt.extend_from_slice(&0u16.to_be_bytes());
    debug_assert_eq!(pkt.len(), cmd_size as usize);
    Ok(pkt)
}

fn parse_tpm2_response_header(rsp: &[u8]) -> Result<(u16, usize), AntiRollbackError> {
    if rsp.len() < 10 {
        return Err(AntiRollbackError::ProtocolFramingError(
            "truncated TPM2 response header (< 10 bytes)",
        ));
    }
    let tag = u16::from_be_bytes([rsp[0], rsp[1]]);
    let size = u32::from_be_bytes([rsp[2], rsp[3], rsp[4], rsp[5]]) as usize;
    let rc = u32::from_be_bytes([rsp[6], rsp[7], rsp[8], rsp[9]]);
    if size != rsp.len() {
        return Err(AntiRollbackError::ProtocolFramingError(
            "TPM2 responseSize field mismatches received byte length",
        ));
    }
    if rc != TPM_RC_SUCCESS {
        return Err(AntiRollbackError::Tpm2ResponseError(rc));
    }
    if tag != TPM_ST_SESSIONS {
        return Err(AntiRollbackError::ProtocolFramingError(
            "TPM2 success response missing expected TPM_ST_SESSIONS tag",
        ));
    }
    if rsp.len() < 19 {
        // 10-byte header + 4-byte parameterSize + >=5-byte TPMS_AUTH_RESPONSE
        return Err(AntiRollbackError::ProtocolFramingError(
            "TPM2 session response shorter than minimum auth response frame",
        ));
    }
    let param_size = u32::from_be_bytes([rsp[10], rsp[11], rsp[12], rsp[13]]) as usize;
    let auth_offset =
        14usize
            .checked_add(param_size)
            .ok_or(AntiRollbackError::ProtocolFramingError(
                "TPM2 parameterSize arithmetic overflow",
            ))?;
    // `param_size` is untrusted: every offset derived from it is checked, so a wrapping
    // `usize` (32-bit targets) is a framing error rather than a panicking slice.
    if auth_offset.checked_add(5).is_none_or(|end| end > rsp.len()) {
        return Err(AntiRollbackError::ProtocolFramingError(
            "TPM2 parameterSize overruns response auth area",
        ));
    }
    // Validate TPMS_AUTH_RESPONSE framing: nonceTPM (TPM2B) + sessionAttributes (1B) + hmac (TPM2B)
    let auth = rsp
        .get(auth_offset..)
        .ok_or(AntiRollbackError::ProtocolFramingError(
            "TPM2 parameterSize overruns response auth area",
        ))?;
    let nonce_len = u16::from_be_bytes([auth[0], auth[1]]) as usize;
    let attr_pos = 2usize
        .checked_add(nonce_len)
        .ok_or(AntiRollbackError::ProtocolFramingError(
            "TPM2 nonceTPM overflow",
        ))?;
    let hmac_size_end = attr_pos
        .checked_add(3)
        .ok_or(AntiRollbackError::ProtocolFramingError(
            "TPM2 nonceTPM overflow",
        ))?;
    if hmac_size_end > auth.len() {
        return Err(AntiRollbackError::ProtocolFramingError(
            "TPM2 auth response truncated before hmac size",
        ));
    }
    let hmac_len = u16::from_be_bytes([auth[attr_pos + 1], auth[attr_pos + 2]]) as usize;
    if hmac_size_end.checked_add(hmac_len) != Some(auth.len()) {
        return Err(AntiRollbackError::ProtocolFramingError(
            "TPM2 auth response trailing bytes mismatch",
        ));
    }
    Ok((tag, param_size))
}

/// Validate a `TPM2_NV_Increment` response packet (`TPM_RC_SUCCESS` and `parameterSize == 0`).
pub fn parse_tpm2_nv_increment_rsp(rsp: &[u8]) -> Result<(), AntiRollbackError> {
    let (_tag, param_size) = parse_tpm2_response_header(rsp)?;
    if param_size != 0 {
        return Err(AntiRollbackError::ProtocolFramingError(
            "TPM2_NV_Increment response must have zero parameter bytes",
        ));
    }
    Ok(())
}

/// Parse and validate a `TPM2_NV_Read` response packet carrying an 8-byte big-endian `u64`
/// `TPM_NT_COUNTER` value (`TPM2B_MAX_NV_BUFFER` with `size == 8`).
pub fn parse_tpm2_nv_read_u64_rsp(rsp: &[u8]) -> Result<u64, AntiRollbackError> {
    let (_tag, param_size) = parse_tpm2_response_header(rsp)?;
    if param_size != 10 {
        return Err(AntiRollbackError::ProtocolFramingError(
            "TPM2_NV_Read u64 response must have 10-byte parameterSize (2B length + 8B counter)",
        ));
    }
    let buf_len = u16::from_be_bytes([rsp[14], rsp[15]]) as usize;
    if buf_len != 8 {
        return Err(AntiRollbackError::ProtocolFramingError(
            "TPM2_NV_Read TPM2B_MAX_NV_BUFFER size != 8",
        ));
    }
    let counter_be: [u8; 8] = rsp[16..24]
        .try_into()
        .map_err(|_| AntiRollbackError::ProtocolFramingError("TPM2 counter slice error"))?;
    Ok(u64::from_be_bytes(counter_be))
}

/// Marshal `TPM2_NV_ReadPublic` (Part 3 §31.6, Table 218): `TPM_ST_NO_SESSIONS`, one
/// handle, no authorization.
pub fn marshal_tpm2_nv_read_public_cmd(nv_index: u32) -> Result<Vec<u8>, AntiRollbackError> {
    if !is_valid_tpm2_nv_index(nv_index) {
        return Err(AntiRollbackError::ProtocolFramingError(
            "nv_index handle outside TPM_HT_NV_INDEX (0x01000000..=0x01FFFFFF)",
        ));
    }
    let mut pkt = Vec::with_capacity(14);
    pkt.extend_from_slice(&TPM_ST_NO_SESSIONS.to_be_bytes());
    pkt.extend_from_slice(&14u32.to_be_bytes());
    pkt.extend_from_slice(&TPM_CC_NV_READ_PUBLIC.to_be_bytes());
    pkt.extend_from_slice(&nv_index.to_be_bytes());
    Ok(pkt)
}

/// The public area of an NV index (`TPMS_NV_PUBLIC`, Part 2 §13.5) as far as an anchor
/// needs it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Tpm2NvPublic {
    pub nv_index: u32,
    pub name_alg: u16,
    /// `TPMA_NV` (Part 2 §13.4).
    pub attributes: u32,
    pub data_size: u16,
}

impl Tpm2NvPublic {
    /// Whether the counter has ever been incremented (`TPMA_NV_WRITTEN`).
    pub const fn is_written(&self) -> bool {
        self.attributes & TPMA_NV_WRITTEN != 0
    }

    /// What an anchor needs of its index, whatever its age:
    ///
    /// * `TPM_NT_COUNTER` with an 8-octet value: only `TPM2_NV_Increment` changes it
    ///   and nothing lowers it (Part 3 §31.2);
    /// * `TPMA_NV_AUTHREAD` and `TPMA_NV_AUTHWRITE`: the anchor authorizes with the
    ///   index's own authorization value;
    /// * `TPMA_NV_ORDERLY` CLEAR: an orderly counter is advanced by up to
    ///   `MAX_ORDERLY_COUNT` at the startup after an unclean shutdown (Part 3 §31.2,
    ///   §31.8 NOTE 2), which a seal holding the exact count would read as a rollback;
    /// * `TPMA_NV_CLEAR_STCLEAR` CLEAR (it cannot be SET on a counter);
    /// * not write- or read-locked.
    pub fn check_anchor_counter(&self, nv_index: u32) -> Result<(), AntiRollbackError> {
        let unsuitable = AntiRollbackError::UnsuitableCounterIndex;
        if self.nv_index != nv_index {
            return Err(AntiRollbackError::ProtocolFramingError(
                "TPM2_NV_ReadPublic answered for another index",
            ));
        }
        if self.attributes & TPMA_NV_TPM_NT_MASK != TPMA_NV_TPM_NT_COUNTER || self.data_size != 8 {
            return Err(unsuitable(
                "the index is not a TPM_NT_COUNTER (define it with nt=counter)",
            ));
        }
        if self.attributes & TPMA_NV_AUTHREAD == 0 || self.attributes & TPMA_NV_AUTHWRITE == 0 {
            return Err(unsuitable(
                "the index lacks TPMA_NV_AUTHREAD or TPMA_NV_AUTHWRITE (define it with authread|authwrite)",
            ));
        }
        if self.attributes & (TPMA_NV_ORDERLY | TPMA_NV_CLEAR_STCLEAR) != 0 {
            return Err(unsuitable(
                "the index is TPMA_NV_ORDERLY: its count jumps after an unclean shutdown (define it without orderly)",
            ));
        }
        if self.attributes & (TPMA_NV_WRITELOCKED | TPMA_NV_READLOCKED) != 0 {
            return Err(unsuitable("the index is read- or write-locked"));
        }
        Ok(())
    }
}

/// Parse a `TPM2_NV_ReadPublic` response (Part 3 §31.6, Table 219): `TPM2B_NV_PUBLIC`
/// then `TPM2B_NAME`, exact lengths.
pub fn parse_tpm2_nv_read_public_rsp(rsp: &[u8]) -> Result<Tpm2NvPublic, AntiRollbackError> {
    let framing = AntiRollbackError::ProtocolFramingError;
    if rsp.len() < 10 {
        return Err(framing("truncated TPM2 response header (< 10 bytes)"));
    }
    let tag = u16::from_be_bytes([rsp[0], rsp[1]]);
    let size = u32::from_be_bytes([rsp[2], rsp[3], rsp[4], rsp[5]]) as usize;
    let rc = u32::from_be_bytes([rsp[6], rsp[7], rsp[8], rsp[9]]);
    if size != rsp.len() {
        return Err(framing(
            "TPM2 responseSize field mismatches received byte length",
        ));
    }
    if rc != TPM_RC_SUCCESS {
        return Err(AntiRollbackError::Tpm2ResponseError(rc));
    }
    if tag != TPM_ST_NO_SESSIONS {
        return Err(framing(
            "TPM2_NV_ReadPublic response must be TPM_ST_NO_SESSIONS",
        ));
    }
    let short = || framing("TPM2_NV_ReadPublic response truncated");
    let body = &rsp[10..];
    let public_len = u16::from_be_bytes(body.get(..2).ok_or_else(short)?.try_into().unwrap());
    let public = body.get(2..2 + public_len as usize).ok_or_else(short)?;
    // nvIndex(4) nameAlg(2) attributes(4) authPolicy.size(2) [authPolicy] dataSize(2)
    if public.len() < 14 {
        return Err(short());
    }
    let policy_len = u16::from_be_bytes([public[10], public[11]]) as usize;
    if public.len() != 14 + policy_len {
        return Err(framing("TPMS_NV_PUBLIC length mismatches its authPolicy"));
    }
    let name = &body[2 + public_len as usize..];
    if name.len() < 2 || name.len() != 2 + u16::from_be_bytes([name[0], name[1]]) as usize {
        return Err(framing("TPM2B_NAME length mismatches the response"));
    }
    Ok(Tpm2NvPublic {
        nv_index: u32::from_be_bytes(public[..4].try_into().unwrap()),
        name_alg: u16::from_be_bytes([public[4], public[5]]),
        attributes: u32::from_be_bytes(public[6..10].try_into().unwrap()),
        data_size: u16::from_be_bytes([public[12 + policy_len], public[13 + policy_len]]),
    })
}

/// Read and parse the public area of `nv_index`.
pub fn tpm2_nv_read_public<T: Tpm2Transport + ?Sized>(
    transport: &T,
    nv_index: u32,
) -> Result<Tpm2NvPublic, AntiRollbackError> {
    parse_tpm2_nv_read_public_rsp(&transport.transmit(&marshal_tpm2_nv_read_public_cmd(nv_index)?)?)
}

/// Transport abstraction over the Linux kernel TPM 2.0 resource manager (`/dev/tpmrm0`) or
/// the software model in [`tpm2_model`].
pub trait Tpm2Transport: Send + Sync {
    fn transmit(&self, command: &[u8]) -> Result<Vec<u8>, AntiRollbackError>;
}

/// Character-device transport speaking directly to `/dev/tpmrm0` (the kernel-managed TPM 2.0
/// resource manager, which isolates transient objects and serializes device access per open fd).
pub struct DevTpmRm0 {
    dev: Mutex<File>,
}

impl DevTpmRm0 {
    /// Default Linux kernel TPM 2.0 resource-manager device node.
    pub const DEFAULT_DEVICE_PATH: &'static str = "/dev/tpmrm0";

    /// Open `/dev/tpmrm0` for synchronous command/response exchange.
    pub fn open_default() -> Result<Self, AntiRollbackError> {
        Self::open_path(Self::DEFAULT_DEVICE_PATH)
    }

    /// Open an explicit TPM resource-manager character device path.
    pub fn open_path(path: impl AsRef<Path>) -> Result<Self, AntiRollbackError> {
        let meta = fs::symlink_metadata(path.as_ref())?;
        if meta.file_type().is_symlink() {
            return Err(AntiRollbackError::ProtocolFramingError(
                "refusing symlinked TPM2 device path",
            ));
        }
        let file = OpenOptions::new().read(true).write(true).open(path)?;
        Ok(Self {
            dev: Mutex::new(file),
        })
    }
}

impl Tpm2Transport for DevTpmRm0 {
    fn transmit(&self, command: &[u8]) -> Result<Vec<u8>, AntiRollbackError> {
        let mut guard = self
            .dev
            .lock()
            .map_err(|_| AntiRollbackError::Io(io::ErrorKind::Other))?;
        guard.write_all(command)?;
        // Linux `/dev/tpmrm0` delivers the complete response in a single `read()` call.
        let mut rsp = vec![0u8; MAX_TPM2_RSP_BYTES];
        let n = loop {
            match guard.read(&mut rsp) {
                Ok(n) => break n,
                Err(e) if e.kind() == io::ErrorKind::Interrupted => continue,
                Err(e) => return Err(AntiRollbackError::Io(e.kind())),
            }
        };
        if n < 10 {
            return Err(AntiRollbackError::ProtocolFramingError(
                "short read from /dev/tpmrm0 (< 10-byte TPM2 header)",
            ));
        }
        rsp.truncate(n);
        Ok(rsp)
    }
}

const TPM_ANCHOR_MAGIC: &[u8; 8] = b"QSTPMNV1";
const TPM_ANCHOR_RECORD_LEN: usize = 152;
// Layout (152 bytes):
//   [0..8]     magic "QSTPMNV1"
//   [8..12]    nv_index (u32 BE)
//   [12..16]   auth_handle (u32 BE)
//   [16..24]   committed_hw_counter (u64 LE)
//   [24..32]   committed_generation (u64 LE)
//   [32..64]   committed_tag ([u8; 32])
//   [64]       has_pending (0 or 1)
//   [65..72]   reserved ([0u8; 7])
//   [72..80]   pending_hw_counter (u64 LE)
//   [80..88]   pending_generation (u64 LE)
//   [88..120]  pending_tag ([u8; 32])
//   [120..152] CSHAKE256 MAC ([u8; 32])

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct TpmSealedState {
    committed_hw: u64,
    committed_cp: LedgerCheckpoint,
    pending: Option<(u64, LedgerCheckpoint)>,
}

/// Hardware-backed [`ExternalMonotoneAnchor`] binding [`LedgerCheckpoint`] progression to a
/// 64-bit TPM 2.0 `TPM_NT_COUNTER` NVRAM index over `/dev/tpmrm0`.
///
/// ### One counter per anchor, proven by the TPM
/// Each sealed record needs its own NV index: sharing one makes an honest advance of
/// either record leave the other behind. A new anchor therefore only accepts a counter
/// that has never been incremented (`TPMA_NV_WRITTEN` CLEAR in `TPM2_NV_ReadPublic`):
/// anything else that used the index would have set it. The anchor's first advance is
/// the first `TPM2_NV_Increment`, which leaves a count above every count any counter
/// on this TPM ever held (Part 3 §31.2), so an index that is undefined and defined
/// again never repeats a sealed value. The exact hardware/seal equality below must
/// never be relaxed to tolerate a shared counter.
///
/// The index must be a `TPM_NT_COUNTER` with `authread|authwrite` and without
/// `orderly` ([`Tpm2NvPublic::check_anchor_counter`]); this is checked on every open.
///
/// ### Two-Phase Crash-Safe & Zero-Slack Anti-Rollback Protocol
/// 1. Before issuing `TPM2_NV_Increment`, [`Tpm2NvMonotoneAnchor::advance_checked`] stages
///    `pending = (hw_counter + 1, next_checkpoint)` in the MAC-authenticated [`LockedRecord`].
/// 2. It transmits `TPM2_NV_Increment` (`0x0000_0134`) followed by `TPM2_NV_Read` (`0x0000_014E`),
///    verifying the hardware counter advanced to `hw_counter + 1`.
/// 3. It finalizes `committed = (hw_counter + 1, next_checkpoint), pending = None`.
///
/// On recovery (`load_checked`), the live hardware counter read via `TPM2_NV_Read` MUST match
/// either `committed.hw_counter` or `pending.hw_counter`. Any disk snapshot restore that rewinds
/// the local record behind the hardware TPM2 counter (`hw_counter > max(committed, pending)`)
/// immediately halts with [`AntiRollbackError::RollbackOrForkDetected`].
pub struct Tpm2NvMonotoneAnchor<T: Tpm2Transport = DevTpmRm0> {
    transport: T,
    record: LockedRecord,
    nv_index: u32,
    auth_handle: u32,
    auth_value: [u8; MAX_TPM2_AUTH_BYTES],
    auth_len: usize,
    mac_key: [u8; 32],
}

impl<T: Tpm2Transport> Drop for Tpm2NvMonotoneAnchor<T> {
    fn drop(&mut self) {
        wipe_bytes(&mut self.auth_value);
        wipe_bytes32(&mut self.mac_key);
    }
}

impl Tpm2NvMonotoneAnchor<DevTpmRm0> {
    /// Open `/dev/tpmrm0` and bind `nv_index` (using index-self password authorization) to the
    /// local sealed state file at `seal_path`.
    pub fn open_dev_tpmrm0(
        seal_path: impl Into<PathBuf>,
        nv_index: u32,
        nv_password: &[u8],
        mut mac_key: [u8; 32],
    ) -> Result<Self, AntiRollbackError> {
        let key_arg = SecretBuffer(&mut mac_key);
        let dev = DevTpmRm0::open_default()?;
        // The by-value argument is the callee's to wipe; `key_arg` wipes this frame's copy.
        Self::open_with_transport(dev, seal_path, nv_index, nv_index, nv_password, **key_arg)
    }
}

impl<T: Tpm2Transport> Tpm2NvMonotoneAnchor<T> {
    /// Construct a [`Tpm2NvMonotoneAnchor`] over any [`Tpm2Transport`] (e.g. [`DevTpmRm0`] or
    /// deterministic mock hardware in unit tests).
    pub fn open_with_transport(
        transport: T,
        seal_path: impl Into<PathBuf>,
        auth_handle: u32,
        nv_index: u32,
        nv_password: &[u8],
        mut mac_key: [u8; 32],
    ) -> Result<Self, AntiRollbackError> {
        // Wipes the by-value key argument on every return, `?` and unwind. The secrets
        // are copied straight into the anchor (whose `Drop` wipes them), never through
        // intermediate by-value stack temporaries.
        let key_arg = SecretBuffer(&mut mac_key);
        if !is_valid_tpm2_nv_index(nv_index) {
            return Err(AntiRollbackError::ProtocolFramingError(
                "nv_index handle outside TPM_HT_NV_INDEX (0x01000000..=0x01FFFFFF)",
            ));
        }
        if nv_password.len() > MAX_TPM2_AUTH_BYTES {
            return Err(AntiRollbackError::ProtocolFramingError(
                "TPM2 password authorization exceeds 64-byte TPM2B_AUTH limit",
            ));
        }

        let this = Self::assemble(
            transport,
            LockedRecord::acquire(seal_path)?,
            auth_handle,
            nv_index,
            nv_password,
            key_arg.as_slice(),
        );
        drop(key_arg);
        let public = tpm2_nv_read_public(&this.transport, nv_index)?;
        public.check_anchor_counter(nv_index)?;
        match (this.is_unenrolled()?, public.is_written()) {
            (true, true) => {
                return Err(AntiRollbackError::UnsuitableCounterIndex(
                    "the counter has already been incremented: it backs another anchor or an earlier enrollment; a new anchor needs an index that was never written",
                ));
            }
            (false, false) => {
                return Err(AntiRollbackError::RollbackOrForkDetected(
                    "a seal exists but the TPM2 NV counter was never written (index redefined, or another TPM)",
                ));
            }
            (true, false) => {}
            // Verify the hardware counter against the local sealed state.
            (false, true) => {
                this.load_checked()?;
            }
        }
        Ok(this)
    }

    fn assemble(
        transport: T,
        record: LockedRecord,
        auth_handle: u32,
        nv_index: u32,
        nv_password: &[u8],
        mac_key: &[u8],
    ) -> Self {
        let mut this = Self {
            transport,
            record,
            nv_index,
            auth_handle,
            auth_value: [0u8; MAX_TPM2_AUTH_BYTES],
            auth_len: nv_password.len(),
            mac_key: [0u8; 32],
        };
        this.mac_key.copy_from_slice(mac_key);
        this.auth_value[..nv_password.len()].copy_from_slice(nv_password);
        this
    }

    /// Move an existing seal from counter `old_nv_index` to the never-written counter
    /// `new_nv_index`, keeping its checkpoint. For seals that were enrolled on a
    /// counter shared with other seals and can therefore never match it again.
    ///
    /// **This does not establish that the seal is current.** The old counter cannot
    /// show it (that is the defect being repaired), so the caller must have proven it
    /// some other way before calling, for every seal it moves; see the CLI's
    /// `reanchor_shared_tpm_index` for the proof used there. What this function does
    /// check: the seal authenticates under `old_nv_index` with no commit in flight,
    /// and the new counter is a suitable, never-written anchor counter.
    ///
    /// A seal already bound to `new_nv_index` (an earlier, interrupted run) is opened
    /// normally against that counter instead.
    ///
    /// Not crash-atomic: the new counter is incremented before the seal is replaced. A
    /// crash or a failed write between the two leaves the seal on `old_nv_index` and
    /// `new_nv_index` written, and a retry then refuses `new_nv_index` as used. That
    /// fails closed (nothing is accepted that was not current), but the seal cannot be
    /// moved to that index any more. A recovery record written before the increment
    /// would have to stay unusable for a disk restored to that moment, since a
    /// never-written counter has no value to pin in advance; none is implemented.
    pub fn rebind_to_new_counter(
        transport: T,
        seal_path: impl Into<PathBuf>,
        old_nv_index: u32,
        new_nv_index: u32,
        nv_password: &[u8],
        mut mac_key: [u8; 32],
    ) -> Result<Self, AntiRollbackError> {
        let key_arg = SecretBuffer(&mut mac_key);
        if !is_valid_tpm2_nv_index(old_nv_index)
            || !is_valid_tpm2_nv_index(new_nv_index)
            || old_nv_index == new_nv_index
        {
            return Err(AntiRollbackError::ProtocolFramingError(
                "re-anchoring needs two distinct NV index handles",
            ));
        }
        if nv_password.len() > MAX_TPM2_AUTH_BYTES {
            return Err(AntiRollbackError::ProtocolFramingError(
                "TPM2 password authorization exceeds 64-byte TPM2B_AUTH limit",
            ));
        }
        let mut this = Self::assemble(
            transport,
            LockedRecord::open_existing(seal_path.into())?,
            new_nv_index,
            new_nv_index,
            nv_password,
            key_arg.as_slice(),
        );
        drop(key_arg);
        let public = tpm2_nv_read_public(&this.transport, new_nv_index)?;
        public.check_anchor_counter(new_nv_index)?;
        let raw = this
            .record
            .read_bounded(TPM_ANCHOR_RECORD_LEN)
            .map_err(|e| AntiRollbackError::Io(e.kind()))?;
        if this.decode_state(&raw).is_ok() {
            if !public.is_written() {
                return Err(AntiRollbackError::RollbackOrForkDetected(
                    "a seal exists but the TPM2 NV counter was never written (index redefined, or another TPM)",
                ));
            }
            this.load_checked()?;
            return Ok(this);
        }
        (this.nv_index, this.auth_handle) = (old_nv_index, old_nv_index);
        let old = this.decode_state(&raw);
        (this.nv_index, this.auth_handle) = (new_nv_index, new_nv_index);
        let old = old?;
        if old.pending.is_some() {
            return Err(AntiRollbackError::RollbackOrForkDetected(
                "the seal has a commit in flight on its old counter; its state cannot be carried over",
            ));
        }
        if public.is_written() {
            return Err(AntiRollbackError::UnsuitableCounterIndex(
                "the new counter has already been incremented; re-anchoring needs an index that was never written",
            ));
        }
        this.increment_hardware_counter()?;
        let rebound = TpmSealedState {
            committed_hw: this.read_hardware_counter()?,
            committed_cp: old.committed_cp,
            pending: None,
        };
        this.record.replace(&this.encode_state(&rebound))?;
        Ok(this)
    }

    /// Test fixture: put an existing seal on `shared_nv_index` the way releases before
    /// per-domain counters enrolled every anchor of a workflow (read the counter,
    /// increment it, seal the new count), whatever else already uses that counter.
    /// Calling it for several seals in turn reproduces a shared-index enrollment.
    #[cfg(any(test, feature = "tpm-model"))]
    pub fn fixture_reseal_on_shared_counter(
        transport: T,
        seal_path: impl Into<PathBuf>,
        current_nv_index: u32,
        shared_nv_index: u32,
        nv_password: &[u8],
        mac_key: [u8; 32],
    ) -> Result<(), AntiRollbackError> {
        let mut this = Self::assemble(
            transport,
            LockedRecord::open_existing(seal_path.into())?,
            current_nv_index,
            current_nv_index,
            nv_password,
            &mac_key,
        );
        let raw = this
            .record
            .read_bounded(TPM_ANCHOR_RECORD_LEN)
            .map_err(|e| AntiRollbackError::Io(e.kind()))?;
        let current = this.decode_state(&raw)?;
        (this.nv_index, this.auth_handle) = (shared_nv_index, shared_nv_index);
        this.increment_hardware_counter()?;
        let shared = TpmSealedState {
            committed_hw: this.read_hardware_counter()?,
            committed_cp: current.committed_cp,
            pending: None,
        };
        this.record.replace(&this.encode_state(&shared))?;
        Ok(())
    }

    /// No seal has been written yet: the anchor's first advance will enrol it.
    fn is_unenrolled(&self) -> Result<bool, AntiRollbackError> {
        match self.record.read_bounded(TPM_ANCHOR_RECORD_LEN) {
            Ok(_) => Ok(false),
            Err(e) if e.kind() == io::ErrorKind::NotFound && self.record.is_fresh() => Ok(true),
            Err(e) => Err(AntiRollbackError::Io(e.kind())),
        }
    }

    fn auth_slice(&self) -> &[u8] {
        &self.auth_value[..self.auth_len]
    }

    /// Read the live 64-bit counter directly from the TPM 2.0 NV index via `TPM2_NV_Read`.
    pub fn read_hardware_counter(&self) -> Result<u64, AntiRollbackError> {
        let mut cmd =
            marshal_tpm2_nv_read_u64_cmd(self.auth_handle, self.nv_index, self.auth_slice())?;
        let rsp_res = self.transport.transmit(&cmd);
        wipe_bytes(&mut cmd);
        let rsp = rsp_res?;
        parse_tpm2_nv_read_u64_rsp(&rsp)
    }

    fn increment_hardware_counter(&self) -> Result<(), AntiRollbackError> {
        let mut cmd =
            marshal_tpm2_nv_increment_cmd(self.auth_handle, self.nv_index, self.auth_slice())?;
        let rsp_res = self.transport.transmit(&cmd);
        wipe_bytes(&mut cmd);
        let rsp = rsp_res?;
        parse_tpm2_nv_increment_rsp(&rsp)
    }

    fn compute_mac(&self, body_without_mac: &[u8]) -> [u8; 32] {
        let mut xof = Cshake256Xof::new(b"QSAG.TPM2.ANCHOR.MAC/v1");
        xof.absorb(&self.mac_key);
        xof.absorb(&self.record.lock_seal());
        xof.absorb(&self.nv_index.to_be_bytes());
        xof.absorb(&self.auth_handle.to_be_bytes());
        xof.absorb(&(body_without_mac.len() as u64).to_le_bytes());
        xof.absorb(body_without_mac);
        let mut out = [0u8; 32];
        xof.squeeze(&mut out);
        out
    }

    fn encode_state(&self, st: &TpmSealedState) -> [u8; TPM_ANCHOR_RECORD_LEN] {
        let mut buf = [0u8; TPM_ANCHOR_RECORD_LEN];
        buf[..8].copy_from_slice(TPM_ANCHOR_MAGIC);
        buf[8..12].copy_from_slice(&self.nv_index.to_be_bytes());
        buf[12..16].copy_from_slice(&self.auth_handle.to_be_bytes());
        buf[16..24].copy_from_slice(&st.committed_hw.to_le_bytes());
        buf[24..32].copy_from_slice(&st.committed_cp.generation.to_le_bytes());
        buf[32..64].copy_from_slice(&st.committed_cp.tag);
        if let Some((pend_hw, pend_cp)) = st.pending {
            buf[64] = 1;
            buf[72..80].copy_from_slice(&pend_hw.to_le_bytes());
            buf[80..88].copy_from_slice(&pend_cp.generation.to_le_bytes());
            buf[88..120].copy_from_slice(&pend_cp.tag);
        }
        let mac = self.compute_mac(&buf[..120]);
        buf[120..152].copy_from_slice(&mac);
        buf
    }

    fn decode_state(&self, raw: &[u8]) -> Result<TpmSealedState, AntiRollbackError> {
        if raw.len() != TPM_ANCHOR_RECORD_LEN || &raw[..8] != TPM_ANCHOR_MAGIC {
            return Err(AntiRollbackError::AuthenticationFailed);
        }
        let expected_mac = self.compute_mac(&raw[..120]);
        let stored_mac: [u8; 32] = raw[120..152]
            .try_into()
            .map_err(|_| AntiRollbackError::AuthenticationFailed)?;
        if !ct_eq_bytes32(&stored_mac, &expected_mac) {
            return Err(AntiRollbackError::AuthenticationFailed);
        }
        let nv_idx = u32::from_be_bytes(raw[8..12].try_into().unwrap());
        let auth_hdl = u32::from_be_bytes(raw[12..16].try_into().unwrap());
        if nv_idx != self.nv_index || auth_hdl != self.auth_handle {
            return Err(AntiRollbackError::AuthenticationFailed);
        }
        if raw[65..72] != [0u8; 7] {
            return Err(AntiRollbackError::AuthenticationFailed);
        }
        let committed_hw = u64::from_le_bytes(raw[16..24].try_into().unwrap());
        let committed_gen = u64::from_le_bytes(raw[24..32].try_into().unwrap());
        let committed_tag: [u8; 32] = raw[32..64].try_into().unwrap();
        let pending = match raw[64] {
            0 => {
                if raw[72..120] != [0u8; 48] {
                    return Err(AntiRollbackError::AuthenticationFailed);
                }
                None
            }
            1 => {
                let pend_hw = u64::from_le_bytes(raw[72..80].try_into().unwrap());
                let pend_gen = u64::from_le_bytes(raw[80..88].try_into().unwrap());
                let pend_tag: [u8; 32] = raw[88..120].try_into().unwrap();
                if pend_hw != committed_hw.saturating_add(1) || pend_gen <= committed_gen {
                    return Err(AntiRollbackError::AuthenticationFailed);
                }
                Some((
                    pend_hw,
                    LedgerCheckpoint {
                        generation: pend_gen,
                        tag: pend_tag,
                    },
                ))
            }
            _ => return Err(AntiRollbackError::AuthenticationFailed),
        };
        Ok(TpmSealedState {
            committed_hw,
            committed_cp: LedgerCheckpoint {
                generation: committed_gen,
                tag: committed_tag,
            },
            pending,
        })
    }

    fn reconcile_with_hardware(
        &self,
        st: TpmSealedState,
        live_hw: u64,
    ) -> Result<(u64, LedgerCheckpoint), AntiRollbackError> {
        if live_hw == st.committed_hw {
            return Ok((st.committed_hw, st.committed_cp));
        }
        if let Some((pend_hw, pend_cp)) = st.pending
            && live_hw == pend_hw
        {
            return Ok((pend_hw, pend_cp));
        }
        if live_hw > st.committed_hw {
            return Err(AntiRollbackError::RollbackOrForkDetected(
                "local custody state lags TPM2 NV monotonic counter (disk rollback, or another anchor incremented this index; the two cannot be told apart)",
            ));
        }
        Err(AntiRollbackError::RollbackOrForkDetected(
            "TPM2 NV counter regressed below sealed baseline (NVRAM reset or wrong TPM)",
        ))
    }

    /// Authenticate local sealed state against the live TPM 2.0 hardware NV counter.
    pub fn load_checked(&self) -> Result<Option<LedgerCheckpoint>, AntiRollbackError> {
        // An unenrolled anchor has an unwritten counter, which cannot be read.
        if self.is_unenrolled()? {
            return Ok(None);
        }
        let live_hw = self.read_hardware_counter()?;
        let raw = self
            .record
            .read_bounded(TPM_ANCHOR_RECORD_LEN)
            .map_err(|e| AntiRollbackError::Io(e.kind()))?;
        let st = self.decode_state(&raw)?;
        let (_hw, cp) = self.reconcile_with_hardware(st, live_hw)?;
        Ok(Some(cp))
    }

    /// Atomically increment the TPM 2.0 hardware NV counter and seal `checkpoint`.
    pub fn advance_checked(&self, checkpoint: LedgerCheckpoint) -> Result<(), AntiRollbackError> {
        match self.record.read_bounded(TPM_ANCHOR_RECORD_LEN) {
            Ok(raw) => {
                let live_hw = self.read_hardware_counter()?;
                let st = self.decode_state(&raw)?;
                let (active_hw, active_cp) = self.reconcile_with_hardware(st, live_hw)?;
                if checkpoint.generation < active_cp.generation {
                    return Err(AntiRollbackError::RollbackOrForkDetected(
                        "checkpoint generation regressed below TPM2-sealed generation",
                    ));
                }
                if checkpoint.generation == active_cp.generation {
                    if !ct_eq_bytes32(&checkpoint.tag, &active_cp.tag) {
                        return Err(AntiRollbackError::RollbackOrForkDetected(
                            "divergent checkpoint tag at equal TPM2 generation",
                        ));
                    }
                    // If `active_cp` came from a crash-interrupted `pending` slot whose TPM2
                    // increment already succeeded, finalize it cleanly without re-incrementing.
                    if st.pending.is_some() && active_hw != st.committed_hw {
                        let finalized = TpmSealedState {
                            committed_hw: active_hw,
                            committed_cp: active_cp,
                            pending: None,
                        };
                        self.record.replace(&self.encode_state(&finalized))?;
                    }
                    return Ok(());
                }

                let next_hw =
                    active_hw
                        .checked_add(1)
                        .ok_or(AntiRollbackError::ProtocolFramingError(
                            "TPM2 64-bit NV counter exhausted",
                        ))?;

                // Phase 1: Stage pending `(next_hw, checkpoint)` to durable disk BEFORE
                // incrementing the irreversible TPM2 NV counter.
                let staged = TpmSealedState {
                    committed_hw: active_hw,
                    committed_cp: active_cp,
                    pending: Some((next_hw, checkpoint)),
                };
                self.record.replace(&self.encode_state(&staged))?;

                // Phase 2: Increment hardware TPM2 NV counter and read-back verify `next_hw`.
                self.increment_hardware_counter()?;
                let after_hw = self.read_hardware_counter()?;
                if after_hw != next_hw {
                    return Err(AntiRollbackError::RollbackOrForkDetected(
                        "concurrent or out-of-band TPM2 NV counter mutation during commit",
                    ));
                }

                // Phase 3: Finalize `committed = (next_hw, checkpoint), pending = None`.
                let finalized = TpmSealedState {
                    committed_hw: next_hw,
                    committed_cp: checkpoint,
                    pending: None,
                };
                self.record.replace(&self.encode_state(&finalized))?;
                Ok(())
            }
            Err(e) if e.kind() == io::ErrorKind::NotFound && self.record.is_fresh() => {
                // Enrollment: the counter is unwritten (checked on open, and a written
                // counter makes the read below the only one that can succeed first).
                // The first increment initializes it above every count this TPM has
                // held (Part 3 §31.2) and is this anchor's alone.
                match self.read_hardware_counter() {
                    Err(AntiRollbackError::Tpm2ResponseError(TPM_RC_NV_UNINITIALIZED)) => {}
                    Ok(_) => {
                        return Err(AntiRollbackError::UnsuitableCounterIndex(
                            "the counter was incremented by something else during enrollment",
                        ));
                    }
                    Err(e) => return Err(e),
                }
                self.increment_hardware_counter()?;
                let next_hw = self.read_hardware_counter()?;
                let initial = TpmSealedState {
                    committed_hw: next_hw,
                    committed_cp: checkpoint,
                    pending: None,
                };
                self.record.replace(&self.encode_state(&initial))?;
                Ok(())
            }
            Err(e) => Err(AntiRollbackError::Io(e.kind())),
        }
    }
}

/// What a seal file holds, authenticated under its MAC key for `nv_index`. Says nothing
/// about the TPM: see [`inspect_tpm2_seal`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Tpm2SealView {
    /// The counter value the seal was last committed at.
    pub sealed_count: u64,
    pub checkpoint: LedgerCheckpoint,
    /// A commit was staged and not finalized.
    pub commit_in_flight: bool,
}

struct NoTpm;

impl Tpm2Transport for NoTpm {
    fn transmit(&self, _command: &[u8]) -> Result<Vec<u8>, AntiRollbackError> {
        Err(AntiRollbackError::ProtocolFramingError(
            "seal inspection does not talk to a TPM",
        ))
    }
}

/// Authenticate the seal at `seal_path` as one written for `nv_index` (authorized by
/// the index itself) and return its contents, without comparing it to any counter.
pub fn inspect_tpm2_seal(
    seal_path: impl Into<PathBuf>,
    nv_index: u32,
    mut mac_key: [u8; 32],
) -> Result<Tpm2SealView, AntiRollbackError> {
    let key_arg = SecretBuffer(&mut mac_key);
    let seal = Tpm2NvMonotoneAnchor::assemble(
        NoTpm,
        LockedRecord::open_existing(seal_path.into())?,
        nv_index,
        nv_index,
        b"",
        key_arg.as_slice(),
    );
    drop(key_arg);
    let raw = seal
        .record
        .read_bounded(TPM_ANCHOR_RECORD_LEN)
        .map_err(|e| AntiRollbackError::Io(e.kind()))?;
    let state = seal.decode_state(&raw)?;
    Ok(Tpm2SealView {
        sealed_count: state.committed_hw,
        checkpoint: state.committed_cp,
        commit_in_flight: state.pending.is_some(),
    })
}

/// Read a written counter with the index's own authorization value.
pub fn tpm2_nv_read_counter<T: Tpm2Transport + ?Sized>(
    transport: &T,
    nv_index: u32,
    nv_password: &[u8],
) -> Result<u64, AntiRollbackError> {
    let mut cmd = marshal_tpm2_nv_read_u64_cmd(nv_index, nv_index, nv_password)?;
    let rsp = transport.transmit(&cmd);
    wipe_bytes(&mut cmd);
    parse_tpm2_nv_read_u64_rsp(&rsp?)
}

impl<T: Tpm2Transport> ExternalMonotoneAnchor for Tpm2NvMonotoneAnchor<T> {
    fn load(&self) -> io::Result<Option<LedgerCheckpoint>> {
        self.load_checked()
            .map_err(AntiRollbackError::into_io_error)
    }

    fn advance(&self, checkpoint: LedgerCheckpoint) -> io::Result<()> {
        self.advance_checked(checkpoint)
            .map_err(AntiRollbackError::into_io_error)
    }
}

/// Composite [`ExternalMonotoneAnchor`] chaining two independent rollback/fork barriers
/// (typically [`HypervisorGenerationAnchor`] for instant VM/volume fork detection plus
/// [`Tpm2NvMonotoneAnchor`] for hardware NVRAM counter monotonicity).
pub struct CompositeAntiRollbackAnchor<A: ExternalMonotoneAnchor, B: ExternalMonotoneAnchor> {
    primary: A,
    secondary: B,
}

impl<A: ExternalMonotoneAnchor, B: ExternalMonotoneAnchor> CompositeAntiRollbackAnchor<A, B> {
    pub const fn new(primary: A, secondary: B) -> Self {
        Self { primary, secondary }
    }
}

impl<A: ExternalMonotoneAnchor, B: ExternalMonotoneAnchor> ExternalMonotoneAnchor
    for CompositeAntiRollbackAnchor<A, B>
{
    fn load(&self) -> io::Result<Option<LedgerCheckpoint>> {
        let a = self.primary.load()?;
        let b = self.secondary.load()?;
        match (a, b) {
            (None, None) => Ok(None),
            (Some(cp), None) | (None, Some(cp)) => Ok(Some(cp)),
            (Some(cp_a), Some(cp_b)) => {
                if cp_a.generation == cp_b.generation {
                    if !ct_eq_bytes32(&cp_a.tag, &cp_b.tag) {
                        return Err(AntiRollbackError::RollbackOrForkDetected(
                            "composite anchors disagree on checkpoint tag at equal generation",
                        )
                        .into_io_error());
                    }
                    Ok(Some(cp_a))
                } else if cp_a.generation > cp_b.generation {
                    Ok(Some(cp_a))
                } else {
                    Ok(Some(cp_b))
                }
            }
        }
    }

    fn advance(&self, checkpoint: LedgerCheckpoint) -> io::Result<()> {
        self.primary.advance(checkpoint)?;
        self.secondary.advance(checkpoint)
    }
}

/// A software model of the TPM 2.0 NV counter commands an anchor issues, for tests
/// that cannot reach a TPM. It is not a TPM: it has no hierarchies, sessions other
/// than `TPM_RS_PW`, policies, dictionary-attack lockout or real Names.
///
/// Modelled, with the clause each rule comes from (TCG TPM 2.0 Library, Level 00
/// Revision 01.59):
///
/// * `TPM2_NV_ReadPublic` returns `TPMS_NV_PUBLIC` without authorization (Part 3 §31.6).
/// * A defined, never-written index: `TPM2_NV_Read` fails with
///   `TPM_RC_NV_UNINITIALIZED` (Part 3 §31.13).
/// * `TPM2_NV_Increment` on an index that is not `TPM_NT_COUNTER` fails with
///   `TPM_RC_ATTRIBUTES`, on a write-locked index with `TPM_RC_NV_LOCKED`; otherwise it
///   SETs `TPMA_NV_WRITTEN` and adds one (Part 3 §31.8).
/// * A new counter starts above every count any counter on the TPM has held since
///   manufacture, including counters since undefined (Part 3 §31.2). As in the TCG
///   reference code the initial value is taken at the first increment.
/// * `TPMA_NV_ORDERLY` counters keep recent increments in RAM; after an unclean
///   shutdown `MAX_ORDERLY_COUNT` is ORed into the count (Part 3 §31.2, §31.8 NOTE 2).
/// * Index authorization: `TPMA_NV_AUTHREAD` / `TPMA_NV_AUTHWRITE` gate the use of the
///   index's own authorization value (`TPM_RC_NV_AUTHORIZATION` otherwise, Part 3
///   §31.1); a wrong value is `TPM_RC_BAD_AUTH` (Part 2 §6.6.3).
/// * A handle that names no index is `TPM_RC_HANDLE` (Part 2 §6.6.3).
///
/// `define_*`, `undefine`, `write_lock` and `restart` stand in for the owner-side
/// commands (`TPM2_NV_DefineSpace` §31.3, `TPM2_NV_UndefineSpace` §31.4,
/// `TPM2_NV_WriteLock` §31.11, `TPM2_Startup` §9.3) that an anchor never issues.
#[cfg(any(test, feature = "tpm-model"))]
pub mod tpm2_model {
    use super::*;
    use std::collections::BTreeMap;
    use std::sync::{Arc, Mutex};

    /// `MAX_ORDERLY_COUNT` of the TCG reference implementation (a power of two minus one).
    pub const MAX_ORDERLY_COUNT: u64 = 255;
    /// `TPM_ALG_SHA256`.
    const NAME_ALG: u16 = 0x000B;

    struct Index {
        attributes: u32,
        auth: Vec<u8>,
        data_size: u16,
        count: u64,
    }

    #[derive(Default)]
    struct State {
        indices: BTreeMap<u32, Index>,
        /// The highest count any counter on this TPM has held.
        max_count: u64,
        forced_rc: Option<u32>,
    }

    /// Shared handle: clones talk to the same TPM.
    #[derive(Clone, Default)]
    pub struct ModelTpm2(Arc<Mutex<State>>);

    fn error_response(rc: u32) -> Vec<u8> {
        let mut rsp = Vec::with_capacity(10);
        rsp.extend_from_slice(&TPM_ST_NO_SESSIONS.to_be_bytes());
        rsp.extend_from_slice(&10u32.to_be_bytes());
        rsp.extend_from_slice(&rc.to_be_bytes());
        rsp
    }

    /// A `TPM_ST_SESSIONS` success response with one password session's
    /// `TPMS_AUTH_RESPONSE` (empty nonce, `continueSession`, empty hmac).
    pub fn session_response(params: &[u8]) -> Vec<u8> {
        let total = (10 + 4 + params.len() + 5) as u32;
        let mut rsp = Vec::with_capacity(total as usize);
        rsp.extend_from_slice(&TPM_ST_SESSIONS.to_be_bytes());
        rsp.extend_from_slice(&total.to_be_bytes());
        rsp.extend_from_slice(&TPM_RC_SUCCESS.to_be_bytes());
        rsp.extend_from_slice(&(params.len() as u32).to_be_bytes());
        rsp.extend_from_slice(params);
        rsp.extend_from_slice(&[0, 0, 1, 0, 0]);
        rsp
    }

    impl ModelTpm2 {
        pub fn new() -> Self {
            Self::default()
        }

        /// A TPM whose counters have already reached `max_count`.
        pub fn with_history(max_count: u64) -> Self {
            let tpm = Self::default();
            tpm.0.lock().unwrap().max_count = max_count;
            tpm
        }

        /// `TPM2_NV_DefineSpace` with explicit `TPMA_NV` attributes. `TPMA_NV_WRITTEN`
        /// and the lock bits are CLEAR in a new index (Part 2 §13.4).
        pub fn define_space(&self, nv_index: u32, attributes: u32, auth: &[u8], data_size: u16) {
            assert!(is_valid_tpm2_nv_index(nv_index));
            let mut state = self.0.lock().unwrap();
            assert!(
                !state.indices.contains_key(&nv_index),
                "TPM_RC_NV_DEFINED: {nv_index:#x}"
            );
            state.indices.insert(
                nv_index,
                Index {
                    attributes: attributes
                        & !(TPMA_NV_WRITTEN | TPMA_NV_WRITELOCKED | TPMA_NV_READLOCKED),
                    auth: auth.to_vec(),
                    data_size,
                    count: 0,
                },
            );
        }

        /// The index an anchor needs: `nt=counter`, `authread|authwrite|no_da`.
        pub fn define_counter(&self, nv_index: u32, auth: &[u8]) {
            self.define_space(
                nv_index,
                TPMA_NV_TPM_NT_COUNTER | TPMA_NV_AUTHREAD | TPMA_NV_AUTHWRITE | TPMA_NV_NO_DA,
                auth,
                8,
            );
        }

        /// `TPM2_NV_UndefineSpace`: the index goes, its count stays in the TPM's maximum.
        pub fn undefine(&self, nv_index: u32) {
            let mut state = self.0.lock().unwrap();
            let index = state.indices.remove(&nv_index).expect("TPM_RC_HANDLE");
            state.max_count = state.max_count.max(index.count);
        }

        /// `TPM2_NV_WriteLock` on an index that allows it.
        pub fn write_lock(&self, nv_index: u32) {
            let mut state = self.0.lock().unwrap();
            state
                .indices
                .get_mut(&nv_index)
                .expect("TPM_RC_HANDLE")
                .attributes |= TPMA_NV_WRITELOCKED;
        }

        /// `TPM2_Shutdown` (or its absence) followed by `TPM2_Startup(CLEAR)`.
        pub fn restart(&self, orderly_shutdown: bool) {
            let mut state = self.0.lock().unwrap();
            let state = &mut *state;
            for index in state.indices.values_mut() {
                index.attributes &= !(TPMA_NV_WRITELOCKED | TPMA_NV_READLOCKED);
                let orderly_counter = index.attributes & TPMA_NV_ORDERLY != 0
                    && index.attributes & TPMA_NV_TPM_NT_MASK == TPMA_NV_TPM_NT_COUNTER
                    && index.attributes & TPMA_NV_WRITTEN != 0;
                if orderly_counter && !orderly_shutdown {
                    index.count |= MAX_ORDERLY_COUNT;
                    state.max_count = state.max_count.max(index.count);
                }
            }
        }

        /// The count of a written counter; `None` while `TPMA_NV_WRITTEN` is CLEAR.
        pub fn count(&self, nv_index: u32) -> Option<u64> {
            let state = self.0.lock().unwrap();
            let index = state.indices.get(&nv_index).expect("TPM_RC_HANDLE");
            (index.attributes & TPMA_NV_WRITTEN != 0).then_some(index.count)
        }

        /// Every defined index with its count (`None` if never written).
        pub fn counts(&self) -> BTreeMap<u32, Option<u64>> {
            let state = self.0.lock().unwrap();
            state
                .indices
                .iter()
                .map(|(nv, index)| {
                    (
                        *nv,
                        (index.attributes & TPMA_NV_WRITTEN != 0).then_some(index.count),
                    )
                })
                .collect()
        }

        /// Answer every command with this response code (a failing device).
        pub fn force_response_code(&self, rc: Option<u32>) {
            self.0.lock().unwrap().forced_rc = rc;
        }

        fn read_public(state: &State, cmd: &[u8]) -> Vec<u8> {
            if cmd.len() != 14 || cmd[..2] != TPM_ST_NO_SESSIONS.to_be_bytes() {
                return error_response(TPM_RC_COMMAND_CODE);
            }
            let nv_index = u32::from_be_bytes(cmd[10..14].try_into().unwrap());
            let Some(index) = state.indices.get(&nv_index) else {
                return error_response(TPM_RC_HANDLE_1);
            };
            let mut public = Vec::new();
            public.extend_from_slice(&nv_index.to_be_bytes());
            public.extend_from_slice(&NAME_ALG.to_be_bytes());
            public.extend_from_slice(&index.attributes.to_be_bytes());
            public.extend_from_slice(&0u16.to_be_bytes());
            public.extend_from_slice(&index.data_size.to_be_bytes());
            // nameAlg || digest. The digest is a placeholder: nothing here checks Names.
            let mut name = Vec::new();
            name.extend_from_slice(&NAME_ALG.to_be_bytes());
            name.extend_from_slice(&[0; 32]);
            let total = 10 + 2 + public.len() + 2 + name.len();
            let mut rsp = Vec::with_capacity(total);
            rsp.extend_from_slice(&TPM_ST_NO_SESSIONS.to_be_bytes());
            rsp.extend_from_slice(&(total as u32).to_be_bytes());
            rsp.extend_from_slice(&TPM_RC_SUCCESS.to_be_bytes());
            rsp.extend_from_slice(&(public.len() as u16).to_be_bytes());
            rsp.extend_from_slice(&public);
            rsp.extend_from_slice(&(name.len() as u16).to_be_bytes());
            rsp.extend_from_slice(&name);
            rsp
        }

        fn nv_command(state: &mut State, cc: u32, cmd: &[u8]) -> Vec<u8> {
            // tag(2) size(4) cc(4) authHandle(4) nvIndex(4) authSize(4) TPM_RS_PW(4)
            // nonce.size(2) attributes(1) hmac.size(2) hmac parameters
            if cmd.len() < 31 || cmd[..2] != TPM_ST_SESSIONS.to_be_bytes() {
                return error_response(TPM_RC_COMMAND_CODE);
            }
            let word = |at: usize| u32::from_be_bytes(cmd[at..at + 4].try_into().unwrap());
            let (auth_handle, nv_index) = (word(10), word(14));
            let hmac_len = u16::from_be_bytes([cmd[29], cmd[30]]) as usize;
            let well_formed = word(22) == TPM_RS_PW
                && cmd[26..28] == [0, 0]
                && word(18) as usize == 9 + hmac_len
                && cmd.len() >= 31 + hmac_len;
            if !well_formed {
                return error_response(TPM_RC_COMMAND_CODE);
            }
            let (hmac, params) = cmd[31..].split_at(hmac_len);
            // The anchor authorizes with the index itself (Auth Role USER, §31.8 Table 222).
            if auth_handle != nv_index {
                return error_response(TPM_RC_NV_AUTHORIZATION);
            }
            let max_count = state.max_count;
            let Some(index) = state.indices.get_mut(&nv_index) else {
                return error_response(TPM_RC_HANDLE_1);
            };
            let needed = if cc == TPM_CC_NV_INCREMENT {
                TPMA_NV_AUTHWRITE
            } else {
                TPMA_NV_AUTHREAD
            };
            if index.attributes & needed == 0 {
                return error_response(TPM_RC_NV_AUTHORIZATION);
            }
            if hmac != index.auth.as_slice() {
                return error_response(TPM_RC_BAD_AUTH_SESSION_1);
            }
            if cc == TPM_CC_NV_INCREMENT {
                if !params.is_empty() {
                    return error_response(TPM_RC_COMMAND_CODE);
                }
                if index.attributes & TPMA_NV_TPM_NT_MASK != TPMA_NV_TPM_NT_COUNTER {
                    return error_response(TPM_RC_ATTRIBUTES_HANDLE_2);
                }
                if index.attributes & TPMA_NV_WRITELOCKED != 0 {
                    return error_response(TPM_RC_NV_LOCKED);
                }
                if index.attributes & TPMA_NV_WRITTEN == 0 {
                    index.attributes |= TPMA_NV_WRITTEN;
                    index.count = max_count;
                }
                index.count = index.count.checked_add(1).expect("64-bit counter");
                let count = index.count;
                state.max_count = state.max_count.max(count);
                return session_response(&[]);
            }
            if params.len() != 4 {
                return error_response(TPM_RC_COMMAND_CODE);
            }
            let size = u16::from_be_bytes([params[0], params[1]]);
            let offset = u16::from_be_bytes([params[2], params[3]]);
            if index.attributes & TPMA_NV_READLOCKED != 0 {
                return error_response(TPM_RC_NV_LOCKED);
            }
            if u32::from(size) + u32::from(offset) > u32::from(index.data_size) {
                return error_response(TPM_RC_NV_RANGE);
            }
            if index.attributes & TPMA_NV_WRITTEN == 0 {
                return error_response(TPM_RC_NV_UNINITIALIZED);
            }
            let value = index.count.to_be_bytes();
            let data = &value[offset as usize..(offset + size) as usize];
            let mut out = Vec::with_capacity(2 + data.len());
            out.extend_from_slice(&size.to_be_bytes());
            out.extend_from_slice(data);
            session_response(&out)
        }
    }

    impl Tpm2Transport for ModelTpm2 {
        fn transmit(&self, cmd: &[u8]) -> Result<Vec<u8>, AntiRollbackError> {
            let mut state = self.0.lock().unwrap();
            if let Some(rc) = state.forced_rc {
                return Ok(error_response(rc));
            }
            if cmd.len() < 10
                || u32::from_be_bytes(cmd[2..6].try_into().unwrap()) as usize != cmd.len()
            {
                return Ok(error_response(TPM_RC_COMMAND_CODE));
            }
            Ok(match u32::from_be_bytes(cmd[6..10].try_into().unwrap()) {
                TPM_CC_NV_READ_PUBLIC => Self::read_public(&state, cmd),
                cc @ (TPM_CC_NV_INCREMENT | TPM_CC_NV_READ) => {
                    Self::nv_command(&mut state, cc, cmd)
                }
                _ => error_response(TPM_RC_COMMAND_CODE),
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    use std::sync::atomic::{AtomicU64, Ordering};

    struct TempDir(PathBuf);
    impl TempDir {
        fn new(tag: &str) -> Self {
            static NEXT: AtomicU64 = AtomicU64::new(0);
            let dir = std::env::temp_dir().join(std::format!(
                "qsag-antirollback-{tag}-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            fs::create_dir_all(&dir).unwrap();
            Self(dir)
        }
    }
    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    use super::tpm2_model::{MAX_ORDERLY_COUNT, ModelTpm2, session_response as build_session_rsp};

    #[test]
    fn tpm2_packet_marshaling_matches_normative_big_endian_wire_bytes() {
        let inc = marshal_tpm2_nv_increment_cmd(0x0150_0007, 0x0150_0007, b"").unwrap();
        assert_eq!(
            inc,
            vec![
                0x80, 0x02, // TPM_ST_SESSIONS
                0x00, 0x00, 0x00, 0x1F, // commandSize = 31
                0x00, 0x00, 0x01, 0x34, // TPM_CC_NV_Increment (0x00000134)
                0x01, 0x50, 0x00, 0x07, // authHandle
                0x01, 0x50, 0x00, 0x07, // nvIndex
                0x00, 0x00, 0x00, 0x09, // authorizationSize = 9
                0x40, 0x00, 0x00, 0x09, // TPM_RS_PW (0x40000009)
                0x00, 0x00, // nonce.size = 0
                0x01, // sessionAttributes = continueSession
                0x00, 0x00, // hmac.size = 0
            ]
        );

        let rd = marshal_tpm2_nv_read_u64_cmd(TPM_RH_OWNER, 0x0150_0007, b"pw").unwrap();
        assert_eq!(
            rd,
            vec![
                0x80, 0x02, // TPM_ST_SESSIONS
                0x00, 0x00, 0x00, 0x25, // commandSize = 37
                0x00, 0x00, 0x01, 0x4E, // TPM_CC_NV_Read (0x0000014E)
                0x40, 0x00, 0x00, 0x01, // authHandle = TPM_RH_OWNER
                0x01, 0x50, 0x00, 0x07, // nvIndex
                0x00, 0x00, 0x00, 0x0B, // authorizationSize = 11
                0x40, 0x00, 0x00, 0x09, // TPM_RS_PW
                0x00, 0x00, // nonce.size = 0
                0x01, // continueSession
                0x00, 0x02, b'p', b'w', // TPM2B_AUTH = "pw"
                0x00, 0x08, // size = 8
                0x00, 0x00, // offset = 0
            ]
        );

        // Non-NV handle must fail closed.
        assert!(matches!(
            marshal_tpm2_nv_increment_cmd(0x8100_0001, 0x8100_0001, b""),
            Err(AntiRollbackError::ProtocolFramingError(_))
        ));
    }

    #[test]
    fn tpm2_response_with_oversized_parameter_size_is_refused_without_panic() {
        // Honest frames parse.
        assert!(parse_tpm2_nv_increment_rsp(&build_session_rsp(&[])).is_ok());
        let mut counter = [0u8; 10];
        counter[..2].copy_from_slice(&8u16.to_be_bytes());
        counter[2..].copy_from_slice(&7u64.to_be_bytes());
        assert_eq!(
            parse_tpm2_nv_read_u64_rsp(&build_session_rsp(&counter)).unwrap(),
            7
        );
        // `parameterSize` patched to every value that overruns the auth area, up to
        // `u32::MAX` (which wraps `14 + param_size + 5` on a 32-bit `usize`).
        let honest = build_session_rsp(&counter);
        let fits = honest.len() - 14 - 5;
        for param_size in [
            fits as u32 + 1,
            fits as u32 + 5,
            honest.len() as u32,
            u32::MAX - 18,
            u32::MAX - 14,
            u32::MAX - 4,
            u32::MAX,
        ] {
            let mut rsp = honest.clone();
            rsp[10..14].copy_from_slice(&param_size.to_be_bytes());
            assert!(
                matches!(
                    parse_tpm2_nv_read_u64_rsp(&rsp),
                    Err(AntiRollbackError::ProtocolFramingError(_))
                ),
                "param_size {param_size:#x}"
            );
            assert!(matches!(
                parse_tpm2_nv_increment_rsp(&rsp),
                Err(AntiRollbackError::ProtocolFramingError(_))
            ));
        }
        // An oversized nonceTPM / hmac size inside the auth area is refused as well.
        for (offset, value) in [
            (14 + 10, u16::MAX),
            (14 + 10 + 3, u16::MAX),
            (14 + 10 + 3, 1),
        ] {
            let mut rsp = honest.clone();
            rsp[offset..offset + 2].copy_from_slice(&value.to_be_bytes());
            assert!(
                matches!(
                    parse_tpm2_nv_read_u64_rsp(&rsp),
                    Err(AntiRollbackError::ProtocolFramingError(_))
                ),
                "offset {offset} value {value:#x}"
            );
        }
    }

    const PW: &[u8] = b"custody-pw";

    fn open_anchor(
        tpm: &ModelTpm2,
        seal: &Path,
        nv_index: u32,
    ) -> Result<Tpm2NvMonotoneAnchor<ModelTpm2>, AntiRollbackError> {
        Tpm2NvMonotoneAnchor::open_with_transport(
            tpm.clone(),
            seal,
            nv_index,
            nv_index,
            PW,
            [0x5A; 32],
        )
    }

    fn checkpoint(generation: u64) -> LedgerCheckpoint {
        LedgerCheckpoint {
            generation,
            tag: [generation as u8 * 0x11; 32],
        }
    }

    fn nv_increment(tpm: &ModelTpm2, nv_index: u32, auth: &[u8]) -> Result<(), AntiRollbackError> {
        let cmd = marshal_tpm2_nv_increment_cmd(nv_index, nv_index, auth).unwrap();
        parse_tpm2_nv_increment_rsp(&tpm.transmit(&cmd).unwrap())
    }

    fn nv_read(tpm: &ModelTpm2, nv_index: u32, auth: &[u8]) -> Result<u64, AntiRollbackError> {
        let cmd = marshal_tpm2_nv_read_u64_cmd(nv_index, nv_index, auth).unwrap();
        parse_tpm2_nv_read_u64_rsp(&tpm.transmit(&cmd).unwrap())
    }

    #[test]
    fn tpm2_nv_anchor_detects_disk_snapshot_rollback_and_recovers_pending_crash() {
        let tmp = TempDir::new("tpm2");
        let seal_path = tmp.0.join("tpm_anchor");
        let nv_index = 0x0150_0042;
        let tpm = ModelTpm2::with_history(100);
        tpm.define_counter(nv_index, PW);

        let anchor = open_anchor(&tpm, &seal_path, nv_index).unwrap();
        assert_eq!(anchor.load_checked().unwrap(), None);
        assert_eq!(tpm.count(nv_index), None, "opening does not write");
        let (cp1, cp2, cp3) = (checkpoint(1), checkpoint(2), checkpoint(3));
        anchor.advance_checked(cp1).unwrap();
        assert_eq!(tpm.count(nv_index), Some(101));
        assert_eq!(anchor.load_checked().unwrap(), Some(cp1));

        // Snapshot the on-disk seal record at generation 1 (hardware counter = 101).
        let disk_snapshot_bytes = fs::read(&seal_path).unwrap();
        anchor.advance_checked(cp2).unwrap();
        assert_eq!(tpm.count(nv_index), Some(102));
        assert_eq!(anchor.load_checked().unwrap(), Some(cp2));
        drop(anchor);

        // The disk goes back to generation 1 while the TPM stays at 102.
        fs::write(&seal_path, &disk_snapshot_bytes).unwrap();
        assert!(matches!(
            open_anchor(&tpm, &seal_path, nv_index),
            Err(AntiRollbackError::RollbackOrForkDetected(_))
        ));

        // Crash mid-commit on a second anchor with its own counter: `pending` is staged,
        // the increment reached the TPM, the final write did not happen.
        let seal_path2 = tmp.0.join("tpm_anchor_crash");
        let nv_index2 = 0x0150_0043;
        tpm.define_counter(nv_index2, PW);
        let anchor2 = open_anchor(&tpm, &seal_path2, nv_index2).unwrap();
        anchor2.advance_checked(cp2).unwrap();
        assert_eq!(tpm.count(nv_index2), Some(103));
        let staged = TpmSealedState {
            committed_hw: 103,
            committed_cp: cp2,
            pending: Some((104, cp3)),
        };
        anchor2
            .record
            .replace(&anchor2.encode_state(&staged))
            .unwrap();
        nv_increment(&tpm, nv_index2, PW).unwrap();
        drop(anchor2);
        let recovered = open_anchor(&tpm, &seal_path2, nv_index2).unwrap();
        assert_eq!(recovered.load_checked().unwrap(), Some(cp3));

        // A device error propagates as the typed response code.
        tpm.force_response_code(Some(TPM_RC_NV_LOCKED));
        assert_eq!(
            recovered.load_checked(),
            Err(AntiRollbackError::Tpm2ResponseError(TPM_RC_NV_LOCKED))
        );
    }

    // Two seals on one counter was the multi-anchor defect: each advance left the other
    // seal behind. A second anchor is now refused when it is opened, not when the first
    // is reopened, because the TPM itself says the counter has been used.
    #[test]
    fn new_tpm2_anchor_requires_a_never_written_counter_of_the_right_kind() {
        let tmp = TempDir::new("tpm2-enrol");
        let tpm = ModelTpm2::with_history(7);
        let unsuitable = |result: Result<Tpm2NvMonotoneAnchor<ModelTpm2>, AntiRollbackError>| {
            matches!(result, Err(AntiRollbackError::UnsuitableCounterIndex(_)))
        };

        let shared = 0x0150_0050;
        tpm.define_counter(shared, PW);
        let first = open_anchor(&tpm, &tmp.0.join("first"), shared).unwrap();
        // Unwritten until the first advance, so a sibling opened in between is not yet
        // refused; whichever advances second is.
        let sibling = open_anchor(&tpm, &tmp.0.join("sibling"), shared).unwrap();
        first.advance_checked(checkpoint(1)).unwrap();
        assert_eq!(
            sibling.advance_checked(checkpoint(1)),
            Err(AntiRollbackError::UnsuitableCounterIndex(
                "the counter was incremented by something else during enrollment"
            ))
        );
        assert_eq!(
            tpm.count(shared),
            Some(8),
            "the refused sibling wrote nothing"
        );
        drop(sibling);
        assert!(unsuitable(open_anchor(&tpm, &tmp.0.join("second"), shared)));
        assert_eq!(first.load_checked().unwrap(), Some(checkpoint(1)));
        drop(first);
        drop(open_anchor(&tpm, &tmp.0.join("first"), shared).unwrap());

        // Index kinds an anchor cannot use.
        let counter = TPMA_NV_TPM_NT_COUNTER | TPMA_NV_AUTHREAD | TPMA_NV_AUTHWRITE;
        for (nv_index, attributes, data_size) in [
            (0x0150_0051, TPMA_NV_AUTHREAD | TPMA_NV_AUTHWRITE, 8),
            (0x0150_0052, counter | TPMA_NV_ORDERLY, 8),
            (0x0150_0053, counter & !TPMA_NV_AUTHWRITE, 8),
            (0x0150_0054, counter & !TPMA_NV_AUTHREAD, 8),
            (0x0150_0055, TPMA_NV_AUTHREAD | TPMA_NV_AUTHWRITE, 32),
        ] {
            tpm.define_space(nv_index, attributes, PW, data_size);
            assert!(
                unsuitable(open_anchor(&tpm, &tmp.0.join("kind"), nv_index)),
                "{nv_index:#x}"
            );
        }
        assert_eq!(
            open_anchor(&tpm, &tmp.0.join("kind"), 0x0150_0056).err(),
            Some(AntiRollbackError::Tpm2ResponseError(TPM_RC_HANDLE_1))
        );

        // An index that is undefined and defined again is unwritten: the old seal is
        // refused, and a new anchor on it starts above every earlier sealed count.
        tpm.undefine(shared);
        tpm.define_counter(shared, PW);
        assert!(matches!(
            open_anchor(&tpm, &tmp.0.join("first"), shared),
            Err(AntiRollbackError::RollbackOrForkDetected(_))
        ));
        let again = open_anchor(&tpm, &tmp.0.join("again"), shared).unwrap();
        again.advance_checked(checkpoint(1)).unwrap();
        assert_eq!(tpm.count(shared), Some(9));
    }

    #[test]
    fn rebinding_a_seal_needs_a_never_written_counter_and_keeps_the_checkpoint() {
        let tmp = TempDir::new("tpm2-rebind");
        let tpm = ModelTpm2::with_history(20);
        let (old, new, used) = (0x0150_00A0, 0x0150_00A1, 0x0150_00A2);
        for nv_index in [old, new, used] {
            tpm.define_counter(nv_index, PW);
        }
        nv_increment(&tpm, used, PW).unwrap();
        let seal = tmp.0.join("seal");
        let anchor = open_anchor(&tpm, &seal, old).unwrap();
        anchor.advance_checked(checkpoint(1)).unwrap();
        anchor.advance_checked(checkpoint(2)).unwrap();
        drop(anchor);
        let view = inspect_tpm2_seal(&seal, old, [0x5A; 32]).unwrap();
        assert_eq!(
            view,
            Tpm2SealView {
                sealed_count: tpm.count(old).unwrap(),
                checkpoint: checkpoint(2),
                commit_in_flight: false,
            }
        );
        assert!(inspect_tpm2_seal(&seal, new, [0x5A; 32]).is_err());
        assert!(inspect_tpm2_seal(&seal, old, [0x5B; 32]).is_err());

        let rebind = |to: u32| {
            Tpm2NvMonotoneAnchor::rebind_to_new_counter(tpm.clone(), &seal, old, to, PW, [0x5A; 32])
        };
        assert!(matches!(
            rebind(used),
            Err(AntiRollbackError::UnsuitableCounterIndex(_))
        ));
        assert!(rebind(old).is_err());
        assert_eq!(tpm.count(new), None);
        let before = fs::read(&seal).unwrap();
        let rebound = rebind(new).unwrap();
        assert_eq!(rebound.load_checked().unwrap(), Some(checkpoint(2)));
        assert!(tpm.count(new).unwrap() > tpm.count(old).unwrap());
        rebound.advance_checked(checkpoint(3)).unwrap();
        drop(rebound);
        // Running it again finds the seal already on the new counter and verifies it.
        let count = tpm.count(new);
        drop(rebind(new).unwrap());
        assert_eq!(tpm.count(new), count);
        assert_eq!(
            open_anchor(&tpm, &seal, new)
                .unwrap()
                .load_checked()
                .unwrap(),
            Some(checkpoint(3))
        );
        // The pre-rebind seal bytes are refused on both counters afterwards.
        fs::write(&seal, before).unwrap();
        assert!(open_anchor(&tpm, &seal, new).is_err());
        assert!(matches!(
            rebind(new),
            Err(AntiRollbackError::UnsuitableCounterIndex(_))
        ));
    }

    // Part 3 §31.13 and §31.2.
    #[test]
    fn model_unwritten_index_cannot_be_read_and_a_new_counter_exceeds_every_past_count() {
        let tpm = ModelTpm2::new();
        let (a, b) = (0x0150_0060, 0x0150_0061);
        tpm.define_counter(a, b"");
        assert_eq!(
            nv_read(&tpm, a, b""),
            Err(AntiRollbackError::Tpm2ResponseError(
                TPM_RC_NV_UNINITIALIZED
            ))
        );
        assert!(!tpm2_nv_read_public(&tpm, a).unwrap().is_written());
        for expected in 1..=3 {
            nv_increment(&tpm, a, b"").unwrap();
            assert_eq!(nv_read(&tpm, a, b""), Ok(expected));
        }
        assert!(tpm2_nv_read_public(&tpm, a).unwrap().is_written());

        // The deleted counter's count still bounds every later counter from below.
        tpm.undefine(a);
        tpm.define_counter(b, b"");
        assert_eq!(tpm.count(b), None);
        nv_increment(&tpm, b, b"").unwrap();
        assert_eq!(nv_read(&tpm, b, b""), Ok(4));
        tpm.define_counter(a, b"");
        assert_eq!(
            nv_read(&tpm, a, b""),
            Err(AntiRollbackError::Tpm2ResponseError(
                TPM_RC_NV_UNINITIALIZED
            ))
        );
        nv_increment(&tpm, a, b"").unwrap();
        assert_eq!(nv_read(&tpm, a, b""), Ok(5));
        nv_increment(&tpm, b, b"").unwrap();
        assert_eq!(nv_read(&tpm, b, b""), Ok(5), "increments add exactly one");
    }

    // Part 3 §31.8.
    #[test]
    fn model_increment_needs_a_counter_that_is_not_write_locked() {
        let tpm = ModelTpm2::new();
        let (ordinary, counter) = (0x0150_0070, 0x0150_0071);
        tpm.define_space(ordinary, TPMA_NV_AUTHREAD | TPMA_NV_AUTHWRITE, b"", 8);
        assert_eq!(
            nv_increment(&tpm, ordinary, b""),
            Err(AntiRollbackError::Tpm2ResponseError(
                TPM_RC_ATTRIBUTES_HANDLE_2
            ))
        );
        tpm.define_counter(counter, b"");
        nv_increment(&tpm, counter, b"").unwrap();
        tpm.write_lock(counter);
        assert_eq!(
            nv_increment(&tpm, counter, b""),
            Err(AntiRollbackError::Tpm2ResponseError(TPM_RC_NV_LOCKED))
        );
        assert_eq!(
            nv_read(&tpm, counter, b""),
            Ok(1),
            "a refused increment adds nothing"
        );
        tpm.restart(true);
        nv_increment(&tpm, counter, b"").unwrap();
        assert_eq!(nv_read(&tpm, counter, b""), Ok(2));
    }

    // Part 3 §31.1 (index authorization), §31.13 (range), Part 2 §6.6.3 (codes).
    #[test]
    fn model_authorization_handles_and_read_range() {
        let tpm = ModelTpm2::new();
        let counter = 0x0150_0080;
        tpm.define_counter(counter, b"secret");
        nv_increment(&tpm, counter, b"secret").unwrap();
        let rc = |result: Result<u64, AntiRollbackError>| match result {
            Err(AntiRollbackError::Tpm2ResponseError(rc)) => rc,
            other => panic!("{other:?}"),
        };
        assert_eq!(
            rc(nv_read(&tpm, counter, b"wrong")),
            TPM_RC_BAD_AUTH_SESSION_1
        );
        assert_eq!(
            nv_increment(&tpm, counter, b""),
            Err(AntiRollbackError::Tpm2ResponseError(
                TPM_RC_BAD_AUTH_SESSION_1
            ))
        );
        assert_eq!(rc(nv_read(&tpm, 0x0150_0081, b"secret")), TPM_RC_HANDLE_1);
        assert_eq!(
            tpm2_nv_read_public(&tpm, 0x0150_0081),
            Err(AntiRollbackError::Tpm2ResponseError(TPM_RC_HANDLE_1))
        );
        // Owner-only indices cannot be used with the index's own authorization.
        let owner_only = 0x0150_0082;
        tpm.define_space(
            owner_only,
            TPMA_NV_TPM_NT_COUNTER | (1 << 1) | (1 << 17),
            b"",
            8,
        );
        assert_eq!(rc(nv_read(&tpm, owner_only, b"")), TPM_RC_NV_AUTHORIZATION);
        assert_eq!(
            nv_increment(&tpm, owner_only, b""),
            Err(AntiRollbackError::Tpm2ResponseError(
                TPM_RC_NV_AUTHORIZATION
            ))
        );
        // size + offset beyond the 8-octet counter.
        let mut cmd = marshal_tpm2_nv_read_u64_cmd(counter, counter, b"secret").unwrap();
        let at = cmd.len() - 2;
        cmd[at..].copy_from_slice(&1u16.to_be_bytes());
        assert_eq!(
            rc(parse_tpm2_nv_read_u64_rsp(&tpm.transmit(&cmd).unwrap())),
            TPM_RC_NV_RANGE
        );
        assert_eq!(nv_read(&tpm, counter, b"secret"), Ok(1));
    }

    // Part 3 §31.2 and §31.8 NOTE 2: the reason an anchor refuses `orderly` counters.
    #[test]
    fn model_orderly_counter_jumps_after_an_unclean_shutdown() {
        let tpm = ModelTpm2::new();
        let (orderly, plain) = (0x0150_0090, 0x0150_0091);
        let counter = TPMA_NV_TPM_NT_COUNTER | TPMA_NV_AUTHREAD | TPMA_NV_AUTHWRITE;
        tpm.define_space(orderly, counter | TPMA_NV_ORDERLY, b"", 8);
        tpm.define_counter(plain, b"");
        for nv_index in [orderly, plain] {
            nv_increment(&tpm, nv_index, b"").unwrap();
            nv_increment(&tpm, nv_index, b"").unwrap();
        }
        let before = nv_read(&tpm, orderly, b"").unwrap();
        let plain_before = nv_read(&tpm, plain, b"").unwrap();
        tpm.restart(true);
        assert_eq!(nv_read(&tpm, orderly, b""), Ok(before));
        tpm.restart(false);
        assert_eq!(nv_read(&tpm, orderly, b""), Ok(before | MAX_ORDERLY_COUNT));
        assert!(nv_read(&tpm, orderly, b"").unwrap() > before);
        // A counter without the attribute keeps its exact count, which is what a seal
        // holds; and later counters start above the jump.
        assert_eq!(nv_read(&tpm, plain, b""), Ok(plain_before));
        let later = 0x0150_0092;
        tpm.define_counter(later, b"");
        nv_increment(&tpm, later, b"").unwrap();
        assert_eq!(
            nv_read(&tpm, later, b""),
            Ok((before | MAX_ORDERLY_COUNT) + 1)
        );
    }

    // Part 3 §31.6, Tables 218 and 219.
    #[test]
    fn tpm2_nv_read_public_wire_format() {
        assert_eq!(
            marshal_tpm2_nv_read_public_cmd(0x0150_0007).unwrap(),
            vec![
                0x80, 0x01, // TPM_ST_NO_SESSIONS
                0x00, 0x00, 0x00, 0x0E, // commandSize = 14
                0x00, 0x00, 0x01, 0x69, // TPM_CC_NV_ReadPublic
                0x01, 0x50, 0x00, 0x07, // nvIndex
            ]
        );
        assert!(marshal_tpm2_nv_read_public_cmd(0x8100_0001).is_err());
        // tpm2_nvdefine -a "authread|authwrite|no_da|nt=counter" with a 32-byte policy.
        let attributes: u32 = 0x0204_0014;
        let mut rsp = vec![0x80, 0x01, 0, 0, 0, 0, 0, 0, 0, 0];
        rsp.extend_from_slice(&46u16.to_be_bytes());
        rsp.extend_from_slice(&0x0150_0007u32.to_be_bytes());
        rsp.extend_from_slice(&0x000Bu16.to_be_bytes());
        rsp.extend_from_slice(&attributes.to_be_bytes());
        rsp.extend_from_slice(&32u16.to_be_bytes());
        rsp.extend_from_slice(&[0xEE; 32]);
        rsp.extend_from_slice(&8u16.to_be_bytes());
        rsp.extend_from_slice(&34u16.to_be_bytes());
        rsp.extend_from_slice(&[0xAA; 34]);
        let size = rsp.len() as u32;
        rsp[2..6].copy_from_slice(&size.to_be_bytes());
        let public = parse_tpm2_nv_read_public_rsp(&rsp).unwrap();
        assert_eq!(
            public,
            Tpm2NvPublic {
                nv_index: 0x0150_0007,
                name_alg: 0x000B,
                attributes,
                data_size: 8,
            }
        );
        assert_eq!(
            attributes,
            TPMA_NV_TPM_NT_COUNTER | TPMA_NV_AUTHREAD | TPMA_NV_AUTHWRITE | TPMA_NV_NO_DA
        );
        public.check_anchor_counter(0x0150_0007).unwrap();
        assert!(public.check_anchor_counter(0x0150_0008).is_err());
        assert!(!public.is_written());
        // Every truncation and a wrong inner length are framing errors, not panics.
        for cut in 0..rsp.len() {
            let mut short = rsp[..cut].to_vec();
            if cut >= 6 {
                short[2..6].copy_from_slice(&(cut as u32).to_be_bytes());
            }
            assert!(parse_tpm2_nv_read_public_rsp(&short).is_err(), "cut {cut}");
        }
        let mut wrong = rsp.clone();
        wrong[10..12].copy_from_slice(&45u16.to_be_bytes());
        assert!(parse_tpm2_nv_read_public_rsp(&wrong).is_err());
    }

    #[derive(Clone)]
    struct MockVmGenSource {
        snap: Arc<Mutex<VmGenSnapshot>>,
    }

    impl VmGenSource for MockVmGenSource {
        fn sample(&self, _guarded_target: &Path) -> Result<VmGenSnapshot, AntiRollbackError> {
            Ok(*self.snap.lock().unwrap())
        }
    }

    #[test]
    fn vmgenid_anchor_halts_on_snapshot_fork_volume_clone_and_pinned_boot_drift() {
        let tmp = TempDir::new("vmgen");
        let wal_file = tmp.0.join("fts.wal");
        fs::write(&wal_file, b"header").unwrap();
        let anchor_file = tmp.0.join("vmgen.anchor");

        let initial_snap = VmGenSnapshot {
            vmgenid: Some(*b"0123456789abcdef"),
            boot_id: Some(*b"boot-session-001"),
            target_dev: 2049,
            target_ino: 99123,
            target_ctime_sec: 1_700_000_000,
        };
        let src = MockVmGenSource {
            snap: Arc::new(Mutex::new(initial_snap)),
        };
        let anchor = HypervisorGenerationAnchor::open_or_create_with_source(
            &anchor_file,
            &wal_file,
            [0x77; 32],
            VmGenPolicy::STRICT_HYPERVISOR,
            src.clone(),
        )
        .unwrap();

        let cp1 = LedgerCheckpoint {
            generation: 1,
            tag: [0xAB; 32],
        };
        anchor.advance_checked(cp1).unwrap();
        assert_eq!(anchor.load_checked().unwrap(), Some(cp1));

        // 1. Normal guest reboot: `boot_id` rotates, `vmgenid` and `(dev, ino)` stay identical.
        src.snap.lock().unwrap().boot_id = Some(*b"boot-session-002");
        assert_eq!(anchor.load_checked().unwrap(), Some(cp1));

        // 2. Hypervisor VM snapshot restore / live fork: `vmgenid` changes by 1 bit -> HALT!
        src.snap.lock().unwrap().vmgenid = Some(*b"0123456789abcdee");
        assert!(matches!(
            anchor.load_checked(),
            Err(AntiRollbackError::RollbackOrForkDetected(_))
        ));
        assert!(matches!(
            anchor.advance_checked(LedgerCheckpoint {
                generation: 2,
                tag: [0xCD; 32],
            }),
            Err(AntiRollbackError::RollbackOrForkDetected(_))
        ));

        // Restore valid vmgenid, then simulate EBS volume clone / file copy (`target_ino` changes) -> HALT!
        src.snap.lock().unwrap().vmgenid = Some(*b"0123456789abcdef");
        assert_eq!(anchor.load_checked().unwrap(), Some(cp1));
        src.snap.lock().unwrap().target_ino = 99124;
        assert!(matches!(
            anchor.load_checked(),
            Err(AntiRollbackError::RollbackOrForkDetected(_))
        ));

        // 3. Pinned boot session (container fork guard): `boot_id` change halts even without VMGENID.
        let pinned_anchor_file = tmp.0.join("pinned.anchor");
        let container_src = MockVmGenSource {
            snap: Arc::new(Mutex::new(VmGenSnapshot {
                vmgenid: None,
                boot_id: Some(*b"container-boot-1"),
                target_dev: 50,
                target_ino: 777,
                target_ctime_sec: 1_700_000_100,
            })),
        };
        let pinned = HypervisorGenerationAnchor::open_or_create_with_source(
            &pinned_anchor_file,
            &wal_file,
            [0x88; 32],
            VmGenPolicy::PINNED_BOOT_SESSION,
            container_src.clone(),
        )
        .unwrap();
        pinned.advance_checked(cp1).unwrap();
        container_src.snap.lock().unwrap().boot_id = Some(*b"container-boot-2");
        assert!(matches!(
            pinned.load_checked(),
            Err(AntiRollbackError::RollbackOrForkDetected(_))
        ));
    }

    #[test]
    fn parse_id128_accepts_uuid_text_and_raw_16_bytes() {
        let uuid = b"f47ac10b-58cc-4372-a567-0e02b2c3d479\n";
        let parsed = parse_id128_bytes(uuid).unwrap();
        assert_eq!(
            parsed,
            [
                0xf4, 0x7a, 0xc1, 0x0b, 0x58, 0xcc, 0x43, 0x72, 0xa5, 0x67, 0x0e, 0x02, 0xb2, 0xc3,
                0xd4, 0x79
            ]
        );
        assert_eq!(parse_id128_bytes(&parsed).unwrap(), parsed);
        assert!(parse_id128_bytes(b"short").is_err());
    }
}
