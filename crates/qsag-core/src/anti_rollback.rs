//! Hardware and hypervisor anti-rollback anchors for stateful post-quantum custody
//! (`FrontierSumFts`, `DurableFtsWal`, `JortsPoseidon2`, and `DurableQueryBudget`).
//!
//! Two orthogonal rollback/fork surfaces threaten stateful hash-based signers (`XMSS`,
//! `LMS/HSS`, `Jorts`, `FTS`):
//!
//! 1. **VM snapshot restore / live-fork / EBS volume clone / container checkpoint-restore:**
//!    Restoring a hypervisor snapshot or cloning a block volume rewinds the filesystem WAL
//!    together with any same-disk sidecar. [`VmGenIdForkGuard`] and [`HypervisorGenerationAnchor`]
//!    bind every checkpoint to the hypervisor's 128-bit ACPI `VMGENID`
//!    (`/sys/devices/virtual/misc/vmgenid` / `QEMU0002:00`), Linux `/proc/sys/kernel/random/boot_id`,
//!    and the guarded state file's `(st_dev, st_ino, st_ctime)` tuple, hard-halting signing with
//!    [`AntiRollbackError::RollbackOrForkDetected`] the instant any fork/clone/restore occurs.
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
/// TPM 2.0 `TPM_CC_NV_Increment` command code (`0x0000_0134`, ISO/IEC 11889-3 §31.5).
pub const TPM_CC_NV_INCREMENT: u32 = 0x0000_0134;
/// TPM 2.0 `TPM_CC_NV_Read` command code (`0x0000_014E`, ISO/IEC 11889-3 §31.6).
pub const TPM_CC_NV_READ: u32 = 0x0000_014E;
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
            Self::ProtocolFramingError(_) | Self::Tpm2ResponseError(_) => io::ErrorKind::Other,
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
    /// `boot_id` and `(dev, ino)` (and `vmgenid` if present), halting on any VM restore,
    /// container checkpoint/restore, or host reboot without TPM2 re-verification.
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

/// Durable [`ExternalMonotoneAnchor`] sealing [`LedgerCheckpoint`] alongside hypervisor
/// `VMGENID`, Linux `boot_id`, and guarded WAL `(dev, ino, ctime)` continuity.
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

/// Transport abstraction over the Linux kernel TPM 2.0 resource manager (`/dev/tpmrm0`) or
/// deterministic in-memory unit-test transceivers.
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

        let record = LockedRecord::acquire(seal_path)?;
        let mut this = Self {
            transport,
            record,
            nv_index,
            auth_handle,
            auth_value: [0u8; MAX_TPM2_AUTH_BYTES],
            auth_len: nv_password.len(),
            mac_key: [0u8; 32],
        };
        this.mac_key.copy_from_slice(key_arg.as_slice());
        drop(key_arg);
        this.auth_value[..nv_password.len()].copy_from_slice(nv_password);
        // Immediately verify hardware counter vs local sealed state on open!
        let _ = this.load_checked()?;
        Ok(this)
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
                "local custody state lags TPM2 NV monotonic counter (disk rollback detected)",
            ));
        }
        Err(AntiRollbackError::RollbackOrForkDetected(
            "TPM2 NV counter regressed below sealed baseline (NVRAM reset or wrong TPM)",
        ))
    }

    /// Authenticate local sealed state against the live TPM 2.0 hardware NV counter.
    pub fn load_checked(&self) -> Result<Option<LedgerCheckpoint>, AntiRollbackError> {
        let live_hw = self.read_hardware_counter()?;
        let raw = match self.record.read_bounded(TPM_ANCHOR_RECORD_LEN) {
            Ok(bytes) => bytes,
            Err(e) if e.kind() == io::ErrorKind::NotFound && self.record.is_fresh() => {
                return Ok(None);
            }
            Err(e) => return Err(AntiRollbackError::Io(e.kind())),
        };
        let st = self.decode_state(&raw)?;
        let (_hw, cp) = self.reconcile_with_hardware(st, live_hw)?;
        Ok(Some(cp))
    }

    /// Atomically increment the TPM 2.0 hardware NV counter and seal `checkpoint`.
    pub fn advance_checked(&self, checkpoint: LedgerCheckpoint) -> Result<(), AntiRollbackError> {
        let live_hw = self.read_hardware_counter()?;
        match self.record.read_bounded(TPM_ANCHOR_RECORD_LEN) {
            Ok(raw) => {
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
                // First provisioning: increment TPM2 NV counter once from `live_hw -> live_hw + 1`
                // so a deleted/re-created seal directory cannot silently re-adopt `live_hw` after
                // signing under a previous seal!
                let next_hw =
                    live_hw
                        .checked_add(1)
                        .ok_or(AntiRollbackError::ProtocolFramingError(
                            "TPM2 64-bit NV counter exhausted",
                        ))?;
                self.increment_hardware_counter()?;
                let after_hw = self.read_hardware_counter()?;
                if after_hw != next_hw {
                    return Err(AntiRollbackError::RollbackOrForkDetected(
                        "unexpected TPM2 NV counter jump during initial anchor provisioning",
                    ));
                }
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

    /// Deterministic in-memory TPM 2.0 NV counter emulator validating every incoming command's
    /// exact big-endian header, commandCode, handles, and `TPM_RS_PW` authorization framing.
    #[derive(Clone)]
    struct MockTpm2Device {
        state: Arc<Mutex<MockTpmState>>,
    }

    struct MockTpmState {
        nv_index: u32,
        expected_auth: Vec<u8>,
        counter: u64,
        forced_rc: Option<u32>,
        recorded_cmds: Vec<Vec<u8>>,
    }

    impl MockTpm2Device {
        fn new(nv_index: u32, auth: &[u8], initial_counter: u64) -> Self {
            Self {
                state: Arc::new(Mutex::new(MockTpmState {
                    nv_index,
                    expected_auth: auth.to_vec(),
                    counter: initial_counter,
                    forced_rc: None,
                    recorded_cmds: Vec::new(),
                })),
            }
        }

        fn counter(&self) -> u64 {
            self.state.lock().unwrap().counter
        }

        fn bump_out_of_band(&self, delta: u64) {
            self.state.lock().unwrap().counter += delta;
        }

        fn set_forced_rc(&self, rc: Option<u32>) {
            self.state.lock().unwrap().forced_rc = rc;
        }
    }

    fn build_session_rsp(params: &[u8]) -> Vec<u8> {
        // 10B header + 4B paramSize + params + 5B minimal TPMS_AUTH_RESPONSE (nonce=0, attr=1, hmac=0)
        let total_len = (10 + 4 + params.len() + 5) as u32;
        let mut rsp = Vec::with_capacity(total_len as usize);
        rsp.extend_from_slice(&TPM_ST_SESSIONS.to_be_bytes());
        rsp.extend_from_slice(&total_len.to_be_bytes());
        rsp.extend_from_slice(&TPM_RC_SUCCESS.to_be_bytes());
        rsp.extend_from_slice(&(params.len() as u32).to_be_bytes());
        rsp.extend_from_slice(params);
        rsp.extend_from_slice(&0u16.to_be_bytes()); // nonceTPM.size = 0
        rsp.push(0x01); // continueSession = 1
        rsp.extend_from_slice(&0u16.to_be_bytes()); // hmac.size = 0
        rsp
    }

    impl Tpm2Transport for MockTpm2Device {
        fn transmit(&self, cmd: &[u8]) -> Result<Vec<u8>, AntiRollbackError> {
            let mut st = self.state.lock().unwrap();
            st.recorded_cmds.push(cmd.to_vec());
            if let Some(rc) = st.forced_rc {
                let mut err_rsp = Vec::with_capacity(10);
                err_rsp.extend_from_slice(&TPM_ST_NO_SESSIONS.to_be_bytes());
                err_rsp.extend_from_slice(&10u32.to_be_bytes());
                err_rsp.extend_from_slice(&rc.to_be_bytes());
                return Ok(err_rsp);
            }
            assert!(cmd.len() >= 27, "command shorter than session frame");
            let tag = u16::from_be_bytes([cmd[0], cmd[1]]);
            let sz = u32::from_be_bytes([cmd[2], cmd[3], cmd[4], cmd[5]]) as usize;
            let cc = u32::from_be_bytes([cmd[6], cmd[7], cmd[8], cmd[9]]);
            assert_eq!(tag, TPM_ST_SESSIONS);
            assert_eq!(sz, cmd.len());
            let _auth_handle = u32::from_be_bytes([cmd[10], cmd[11], cmd[12], cmd[13]]);
            let nv_idx = u32::from_be_bytes([cmd[14], cmd[15], cmd[16], cmd[17]]);
            assert_eq!(nv_idx, st.nv_index);
            let auth_size = u32::from_be_bytes([cmd[18], cmd[19], cmd[20], cmd[21]]) as usize;
            let session_handle = u32::from_be_bytes([cmd[22], cmd[23], cmd[24], cmd[25]]);
            assert_eq!(session_handle, TPM_RS_PW);
            let nonce_sz = u16::from_be_bytes([cmd[26], cmd[27]]) as usize;
            assert_eq!(nonce_sz, 0);
            assert_eq!(cmd[28], 0x01);
            let hmac_sz = u16::from_be_bytes([cmd[29], cmd[30]]) as usize;
            assert_eq!(auth_size, 9 + hmac_sz);
            assert_eq!(&cmd[31..31 + hmac_sz], st.expected_auth.as_slice());

            let params = &cmd[31 + hmac_sz..];
            match cc {
                TPM_CC_NV_INCREMENT => {
                    assert!(params.is_empty());
                    st.counter = st.counter.checked_add(1).unwrap();
                    Ok(build_session_rsp(&[]))
                }
                TPM_CC_NV_READ => {
                    assert_eq!(params, &[0x00, 0x08, 0x00, 0x00]);
                    let mut out_params = [0u8; 10];
                    out_params[..2].copy_from_slice(&8u16.to_be_bytes());
                    out_params[2..10].copy_from_slice(&st.counter.to_be_bytes());
                    Ok(build_session_rsp(&out_params))
                }
                other => panic!("unexpected TPM_CC 0x{other:08x}"),
            }
        }
    }

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
        for (offset, value) in [(14 + 10, u16::MAX), (14 + 10 + 3, u16::MAX), (14 + 10 + 3, 1)] {
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

    #[test]
    fn tpm2_nv_anchor_detects_disk_snapshot_rollback_and_recovers_pending_crash() {
        let tmp = TempDir::new("tpm2");
        let seal_path = tmp.0.join("tpm_anchor");
        let nv_index = 0x0150_0042;
        let mac_key = [0x5Au8; 32];
        let tpm = MockTpm2Device::new(nv_index, b"custody-pw", 100);

        let anchor = Tpm2NvMonotoneAnchor::open_with_transport(
            tpm.clone(),
            &seal_path,
            nv_index,
            nv_index,
            b"custody-pw",
            mac_key,
        )
        .unwrap();
        assert_eq!(anchor.load_checked().unwrap(), None);

        let cp1 = LedgerCheckpoint {
            generation: 1,
            tag: [0x11; 32],
        };
        let cp2 = LedgerCheckpoint {
            generation: 2,
            tag: [0x22; 32],
        };
        anchor.advance_checked(cp1).unwrap();
        assert_eq!(tpm.counter(), 101);
        assert_eq!(anchor.load_checked().unwrap(), Some(cp1));

        // Snapshot the on-disk seal record at generation 1 (hardware counter = 101).
        let disk_snapshot_bytes = fs::read(&seal_path).unwrap();

        // Advance to generation 2 (hardware counter -> 102).
        anchor.advance_checked(cp2).unwrap();
        assert_eq!(tpm.counter(), 102);
        assert_eq!(anchor.load_checked().unwrap(), Some(cp2));
        drop(anchor);

        // Simulate attacker restoring disk snapshot back to generation 1 while hardware TPM2
        // remains at 102: reopen MUST immediately halt with RollbackOrForkDetected!
        fs::write(&seal_path, &disk_snapshot_bytes).unwrap();
        let reopened = Tpm2NvMonotoneAnchor::open_with_transport(
            tpm.clone(),
            &seal_path,
            nv_index,
            nv_index,
            b"custody-pw",
            mac_key,
        );
        assert!(matches!(
            reopened,
            Err(AntiRollbackError::RollbackOrForkDetected(_))
        ));

        // Simulate crash mid-commit: stage `pending = (103, cp3)` in a fresh anchor, bump TPM2
        // to 103, and verify recovery promotes `cp3` cleanly without bricking!
        let seal_path2 = tmp.0.join("tpm_anchor_crash");
        let anchor2 = Tpm2NvMonotoneAnchor::open_with_transport(
            tpm.clone(),
            &seal_path2,
            nv_index,
            nv_index,
            b"custody-pw",
            mac_key,
        )
        .unwrap();
        anchor2.advance_checked(cp2).unwrap();
        assert_eq!(tpm.counter(), 103);
        let cp3 = LedgerCheckpoint {
            generation: 3,
            tag: [0x33; 32],
        };
        let staged = TpmSealedState {
            committed_hw: 103,
            committed_cp: cp2,
            pending: Some((104, cp3)),
        };
        anchor2
            .record
            .replace(&anchor2.encode_state(&staged))
            .unwrap();
        tpm.bump_out_of_band(1); // hardware counter = 104 (TPM2_NV_Increment succeeded right before power loss)
        drop(anchor2);

        let recovered = Tpm2NvMonotoneAnchor::open_with_transport(
            tpm.clone(),
            &seal_path2,
            nv_index,
            nv_index,
            b"custody-pw",
            mac_key,
        )
        .unwrap();
        assert_eq!(recovered.load_checked().unwrap(), Some(cp3));

        // TPM2 hardware error response propagates typed `Tpm2ResponseError`.
        tpm.set_forced_rc(Some(0x0000_014A));
        assert_eq!(
            recovered.load_checked(),
            Err(AntiRollbackError::Tpm2ResponseError(0x0000_014A))
        );
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
