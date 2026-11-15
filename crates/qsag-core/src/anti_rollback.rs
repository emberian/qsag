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
                write!(f, "anti-rollback halt (rollback or VM fork detected): {msg}")
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
        Err(e) if e.kind() == io::ErrorKind::NotFound || e.kind() == io::ErrorKind::PermissionDenied => {
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
        mac_key: [u8; 32],
        policy: VmGenPolicy,
    ) -> Result<Self, AntiRollbackError> {
        Self::open_or_create_with_source(
            anchor_path,
            guarded_target,
            mac_key,
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
        mac_key: [u8; 32],
        policy: VmGenPolicy,
        source: S,
    ) -> Result<Self, AntiRollbackError> {
        let key_guard = SecretBuffer(mac_key);
        let record = LockedRecord::acquire(anchor_path)?;
        let guarded_target = guarded_target.into();
        let guard = VmGenIdForkGuard::new(policy);
        let owned_key = *key_guard;
        drop(key_guard);
        let this = Self {
            record,
            guarded_target,
            mac_key: owned_key,
            guard,
            source,
        };
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
        self.load_checked().map_err(AntiRollbackError::into_io_error)
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
    let auth_offset = 14usize
        .checked_add(param_size)
        .ok_or(AntiRollbackError::ProtocolFramingError(
            "TPM2 parameterSize arithmetic overflow",
        ))?;
    if auth_offset + 5 > rsp.len() {
        return Err(AntiRollbackError::ProtocolFramingError(
            "TPM2 parameterSize overruns response auth area",
        ));
    }
    // Validate TPMS_AUTH_RESPONSE framing: nonceTPM (TPM2B) + sessionAttributes (1B) + hmac (TPM2B)
    let auth = &rsp[auth_offset..];
    let nonce_len = u16::from_be_bytes([auth[0], auth[1]]) as usize;
    let attr_pos = 2usize
        .checked_add(nonce_len)
        .ok_or(AntiRollbackError::ProtocolFramingError("TPM2 nonceTPM overflow"))?;
    if attr_pos + 3 > auth.len() {
        return Err(AntiRollbackError::ProtocolFramingError(
            "TPM2 auth response truncated before hmac size",
        ));
    }
    let hmac_len = u16::from_be_bytes([auth[attr_pos + 1], auth[attr_pos + 2]]) as usize;
    if attr_pos + 3 + hmac_len != auth.len() {
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
