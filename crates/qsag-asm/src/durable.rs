//! Exclusive process lock and crash-atomic record replacement for durable callers.
//!
//! Trust and failure model:
//! - The containing directory must be trusted: final-component no-follow checks do not protect
//!   against replacement of ancestor directories. Sidecars must never be unlinked while in use.
//! - `File::sync_all` requests `fcntl(F_FULLFSYNC)` on macOS (including APFS) to drain volatile
//!   device caches. On Linux it uses `fsync`; filesystem/block-layer flushes use `REQ_PREFLUSH` /
//!   `REQ_FUA` as required by the storage stack, not necessarily both flags on every call.
//!   Durability still requires a device that honors flushes. An I/O failure cannot be repaired
//!   by retrying on the same handle.
//! - The sidecar header stores `st_dev || st_ino` of its own inode and every open compares it
//!   with `fstat`. Restoring a sidecar by copy, or remounting the filesystem under a different
//!   device number, therefore fails closed and needs operator re-provisioning.
//! - Genesis is not resumable: a crash after the sidecar entry is created and before the first
//!   [`LockedRecord::replace`] leaves a sidecar without a record. [`LockedRecord::create_new`]
//!   then refuses, and [`LockedRecord::acquire`] reports a non-fresh handle, so a deleted record
//!   can never be mistaken for a new one.
//! - `NotFound` from the constructors means the record itself is absent. A present record whose
//!   sidecar is missing is reported as `InvalidData`.
use core::sync::atomic::{AtomicBool, Ordering};
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use std::sync::Mutex;

const LOCK_MAGIC: &[u8; 8] = b"QSAGLCK1";
const RECORD_MAGIC: &[u8; 8] = b"QSAGREC1";

/// Holds a permanent sidecar inode locked for the lifetime of this handle.
/// The seal detects accidental sidecar replacement; it is not an authentication tag.
pub struct LockedRecord {
    path: PathBuf,
    _lock: File,
    fresh: bool,
    seal: [u8; 8],
    inode: [u8; 16],
    poisoned: AtomicBool,
    operations: Mutex<()>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Sidecar {
    CreateOrOpen,
    MustCreate,
    MustExist,
}

fn side_path(path: &Path, suffix: &str) -> PathBuf {
    let mut name = path.as_os_str().to_os_string();
    name.push(suffix);
    name.into()
}

fn invalid() -> io::Error {
    io::Error::new(
        io::ErrorKind::InvalidData,
        "invalid durable record or lock sidecar",
    )
}

fn regular_metadata(path: &Path) -> io::Result<Option<fs::Metadata>> {
    match fs::symlink_metadata(path) {
        Ok(meta) if meta.is_file() => Ok(Some(meta)),
        Ok(_) => Err(invalid()),
        Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(None),
        Err(e) => Err(e),
    }
}

/// `O_NOFOLLOW | O_NONBLOCK` for the targets whose `fcntl.h` values are known
/// (`O_NONBLOCK` makes opening a FIFO fail instead of block). Linux `asm/fcntl.h`
/// overrides `asm-generic` per architecture; Darwin uses `sys/fcntl.h`. `None` means
/// the caller must fail closed rather than pass another target's constants.
pub const fn open_nofollow_nonblock_flags(os: &str, arch: &str) -> Option<i32> {
    match os.as_bytes() {
        b"macos" => Some(0x100 | 0x4),
        b"linux" => match arch.as_bytes() {
            b"x86_64" | b"x86" | b"riscv64" | b"riscv32" | b"s390x" | b"loongarch64" => {
                Some(0x20000 | 0x800)
            }
            b"aarch64" | b"arm" | b"powerpc" | b"powerpc64" => Some(0x8000 | 0x800),
            b"mips" | b"mips64" => Some(0x20000 | 0x80),
            b"sparc" | b"sparc64" => Some(0x20000 | 0x4000),
            _ => None,
        },
        _ => None,
    }
}

/// Open options for a private (`0600`) durable file whose final path component is
/// never followed through a symlink. The caller adds the access mode. Targets
/// without a known flag encoding get `Unsupported`.
pub fn no_follow_options() -> io::Result<OpenOptions> {
    let unsupported = || {
        io::Error::new(
            io::ErrorKind::Unsupported,
            "no-follow durable files are unavailable on this target",
        )
    };
    let flags = open_nofollow_nonblock_flags(std::env::consts::OS, std::env::consts::ARCH)
        .ok_or_else(unsupported)?;
    let mut options = OpenOptions::new();
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600).custom_flags(flags);
        Ok(options)
    }
    #[cfg(not(unix))]
    {
        let _ = (flags, &mut options);
        Err(unsupported())
    }
}

/// `(st_dev, st_ino)` of an open file or `lstat` result; `None` where the target
/// has no such identity.
pub fn file_dev_ino(meta: &fs::Metadata) -> Option<(u64, u64)> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        Some((meta.dev(), meta.ino()))
    }
    #[cfg(not(unix))]
    {
        let _ = meta;
        None
    }
}

/// Canonical `dev_le64 || ino_le64` file identity. All zero off unix, where every
/// identity comparison is therefore vacuous.
pub fn file_identity(meta: &fs::Metadata) -> [u8; 16] {
    let (dev, ino) = file_dev_ino(meta).unwrap_or((0, 0));
    let mut id = [0; 16];
    id[..8].copy_from_slice(&dev.to_le_bytes());
    id[8..].copy_from_slice(&ino.to_le_bytes());
    id
}

// Compare fstat(fd) with lstat(path), never just two pathname observations.
fn verify_path(file: &File, path: &Path) -> io::Result<fs::Metadata> {
    let held = file.metadata()?;
    let named = regular_metadata(path)?.ok_or_else(invalid)?;
    if !held.is_file() || file_identity(&held) != file_identity(&named) {
        return Err(invalid());
    }
    Ok(held)
}

/// Flush the directory entry of `path` (creation or rename) to stable storage.
pub fn sync_parent_dir(path: &Path) -> io::Result<()> {
    let parent = path
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    File::open(parent)?.sync_all()
}

/// Write all of `bytes` at `offset`, independent of the descriptor's cursor on unix.
pub fn write_at_exact(file: &File, offset: u64, bytes: &[u8]) -> io::Result<()> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::FileExt;
        file.write_all_at(bytes, offset)
    }
    #[cfg(not(unix))]
    {
        use std::io::{Seek, SeekFrom};
        let mut file = file;
        file.seek(SeekFrom::Start(offset))?;
        file.write_all(bytes)
    }
}

impl LockedRecord {
    /// Combined open. A missing sidecar is created only if the record is also absent.
    /// Prefer [`Self::create_new`] and [`Self::open_existing`] for explicit provisioning.
    pub fn acquire(path: impl Into<PathBuf>) -> io::Result<Self> {
        Self::acquire_with(path.into(), Sidecar::CreateOrOpen)
    }

    /// Genesis provisioning. Fails with `AlreadyExists` if any record directory entry exists,
    /// including a dangling symlink, before attempting to create the permanent sidecar.
    pub fn create_new(path: impl Into<PathBuf>) -> io::Result<Self> {
        Self::acquire_with(path.into(), Sidecar::MustCreate)
    }

    /// Recovery: neither file is created. Empty legacy sidecars and replaced inodes fail closed.
    pub fn open_existing(path: impl Into<PathBuf>) -> io::Result<Self> {
        Self::acquire_with(path.into(), Sidecar::MustExist)
    }

    fn acquire_with(path: PathBuf, sidecar: Sidecar) -> io::Result<Self> {
        if sidecar == Sidecar::MustCreate {
            match fs::symlink_metadata(&path) {
                Ok(_) => {
                    return Err(io::Error::new(
                        io::ErrorKind::AlreadyExists,
                        "record already provisioned",
                    ));
                }
                Err(e) if e.kind() == io::ErrorKind::NotFound => {}
                Err(e) => return Err(e),
            }
        }
        let present = regular_metadata(&path)?.is_some();
        if sidecar == Sidecar::MustExist && !present {
            return Err(io::Error::new(
                io::ErrorKind::NotFound,
                "provisioned record is missing",
            ));
        }
        let name = side_path(&path, ".lock");
        regular_metadata(&name)?;
        // A record without its sidecar is damage, not absence: keep `NotFound` for the record.
        let open_present = || {
            no_follow_options()?.read(true).write(true).open(&name).map_err(|e| {
                if present && e.kind() == io::ErrorKind::NotFound {
                    invalid()
                } else {
                    e
                }
            })
        };
        let (mut lock, fresh) = match sidecar {
            Sidecar::MustExist => (open_present()?, false),
            Sidecar::CreateOrOpen if present => (open_present()?, false),
            Sidecar::MustCreate | Sidecar::CreateOrOpen => {
                match no_follow_options()?
                    .read(true)
                    .write(true)
                    .create_new(true)
                    .open(&name)
                {
                    Ok(file) => (file, true),
                    Err(e)
                        if e.kind() == io::ErrorKind::AlreadyExists
                            && sidecar == Sidecar::CreateOrOpen =>
                    {
                        (open_present()?, false)
                    }
                    Err(e) => return Err(e),
                }
            }
        };
        if !lock.metadata()?.is_file() {
            return Err(invalid());
        }
        #[cfg(unix)]
        {
            use std::os::fd::AsRawFd;
            unsafe extern "C" {
                fn flock(fd: core::ffi::c_int, operation: core::ffi::c_int) -> core::ffi::c_int;
            }
            // SAFETY: valid owned descriptor; LOCK_EX | LOCK_NB does not access Rust memory.
            if unsafe { flock(lock.as_raw_fd(), 2 | 4) } != 0 {
                return Err(io::Error::last_os_error());
            }
        }
        let mut header = [0u8; 32];
        let id = file_identity(&verify_path(&lock, &name)?);
        if fresh {
            header[..8].copy_from_slice(LOCK_MAGIC);
            File::open("/dev/urandom")?.read_exact(&mut header[8..16])?;
            header[16..].copy_from_slice(&id);
            lock.write_all(&header)?;
            lock.sync_all()?;
            sync_parent_dir(&path)?;
        } else {
            lock.read_exact(&mut header)?;
            if &header[..8] != LOCK_MAGIC || header[16..] != id || lock.metadata()?.len() != 32 {
                return Err(invalid());
            }
        }
        let present = regular_metadata(&path)?.is_some();
        match sidecar {
            Sidecar::MustCreate if present => {
                return Err(io::Error::new(
                    io::ErrorKind::AlreadyExists,
                    "record already provisioned",
                ));
            }
            Sidecar::MustExist if !present => {
                return Err(io::Error::new(
                    io::ErrorKind::NotFound,
                    "provisioned record is missing",
                ));
            }
            _ => {}
        }
        let record = Self {
            path,
            _lock: lock,
            fresh,
            seal: header[8..16].try_into().expect("eight-byte seal"),
            inode: id,
            poisoned: AtomicBool::new(false),
            operations: Mutex::new(()),
        };
        record.check_lock()?;
        Ok(record)
    }

    /// False after the first creation, even if the record itself was deleted.
    pub fn is_fresh(&self) -> bool {
        self.fresh
    }

    /// Legacy creation nonce. Retained byte-for-byte for existing WAL formats.
    /// This alone does not bind device/inode identity; new authenticated formats
    /// must use [`Self::lock_identity_seal`] instead.
    pub fn lock_seal(&self) -> [u8; 8] {
        self.seal
    }

    /// `dev_le64 || ino_le64` of the sidecar inode this handle holds locked, taken
    /// from the descriptor at acquisition and re-checked on every operation. Callers
    /// that bind the sidecar into a MAC or KDF use this, never a fresh `lstat` of the
    /// `.lock` pathname: that observes whatever the name points at now.
    pub fn lock_inode(&self) -> [u8; 16] {
        self.inode
    }

    /// Canonical `dev_le64 || ino_le64 || nonce8` identity for a caller's MAC/KDF.
    ///
    /// This is public associated data, NOT a MAC. Authenticate all 24 bytes with
    /// the record's version, domain and payload, then verify on recovery before
    /// releasing authority. A copied sidecar with a rewritten inode retains the
    /// legacy nonce but cannot retain this identity. This does not prevent disk
    /// rollback or inode reuse; independent monotonic custody is still required.
    pub fn lock_identity_seal(&self) -> [u8; 24] {
        let mut seal = [0; 24];
        seal[..16].copy_from_slice(&self.inode);
        seal[16..].copy_from_slice(&self.seal);
        seal
    }

    /// Verify a previously authenticated identity and the currently held lock.
    /// An identity mismatch permanently invalidates this handle. The expected
    /// value must come from authenticated custody, not an unauthenticated header.
    pub fn verify_lock_identity(&self, expected: &[u8; 24]) -> io::Result<()> {
        let _operation = self
            .operations
            .lock()
            .map_err(|_| io::Error::other("record mutex poisoned"))?;
        let result = self.check_lock().and_then(|()| {
            if crate::ct_eq_bytes(&self.lock_identity_seal(), expected) {
                Ok(())
            } else {
                Err(invalid())
            }
        });
        if result.is_err() {
            self.poisoned.store(true, Ordering::SeqCst);
        }
        result
    }

    fn check_lock(&self) -> io::Result<()> {
        if self.poisoned.load(Ordering::SeqCst) {
            return Err(io::Error::other("durable record handle is poisoned"));
        }
        let name = side_path(&self.path, ".lock");
        if file_identity(&verify_path(&self._lock, &name)?) != self.inode {
            return Err(invalid());
        }
        // Read from the locked descriptor itself: reopening the pathname can
        // select a different inode between lstat and open. Positional I/O also
        // leaves the descriptor offset unchanged across successive operations.
        #[cfg(not(unix))]
        {
            Err(io::Error::new(
                io::ErrorKind::Unsupported,
                "positional lock reads unavailable",
            ))
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::FileExt;
            let mut header = [0u8; 32];
            self._lock.read_exact_at(&mut header, 0)?;
            if verify_path(&self._lock, &name)?.len() != 32
                || &header[..8] != LOCK_MAGIC
                || header[8..16] != self.seal
                || header[16..] != self.inode
            {
                return Err(invalid());
            }
            Ok(())
        }
    }

    /// Default upper bound (`64 MiB`) enforced by [`LockedRecord::read`] before allocating a
    /// heap payload buffer, preventing OOM kills if an attacker or filesystem corruption
    /// substitutes a multi-gigabyte sparse regular file.
    pub const MAX_DEFAULT_RECORD_BYTES: usize = 64 * 1024 * 1024;

    pub fn read(&self) -> io::Result<std::vec::Vec<u8>> {
        self.read_bounded(Self::MAX_DEFAULT_RECORD_BYTES)
    }

    /// Read and authenticate the record payload while enforcing `payload_len <= max_bytes`
    /// via `fstat` on the opened descriptor *before* any heap allocation.
    pub fn read_bounded(&self, max_bytes: usize) -> io::Result<std::vec::Vec<u8>> {
        let _operation = self
            .operations
            .lock()
            .map_err(|_| io::Error::other("record mutex poisoned"))?;
        (|| {
            self.check_lock()?;
            regular_metadata(&self.path)?;
            let mut file = no_follow_options()?.read(true).open(&self.path)?;
            let meta = verify_path(&file, &self.path)?;
            let raw_payload_len = meta.len().checked_sub(16).ok_or_else(invalid)?;
            if raw_payload_len > max_bytes as u64 {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "durable record exceeds bounded payload limit",
                ));
            }
            let len = usize::try_from(raw_payload_len).map_err(|_| invalid())?;
            let mut header = [0u8; 16];
            file.read_exact(&mut header)?;
            if &header[..8] != RECORD_MAGIC || header[8..] != self.seal {
                return Err(invalid());
            }
            // A failed read erases the partial payload. One allocation at the observed
            // length: growth would abandon an unerased copy.
            let mut bytes = crate::wipe::SecretBuffer(std::vec::Vec::new());
            bytes.try_reserve_exact(len).map_err(io::Error::other)?;
            bytes.resize(len, 0);
            file.read_exact(&mut bytes)?;
            if verify_path(&file, &self.path)?.len() != meta.len() {
                return Err(invalid());
            }
            self.check_lock()?;
            Ok(bytes.into_inner())
        })()
    }

    /// Atomically replace and sync the record. Any failure permanently poisons this handle;
    /// callers must recover using a new handle and validate their WAL before continuing.
    pub fn replace(&self, bytes: &[u8]) -> io::Result<()> {
        let _operation = self
            .operations
            .lock()
            .map_err(|_| io::Error::other("record mutex poisoned"))?;
        let result = (|| {
            self.check_lock()?;
            regular_metadata(&self.path)?;
            let name = side_path(&self.path, ".tmp");
            if regular_metadata(&name)?.is_some() {
                fs::remove_file(&name)?;
            }
            let mut file = no_follow_options()?.write(true).create_new(true).open(&name)?;
            file.write_all(RECORD_MAGIC)?;
            file.write_all(&self.lock_seal())?;
            file.write_all(bytes)?;
            file.sync_all()?;
            verify_path(&file, &name)?;
            self.check_lock()?;
            regular_metadata(&self.path)?;
            fs::rename(&name, &self.path)?;
            verify_path(&file, &self.path)?;
            sync_parent_dir(&self.path)?;
            self.check_lock()
        })();
        if result.is_err() {
            self.poisoned.store(true, Ordering::SeqCst);
        }
        result
    }
}

/// Size of one high-water-mark slot: `counter(8) || tip(32) || mac(32) || zero(8)`.
pub const HWM_SLOT_BYTES: usize = 80;

/// Byte order of the slot counter. It is part of each journal's persisted format.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CounterOrder {
    Big,
    Little,
}

/// Authenticates one slot: `(slot index, encoded counter, chain tip, reserved bytes)`.
/// The caller's closure supplies the key, domain tag and every journal-specific binding.
pub type HwmSlotMac<'a> = &'a dyn Fn(u8, &[u8; 8], &[u8; 32], &[u8; 8]) -> [u8; 32];

/// The hash chain as read back from disk, after every record MAC verified.
pub struct ChainHead<'a> {
    /// Number of committed records the chain holds.
    pub len: u64,
    /// Tag of the last record (the genesis tag when `len == 0`).
    pub tip: &'a [u8; 32],
    /// Tag of the record before it (the genesis tag when `len <= 1`).
    pub previous_tip: &'a [u8; 32],
}

/// Two authenticated high-water-mark slots guarding an append-only hash chain
/// against tail truncation.
///
/// A commit appends and syncs the record first, then writes and syncs slot A, then
/// slot B. A valid file therefore has `A == B` (steady state) or `A == B + 1` (crash
/// between the two slot syncs), and the chain holds `A` or `A + 1` records (crash
/// after the record sync, before slot A). Anything else, including a chain shorter
/// than `A`, is rejected; the two crash states are healed forward.
pub struct TwoSlotHwm<'a> {
    pub offset_a: u64,
    pub offset_b: u64,
    pub order: CounterOrder,
    pub mac: HwmSlotMac<'a>,
}

impl TwoSlotHwm<'_> {
    fn counter_bytes(&self, counter: u64) -> [u8; 8] {
        match self.order {
            CounterOrder::Big => counter.to_be_bytes(),
            CounterOrder::Little => counter.to_le_bytes(),
        }
    }

    pub fn encode(&self, slot: u8, counter: u64, tip: &[u8; 32]) -> [u8; HWM_SLOT_BYTES] {
        let counter = self.counter_bytes(counter);
        let mut out = [0u8; HWM_SLOT_BYTES];
        out[..8].copy_from_slice(&counter);
        out[8..40].copy_from_slice(tip);
        out[40..72].copy_from_slice(&(self.mac)(slot, &counter, tip, &[0u8; 8]));
        out
    }

    /// Authenticate one slot and return its `(counter, tip)`.
    pub fn verify(&self, slot: u8, raw: &[u8]) -> io::Result<(u64, [u8; 32])> {
        let raw: &[u8; HWM_SLOT_BYTES] = raw.try_into().map_err(|_| invalid())?;
        let counter: [u8; 8] = raw[..8].try_into().map_err(|_| invalid())?;
        let tip: [u8; 32] = raw[8..40].try_into().map_err(|_| invalid())?;
        let stored: [u8; 32] = raw[40..72].try_into().map_err(|_| invalid())?;
        let reserved: [u8; 8] = raw[72..].try_into().map_err(|_| invalid())?;
        if reserved != [0u8; 8]
            || !crate::ct_eq_32(&(self.mac)(slot, &counter, &tip, &reserved), &stored)
        {
            return Err(invalid());
        }
        let counter = match self.order {
            CounterOrder::Big => u64::from_be_bytes(counter),
            CounterOrder::Little => u64::from_le_bytes(counter),
        };
        Ok((counter, tip))
    }

    /// Record `counter` records ending at `tip`: slot A, sync, slot B, sync. Call
    /// only after the record itself is synced.
    pub fn commit(&self, file: &File, counter: u64, tip: &[u8; 32]) -> io::Result<()> {
        write_at_exact(file, self.offset_a, &self.encode(0, counter, tip))?;
        file.sync_all()?;
        write_at_exact(file, self.offset_b, &self.encode(1, counter, tip))?;
        file.sync_all()
    }

    /// Reconcile both stored slots with the chain found on disk, healing the two
    /// legal crash states. Returns an error, without writing, for every other state.
    pub fn recover(
        &self,
        file: &File,
        raw_a: &[u8],
        raw_b: &[u8],
        head: &ChainHead<'_>,
    ) -> io::Result<()> {
        let (a, tip_a) = self.verify(0, raw_a)?;
        let (b, tip_b) = self.verify(1, raw_b)?;
        if a < b || a - b > 1 {
            return Err(invalid());
        }
        if head.len == a {
            if !crate::ct_eq_32(head.tip, &tip_a) {
                return Err(invalid());
            }
            if b != a || !crate::ct_eq_32(&tip_b, &tip_a) {
                write_at_exact(file, self.offset_b, &self.encode(1, a, head.tip))?;
                file.sync_all()?;
            }
            Ok(())
        } else if a.checked_add(1) == Some(head.len) {
            // The record reached the disk; neither slot was advanced yet.
            if a != b
                || !crate::ct_eq_32(&tip_a, &tip_b)
                || !crate::ct_eq_32(head.previous_tip, &tip_a)
            {
                return Err(invalid());
            }
            self.commit(file, head.len, head.tip)
        } else {
            Err(invalid())
        }
    }
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;
    use std::os::unix::fs::symlink;
    use std::sync::atomic::AtomicU64;

    struct Temp(PathBuf);
    impl Temp {
        fn new() -> Self {
            static NEXT: AtomicU64 = AtomicU64::new(0);
            let path = std::env::temp_dir().join(std::format!(
                "qsag-record-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            fs::create_dir(&path).unwrap();
            Self(path)
        }
        fn record(&self) -> PathBuf {
            self.0.join("record")
        }
    }
    impl Drop for Temp {
        fn drop(&mut self) {
            fs::remove_dir_all(&self.0).unwrap();
        }
    }

    #[test]
    fn legacy_acquire_read_before_initial_write_remains_supported() {
        let temp = Temp::new();
        let record = LockedRecord::acquire(temp.record()).unwrap();
        assert!(record.is_fresh());
        assert_eq!(record.read().unwrap_err().kind(), io::ErrorKind::NotFound);
        record.replace(b"genesis").unwrap();
        assert_eq!(record.read().unwrap(), b"genesis");
        // A damaged inactive slot can be replaced after the higher-level ledger
        // authenticates its surviving slot and external checkpoint.
        fs::write(temp.record(), b"torn").unwrap();
        assert!(record.read().is_err());
        record.replace(b"recovered").unwrap();
        assert_eq!(record.read().unwrap(), b"recovered");
    }

    #[test]
    fn recovery_probes_do_not_provision_sidecars() {
        let temp = Temp::new();
        let path = temp.record();
        for _ in 0..2 {
            assert_eq!(
                LockedRecord::open_existing(&path).err().unwrap().kind(),
                io::ErrorKind::NotFound
            );
            assert!(!side_path(&path, ".lock").exists());
        }
        let record = LockedRecord::create_new(&path).unwrap();
        record.replace(b"fresh").unwrap();
        let expected = record.lock_identity_seal();
        drop(record);
        let record = LockedRecord::open_existing(&path).unwrap();
        record.verify_lock_identity(&expected).unwrap();
        assert_eq!(record.read().unwrap(), b"fresh");
    }

    #[test]
    fn rewritten_sidecar_inode_changes_authenticated_identity() {
        let temp = Temp::new();
        let path = temp.record();
        let old = LockedRecord::create_new(&path).unwrap();
        old.replace(b"payload").unwrap();
        let expected = old.lock_identity_seal();
        let name = side_path(&path, ".lock");
        fs::rename(&name, side_path(&path, ".old-lock")).unwrap();
        fs::copy(side_path(&path, ".old-lock"), &name).unwrap();
        // Model an attacker rewriting the unauthenticated inode fields while
        // keeping the nonce. Only the full authenticated identity distinguishes it.
        let mut header = fs::read(&name).unwrap();
        header[16..].copy_from_slice(&file_identity(&fs::metadata(&name).unwrap()));
        fs::write(&name, header).unwrap();
        let new = LockedRecord::open_existing(&path).unwrap();
        assert_eq!(old.lock_seal(), new.lock_seal());
        assert_ne!(expected, new.lock_identity_seal());
        assert!(new.verify_lock_identity(&expected).is_err());
        assert!(new.read().is_err());
        assert!(old.read().is_err());
    }

    #[test]
    fn descriptor_identity_rejects_identical_path_replacement() {
        let temp = Temp::new();
        let path = temp.record();
        fs::write(&path, b"identical").unwrap();
        let held = File::open(&path).unwrap();
        verify_path(&held, &path).unwrap();
        fs::rename(&path, side_path(&path, ".old")).unwrap();
        fs::write(&path, b"identical").unwrap();
        assert!(verify_path(&held, &path).is_err());
    }

    #[test]
    fn empty_and_large_payloads_preserve_legacy_format() {
        let temp = Temp::new();
        let path = temp.record();
        let record = LockedRecord::create_new(&path).unwrap();
        for bytes in [std::vec![], std::vec![0x5a; 65537]] {
            record.replace(&bytes).unwrap();
            assert_eq!(record.read().unwrap(), bytes);
            let raw = fs::read(&path).unwrap();
            assert_eq!(&raw[..8], RECORD_MAGIC);
            assert_eq!(&raw[8..16], &record.lock_seal());
            assert_eq!(&raw[16..], &bytes);
        }
        let expected = record.lock_identity_seal();
        let mut wrong = expected;
        wrong[23] ^= 1;
        assert!(record.verify_lock_identity(&wrong).is_err());
        assert!(record.verify_lock_identity(&expected).is_err());
    }

    #[test]
    fn same_inode_seal_overwrite_is_rejected() {
        let temp = Temp::new();
        let path = temp.record();
        let record = LockedRecord::create_new(&path).unwrap();
        record.replace(b"committed").unwrap();
        let lock = side_path(&path, ".lock");
        let mut bytes = fs::read(&lock).unwrap();
        bytes[8] ^= 1;
        fs::write(lock, bytes).unwrap();
        assert!(record.read().is_err());
        assert!(record.replace(b"bad").is_err());
    }

    #[test]
    fn missing_sidecar_cannot_split_lock() {
        let temp = Temp::new();
        let path = temp.record();
        let first = LockedRecord::create_new(&path).unwrap();
        first.replace(b"committed").unwrap();
        let lock = side_path(&path, ".lock");
        fs::remove_file(&lock).unwrap();
        assert_eq!(
            LockedRecord::create_new(&path).err().unwrap().kind(),
            io::ErrorKind::AlreadyExists
        );
        assert!(!lock.exists());
        assert_eq!(
            LockedRecord::open_existing(&path).err().unwrap().kind(),
            io::ErrorKind::InvalidData
        );
        assert_eq!(
            LockedRecord::acquire(&path).err().unwrap().kind(),
            io::ErrorKind::InvalidData
        );
        assert!(!lock.exists());
        assert!(first.read().is_err());
        assert!(first.replace(b"split").is_err());
    }

    #[test]
    fn seal_roundtrip_and_replacement_rejection() {
        let temp = Temp::new();
        let path = temp.record();
        let first = LockedRecord::acquire(&path).unwrap();
        assert!(first.is_fresh());
        first.replace(b"first").unwrap();
        assert!(LockedRecord::open_existing(&path).is_err());
        let seal = first.lock_seal();
        drop(first);
        let second = LockedRecord::open_existing(&path).unwrap();
        assert!(!second.is_fresh());
        assert_eq!(second.lock_seal(), seal);
        fs::write(side_path(&path, ".tmp"), b"stale").unwrap();
        second.replace(b"second").unwrap();
        assert_eq!(second.read().unwrap(), b"second");
        drop(second);
        let lock = side_path(&path, ".lock");
        fs::rename(&lock, side_path(&path, ".old-lock")).unwrap();
        fs::copy(side_path(&path, ".old-lock"), &lock).unwrap();
        assert!(LockedRecord::open_existing(&path).is_err());
        for header in [&b""[..], &b"QSAGLCK1"[..], &[0u8; 32][..]] {
            fs::write(&lock, header).unwrap();
            assert!(LockedRecord::open_existing(&path).is_err());
        }
    }

    #[test]
    fn symlinks_are_rejected_without_touching_targets() {
        for suffix in [".lock", ".tmp", ""] {
            let temp = Temp::new();
            let path = temp.record();
            let target = temp.0.join("target");
            fs::write(&target, b"untouched").unwrap();
            if suffix == ".lock" {
                symlink(&target, side_path(&path, suffix)).unwrap();
                assert!(LockedRecord::acquire(&path).is_err());
                assert!(LockedRecord::open_existing(&path).is_err());
            } else {
                let record = LockedRecord::create_new(&path).unwrap();
                symlink(&target, side_path(&path, suffix)).unwrap();
                if suffix.is_empty() {
                    assert!(record.read().is_err());
                }
                assert!(record.replace(b"bad").is_err());
            }
            assert_eq!(fs::read(&target).unwrap(), b"untouched");
        }
        let temp = Temp::new();
        let path = temp.record();
        symlink(temp.0.join("absent"), &path).unwrap();
        assert_eq!(
            LockedRecord::create_new(&path).err().unwrap().kind(),
            io::ErrorKind::AlreadyExists
        );
        assert!(!side_path(&path, ".lock").exists());
    }

    #[test]
    fn failed_replace_stays_poisoned_after_path_repair() {
        let temp = Temp::new();
        let path = temp.record();
        let record = LockedRecord::create_new(&path).unwrap();
        record.replace(b"committed").unwrap();
        // Deterministic path failure, including when tests run with elevated privileges.
        let tmp = side_path(&path, ".tmp");
        fs::create_dir(&tmp).unwrap();
        assert!(record.replace(b"lost").is_err());
        fs::remove_dir(&tmp).unwrap();
        assert!(record.read().is_err());
        assert!(record.replace(b"retry").is_err());
        drop(record);
        assert_eq!(
            LockedRecord::open_existing(path).unwrap().read().unwrap(),
            b"committed"
        );
    }

    #[test]
    fn read_bounded_rejects_oversized_sparse_record_before_allocation() {
        let temp = Temp::new();
        let path = temp.record();
        let record = LockedRecord::create_new(&path).unwrap();
        record.replace(b"small-payload").unwrap();
        assert_eq!(record.read_bounded(13).unwrap(), b"small-payload");
        assert_eq!(
            record.read_bounded(12).unwrap_err().kind(),
            io::ErrorKind::InvalidData
        );

        // Inflate the backing regular file to a 1 GiB sparse file while preserving its
        // 16-byte header (`RECORD_MAGIC || seal`): both `read_bounded` and default `read`
        // must reject via `fstat` before attempting any heap allocation.
        let file = fs::OpenOptions::new().write(true).open(&path).unwrap();
        file.set_len((1u64 << 30) + 16).unwrap();
        drop(file);

        assert_eq!(
            record.read_bounded(4096).unwrap_err().kind(),
            io::ErrorKind::InvalidData
        );
        assert_eq!(
            record.read().unwrap_err().kind(),
            io::ErrorKind::InvalidData
        );
    }

    #[test]
    fn nofollow_flag_table_fails_closed_on_unknown_targets() {
        assert_eq!(
            open_nofollow_nonblock_flags("linux", "x86_64"),
            Some(0x20000 | 0x800)
        );
        assert_eq!(
            open_nofollow_nonblock_flags("linux", "aarch64"),
            Some(0x8000 | 0x800)
        );
        assert_eq!(
            open_nofollow_nonblock_flags("linux", "mips64"),
            Some(0x20000 | 0x80)
        );
        assert_eq!(
            open_nofollow_nonblock_flags("linux", "sparc64"),
            Some(0x20000 | 0x4000)
        );
        assert_eq!(open_nofollow_nonblock_flags("macos", "aarch64"), Some(0x104));
        assert_eq!(open_nofollow_nonblock_flags("linux", "alpha"), None);
        assert_eq!(open_nofollow_nonblock_flags("freebsd", "x86_64"), None);
    }

    #[test]
    fn lock_inode_is_the_held_descriptor_identity() {
        let temp = Temp::new();
        let path = temp.record();
        let record = LockedRecord::create_new(&path).unwrap();
        record.replace(b"payload").unwrap();
        let named = fs::symlink_metadata(side_path(&path, ".lock")).unwrap();
        assert_eq!(record.lock_inode(), file_identity(&named));
        assert_eq!(record.lock_identity_seal()[..16], record.lock_inode());
    }

    /// A keyless stand-in for the caller's MAC: binds every input so a slot moved to
    /// the other index, or edited anywhere, stops verifying.
    fn toy_mac(slot: u8, counter: &[u8; 8], tip: &[u8; 32], reserved: &[u8; 8]) -> [u8; 32] {
        let mut out = [0x5au8; 32];
        for (i, b) in counter.iter().chain(tip).chain(reserved).enumerate() {
            out[i % 32] = out[i % 32].rotate_left(3) ^ b ^ (i as u8) ^ slot.wrapping_mul(0x9d);
        }
        out
    }

    struct HwmFile {
        _temp: Temp,
        file: File,
    }
    impl HwmFile {
        fn new() -> Self {
            let temp = Temp::new();
            let file = OpenOptions::new()
                .read(true)
                .write(true)
                .create_new(true)
                .open(temp.record())
                .unwrap();
            file.set_len(2 * HWM_SLOT_BYTES as u64).unwrap();
            Self { _temp: temp, file }
        }
        fn slots(&self) -> ([u8; HWM_SLOT_BYTES], [u8; HWM_SLOT_BYTES]) {
            use std::os::unix::fs::FileExt;
            let mut a = [0u8; HWM_SLOT_BYTES];
            let mut b = [0u8; HWM_SLOT_BYTES];
            self.file.read_exact_at(&mut a, 0).unwrap();
            self.file.read_exact_at(&mut b, HWM_SLOT_BYTES as u64).unwrap();
            (a, b)
        }
    }

    #[test]
    fn two_slot_hwm_heals_only_the_two_crash_states() {
        for order in [CounterOrder::Big, CounterOrder::Little] {
            let hwm = TwoSlotHwm {
                offset_a: 0,
                offset_b: HWM_SLOT_BYTES as u64,
                order,
                mac: &toy_mac,
            };
            let tips: [[u8; 32]; 4] = core::array::from_fn(|i| [i as u8 + 1; 32]);
            let head = |len: usize| ChainHead {
                len: len as u64,
                tip: &tips[len],
                previous_tip: &tips[len.saturating_sub(1)],
            };
            let disk = HwmFile::new();

            // Steady state round trip; the counter is stored in the declared order.
            hwm.commit(&disk.file, 2, &tips[2]).unwrap();
            let (a, b) = disk.slots();
            assert_eq!(hwm.verify(0, &a).unwrap(), (2, tips[2]));
            assert_eq!(hwm.verify(1, &b).unwrap(), (2, tips[2]));
            let stored = match order {
                CounterOrder::Big => 2u64.to_be_bytes(),
                CounterOrder::Little => 2u64.to_le_bytes(),
            };
            assert_eq!(a[..8], stored);
            hwm.recover(&disk.file, &a, &b, &head(2)).unwrap();
            assert_eq!(disk.slots(), (a, b), "steady state is not rewritten");

            // A slot is bound to its index, its length and every byte.
            assert!(hwm.verify(1, &a).is_err());
            assert!(hwm.verify(0, &a[..79]).is_err());
            for i in 0..HWM_SLOT_BYTES {
                let mut bad = a;
                bad[i] ^= 1;
                assert!(hwm.verify(0, &bad).is_err(), "byte {i}");
            }

            // Tail truncation and a foreign tip are refused without writing.
            assert!(hwm.recover(&disk.file, &a, &b, &head(1)).is_err());
            assert!(hwm.recover(&disk.file, &a, &b, &head(0)).is_err());
            let foreign = ChainHead {
                len: 2,
                tip: &tips[3],
                previous_tip: &tips[1],
            };
            assert!(hwm.recover(&disk.file, &a, &b, &foreign).is_err());
            // Two records beyond the mark cannot come from one interrupted commit.
            hwm.commit(&disk.file, 1, &tips[1]).unwrap();
            let (a1, b1) = disk.slots();
            assert!(hwm.recover(&disk.file, &a1, &b1, &head(3)).is_err());
            assert_eq!(disk.slots(), (a1, b1));

            // Crash after the record sync, before slot A: both slots advance.
            hwm.recover(&disk.file, &a1, &b1, &head(2)).unwrap();
            assert_eq!(disk.slots(), (a, b));
            // ...but only onto the record that extends the marked tip.
            hwm.commit(&disk.file, 1, &tips[1]).unwrap();
            let wrong_parent = ChainHead {
                len: 2,
                tip: &tips[2],
                previous_tip: &tips[3],
            };
            assert!(hwm.recover(&disk.file, &a1, &b1, &wrong_parent).is_err());

            // Crash between the slot syncs (A ahead by one): slot B is healed.
            hwm.recover(&disk.file, &a, &b1, &head(2)).unwrap();
            assert_eq!(disk.slots().1, b);
            // With A ahead, a chain one past A is not a legal crash state.
            assert!(hwm.recover(&disk.file, &a, &b1, &head(3)).is_err());
            // B ahead of A, or A ahead by two, never happens.
            assert!(hwm.recover(&disk.file, &a1, &b, &head(2)).is_err());
            let a3 = hwm.encode(0, 3, &tips[3]);
            assert!(hwm.recover(&disk.file, &a3, &b1, &head(3)).is_err());
        }
    }
}
