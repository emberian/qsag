//! Exclusive process lock and crash-atomic record replacement for durable callers.
//!
//! The containing directory must be trusted: final-component no-follow checks do not protect
//! against replacement of ancestor directories. Sidecars must never be unlinked while in use.
//! `File::sync_all` requests `fcntl(F_FULLFSYNC)` on macOS (including APFS) to drain volatile
//! device caches. On Linux it uses
//! `fsync`; filesystem/block-layer flushes use `REQ_PREFLUSH` / `REQ_FUA` as required by the
//! storage stack, not necessarily both flags on every call. Durability still requires a device
//! that honors flushes. An I/O failure cannot be repaired by retrying on the same handle.
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
    poisoned: AtomicBool,
    operations: Mutex<()>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Sidecar { CreateOrOpen, MustCreate, MustExist }

fn side_path(path: &Path, suffix: &str) -> PathBuf {
    let mut name = path.as_os_str().to_os_string();
    name.push(suffix);
    name.into()
}

fn invalid() -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, "invalid durable record or lock sidecar")
}

fn regular_metadata(path: &Path) -> io::Result<Option<fs::Metadata>> {
    match fs::symlink_metadata(path) {
        Ok(meta) if meta.is_file() => Ok(Some(meta)),
        Ok(_) => Err(invalid()),
        Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(None),
        Err(e) => Err(e),
    }
}

fn options() -> io::Result<OpenOptions> {
    let mut options = OpenOptions::new();
    // Linux UAPI asm/fcntl.h overrides asm-generic on ARM; Darwin uses sys/fcntl.h.
    #[cfg(all(target_os = "linux", any(target_arch = "aarch64", target_arch = "arm")))]
    let flags = 0x8000 | 0x800; // O_NOFOLLOW | O_NONBLOCK (reject FIFOs without blocking).
    #[cfg(all(target_os = "linux", any(target_arch = "x86_64", target_arch = "x86", target_arch = "riscv64", target_arch = "riscv32")))]
    let flags = 0x20000 | 0x800;
    #[cfg(target_os = "macos")]
    let flags = 0x100 | 0x4;
    #[cfg(any(target_os = "macos", all(target_os = "linux", any(target_arch = "aarch64", target_arch = "arm", target_arch = "x86_64", target_arch = "x86", target_arch = "riscv64", target_arch = "riscv32"))))]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600).custom_flags(flags);
        Ok(options)
    }
    #[cfg(not(any(target_os = "macos", all(target_os = "linux", any(target_arch = "aarch64", target_arch = "arm", target_arch = "x86_64", target_arch = "x86", target_arch = "riscv64", target_arch = "riscv32")))))]
    {
        let _ = &mut options;
        Err(io::Error::new(io::ErrorKind::Unsupported, "no-follow locking unavailable on this target"))
    }
}

fn identity(meta: &fs::Metadata) -> [u8; 16] {
    let mut id = [0; 16];
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        id[..8].copy_from_slice(&meta.dev().to_le_bytes());
        id[8..].copy_from_slice(&meta.ino().to_le_bytes());
    }
    id
}

fn sync_parent(path: &Path) -> io::Result<()> {
    let parent = path.parent().filter(|p| !p.as_os_str().is_empty()).unwrap_or(Path::new("."));
    File::open(parent)?.sync_all()
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
                Ok(_) => return Err(io::Error::new(io::ErrorKind::AlreadyExists, "record already provisioned")),
                Err(e) if e.kind() == io::ErrorKind::NotFound => {}
                Err(e) => return Err(e),
            }
        }
        let present = regular_metadata(&path)?.is_some();
        let name = side_path(&path, ".lock");
        regular_metadata(&name)?;
        let open_present = || options()?.read(true).write(true).open(&name);
        let (mut lock, fresh) = match sidecar {
            Sidecar::MustExist => (open_present()?, false),
            Sidecar::CreateOrOpen if present => (open_present()?, false),
            Sidecar::MustCreate | Sidecar::CreateOrOpen => {
                match options()?.read(true).write(true).create_new(true).open(&name) {
                    Ok(file) => (file, true),
                    Err(e) if e.kind() == io::ErrorKind::AlreadyExists && sidecar == Sidecar::CreateOrOpen => (open_present()?, false),
                    Err(e) => return Err(e),
                }
            }
        };
        if !lock.metadata()?.is_file() { return Err(invalid()); }
        #[cfg(unix)]
        {
            use std::os::fd::AsRawFd;
            unsafe extern "C" { fn flock(fd: core::ffi::c_int, operation: core::ffi::c_int) -> core::ffi::c_int; }
            // SAFETY: valid owned descriptor; LOCK_EX | LOCK_NB does not access Rust memory.
            if unsafe { flock(lock.as_raw_fd(), 2 | 4) } != 0 { return Err(io::Error::last_os_error()); }
        }
        let mut header = [0u8; 32];
        let id = identity(&lock.metadata()?);
        if fresh {
            header[..8].copy_from_slice(LOCK_MAGIC);
            File::open("/dev/urandom")?.read_exact(&mut header[8..16])?;
            header[16..].copy_from_slice(&id);
            lock.write_all(&header)?;
            lock.sync_all()?;
            sync_parent(&path)?;
        } else {
            lock.read_exact(&mut header)?;
            if &header[..8] != LOCK_MAGIC || header[16..] != id || lock.metadata()?.len() != 32 {
                return Err(invalid());
            }
        }
        let present = regular_metadata(&path)?.is_some();
        match sidecar {
            Sidecar::MustCreate if present => return Err(io::Error::new(io::ErrorKind::AlreadyExists, "record already provisioned")),
            Sidecar::MustExist if !present => return Err(io::Error::new(io::ErrorKind::NotFound, "provisioned record is missing")),
            _ => {}
        }
        let record = Self {
            path, _lock: lock, fresh, seal: header[8..16].try_into().expect("eight-byte seal"),
            poisoned: AtomicBool::new(false), operations: Mutex::new(()),
        };
        record.check_lock()?;
        Ok(record)
    }

    /// False after the first creation, even if the record itself was deleted.
    pub fn is_fresh(&self) -> bool { self.fresh }

    /// Persistent creation seal, suitable for binding a higher-level WAL to this sidecar.
    pub fn lock_seal(&self) -> [u8; 8] { self.seal }

    fn check_lock(&self) -> io::Result<()> {
        if self.poisoned.load(Ordering::SeqCst) {
            return Err(io::Error::other("durable record handle is poisoned"));
        }
        let meta = regular_metadata(&side_path(&self.path, ".lock"))?.ok_or_else(invalid)?;
        if identity(&meta) != identity(&self._lock.metadata()?) { return Err(invalid()); }
        // Revalidate the persistent seal as well as inode identity on every operation.
        // A same-inode header overwrite must not silently change the lock's identity.
        let mut header = [0u8; 32];
        let mut lock = options()?.read(true).open(side_path(&self.path, ".lock"))?;
        lock.read_exact(&mut header)?;
        if lock.metadata()?.len() != 32 || &header[..8] != LOCK_MAGIC
            || header[8..16] != self.lock_seal()
            || header[16..] != identity(&self._lock.metadata()?) {
            return Err(invalid());
        }
        Ok(())
    }

    pub fn read(&self) -> io::Result<std::vec::Vec<u8>> {
        let _operation = self.operations.lock().map_err(|_| io::Error::other("record mutex poisoned"))?;
        self.check_lock()?;
        regular_metadata(&self.path)?;
        let mut file = options()?.read(true).open(&self.path)?;
        if !file.metadata()?.is_file() { return Err(invalid()); }
        let mut bytes = std::vec::Vec::new();
        file.read_to_end(&mut bytes)?;
        if bytes.len() < 16 || &bytes[..8] != RECORD_MAGIC || bytes[8..16] != self.lock_seal() {
            return Err(invalid());
        }
        bytes.drain(..16);
        Ok(bytes)
    }

    /// Atomically replace and sync the record. Any failure permanently poisons this handle;
    /// callers must recover using a new handle and validate their WAL before continuing.
    pub fn replace(&self, bytes: &[u8]) -> io::Result<()> {
        let _operation = self.operations.lock().map_err(|_| io::Error::other("record mutex poisoned"))?;
        let result = (|| {
            self.check_lock()?;
            regular_metadata(&self.path)?;
            let name = side_path(&self.path, ".tmp");
            if regular_metadata(&name)?.is_some() { fs::remove_file(&name)?; }
            let mut file = options()?.write(true).create_new(true).open(&name)?;
            file.write_all(RECORD_MAGIC)?;
            file.write_all(&self.lock_seal())?;
            file.write_all(bytes)?;
            file.sync_all()?;
            self.check_lock()?;
            regular_metadata(&self.path)?;
            fs::rename(&name, &self.path)?;
            sync_parent(&self.path)
        })();
        if result.is_err() { self.poisoned.store(true, Ordering::SeqCst); }
        result
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
            let path = std::env::temp_dir().join(std::format!("qsag-record-{}-{}", std::process::id(), NEXT.fetch_add(1, Ordering::Relaxed)));
            fs::create_dir(&path).unwrap();
            Self(path)
        }
        fn record(&self) -> PathBuf { self.0.join("record") }
    }
    impl Drop for Temp {
        fn drop(&mut self) { fs::remove_dir_all(&self.0).unwrap(); }
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
        assert_eq!(LockedRecord::create_new(&path).err().unwrap().kind(), io::ErrorKind::AlreadyExists);
        assert!(!lock.exists());
        assert!(LockedRecord::open_existing(&path).is_err());
        assert!(LockedRecord::acquire(&path).is_err());
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
                if suffix.is_empty() { assert!(record.read().is_err()); }
                assert!(record.replace(b"bad").is_err());
            }
            assert_eq!(fs::read(&target).unwrap(), b"untouched");
        }
        let temp = Temp::new();
        let path = temp.record();
        symlink(temp.0.join("absent"), &path).unwrap();
        assert_eq!(LockedRecord::create_new(&path).err().unwrap().kind(), io::ErrorKind::AlreadyExists);
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
        assert_eq!(LockedRecord::open_existing(path).unwrap().read().unwrap(), b"committed");
    }
}
