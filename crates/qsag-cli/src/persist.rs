//! Durable file primitives shared by every piece of CLI custody state: exclusive creation,
//! crash-atomic replacement, lock files, file and directory identity, and the canonical
//! bytes a JSON header is authenticated over.
//!
//! The containing directory must be trusted: the final path component is never followed
//! through a symlink, but an ancestor that is replaced is not detected here.

use std::fs::{File, Metadata, OpenOptions};
use std::io::{self, Write};
use std::path::{Path, PathBuf};

use crate::cli::{CliError, ZeroizingBuf, os_random_32};
use crate::codec::{Json, to_hex};

fn invalid(msg: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, msg)
}

/// `(st_dev, st_ino)`. Zero off Unix, where no file below can be opened at all.
pub fn file_identity(meta: &Metadata) -> (u64, u64) {
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        (meta.dev(), meta.ino())
    }
    #[cfg(not(unix))]
    {
        let _ = meta;
        (0, 0)
    }
}

/// Canonical `dev_le64 || ino_le64`, the form bound into lock headers and MACs.
pub fn identity_bytes(meta: &Metadata) -> [u8; 16] {
    let (dev, ino) = file_identity(meta);
    let mut out = [0u8; 16];
    out[..8].copy_from_slice(&dev.to_le_bytes());
    out[8..].copy_from_slice(&ino.to_le_bytes());
    out
}

fn owner_only(meta: &Metadata) -> bool {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        meta.permissions().mode() & 0o077 == 0
    }
    #[cfg(not(unix))]
    {
        let _ = meta;
        false
    }
}

/// The directory holding `path`; the working directory for a bare file name.
pub fn parent_dir(path: &Path) -> &Path {
    path.parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or(Path::new("."))
}

/// Flush the directory entry of `path` (a creation, rename or removal) to stable storage.
pub fn sync_parent_dir(path: &Path) -> io::Result<()> {
    File::open(parent_dir(path))?.sync_all()
}

/// Open options that never follow a final symlink and never block on a FIFO.
pub fn no_follow() -> io::Result<OpenOptions> {
    let mut options = OpenOptions::new();
    crate::cli::set_nofollow_nonblocking(&mut options)
        .map_err(|e| io::Error::new(io::ErrorKind::Unsupported, e.message))?;
    Ok(options)
}

fn owner_only_mode(options: &mut OpenOptions) {
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600);
    }
    #[cfg(not(unix))]
    let _ = options;
}

/// `lstat` of a path that must be a regular file if it exists at all.
pub fn regular_metadata(path: &Path) -> io::Result<Option<Metadata>> {
    match std::fs::symlink_metadata(path) {
        Ok(meta) if meta.is_file() => Ok(Some(meta)),
        Ok(_) => Err(invalid("path is not a regular file")),
        Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(None),
        Err(e) => Err(e),
    }
}

/// Check that the open `file` is still the regular file `path` names: `fstat` of the
/// descriptor against `lstat` of the name, never two observations of the name. With
/// `private`, a file that anyone but its owner can access is refused.
pub fn verify_held(file: &File, path: &Path, private: bool) -> io::Result<Metadata> {
    let held = file.metadata()?;
    let named = regular_metadata(path)?.ok_or_else(|| invalid("file vanished from its path"))?;
    if private && !owner_only(&held) {
        return Err(invalid("file permissions exceed 0600"));
    }
    if !held.is_file() || file_identity(&held) != file_identity(&named) {
        return Err(invalid("file inode mismatch"));
    }
    Ok(held)
}

/// A file this process created exclusively and has not yet made durable.
pub struct Created {
    file: File,
    path: PathBuf,
}

/// Create `path`, refusing to replace anything already there. A `private` file is
/// owner-only from the moment it exists.
pub fn create_new(path: &Path, private: bool) -> io::Result<Created> {
    let mut options = no_follow()?;
    options.write(true).create_new(true);
    if private {
        owner_only_mode(&mut options);
    }
    let created = Created {
        file: options.open(path)?,
        path: path.to_owned(),
    };
    if let Err(e) = verify_held(&created.file, path, private) {
        created.discard();
        return Err(e);
    }
    Ok(created)
}

impl Created {
    /// Write the contents, sync the file, then sync its directory entry. A failure removes
    /// the partial file.
    pub fn commit(mut self, write: impl FnOnce(&mut File) -> io::Result<()>) -> io::Result<()> {
        let result = write(&mut self.file)
            .and_then(|()| self.file.sync_all())
            .and_then(|()| sync_parent_dir(&self.path));
        if result.is_err() {
            self.discard();
        }
        result
    }

    /// Remove the file, but only while the name still refers to the inode created here: an
    /// entry that replaced it is never removed.
    fn discard(&self) {
        if let (Ok(held), Ok(named)) = (
            self.file.metadata(),
            std::fs::symlink_metadata(&self.path),
        ) && named.is_file()
            && file_identity(&held) == file_identity(&named)
        {
            let _ = std::fs::remove_file(&self.path);
            let _ = sync_parent_dir(&self.path);
        }
    }
}

const TEMPORARY_NONCE_HEX: usize = 64;
/// Nonce length of the temporaries written by external-anchor records before both writers
/// shared [`replace`]. A leftover of that form is still recognized.
const LEGACY_TEMPORARY_NONCE_HEX: usize = 32;

fn side_path(path: &Path, suffix: &str) -> PathBuf {
    let mut os = path.as_os_str().to_os_string();
    os.push(suffix);
    PathBuf::from(os)
}

/// Durably replace `path` with an owner-only file holding `contents`: write a sibling
/// temporary file, sync it and its directory entry, run `before_rename`, rename it over
/// the original, then sync the directory. Readers see the old file or the new one.
pub fn replace(
    path: &Path,
    contents: &[u8],
    before_rename: impl FnOnce() -> io::Result<()>,
) -> io::Result<()> {
    let nonce = os_random_32().map_err(|e| io::Error::other(e.message))?;
    let tmp = side_path(path, &format!(".{}.tmp", to_hex(&nonce)));
    create_new(&tmp, true)?.commit(|file| file.write_all(contents))?;
    let result = before_rename()
        .and_then(|()| std::fs::rename(&tmp, path))
        .and_then(|()| sync_parent_dir(path));
    if result.is_err() {
        let _ = std::fs::remove_file(&tmp);
    }
    result
}

/// Unlink the temporary files that interrupted [`replace`] calls on `path` left behind.
/// The caller holds the exclusive lock of `path`, so no live writer owns one. Best effort:
/// a leftover is inert.
pub fn remove_interrupted_replacements(path: &Path) {
    let (Some(dir), Some(name)) = (path.parent(), path.file_name().and_then(|n| n.to_str()))
    else {
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
            .is_some_and(|hex| {
                matches!(hex.len(), TEMPORARY_NONCE_HEX | LEGACY_TEMPORARY_NONCE_HEX)
                    && hex.bytes().all(|b| b.is_ascii_hexdigit())
            });
        if stale && entry.file_type().is_ok_and(|t| t.is_file()) {
            let _ = std::fs::remove_file(entry.path());
        }
    }
}

/// Open the owner-only lock file at `path` and take its exclusive OS lock, waiting up to
/// five seconds for another holder. With `create` the file must not exist yet; otherwise
/// it must. Independently opened descriptors contend on the same inode lock, including
/// threads and path aliases.
///
/// `NotFound` means the lock file is missing, `WouldBlock` that another holder kept it,
/// and `InvalidData` that the name does not refer to the private regular file that was
/// locked. The caller writes and syncs whatever a fresh lock file must contain.
pub fn acquire_lock(path: &Path, create: bool) -> io::Result<(File, Metadata)> {
    let before = regular_metadata(path)?;
    if !create && before.is_none() {
        return Err(io::Error::new(
            io::ErrorKind::NotFound,
            "lock file is missing",
        ));
    }
    let mut options = no_follow()?;
    options.read(true).write(true).create_new(create);
    owner_only_mode(&mut options);
    let file = options.open(path)?;
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(5);
    loop {
        match file.try_lock() {
            Ok(()) => break,
            Err(std::fs::TryLockError::WouldBlock) if std::time::Instant::now() < deadline => {
                std::thread::sleep(std::time::Duration::from_millis(10));
            }
            Err(_) => {
                return Err(io::Error::new(
                    io::ErrorKind::WouldBlock,
                    "lock unavailable",
                ));
            }
        }
    }
    let held = verify_held(&file, path, true)?;
    if before.is_some_and(|seen| file_identity(&seen) != file_identity(&held)) {
        return Err(invalid("lock file was replaced while it was opened"));
    }
    Ok((file, held))
}

/// A directory holding custody state: owner-only, never a symlink. With `create`, missing
/// components are made with mode 0700. A directory that already exists is accepted only if
/// no other user can enter it; its permissions are never changed here. Returns the
/// `(device, inode)` of the directory that was opened and checked.
pub fn private_dir(path: &str, create: bool) -> Result<(u64, u64), CliError> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::DirBuilderExt;
        if create {
            std::fs::DirBuilder::new()
                .recursive(true)
                .mode(0o700)
                .create(path)
                .map_err(|e| CliError::io(format_args!("creating {path}"), e))?;
        }
        let refused = || {
            CliError::state(format!(
                "{path} must be a directory only its owner can access (mode 0700), not a symlink"
            ))
        };
        let named = std::fs::symlink_metadata(path)
            .map_err(|e| CliError::io(format_args!("inspecting {path}"), e))?;
        if !named.is_dir() || !owner_only(&named) {
            return Err(refused());
        }
        // The descriptor, not a second look at the name, is what the identity is taken from.
        let held = no_follow()
            .and_then(|mut options| options.read(true).open(path))
            .and_then(|dir| dir.metadata())
            .map_err(|e| CliError::io(format_args!("opening directory {path}"), e))?;
        if !held.is_dir() || !owner_only(&held) || file_identity(&named) != file_identity(&held) {
            return Err(refused());
        }
        Ok(file_identity(&held))
    }
    #[cfg(not(unix))]
    {
        let _ = create;
        Err(CliError::state(format!(
            "{path}: owner-only directories require Unix permissions"
        )))
    }
}

/// The bytes a JSON header is authenticated over: its canonical rendering without the
/// `excluded` top-level fields (the MAC itself and whatever may change beneath it).
pub fn authenticated_bytes(json: &Json, excluded: &[&str]) -> ZeroizingBuf {
    let mut covered = json.clone();
    if let Json::Object(fields) = &mut covered {
        fields.retain(|(name, _)| !excluded.contains(&name.as_str()));
    }
    ZeroizingBuf(covered.to_pretty().into_bytes())
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;
    use std::os::unix::fs::PermissionsExt;

    fn temp_dir(label: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "qsag-persist-{label}-{}",
            to_hex(&os_random_32().unwrap()[..16])
        ));
        private_dir(dir.to_str().unwrap(), true).unwrap();
        dir
    }

    fn names(dir: &Path) -> Vec<String> {
        let mut names: Vec<String> = std::fs::read_dir(dir)
            .unwrap()
            .map(|e| e.unwrap().file_name().into_string().unwrap())
            .collect();
        names.sort();
        names
    }

    #[test]
    fn replace_is_exclusive_private_and_leaves_no_temporary() {
        let dir = temp_dir("replace");
        let path = dir.join("record");
        // A public file is replaced by an owner-only one with exactly the new bytes.
        create_new(&path, false)
            .unwrap()
            .commit(|f| f.write_all(b"old"))
            .unwrap();
        assert!(create_new(&path, false).is_err());
        replace(&path, b"new contents", || Ok(())).unwrap();
        assert_eq!(std::fs::read(&path).unwrap(), b"new contents");
        let mode = std::fs::metadata(&path).unwrap().permissions().mode();
        assert_eq!(mode & 0o777, 0o600);
        assert_eq!(names(&dir), ["record"]);

        // A refusal before the rename keeps the old file and removes the temporary.
        let refused = replace(&path, b"never", || Err(io::Error::other("refused")));
        assert!(refused.is_err());
        assert_eq!(std::fs::read(&path).unwrap(), b"new contents");
        assert_eq!(names(&dir), ["record"]);

        // Leftovers of both temporary name forms are removed; other files are kept.
        let long = side_path(&path, &format!(".{}.tmp", "ab".repeat(32)));
        let legacy = side_path(&path, &format!(".{}.tmp", "cd".repeat(16)));
        let unrelated = side_path(&path, ".note.tmp");
        for leftover in [&long, &legacy, &unrelated] {
            std::fs::write(leftover, b"half").unwrap();
        }
        remove_interrupted_replacements(&path);
        assert_eq!(names(&dir), ["record", "record.note.tmp"]);
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn lock_is_exclusive_private_and_bound_to_its_inode() {
        let dir = temp_dir("lock");
        let path = dir.join("state.lock");
        assert_eq!(
            acquire_lock(&path, false).unwrap_err().kind(),
            io::ErrorKind::NotFound
        );
        let (held, meta) = acquire_lock(&path, true).unwrap();
        assert_eq!(meta.permissions().mode() & 0o777, 0o600);
        assert_eq!(
            acquire_lock(&path, true).unwrap_err().kind(),
            io::ErrorKind::AlreadyExists
        );
        verify_held(&held, &path, true).unwrap();
        drop(held);

        // A lock file anyone else can read, a symlink to one, and a replaced inode are refused.
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o640)).unwrap();
        assert_eq!(
            acquire_lock(&path, false).unwrap_err().kind(),
            io::ErrorKind::InvalidData
        );
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o600)).unwrap();
        let (held, _) = acquire_lock(&path, false).unwrap();
        let aside = dir.join("aside");
        std::fs::rename(&path, &aside).unwrap();
        assert!(verify_held(&held, &path, true).is_err());
        std::os::unix::fs::symlink(&aside, &path).unwrap();
        assert!(verify_held(&held, &path, true).is_err());
        drop(held);
        assert!(acquire_lock(&path, false).is_err());
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn private_dir_refuses_shared_and_symlinked_directories() {
        let dir = temp_dir("dir");
        let inner = dir.join("a").join("b");
        let id = private_dir(inner.to_str().unwrap(), true).unwrap();
        assert_eq!(id, file_identity(&std::fs::metadata(&inner).unwrap()));
        assert_eq!(private_dir(inner.to_str().unwrap(), false).unwrap(), id);
        let link = dir.join("link");
        std::os::unix::fs::symlink(&inner, &link).unwrap();
        assert!(private_dir(link.to_str().unwrap(), false).is_err());
        std::fs::set_permissions(&inner, std::fs::Permissions::from_mode(0o750)).unwrap();
        assert!(private_dir(inner.to_str().unwrap(), false).is_err());
        assert!(private_dir(dir.join("absent").to_str().unwrap(), false).is_err());
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn authenticated_bytes_drop_only_the_named_top_level_fields() {
        let json = Json::object(vec![
            ("scheme", Json::str("test")),
            ("state_mac", Json::hex(&[1u8; 4])),
            ("nested", Json::object(vec![("state_mac", Json::num(7u64))])),
        ]);
        let expected = Json::object(vec![
            ("scheme", Json::str("test")),
            ("nested", Json::object(vec![("state_mac", Json::num(7u64))])),
        ]);
        assert_eq!(
            authenticated_bytes(&json, &["state_mac"]).0,
            expected.to_pretty().into_bytes()
        );
        assert_eq!(
            authenticated_bytes(&json, &[]).0,
            json.to_pretty().into_bytes()
        );
    }
}
