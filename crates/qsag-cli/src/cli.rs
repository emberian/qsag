//! Argument parsing, error type, exit codes, and file helpers.

use std::collections::BTreeMap;
use std::fmt;
use std::io::{Read, Write};
use std::path::Path;

/// Process exit codes. They are part of the command-line contract.
pub mod exit {
    pub const OK: u8 = 0;
    /// Bad command line, malformed input file, or unsupported scheme.
    pub const USAGE: u8 = 1;
    /// A signature, proof, address, or known-answer test failed to verify.
    pub const VERIFY_FAILED: u8 = 2;
    /// A transaction policy refused the request.
    pub const POLICY_DENIED: u8 = 3;
    /// A stateful key refused to sign: budget exhausted, epoch reused, or journal conflict.
    pub const STATE_CONFLICT: u8 = 4;
    /// File system or entropy source failure.
    pub const IO: u8 = 5;
}

#[derive(Debug)]
pub struct CliError {
    pub code: u8,
    pub message: String,
}

impl CliError {
    pub fn new(code: u8, message: impl Into<String>) -> Self {
        Self {
            code,
            message: message.into(),
        }
    }
    pub fn usage(message: impl Into<String>) -> Self {
        Self::new(exit::USAGE, message)
    }
    pub fn input(message: impl Into<String>) -> Self {
        Self::new(exit::USAGE, message)
    }
    pub fn verify(message: impl Into<String>) -> Self {
        Self::new(exit::VERIFY_FAILED, message)
    }
    pub fn state(message: impl Into<String>) -> Self {
        Self::new(exit::STATE_CONFLICT, message)
    }
    pub fn io(what: impl fmt::Display, err: std::io::Error) -> Self {
        Self::new(exit::IO, format!("{what}: {err}"))
    }
}

impl fmt::Display for CliError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for CliError {}

/// Parsed `--name value` options, bare `--flag`s, and positional arguments of one subcommand.
pub struct Args {
    options: BTreeMap<String, String>,
    flags: Vec<String>,
    pub positional: Vec<String>,
}

impl Args {
    /// `value_options` take one value; `flag_options` take none. Anything else is an error,
    /// as is repeating an option.
    pub fn parse(
        raw: &[String],
        value_options: &[&str],
        flag_options: &[&str],
    ) -> Result<Self, CliError> {
        let mut args = Self {
            options: BTreeMap::new(),
            flags: Vec::new(),
            positional: Vec::new(),
        };
        let mut iter = raw.iter();
        while let Some(arg) = iter.next() {
            let Some(name) = arg.strip_prefix("--") else {
                args.positional.push(arg.clone());
                continue;
            };
            let (name, inline) = match name.split_once('=') {
                Some((name, value)) => (name, Some(value.to_string())),
                None => (name, None),
            };
            if flag_options.contains(&name) {
                if inline.is_some() {
                    return Err(CliError::usage(format!("--{name} does not take a value")));
                }
                if !args.flags.iter().any(|f| f == name) {
                    args.flags.push(name.to_string());
                }
            } else if value_options.contains(&name) {
                let value = match inline {
                    Some(value) => value,
                    None => iter
                        .next()
                        .cloned()
                        .ok_or_else(|| CliError::usage(format!("--{name} requires a value")))?,
                };
                if args.options.insert(name.to_string(), value).is_some() {
                    return Err(CliError::usage(format!("--{name} given more than once")));
                }
            } else {
                return Err(CliError::usage(format!(
                    "unknown option --{name} (try --help)"
                )));
            }
        }
        Ok(args)
    }

    pub fn flag(&self, name: &str) -> bool {
        self.flags.iter().any(|f| f == name)
    }
    pub fn get(&self, name: &str) -> Option<&str> {
        self.options.get(name).map(String::as_str)
    }
    pub fn require(&self, name: &str) -> Result<&str, CliError> {
        self.get(name)
            .ok_or_else(|| CliError::usage(format!("missing required option --{name}")))
    }
    pub fn get_u64(&self, name: &str) -> Result<Option<u64>, CliError> {
        self.get(name)
            .map(|v| {
                v.parse().map_err(|_| {
                    CliError::usage(format!("--{name} must be a non-negative integer"))
                })
            })
            .transpose()
    }
    pub fn no_positionals(&self) -> Result<(), CliError> {
        match self.positional.first() {
            Some(extra) => Err(CliError::usage(format!("unexpected argument '{extra}'"))),
            None => Ok(()),
        }
    }
}

pub const MAX_KEY_FILE_BYTES: u64 = 1024 * 1024;
pub const MAX_SIG_PROOF_BYTES: u64 = 64 * 1024 * 1024;
pub const MAX_MSG_BYTES: u64 = 64 * 1024 * 1024;

#[cfg(test)]
std::thread_local! {
    // Observe bytes only after wiping and before deallocation; never inspect freed memory.
    static WIPED_BUFFERS: std::cell::RefCell<Option<Vec<(usize, bool)>>> = const { std::cell::RefCell::new(None) };
}

pub struct ZeroizingBuf(pub Vec<u8>);
impl std::ops::Deref for ZeroizingBuf {
    type Target = [u8];
    fn deref(&self) -> &[u8] {
        &self.0
    }
}
impl Drop for ZeroizingBuf {
    fn drop(&mut self) {
        let cap = self.0.capacity();
        if cap > self.0.len() {
            self.0.resize(cap, 0);
        }
        qsag_accel::ct::ct_zeroize_bytes(&mut self.0);
        #[cfg(test)]
        WIPED_BUFFERS.with(|events| {
            if let Some(events) = &mut *events.borrow_mut() {
                events.push((cap, self.0.iter().all(|byte| *byte == 0)));
            }
        });
        self.0.clear();
    }
}

pub struct Secret32(pub [u8; 32]);
impl std::ops::Deref for Secret32 {
    type Target = [u8; 32];
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl Drop for Secret32 {
    fn drop(&mut self) {
        qsag_accel::ct::ct_zeroize_bytes(&mut self.0);
    }
}

fn append_zeroizing(buf: &mut Vec<u8>, chunk: &[u8]) {
    if buf.len() + chunk.len() > buf.capacity() {
        let next_cap = buf
            .capacity()
            .max(64)
            .saturating_mul(2)
            .max(buf.len().saturating_add(chunk.len()));
        let mut next = Vec::with_capacity(next_cap);
        next.extend_from_slice(buf);
        // Reuse the drop guard so reallocation and error cleanup share one wipe.
        drop(ZeroizingBuf(std::mem::replace(buf, next)));
    }
    buf.extend_from_slice(chunk);
}

fn read_limited_with_hint(
    mut reader: impl Read,
    max: u64,
    cap_hint: usize,
) -> Result<ZeroizingBuf, CliError> {
    let bounded_hint = cap_hint.min(usize::try_from(max).unwrap_or(usize::MAX).saturating_add(1));
    let mut data = ZeroizingBuf(Vec::with_capacity(bounded_hint));
    let mut chunk = [0u8; 4096];
    let limit = max.saturating_add(1);
    let mut total = 0u64;
    loop {
        let to_read = chunk.len().min((limit - total) as usize);
        if to_read == 0 {
            break;
        }
        let n = match reader.read(&mut chunk[..to_read]) {
            Ok(0) => break,
            Ok(n) => n,
            Err(e) if e.kind() == std::io::ErrorKind::Interrupted => continue,
            Err(e) => {
                qsag_accel::ct::ct_zeroize_bytes(&mut chunk);
                return Err(CliError::io("reading bounded input", e));
            }
        };
        append_zeroizing(&mut data.0, &chunk[..n]);
        total += n as u64;
        if total > max {
            qsag_accel::ct::ct_zeroize_bytes(&mut chunk);
            return Err(CliError::input("input exceeds size limit"));
        }
    }
    qsag_accel::ct::ct_zeroize_bytes(&mut chunk);
    Ok(data)
}

fn read_limited(reader: impl Read, max: u64) -> Result<ZeroizingBuf, CliError> {
    read_limited_with_hint(reader, max, 256)
}

// Linux UAPI values differ by architecture. Keep the table testable on any host.
fn linux_open_flags(arch: &str) -> Option<i32> {
    let nofollow = match arch {
        "aarch64" | "arm" => 0x8000,
        "powerpc" | "powerpc64" => 0x10000,
        "m68k" => 0x4000,
        "x86_64" | "x86" | "riscv64" | "riscv32" => 0x20000,
        _ => return None,
    };
    Some(nofollow | 0x800)
}

pub fn set_nofollow_nonblocking(opts: &mut std::fs::OpenOptions) -> Result<(), CliError> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        let flags = match std::env::consts::OS {
            "linux" => linux_open_flags(std::env::consts::ARCH),
            "macos" => Some(0x100 | 0x4),
            _ => None,
        }
        .ok_or_else(|| CliError::state("unsupported no-follow file flags"))?;
        opts.custom_flags(flags);
        Ok(())
    }
    #[cfg(not(unix))]
    {
        let _ = opts;
        Err(CliError::state("no-follow file access requires Unix"))
    }
}

fn open_nonblocking_regular(path: &str) -> Result<std::fs::File, CliError> {
    let mut opts = std::fs::OpenOptions::new();
    opts.read(true);
    set_nofollow_nonblocking(&mut opts)?;
    opts.open(path)
        .map_err(|e| CliError::io("opening input", e))
}

pub fn read_bounded_file(path: &str, max_bytes: u64) -> Result<ZeroizingBuf, CliError> {
    let file = open_nonblocking_regular(path)?;
    let meta = file
        .metadata()
        .map_err(|e| CliError::io("inspecting input", e))?;
    if !meta.is_file() || meta.len() > max_bytes {
        return Err(CliError::input(
            "input is not a regular file within size limit",
        ));
    }
    let hint = usize::try_from(meta.len()).unwrap_or(0).saturating_add(1);
    read_limited_with_hint(file, max_bytes, hint)
}

/// Read a bounded message, including standard input.
pub fn read_input(path: &str) -> Result<ZeroizingBuf, CliError> {
    if path == "-" {
        read_limited(std::io::stdin(), MAX_MSG_BYTES)
    } else {
        read_bounded_file(path, MAX_MSG_BYTES)
    }
}

pub struct ZeroizingText(ZeroizingBuf);
impl std::ops::Deref for ZeroizingText {
    type Target = str;
    fn deref(&self) -> &str {
        // Construction validates UTF-8; the buffer is never exposed mutably.
        std::str::from_utf8(&self.0).expect("validated UTF-8")
    }
}

pub fn read_text(path: &str) -> Result<ZeroizingText, CliError> {
    let bytes = read_bounded_file(path, MAX_KEY_FILE_BYTES)?;
    std::str::from_utf8(&bytes.0)
        .map_err(|_| CliError::input(format!("{path} is not UTF-8 text")))?;
    Ok(ZeroizingText(bytes))
}

pub fn sync_parent(path: &str) -> Result<(), CliError> {
    let parent = Path::new(path)
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    std::fs::File::open(parent)
        .and_then(|dir| dir.sync_all())
        .map_err(|e| CliError::io("syncing parent directory", e))
}

/// A directory holding custody state: owner-only, never a symlink. With `create`, missing
/// components are made with mode 0700. A directory that already exists is accepted only if
/// no other user can enter it; its permissions are never changed here.
pub fn private_dir(path: &str, create: bool) -> Result<(), CliError> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::{DirBuilderExt, PermissionsExt};
        if create {
            std::fs::DirBuilder::new()
                .recursive(true)
                .mode(0o700)
                .create(path)
                .map_err(|e| CliError::io(format_args!("creating {path}"), e))?;
        }
        let meta = std::fs::symlink_metadata(path)
            .map_err(|e| CliError::io(format_args!("inspecting {path}"), e))?;
        if !meta.is_dir() || meta.permissions().mode() & 0o077 != 0 {
            return Err(CliError::state(format!(
                "{path} must be a directory only its owner can access (mode 0700), not a symlink"
            )));
        }
        Ok(())
    }
    #[cfg(not(unix))]
    {
        let _ = create;
        Err(CliError::state(format!(
            "{path}: owner-only directories require Unix permissions"
        )))
    }
}

/// Create a new file and refuse to overwrite an existing one. Secret files are created with
/// owner-only permissions.
pub fn write_new(path: &str, contents: &[u8], secret: bool) -> Result<(), CliError> {
    let mut options = std::fs::OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    if secret {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600);
    }
    #[cfg(not(unix))]
    let _ = secret;
    let mut file = options
        .open(path)
        .map_err(|e| CliError::io(format_args!("creating {path}"), e))?;
    file.write_all(contents)
        .and_then(|()| file.sync_all())
        .map_err(|e| CliError::io(format_args!("writing {path}"), e))?;
    sync_parent(path)
}

/// Durably replace an existing owner-only file: write a sibling temporary file, sync it,
/// rename it over the original, then sync the directory.
pub fn replace_secret(path: &str, contents: &[u8]) -> Result<(), CliError> {
    let tmp = format!("{path}.{}.tmp", crate::codec::to_hex(&os_random_32()?));
    let result = (|| {
        write_new(&tmp, contents, true)?;
        std::fs::rename(&tmp, path)
            .map_err(|e| CliError::io(format_args!("replacing {path}"), e))?;
        sync_parent(path)
    })();
    if result.is_err() {
        let _ = std::fs::remove_file(&tmp);
    }
    result
}

/// 32 bytes from the operating system's entropy device.
pub fn os_random_32() -> Result<[u8; 32], CliError> {
    let mut out = Secret32([0u8; 32]);
    std::fs::File::open("/dev/urandom")
        .and_then(|mut f| f.read_exact(&mut out.0))
        .map_err(|e| {
            CliError::io(
                "reading /dev/urandom (pass --seed-file on platforms without it)",
                e,
            )
        })?;
    Ok(out.0)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn strings(items: &[&str]) -> Vec<String> {
        items.iter().map(|s| s.to_string()).collect()
    }

    #[cfg(unix)]
    #[test]
    fn private_dir_is_owner_only_and_refuses_shared_or_linked_directories() {
        use std::os::unix::fs::PermissionsExt;
        let root = std::env::temp_dir().join(format!(
            "qsag-private-dir-{}",
            crate::codec::to_hex(&os_random_32().unwrap())
        ));
        let path = |name: &str| root.join(name).to_str().unwrap().to_owned();
        let mode = |name: &str| {
            std::fs::symlink_metadata(path(name))
                .unwrap()
                .permissions()
                .mode()
                & 0o777
        };
        // Missing ancestors are created private too.
        private_dir(&path("a/b"), true).unwrap();
        assert_eq!(mode("a"), 0o700);
        assert_eq!(mode("a/b"), 0o700);
        assert_eq!(
            std::fs::symlink_metadata(&root)
                .unwrap()
                .permissions()
                .mode()
                & 0o777,
            0o700
        );
        // Idempotent on a directory that is already private.
        private_dir(&path("a/b"), true).unwrap();
        private_dir(&path("a/b"), false).unwrap();
        // Absent without `create`.
        assert!(private_dir(&path("absent"), false).is_err());
        // An existing shared directory is refused and left as it was.
        std::fs::create_dir(path("shared")).unwrap();
        for shared in [0o755, 0o750, 0o701] {
            std::fs::set_permissions(path("shared"), std::fs::Permissions::from_mode(shared))
                .unwrap();
            assert!(private_dir(&path("shared"), true).is_err());
            assert!(private_dir(&path("shared"), false).is_err());
            assert_eq!(mode("shared"), shared);
        }
        // A symlink to a private directory, and a regular file.
        std::os::unix::fs::symlink(path("a"), path("link")).unwrap();
        assert!(private_dir(&path("link"), true).is_err());
        std::fs::write(path("file"), b"").unwrap();
        assert!(private_dir(&path("file"), true).is_err());
        std::fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn failed_replace_removes_temporary_file() {
        let dir = std::env::temp_dir().join(format!(
            "qsag-replace-{}",
            crate::codec::to_hex(&os_random_32().unwrap())
        ));
        std::fs::create_dir(&dir).unwrap();
        let destination = dir.join("directory");
        std::fs::create_dir(&destination).unwrap();
        assert!(replace_secret(destination.to_str().unwrap(), b"secret").is_err());
        assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 1);
        std::fs::remove_dir_all(dir).unwrap();
    }
    #[test]
    fn parses_options_flags_and_positionals() {
        let args = Args::parse(
            &strings(&["--out", "a", "--json", "pos", "--in=b"]),
            &["out", "in"],
            &["json"],
        )
        .unwrap();
        assert_eq!(args.get("out"), Some("a"));
        assert_eq!(args.get("in"), Some("b"));
        assert!(args.flag("json"));
        assert_eq!(args.positional, strings(&["pos"]));
        assert!(args.no_positionals().is_err());
    }

    #[test]
    fn rejects_unknown_repeated_and_incomplete_options() {
        for bad in [
            &["--nope"][..],
            &["--out"],
            &["--out", "a", "--out", "b"],
            &["--json=1"],
        ] {
            let err = Args::parse(&strings(bad), &["out"], &["json"])
                .err()
                .expect("must be rejected");
            assert_eq!(err.code, exit::USAGE);
        }
        let args = Args::parse(&strings(&["--n", "x"]), &["n"], &[]).unwrap();
        assert!(args.get_u64("n").is_err());
        assert!(args.require("missing").is_err());
    }
}

#[cfg(test)]
mod custody_buffer_tests {
    use super::*;

    #[test]
    fn linux_nofollow_architecture_constants() {
        for arch in ["arm", "aarch64"] {
            assert_eq!(linux_open_flags(arch), Some(0x8800));
        }
        for arch in ["powerpc", "powerpc64"] {
            assert_eq!(linux_open_flags(arch), Some(0x10800));
        }
        assert_eq!(linux_open_flags("m68k"), Some(0x4800));
        for arch in ["x86", "x86_64", "riscv32", "riscv64"] {
            assert_eq!(linux_open_flags(arch), Some(0x20800));
        }
        assert_eq!(linux_open_flags("unknown"), None);
    }

    #[test]
    fn secret_buffers_wipe_on_growth_drop_and_error() {
        WIPED_BUFFERS.with(|events| *events.borrow_mut() = Some(Vec::new()));
        let mut bytes = ZeroizingBuf(vec![0xAB; 17]);
        let old_capacity = bytes.0.capacity();
        append_zeroizing(&mut bytes.0, &[0xCD; 256]);
        assert_eq!(&bytes[..17], &[0xAB; 17]);
        assert_eq!(&bytes[17..], &[0xCD; 256]);
        drop(bytes);
        // Exercise decrypted JSON ownership, its clone used by vault MACs, and
        // early-return unwinding while the plaintext strings are still live.
        fn fail_with_plaintext() -> Result<(), CliError> {
            let key =
                crate::codec::Json::object(vec![("seed", crate::codec::Json::hex(&[0x42; 32]))]);
            let opened = crate::envelope::open(&key, None)?;
            let _unsigned = opened.clone();
            let _encoded = ZeroizingBuf(opened.to_pretty().into_bytes());
            Err(CliError::input("injected error"))?;
            Ok(())
        }
        assert!(fail_with_plaintext().is_err());
        let events = WIPED_BUFFERS.with(|events| events.borrow_mut().take().unwrap());
        assert_eq!(events[0], (old_capacity, true));
        assert!(events.iter().all(|(_, wiped)| *wiped));
        // Original, decrypted, and cloned hex strings each reach the drop guard.
        assert_eq!(events.iter().filter(|(cap, _)| *cap == 64).count(), 3);
    }

    #[test]
    fn input_helpers_keep_zeroizing_ownership() {
        // These signatures prevent accidentally returning an unguarded copy again.
        let _: fn(&str) -> Result<ZeroizingBuf, CliError> = read_input;
        let _: fn(&str) -> Result<ZeroizingText, CliError> = read_text;
        assert!(std::mem::needs_drop::<ZeroizingText>());
        let text = ZeroizingText(ZeroizingBuf(b"secret text".to_vec()));
        assert_eq!(&*text, "secret text");
    }
}
