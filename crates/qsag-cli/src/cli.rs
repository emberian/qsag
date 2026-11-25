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

fn wipe_text(text: &mut String) {
    drop(ZeroizingBuf::new(std::mem::take(text).into_bytes()));
}

impl Drop for Args {
    fn drop(&mut self) {
        for value in self
            .options
            .values_mut()
            .chain(&mut self.positional)
            .chain(&mut self.flags)
        {
            wipe_text(value);
        }
    }
}

/// Own command-line copies through parsing failures and command completion.
pub(crate) struct SecretArgs(pub Vec<String>);
impl Drop for SecretArgs {
    fn drop(&mut self) {
        for value in &mut self.0 {
            wipe_text(value);
        }
    }
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
                Some((name, value)) => (name, Some(value)),
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
                if args.options.contains_key(name) {
                    return Err(CliError::usage(format!("--{name} given more than once")));
                }
                let value = match inline {
                    Some(value) => value.to_owned(),
                    None => iter
                        .next()
                        .cloned()
                        .ok_or_else(|| CliError::usage(format!("--{name} requires a value")))?,
                };
                args.options.insert(name.to_string(), value);
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
    pub fn get_u128(&self, name: &str) -> Result<Option<u128>, CliError> {
        self.get(name)
            .map(|v| {
                v.parse().map_err(|_| {
                    CliError::usage(format!("--{name} must be a non-negative u128 integer"))
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

pub type ZeroizingBuf = qsag_core::wipe::SecretVec<u8>;
pub type Secret32 = qsag_core::wipe::SecretBytes<32>;

fn append_zeroizing(buf: &mut Vec<u8>, chunk: &[u8]) {
    qsag_core::wipe::secret_vec_extend_from_slice(buf, chunk);
}

fn read_limited_with_hint(
    mut reader: impl Read,
    max: u64,
    cap_hint: usize,
) -> Result<ZeroizingBuf, CliError> {
    let bounded_hint = cap_hint.min(usize::try_from(max).unwrap_or(usize::MAX).saturating_add(1));
    let mut data = ZeroizingBuf::new(Vec::with_capacity(bounded_hint));
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

pub fn set_nofollow_nonblocking(opts: &mut std::fs::OpenOptions) -> Result<(), CliError> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        let flags = qsag_asm::durable::open_nofollow_nonblock_flags(
            std::env::consts::OS,
            std::env::consts::ARCH,
        )
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
    crate::persist::sync_parent_dir(Path::new(path))
        .map_err(|e| CliError::io("syncing parent directory", e))
}

/// A directory holding custody state: owner-only, never a symlink. See
/// [`crate::persist::private_dir`].
pub fn private_dir(path: &str, create: bool) -> Result<(), CliError> {
    crate::persist::private_dir(path, create).map(|_| ())
}

pub const SINGLE_HOST_CUSTODY: &str = "single-host local ceremony (all shares in one process)";

/// Reserve the exclusive destination before spending a one-time key.
pub fn reserve_output(path: &str, private: bool) -> Result<crate::persist::Created, CliError> {
    crate::persist::create_new(Path::new(path), private)
        .map_err(|e| CliError::io(format_args!("creating {path}"), e))
}

pub fn finish_output(file: crate::persist::Created, bytes: &[u8]) -> Result<(), CliError> {
    file.commit(|f| f.write_all(bytes))
        .map_err(|e| CliError::io("writing output", e))
}

/// Create a new file and refuse to overwrite an existing one. Secret files are created with
/// owner-only permissions.
pub fn write_new(path: &str, contents: &[u8], secret: bool) -> Result<(), CliError> {
    write_new_with(path, secret, |file| file.write_all(contents))
}

fn write_new_with(
    path: &str,
    secret: bool,
    write: impl FnOnce(&mut std::fs::File) -> std::io::Result<()>,
) -> Result<(), CliError> {
    crate::persist::create_new(Path::new(path), secret)
        .map_err(|e| CliError::io(format_args!("creating {path}"), e))?
        .commit(write)
        .map_err(|e| CliError::io(format_args!("writing {path}"), e))
}

/// Durably replace an existing owner-only file: write a sibling temporary file, sync it,
/// rename it over the original, then sync the directory.
pub fn replace_secret(path: &str, contents: &[u8]) -> Result<(), CliError> {
    crate::persist::replace(Path::new(path), contents, || Ok(()))
        .map_err(|e| CliError::io(format_args!("replacing {path}"), e))
}

/// 32 bytes from the operating system's entropy device.
pub fn os_random_32() -> Result<[u8; 32], CliError> {
    let mut out = Secret32::new([0u8; 32]);
    qsag_asm::fill_os_random(&mut out.0).map_err(|e| CliError::io("reading OS entropy", e))?;
    Ok(out.0)
}

#[cfg(test)]
mod tests {
    #[cfg(unix)]
    #[test]
    fn failed_partial_write_removes_only_its_own_file() {
        use std::io::Write;
        let path = std::env::temp_dir().join(format!(
            "partial-file-{}",
            crate::codec::to_hex(&super::os_random_32().unwrap())
        ));
        let path = path.to_str().unwrap();
        let result = super::write_new_with(path, true, |file| {
            file.write_all(b"partial secret")?;
            Err(std::io::Error::other("injected short write"))
        });
        assert!(result.is_err());
        assert!(!std::path::Path::new(path).exists());
        super::write_new(path, b"existing", true).unwrap();
        assert!(super::write_new(path, b"new", true).is_err());
        assert_eq!(std::fs::read(path).unwrap(), b"existing");
        std::fs::remove_file(path).unwrap();
    }
    #[test]
    fn malformed_and_duplicate_secret_arguments_are_rejected() {
        for items in [
            vec!["--seed", "private", "--seed=duplicate"],
            vec!["--seed", "private", "--bad=secret"],
        ] {
            let raw = SecretArgs(strings(&items));
            assert!(Args::parse(&raw.0, &["seed"], &[]).is_err());
            drop(raw);
        }
    }

    #[cfg(unix)]
    #[test]
    fn secret_file_creation_and_replacement_keep_owner_only_permissions() {
        use std::os::unix::fs::{PermissionsExt, symlink};
        let root = std::env::temp_dir().join(format!(
            "private-file-{}",
            crate::codec::to_hex(&os_random_32().unwrap())
        ));
        std::fs::create_dir(&root).unwrap();
        let path = root.join("key");
        let path = path.to_str().unwrap();
        write_new(path, b"first", true).unwrap();
        assert_eq!(
            std::fs::metadata(path).unwrap().permissions().mode() & 0o777,
            0o600
        );
        replace_secret(path, b"second").unwrap();
        assert_eq!(
            std::fs::metadata(path).unwrap().permissions().mode() & 0o777,
            0o600
        );
        let link = root.join("link");
        symlink(path, &link).unwrap();
        assert!(write_new(link.to_str().unwrap(), b"overwrite", true).is_err());
        assert!(read_bounded_file(link.to_str().unwrap(), 100).is_err());
        assert_eq!(std::fs::read(path).unwrap(), b"second");
        std::fs::remove_dir_all(root).unwrap();
    }
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
        use qsag_asm::durable::open_nofollow_nonblock_flags;
        for arch in ["arm", "aarch64", "powerpc", "powerpc64"] {
            assert_eq!(open_nofollow_nonblock_flags("linux", arch), Some(0x8800));
        }
        assert_eq!(
            open_nofollow_nonblock_flags("linux", "mips64"),
            Some(0x20080)
        );
        assert_eq!(
            open_nofollow_nonblock_flags("linux", "sparc64"),
            Some(0x24000)
        );
        assert_eq!(open_nofollow_nonblock_flags("linux", "m68k"), None);
        for arch in [
            "x86",
            "x86_64",
            "riscv32",
            "riscv64",
            "s390x",
            "loongarch64",
        ] {
            assert_eq!(open_nofollow_nonblock_flags("linux", arch), Some(0x20800));
        }
        assert_eq!(
            open_nofollow_nonblock_flags("macos", "aarch64"),
            Some(0x104)
        );
        assert_eq!(open_nofollow_nonblock_flags("linux", "unknown"), None);
    }

    #[test]
    fn canonical_buffers_preserve_data_during_growth_and_error() {
        let mut bytes = ZeroizingBuf::new(vec![0xAB; 17]);
        let _: &qsag_core::wipe::SecretVec<u8> = &bytes;
        assert_eq!(format!("{bytes:?}"), "SecretBuffer([REDACTED])");
        assert_eq!(
            format!("{:?}", Secret32::new([7; 32])),
            "SecretBuffer([REDACTED])"
        );
        append_zeroizing(&mut bytes.0, &[0xCD; 256]);
        assert_eq!(&bytes[..17], &[0xAB; 17]);
        assert_eq!(&bytes[17..], &[0xCD; 256]);
        drop(bytes);
        // Exercise the key file's hex string, the opened plaintext, the vault MAC key
        // material derived from it, and early-return unwinding while all three are live.
        fn fail_with_plaintext() -> Result<(), CliError> {
            let key =
                crate::codec::Json::object(vec![("seed", crate::codec::Json::hex(&[0x42; 32]))]);
            let opened = crate::envelope::open(&key, None)?;
            let _material = opened.vault_key_material();
            let _encoded = ZeroizingBuf::new(key.to_pretty().into_bytes());
            Err(CliError::input("injected error"))?;
            Ok(())
        }
        assert!(fail_with_plaintext().is_err());
    }

    #[test]
    fn opened_envelope_uses_canonical_secret_owner() {
        let mut key = crate::codec::Json::object(vec![
            ("scheme", crate::codec::Json::str("test")),
            ("secret_key", crate::codec::Json::hex(&[0x42; 48])),
        ]);
        crate::envelope::seal(&mut key, b"correct horse").unwrap();
        let opened = crate::envelope::open(&key, Some(b"correct horse")).unwrap();
        assert_eq!(opened.secret_key().unwrap(), &[0x42u8; 48][..]);
        drop(opened);
    }

    #[test]
    fn input_helpers_keep_zeroizing_ownership() {
        // These signatures prevent accidentally returning an unguarded copy again.
        let _: fn(&str) -> Result<ZeroizingBuf, CliError> = read_input;
        let _: fn(&str) -> Result<ZeroizingText, CliError> = read_text;
        assert!(std::mem::needs_drop::<ZeroizingText>());
        let text = ZeroizingText(ZeroizingBuf::new(b"secret text".to_vec()));
        assert_eq!(&*text, "secret text");
    }
}
