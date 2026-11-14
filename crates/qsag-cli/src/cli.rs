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

pub struct ZeroizingBuf(pub Vec<u8>);
impl std::ops::Deref for ZeroizingBuf {
    type Target = [u8];
    fn deref(&self) -> &[u8] { &self.0 }
}
impl Drop for ZeroizingBuf {
    fn drop(&mut self) {
        let cap = self.0.capacity();
        if cap > self.0.len() {
            self.0.resize(cap, 0);
        }
        qsag_accel::ct::ct_zeroize_bytes(&mut self.0);
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
        let old_len = buf.capacity();
        buf.resize(old_len, 0);
        qsag_accel::ct::ct_zeroize_bytes(buf);
        *buf = next;
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

fn open_nonblocking_regular(path: &str) -> Result<std::fs::File, CliError> {
    let mut opts = std::fs::OpenOptions::new();
    opts.read(true);
    #[cfg(all(target_os = "linux", any(target_arch = "aarch64", target_arch = "arm")))]
    {
        use std::os::unix::fs::OpenOptionsExt;
        opts.custom_flags(0x8000 | 0x800);
    }
    #[cfg(all(
        target_os = "linux",
        any(
            target_arch = "x86_64",
            target_arch = "x86",
            target_arch = "riscv64",
            target_arch = "riscv32"
        )
    ))]
    {
        use std::os::unix::fs::OpenOptionsExt;
        opts.custom_flags(0x20000 | 0x800);
    }
    #[cfg(target_os = "macos")]
    {
        use std::os::unix::fs::OpenOptionsExt;
        opts.custom_flags(0x100 | 0x4);
    }
    opts.open(path).map_err(|e| CliError::io("opening input", e))
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
pub fn read_input(path: &str) -> Result<Vec<u8>, CliError> {
    let mut bytes = if path == "-" {
        read_limited(std::io::stdin(), MAX_MSG_BYTES)?
    } else {
        read_bounded_file(path, MAX_MSG_BYTES)?
    };
    Ok(std::mem::take(&mut bytes.0))
}

pub fn read_text(path: &str) -> Result<String, CliError> {
    let bytes = read_bounded_file(path, MAX_KEY_FILE_BYTES)?;
    std::str::from_utf8(&bytes.0)
        .map(str::to_owned)
        .map_err(|_| CliError::input(format!("{path} is not UTF-8 text")))
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
        std::fs::rename(&tmp, path).map_err(|e| CliError::io(format_args!("replacing {path}"), e))?;
        sync_parent(path)
    })();
    if result.is_err() { let _ = std::fs::remove_file(&tmp); }
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

    #[test]
    fn failed_replace_removes_temporary_file() {
        let dir = std::env::temp_dir().join(format!("qsag-replace-{}", crate::codec::to_hex(&os_random_32().unwrap())));
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
