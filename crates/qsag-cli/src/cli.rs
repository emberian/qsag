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
impl Drop for ZeroizingBuf {
    fn drop(&mut self) {
        self.0.fill(0);
        core::hint::black_box(self.0.as_mut_slice());
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
        self.0.fill(0);
        core::hint::black_box(&mut self.0);
    }
}

fn read_limited(reader: impl Read, max: u64) -> Result<ZeroizingBuf, CliError> {
    let mut data = ZeroizingBuf(Vec::new());
    reader
        .take(max.saturating_add(1))
        .read_to_end(&mut data.0)
        .map_err(|e| CliError::io("reading bounded input", e))?;
    if data.0.len() as u64 > max {
        return Err(CliError::input("input exceeds size limit"));
    }
    Ok(data)
}

pub fn read_bounded_file(path: &str, max_bytes: u64) -> Result<ZeroizingBuf, CliError> {
    let file = std::fs::File::open(path).map_err(|e| CliError::io("opening input", e))?;
    let meta = file
        .metadata()
        .map_err(|e| CliError::io("inspecting input", e))?;
    if !meta.is_file() || meta.len() > max_bytes {
        return Err(CliError::input(
            "input is not a regular file within size limit",
        ));
    }
    read_limited(file, max_bytes)
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
    write_new(&tmp, contents, true)?;
    std::fs::rename(&tmp, path).map_err(|e| CliError::io(format_args!("replacing {path}"), e))?;
    sync_parent(path)
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
