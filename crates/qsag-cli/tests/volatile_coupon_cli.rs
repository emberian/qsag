//! `qsag quorum coupon`: generate a sealed Baggy root key, mint a batch of volatile coupons
//! in one session, sign from it, and verify the signature with the root public key alone.
//! The session holds its coupons in locked memory, so minting and signing are one process
//! driven through standard input. The batch is a single coupon: minting is real dealerless
//! MPC and dominates the run time, at more than half a minute per coupon.

#![cfg(all(target_os = "linux", target_pointer_width = "64"))]

use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Output, Stdio};

const PASS_ENV: &str = "QSAG_COUPON_TEST_PASSPHRASE";
const PASSPHRASE: &str = "coupon root passphrase";

struct Workdir(PathBuf);

impl Workdir {
    fn new(name: &str) -> Self {
        let dir = std::env::temp_dir().join(format!("qsag-coupon-{name}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        Self(dir)
    }
    fn path(&self, name: &str) -> String {
        self.0.join(name).to_str().unwrap().to_string()
    }
    fn file(&self, name: &str, contents: &str) -> String {
        let path = self.path(name);
        std::fs::write(&path, contents).unwrap();
        path
    }
    fn exists(&self, name: &str) -> bool {
        self.0.join(name).exists()
    }
}

impl Drop for Workdir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// Run `qsag` with `stdin` as its standard input and require `expected_code`.
#[track_caller]
fn run_with(args: &[&str], passphrase: &str, stdin: &str, expected_code: i32) -> Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_qsag"))
        .args(args)
        .env(PASS_ENV, passphrase)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(stdin.as_bytes())
        .unwrap();
    let output = child.wait_with_output().unwrap();
    assert_eq!(
        output.status.code(),
        Some(expected_code),
        "qsag {args:?}\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    output
}

#[track_caller]
fn run(args: &[&str], expected_code: i32) -> Output {
    run_with(args, PASSPHRASE, "", expected_code)
}

/// The top-level JSON objects of a stream of pretty-printed ones.
fn objects(stdout: &[u8]) -> Vec<String> {
    let text = String::from_utf8(stdout.to_vec()).unwrap();
    text.split_inclusive("\n}\n").map(str::to_owned).collect()
}

fn member(object: &str, name: &str) -> String {
    let key = format!("\"{name}\": ");
    let rest = &object[object
        .find(&key)
        .unwrap_or_else(|| panic!("no {name} in {object}"))
        + key.len()..];
    let end = rest.find('\n').unwrap_or(rest.len());
    rest[..end]
        .trim_end_matches(',')
        .trim_matches('"')
        .to_string()
}

/// `text` with the hex digit at `nibble` of its member `name` changed.
fn flip_hex(text: &str, name: &str, nibble: usize) -> String {
    let key = format!("\"{name}\": \"");
    let at = text.find(&key).unwrap() + key.len() + nibble;
    let old = text.as_bytes()[at];
    assert!(old.is_ascii_hexdigit());
    let new = if old == b'0' { '1' } else { '0' };
    format!("{}{new}{}", &text[..at], &text[at + 1..])
}

#[track_caller]
fn verify(public: &str, message: &str, sig: &str, expected_code: i32) -> Output {
    run(
        &[
            "quorum", "coupon", "verify", "--public", public, "--in", message, "--sig", sig,
        ],
        expected_code,
    )
}

fn verify_json(public: &str, message: &str, sig: &str) -> Output {
    run(
        &[
            "quorum", "coupon", "verify", "--public", public, "--in", message, "--sig", sig,
            "--json",
        ],
        0,
    )
}

#[test]
fn mint_a_batch_sign_from_it_and_verify_statelessly() {
    let dir = Workdir::new("flow");
    let vault = dir.path("vault");
    let public = dir.path("root.json");
    run(
        &[
            "quorum",
            "coupon",
            "keygen",
            "--vault-dir",
            &vault,
            "--public-out",
            &public,
            "--passphrase-env",
            PASS_ENV,
        ],
        0,
    );
    let party = std::fs::read_to_string(dir.path("vault/coupon-root-party-0.sk")).unwrap();
    assert_eq!(member(&party, "envelope"), "cshake256-balloon-v2");

    // A wrong passphrase is refused before anything is minted.
    let session_args = [
        "quorum",
        "coupon",
        "session",
        "--vault-dir",
        &vault,
        "--members",
        "0,2",
        "--coupons",
        "1",
        "--ttl-secs",
        "600",
        "--passphrase-env",
        PASS_ENV,
    ];
    let refused = run_with(&session_args, "not the passphrase", "", 1);
    assert!(refused.stdout.is_empty());

    let first = dir.file("first.msg", "pay 5 to alice");
    let second = dir.file("second.msg", "pay 7 to bob");
    let request = |coupon: usize, message: &str, out: &str| {
        format!(
            "{{\"coupon\": {coupon}, \"message\": \"{message}\", \"out\": \"{}\"}}\n",
            dir.path(out)
        )
    };
    let requests = [
        request(0, &first, "first.sig"),
        // Coupon 0 is spent: neither another message nor the same one opens it again.
        request(0, &second, "reuse-other.sig"),
        request(0, &first, "reuse-same.sig"),
        request(1, &second, "outside.sig"),
    ]
    .concat();
    let session = run_with(&session_args, PASSPHRASE, &requests, 4);
    let replies = objects(&session.stdout);
    assert_eq!(replies.len(), 5, "{replies:?}");

    let batch = &replies[0];
    assert_eq!(member(batch, "format"), "qsag-quorum-coupon-session-v1");
    assert_eq!(member(batch, "threshold"), "2");
    assert_eq!(member(batch, "parties"), "3");
    let root = std::fs::read_to_string(&public).unwrap();
    assert_eq!(member(batch, "pk_root"), member(&root, "pk_root"));

    let outcome: Vec<_> = replies[1..]
        .iter()
        .map(|reply| (member(reply, "ok"), reply.as_str()))
        .collect();
    for (index, expected) in ["true", "false", "false", "false"].into_iter().enumerate() {
        assert_eq!(outcome[index].0, expected, "{}", outcome[index].1);
    }
    for spent in [1, 2] {
        assert!(
            outcome[spent].1.contains("MissingOrSpent"),
            "{}",
            outcome[spent].1
        );
        assert_eq!(member(outcome[spent].1, "exit_code"), "4");
    }
    assert!(
        outcome[3].1.contains("not in this batch"),
        "{}",
        outcome[3].1
    );
    for refused in ["reuse-other.sig", "reuse-same.sig", "outside.sig"] {
        assert!(!dir.exists(refused), "{refused} was written");
    }

    // Stateless verification: root public key, message and signature only.
    let first_sig = dir.path("first.sig");
    let valid = verify(&public, &first, &first_sig, 0);
    assert!(String::from_utf8_lossy(&valid.stdout).starts_with("VALID"));
    assert_eq!(
        member(
            &String::from_utf8_lossy(&verify_json(&public, &first, &first_sig).stdout),
            "coupon_id"
        ),
        member(outcome[0].1, "coupon_id")
    );
    // Wrong message.
    verify(&public, &second, &first_sig, 2);
    let altered = dir.file("altered.msg", "pay 5 to alicf");
    verify(&public, &altered, &first_sig, 2);

    // Tampered signatures. The wire form is: 12 bytes of subset header, pk_seed, leaf,
    // expires_at, 128 chain ends, the length-prefixed root certificate, counter, 128 nodes.
    let sig_text = std::fs::read_to_string(&first_sig).unwrap();
    let hex_len = member(&sig_text, "signature").len();
    let expires_at = 2 * (12 + 32 + 8 + 7);
    let chain_end = 2 * (12 + 48 + 100);
    let certificate = 2 * (12 + 48 + 4096 + 4 + 40);
    for (name, nibble) in [
        ("node", hex_len - 1),
        ("counter", hex_len - 2 * 4096 - 1),
        ("certificate", certificate),
        ("chain-end", chain_end),
        ("expiry", expires_at),
        ("member", 2 * 11 + 1),
    ] {
        let tampered = dir.file(
            &format!("{name}.sig"),
            &flip_hex(&sig_text, "signature", nibble),
        );
        let output = verify(&public, &first, &tampered, 2);
        assert!(output.stdout.is_empty(), "{name}");
    }
    let key = "\"signature\": \"";
    let start = sig_text.find(key).unwrap() + key.len();
    let truncated = format!(
        "{}{}",
        &sig_text[..start + hex_len - 2],
        &sig_text[start + hex_len..]
    );
    verify(&public, &first, &dir.file("truncated.sig", &truncated), 2);

    // Another root key does not accept the signature.
    let other_root = dir.file("other-root.json", &flip_hex(&root, "pk_root", 0));
    verify(&other_root, &first, &first_sig, 2);
}

#[test]
fn coupon_commands_refuse_malformed_requests_before_any_ceremony() {
    let dir = Workdir::new("usage");
    let vault = dir.path("vault");
    for args in [
        &["quorum", "coupon"][..],
        &["quorum", "coupon", "mint"],
        &["quorum", "coupon", "session", "--vault-dir", &vault],
        &[
            "quorum",
            "coupon",
            "session",
            "--vault-dir",
            &vault,
            "--members",
            "2,0",
            "--coupons",
            "1",
            "--ttl-secs",
            "60",
        ],
        &[
            "quorum",
            "coupon",
            "session",
            "--vault-dir",
            &vault,
            "--members",
            "0,3",
            "--coupons",
            "1",
            "--ttl-secs",
            "60",
        ],
        &[
            "quorum",
            "coupon",
            "session",
            "--vault-dir",
            &vault,
            "--members",
            "0,1",
            "--coupons",
            "0",
            "--ttl-secs",
            "60",
        ],
        &[
            "quorum",
            "coupon",
            "session",
            "--vault-dir",
            &vault,
            "--members",
            "0,1",
            "--coupons",
            "1",
            "--ttl-secs",
            "0",
        ],
        &[
            "quorum",
            "coupon",
            "keygen",
            "--vault-dir",
            &vault,
            "--public-out",
            &dir.path("root.json"),
            "--params",
            "sha2-128f",
        ],
    ] {
        run(args, 1);
    }
    assert!(!dir.exists("vault"));
    let help = run(&["quorum", "coupon", "--help"], 0);
    assert!(String::from_utf8_lossy(&help.stdout).contains("session"));
}
