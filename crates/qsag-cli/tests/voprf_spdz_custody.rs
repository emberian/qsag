//! Shamir-SPDZ TOPRF custody: a (3, 5) committee evaluates from any three persisted
//! encrypted share files, with the other two deleted from disk.
use std::{
    path::PathBuf,
    process::{Command, Output},
};

struct Scratch(PathBuf);
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}
fn run(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_qsag"))
        .args(args)
        .env("QSAG_TOPRF_PASS", "TOPRF test passphrase")
        .output()
        .unwrap()
}
#[track_caller]
fn success(args: &[&str]) {
    let output = run(args);
    assert!(
        output.status.success(),
        "{args:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}
#[track_caller]
fn refused(args: &[&str], needle: &str) {
    let output = run(args);
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    assert!(!output.status.success(), "{args:?} unexpectedly succeeded");
    assert!(stderr.contains(needle), "{args:?}: {stderr}");
}
fn prf_output(path: &str) -> String {
    let text = std::fs::read_to_string(path).unwrap();
    let at = text.find("\"prf_output\"").unwrap();
    text[at..].split('"').nth(3).unwrap().to_owned()
}
fn as_refs(args: &[String]) -> Vec<&str> {
    args.iter().map(String::as_str).collect()
}
/// Flip one digit in the middle of the longest hexadecimal run of a share file.
fn corrupt_longest_hex_run(path: &str) {
    let mut bytes = std::fs::read(path).unwrap();
    let (mut best, mut start) = ((0, 0), 0);
    for end in 0..=bytes.len() {
        if end == bytes.len() || !bytes[end].is_ascii_hexdigit() {
            if end - start > best.1 - best.0 {
                best = (start, end);
            }
            start = end + 1;
        }
    }
    assert!(best.1 - best.0 >= 64, "no ciphertext found in {path}");
    let at = (best.0 + best.1) / 2;
    bytes[at] = if bytes[at] == b'0' { b'1' } else { b'0' };
    std::fs::write(path, bytes).unwrap();
}

#[test]
fn three_of_five_evaluates_from_three_remaining_share_files() {
    let scratch =
        Scratch(std::env::temp_dir().join(format!("qsag-toprf-spdz-{}", std::process::id())));
    std::fs::create_dir(&scratch.0).unwrap();
    let path = |name: &str| scratch.0.join(name).to_str().unwrap().to_owned();
    let (vault, public, input) = (path("vault"), path("public"), path("input"));
    std::fs::write(&input, b"persisted Shamir-SPDZ TOPRF request").unwrap();
    let share = |party: usize| format!("{vault}/voprf-party-{party}.share");
    let counter_file = |party: usize| format!("{vault}/voprf-counter-{party}.json");

    // The replicated backend refuses the shape; the default for it is Shamir-SPDZ.
    refused(
        &[
            "cred",
            "voprf-keygen",
            "--vault-dir",
            &vault,
            "--public-out",
            &public,
            "--threshold",
            "3",
            "--parties",
            "5",
            "--backend",
            "rss",
            "--passphrase-env",
            "QSAG_TOPRF_PASS",
        ],
        "shamir-spdz",
    );
    success(&[
        "cred",
        "voprf-keygen",
        "--vault-dir",
        &vault,
        "--public-out",
        &public,
        "--threshold",
        "3",
        "--parties",
        "5",
        "--passphrase-env",
        "QSAG_TOPRF_PASS",
    ]);
    for party in 0..5 {
        let bundle = std::fs::read_to_string(share(party)).unwrap();
        assert!(bundle.contains("qsag-cred-voprf-spdz-share-v1"));
        assert!(bundle.contains("cshake256-iterated-v1"));
    }

    let eval = |counter: &str, out: &str, signers: Option<&str>| {
        let mut args = vec![
            "cred",
            "voprf-eval",
            "--vault-dir",
            &vault,
            "--public",
            &public,
            "--counter",
            counter,
            "--in",
            &input,
            "--out",
            out,
            "--passphrase-env",
            "QSAG_TOPRF_PASS",
        ]
        .into_iter()
        .map(str::to_owned)
        .collect::<Vec<_>>();
        if let Some(signers) = signers {
            args.extend(["--signers".to_owned(), signers.to_owned()]);
        }
        args
    };

    // Servers 1, 2 and 4 evaluate while all five files exist.
    let first = path("first");
    success(&as_refs(&eval("0", &first, Some("1,2,4"))));

    // Two servers are gone for good.
    std::fs::remove_file(share(1)).unwrap();
    std::fs::remove_file(share(2)).unwrap();

    // Two servers are below the threshold, and nothing is spent on the attempt.
    let below = path("below");
    let before = std::fs::read(counter_file(0)).unwrap();
    refused(
        &as_refs(&eval("1", &below, Some("0,3"))),
        "needs 3 online servers",
    );
    assert_eq!(std::fs::read(counter_file(0)).unwrap(), before);
    assert!(!PathBuf::from(&below).exists());

    // The three remaining files evaluate, and a different quorum computes the same function.
    let second = path("second");
    success(&as_refs(&eval("1", &second, None)));
    assert!(
        std::fs::read_to_string(&second)
            .unwrap()
            .contains("voprf-poseidon2-shamir-spdz")
    );
    assert_eq!(prf_output(&first), prf_output(&second));

    // Server 4 already spent counter 0 and server 0 spent counter 1.
    let replay = path("replay");
    refused(&as_refs(&eval("1", &replay, None)), "counter");
    assert!(!PathBuf::from(&replay).exists());

    // A corrupted share file is refused before any counter moves.
    corrupt_longest_hex_run(&share(3));
    let before = std::fs::read(counter_file(0)).unwrap();
    let corrupted = path("corrupted");
    let output = run(&as_refs(&eval("2", &corrupted, None)));
    assert!(!output.status.success());
    assert_eq!(std::fs::read(counter_file(0)).unwrap(), before);
    assert!(!PathBuf::from(&corrupted).exists());
}
