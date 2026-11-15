//! Persisted TOPRF shares eliminate enrollment replay. The current replicated
//! evaluation protocol still requires five online servers.
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
fn run(args: &[&str], pass: &str) -> Output {
    Command::new(env!("CARGO_BIN_EXE_qsag"))
        .args(args)
        .env("QSAG_TOPRF_PASS", pass)
        .output()
        .unwrap()
}
#[track_caller]
fn success(args: &[&str]) {
    let output = run(args, "TOPRF test passphrase");
    assert!(
        output.status.success(),
        "{args:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}
#[test]
fn encrypted_toprf_bundles_restore_and_reject_bad_passphrases() {
    let scratch =
        Scratch(std::env::temp_dir().join(format!("qsag-toprf-custody-{}", std::process::id())));
    std::fs::create_dir(&scratch.0).unwrap();
    let path = |name: &str| scratch.0.join(name).to_str().unwrap().to_owned();
    let vault = path("vault");
    let public = path("public");
    let input = path("input");
    let output = path("output");
    std::fs::write(&input, b"persisted TOPRF request").unwrap();
    success(&[
        "cred",
        "voprf-keygen",
        "--vault-dir",
        &vault,
        "--public-out",
        &public,
        "--threshold",
        "2",
        "--parties",
        "5",
        "--deterministic",
        "--passphrase-env",
        "QSAG_TOPRF_PASS",
    ]);
    for party in 0..5 {
        let bundle = std::fs::read_to_string(format!("{vault}/voprf-party-{party}.share")).unwrap();
        assert!(bundle.contains("cshake256-iterated-v1"));
        assert!(!PathBuf::from(format!("{vault}/voprf-party-{party}.seed")).exists());
    }
    let args = [
        "cred",
        "voprf-eval",
        "--vault-dir",
        &vault,
        "--public",
        &public,
        "--counter",
        "0",
        "--in",
        &input,
        "--out",
        &output,
        "--deterministic",
        "--passphrase-env",
        "QSAG_TOPRF_PASS",
    ];
    let before = std::fs::read(format!("{vault}/voprf-counter-0.json")).unwrap();
    let refused = run(&args, "wrong passphrase");
    assert!(!refused.status.success());
    assert!(String::from_utf8_lossy(&refused.stderr).contains("wrong passphrase"));
    assert_eq!(
        std::fs::read(format!("{vault}/voprf-counter-0.json")).unwrap(),
        before
    );
    assert!(!PathBuf::from(&output).exists());
    success(&args);
    let replay_out = path("replay");
    let mut replay = args;
    replay[11] = &replay_out;
    let refused = run(&replay, "TOPRF test passphrase");
    assert!(!refused.status.success());
    assert!(!PathBuf::from(&replay_out).exists());
    assert!(String::from_utf8_lossy(&refused.stderr).contains("counter"));
}
