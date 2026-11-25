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
    let mut args = args.to_vec();
    let stateful = matches!(
        (args.first(), args.get(1)),
        (Some(&"cred"), Some(&"voprf-keygen" | &"voprf-eval"))
    );
    let has_anchor = args.iter().any(|a| {
        matches!(
            *a,
            "--anchor-dir"
                | "--anchor-tpm-nv"
                | "--anchor-vmgenid"
                | "--ephemeral-unanchored"
                | "--help"
        )
    });
    if stateful && !has_anchor {
        args.push("--ephemeral-unanchored");
    }
    Command::new(env!("CARGO_BIN_EXE_qsag"))
        .args(&args)
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
        "--deterministic-test-only",
        "--passphrase-env",
        "QSAG_TOPRF_PASS",
    ]);
    for party in 0..5 {
        let bundle = std::fs::read_to_string(format!("{vault}/voprf-party-{party}.share")).unwrap();
        assert!(bundle.contains("cshake256-balloon-v2"));
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
        "--deterministic-test-only",
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

#[cfg(unix)]
#[test]
fn anchored_toprf_enforces_locked_record_quota_and_rejects_rollback() {
    use std::os::unix::fs::DirBuilderExt;
    let scratch =
        Scratch(std::env::temp_dir().join(format!("qsag-toprf-anchored-{}", std::process::id())));
    std::fs::create_dir(&scratch.0).unwrap();
    let path = |name: &str| scratch.0.join(name).to_str().unwrap().to_owned();
    let anchor = scratch.0.join("anchor");
    std::fs::DirBuilder::new()
        .mode(0o700)
        .create(&anchor)
        .unwrap();
    let anchor_s = anchor.to_str().unwrap();
    let vault = path("vault");
    let public = path("public");
    let input = path("input");
    std::fs::write(&input, b"anchored TOPRF query").unwrap();

    success(&[
        "cred",
        "voprf-keygen",
        "--vault-dir",
        &vault,
        "--public-out",
        &public,
        "--max-evaluations",
        "1",
        "--anchor-dir",
        anchor_s,
        "--allow-single-disk-anchor",
        "--passphrase-env",
        "QSAG_TOPRF_PASS",
    ]);
    // Counter ledger is now a binary QSTOPRF1 LockedRecord with companion .lock file.
    let raw_ctr0 = std::fs::read(format!("{vault}/voprf-counter-0.json")).unwrap();
    assert!(raw_ctr0.windows(8).any(|w| w == b"QSTOPRF1"));
    assert!(PathBuf::from(format!("{vault}/voprf-counter-0.json.lock")).is_file());

    let snap_ctrs: Vec<Vec<u8>> = (0..5)
        .map(|p| std::fs::read(format!("{vault}/voprf-counter-{p}.json")).unwrap())
        .collect();

    let out0 = path("out0");
    success(&[
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
        &out0,
        "--anchor-dir",
        anchor_s,
        "--allow-single-disk-anchor",
        "--passphrase-env",
        "QSAG_TOPRF_PASS",
    ]);

    // Evaluation #2 exceeds --max-evaluations 1 quota and is refused!
    let out1 = path("out1");
    let quota_refused = run(
        &[
            "cred",
            "voprf-eval",
            "--vault-dir",
            &vault,
            "--public",
            &public,
            "--counter",
            "1",
            "--in",
            &input,
            "--out",
            &out1,
            "--anchor-dir",
            anchor_s,
            "--allow-single-disk-anchor",
            "--passphrase-env",
            "QSAG_TOPRF_PASS",
        ],
        "TOPRF test passphrase",
    );
    assert!(!quota_refused.status.success());
    assert!(String::from_utf8_lossy(&quota_refused.stderr).contains("quota"));

    // Snapshot rollback of all 5 counter files in place is caught by external anchor!
    for (p, bytes) in snap_ctrs.iter().enumerate() {
        std::fs::write(format!("{vault}/voprf-counter-{p}.json"), bytes).unwrap();
    }
    let out_rb = path("out-rb");
    let rb_refused = run(
        &[
            "cred",
            "voprf-eval",
            "--vault-dir",
            &vault,
            "--public",
            &public,
            "--counter",
            "2",
            "--in",
            &input,
            "--out",
            &out_rb,
            "--anchor-dir",
            anchor_s,
            "--allow-single-disk-anchor",
            "--passphrase-env",
            "QSAG_TOPRF_PASS",
        ],
        "TOPRF test passphrase",
    );
    assert!(!rb_refused.status.success());
    assert!(!PathBuf::from(&out_rb).exists());
}
