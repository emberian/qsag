//! The current ML-DSA protocol needs 2t-1 online custodians. Persisted local
//! bundles must not require the other n-(2t-1) custodians for restoration.
use std::path::PathBuf;
use std::process::{Command, Output};

struct Scratch(PathBuf);
impl Scratch {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!("qsag-cred-custody-{}", std::process::id()));
        std::fs::create_dir(&path).unwrap();
        Self(path)
    }
    fn path(&self, name: &str) -> String {
        self.0.join(name).to_str().unwrap().to_owned()
    }
}
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}
fn run(args: &[&str], pass: &str) -> Output {
    Command::new(env!("CARGO_BIN_EXE_qsag"))
        .args(args)
        .env("QSAG_CUSTODY_TEST_PASS", pass)
        .output()
        .unwrap()
}
#[track_caller]
fn success(args: &[&str]) {
    let out = run(args, "custody test passphrase");
    assert!(
        out.status.success(),
        "{args:?}: {}",
        String::from_utf8_lossy(&out.stderr)
    );
}

#[test]
fn mldsa_selected_encrypted_bundles_survive_absent_custodians() {
    let dir = Scratch::new();
    let vault = dir.path("vault");
    let public = dir.path("public");
    let message = dir.path("message");
    let signature = dir.path("signature");
    std::fs::write(&message, b"persisted non-contiguous quorum").unwrap();
    success(&[
        "cred",
        "mldsa-keygen",
        "--threshold",
        "2",
        "--parties",
        "5",
        "--vault-dir",
        &vault,
        "--public-out",
        &public,
        "--deterministic",
        "--passphrase-env",
        "QSAG_CUSTODY_TEST_PASS",
    ]);
    for party in 0..5 {
        let bundle = std::fs::read_to_string(format!("{vault}/mldsa-party-{party}.share")).unwrap();
        assert!(bundle.contains("cshake256-iterated-v1"));
        assert!(!PathBuf::from(format!("{vault}/mldsa-party-{party}.seed")).exists());
        assert!(!PathBuf::from(format!("{vault}/mldsa-burn-{party}.mac")).exists());
    }
    // Physically delete every private/state file belonging to the two offline parties.
    for party in [1, 3] {
        for name in [
            format!("mldsa-party-{party}.share"),
            format!("mldsa-party-{party}.share.vault.lock"),
            format!("mldsa-party-{party}.burn"),
            format!("mldsa-party-{party}.burn.lock"),
        ] {
            std::fs::remove_file(PathBuf::from(&vault).join(name)).unwrap();
        }
    }
    let sign = [
        "cred",
        "mldsa-sign",
        "--vault-dir",
        &vault,
        "--signers",
        "0,2,4",
        "--epoch",
        "0",
        "--in",
        &message,
        "--out",
        &signature,
        "--deterministic",
        "--passphrase-env",
        "QSAG_CUSTODY_TEST_PASS",
    ];
    let before = std::fs::read(format!("{vault}/mldsa-party-0.burn")).unwrap();
    let refused = run(&sign, "wrong passphrase");
    assert!(!refused.status.success());
    assert!(String::from_utf8_lossy(&refused.stderr).contains("wrong passphrase"));
    assert_eq!(
        std::fs::read(format!("{vault}/mldsa-party-0.burn")).unwrap(),
        before
    );
    assert!(!PathBuf::from(&signature).exists());
    success(&sign);
    success(&[
        "cred",
        "mldsa-verify",
        "--public",
        &public,
        "--in",
        &message,
        "--sig",
        &signature,
    ]);
    // A sub-quorum is still refused; persistence must not weaken the protocol threshold.
    let refused = run(
        &[
            "cred",
            "mldsa-sign",
            "--vault-dir",
            &vault,
            "--signers",
            "0,4",
            "--epoch",
            "1",
            "--in",
            &message,
            "--out",
            &dir.path("too-small"),
            "--passphrase-env",
            "QSAG_CUSTODY_TEST_PASS",
        ],
        "custody test passphrase",
    );
    assert_eq!(refused.status.code(), Some(4));
    assert!(String::from_utf8_lossy(&refused.stderr).contains("quorum too small"));
}
