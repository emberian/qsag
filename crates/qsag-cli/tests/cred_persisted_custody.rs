//! The current ML-DSA protocol needs 2t-1 online custodians. Persisted local
//! bundles must not require the other n-(2t-1) custodians for restoration.
use std::path::PathBuf;
use std::process::{Command, Output};

struct Scratch(PathBuf);
impl Scratch {
    fn new() -> Self {
        Self::named("rss")
    }
    fn named(tag: &str) -> Self {
        let path =
            std::env::temp_dir().join(format!("qsag-cred-custody-{tag}-{}", std::process::id()));
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
    let mut args = args.to_vec();
    let stateful = matches!(
        (args.first(), args.get(1)),
        (
            Some(&"cred"),
            Some(&"mldsa-keygen" | &"mldsa-sign" | &"voprf-keygen" | &"voprf-eval")
        )
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

#[cfg(unix)]
#[test]
fn anchored_mldsa_enforces_open_at_least_and_rejects_snapshot_rollback() {
    use std::os::unix::fs::DirBuilderExt;
    let dir = Scratch::named("anchored");
    let anchor = dir.0.join("anchor");
    std::fs::DirBuilder::new()
        .mode(0o700)
        .create(&anchor)
        .unwrap();
    let anchor_s = anchor.to_str().unwrap();
    let vault = dir.path("vault");
    let public = dir.path("public");
    let message = dir.path("message");
    std::fs::write(&message, b"anchored threshold ML-DSA").unwrap();

    success(&[
        "cred",
        "mldsa-keygen",
        "--threshold",
        "2",
        "--parties",
        "3",
        "--vault-dir",
        &vault,
        "--public-out",
        &public,
        "--anchor-dir",
        anchor_s,
        "--allow-single-disk-anchor",
        "--deterministic",
        "--passphrase-env",
        "QSAG_CUSTODY_TEST_PASS",
    ]);

    let snap_burns: Vec<Vec<u8>> = (0..3)
        .map(|p| std::fs::read(format!("{vault}/mldsa-party-{p}.burn")).unwrap())
        .collect();

    let sig0 = dir.path("sig0");
    success(&[
        "cred",
        "mldsa-sign",
        "--vault-dir",
        &vault,
        "--epoch",
        "0",
        "--in",
        &message,
        "--out",
        &sig0,
        "--anchor-dir",
        anchor_s,
        "--allow-single-disk-anchor",
        "--deterministic",
        "--passphrase-env",
        "QSAG_CUSTODY_TEST_PASS",
    ]);
    success(&[
        "cred",
        "mldsa-verify",
        "--public",
        &public,
        "--in",
        &message,
        "--sig",
        &sig0,
    ]);

    // Omitting --anchor-dir is refused.
    let no_anchor = run(
        &[
            "cred",
            "mldsa-sign",
            "--vault-dir",
            &vault,
            "--epoch",
            "1",
            "--in",
            &message,
            "--out",
            &dir.path("no-anchor.sig"),
            "--passphrase-env",
            "QSAG_CUSTODY_TEST_PASS",
        ],
        "custody test passphrase",
    );
    assert_eq!(no_anchor.status.code(), Some(4));

    // Roll back all burn ledgers in place to genesis; FsNonceBurnStore::open_at_least rejects!
    for (p, bytes) in snap_burns.iter().enumerate() {
        std::fs::write(format!("{vault}/mldsa-party-{p}.burn"), bytes).unwrap();
    }
    let rb = run(
        &[
            "cred",
            "mldsa-sign",
            "--vault-dir",
            &vault,
            "--epoch",
            "1",
            "--in",
            &message,
            "--out",
            &dir.path("rollback.sig"),
            "--anchor-dir",
            anchor_s,
            "--allow-single-disk-anchor",
            "--passphrase-env",
            "QSAG_CUSTODY_TEST_PASS",
        ],
        "custody test passphrase",
    );
    assert_eq!(rb.status.code(), Some(4));
    assert!(!PathBuf::from(dir.path("rollback.sig")).exists());
}

/// Seventeen custodians are above the replicated bound: each holds one Shamir share,
/// and any three of them (2t - 1 for t = 2) sign from their own files.
#[test]
fn mldsa_seventeen_custodians_sign_from_three_shamir_share_files() {
    let dir = Scratch::named("shamir");
    let vault = dir.path("vault");
    let public = dir.path("public");
    let message = dir.path("message");
    let signature = dir.path("signature");
    std::fs::write(&message, b"seventeen custodians, three online").unwrap();
    let keygen = |backend: &[&str], out: &str| {
        let mut args = vec![
            "cred",
            "mldsa-keygen",
            "--threshold",
            "2",
            "--parties",
            "17",
            "--vault-dir",
            out,
            "--public-out",
            &public,
            "--deterministic",
            "--passphrase-env",
            "QSAG_CUSTODY_TEST_PASS",
        ];
        args.extend_from_slice(backend);
        run(&args, "custody test passphrase")
    };
    // The replicated backend refuses seventeen custodians.
    let refused = keygen(&["--backend", "rss"], &dir.path("replicated"));
    assert!(!refused.status.success());
    let created = keygen(&[], &vault);
    assert!(
        created.status.success(),
        "{}",
        String::from_utf8_lossy(&created.stderr)
    );
    for party in 0..17 {
        let bundle = std::fs::read_to_string(format!("{vault}/mldsa-party-{party}.share")).unwrap();
        assert!(bundle.contains("qsag-cred-mldsa-shamir-share-v1"));
        assert!(bundle.contains("cshake256-iterated-v1"));
    }
    // Only custodians 3, 9 and 16 keep their files.
    for party in (0..17).filter(|party| ![3, 9, 16].contains(party)) {
        for name in [
            format!("mldsa-party-{party}.share"),
            format!("mldsa-party-{party}.share.vault.lock"),
            format!("mldsa-party-{party}.burn"),
            format!("mldsa-party-{party}.burn.lock"),
        ] {
            std::fs::remove_file(PathBuf::from(&vault).join(name)).unwrap();
        }
    }
    let sign = |signers: &str, epoch: &str, out: &str| {
        run(
            &[
                "cred",
                "mldsa-sign",
                "--vault-dir",
                &vault,
                "--signers",
                signers,
                "--epoch",
                epoch,
                "--in",
                &message,
                "--out",
                out,
                "--deterministic",
                "--passphrase-env",
                "QSAG_CUSTODY_TEST_PASS",
            ],
            "custody test passphrase",
        )
    };
    let signed = sign("3,9,16", "0", &signature);
    assert!(
        signed.status.success(),
        "{}",
        String::from_utf8_lossy(&signed.stderr)
    );
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
    let refused = sign("3,16", "1", &dir.path("too-small"));
    assert_eq!(refused.status.code(), Some(4));
    assert!(String::from_utf8_lossy(&refused.stderr).contains("quorum too small"));
}
