//! Recovery must not open absent custodians or run their DKG state machines.
use std::{fs, path::PathBuf, process::Command};

struct Temp(PathBuf);
impl Drop for Temp {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
fn run(args: &[&str], success: bool) {
    let mut args = args.to_vec();
    let stateful = matches!(
        (args.first(), args.get(1)),
        (Some(&"hd"), Some(&"keygen" | &"recover" | &"export-rss")) | (Some(&"sign"), _)
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
    let out = Command::new(env!("CARGO_BIN_EXE_qsag"))
        .args(&args)
        .env("QSAG_HD_TEST_PASS", "isolated custody fixture")
        .output()
        .unwrap();
    assert_eq!(
        out.status.success(),
        success,
        "{args:?}: {}",
        String::from_utf8_lossy(&out.stderr)
    );
}
#[test]
fn encrypted_hd_recovers_and_signs_with_nonparticipant_file_absent() {
    let tmp = Temp(std::env::temp_dir().join(format!(
            "qsag-hd-subset-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        )));
    fs::create_dir(&tmp.0).unwrap();
    let path = |s: &str| tmp.0.join(s).to_string_lossy().into_owned();
    let vault = path("vault");
    let watch = path("watch");
    let proof = path("proof");
    let sk = path("sk");
    let pk = path("pk");
    let msg = path("message");
    let sig = path("sig");
    run(
        &[
            "hd",
            "keygen",
            "--threshold",
            "2",
            "--parties",
            "3",
            "--count",
            "2",
            "--vault-dir",
            &vault,
            "--watch-out",
            &watch,
            "--deterministic",
            "--passphrase-env",
            "QSAG_HD_TEST_PASS",
        ],
        true,
    );
    for party in 0..3 {
        let contents =
            fs::read_to_string(PathBuf::from(&vault).join(format!("hd-custodian-{party}.share")))
                .unwrap();
        assert!(contents.contains("cshake256-iterated-v1"));
        assert!(
            !PathBuf::from(&vault)
                .join(format!("hd-custodian-{party}.seed"))
                .exists()
        );
    }
    fs::remove_file(PathBuf::from(&vault).join("hd-custodian-1.share")).unwrap();
    run(
        &[
            "hd", "derive", "--watch", &watch, "--index", "0", "--out", &proof,
        ],
        true,
    );
    run(
        &[
            "hd",
            "recover",
            "--vault-dir",
            &vault,
            "--signers",
            "0,2",
            "--index",
            "0",
            "--proof",
            &proof,
            "--secret-out",
            &sk,
            "--public-out",
            &pk,
            "--passphrase-env",
            "QSAG_HD_TEST_PASS",
        ],
        true,
    );
    fs::write(&msg, b"only two custodians are present").unwrap();
    run(
        &[
            "sign",
            "--secret",
            &sk,
            "--in",
            &msg,
            "--out",
            &sig,
            "--passphrase-env",
            "QSAG_HD_TEST_PASS",
        ],
        true,
    );
    run(
        &["verify", "--public", &pk, "--in", &msg, "--sig", &sig],
        true,
    );
    run(
        &[
            "hd",
            "recover",
            "--vault-dir",
            &vault,
            "--signers",
            "0",
            "--index",
            "0",
            "--proof",
            &proof,
            "--secret-out",
            &path("insufficient"),
            "--passphrase-env",
            "QSAG_HD_TEST_PASS",
        ],
        false,
    );
}

#[cfg(unix)]
#[test]
fn anchored_hd_enforces_budget_export_rss_and_rejects_rollback() {
    use std::os::unix::fs::DirBuilderExt;
    let tmp = Temp(std::env::temp_dir().join(format!(
        "qsag-hd-anchored-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    )));
    fs::create_dir(&tmp.0).unwrap();
    let path = |s: &str| tmp.0.join(s).to_string_lossy().into_owned();
    let anchor = tmp.0.join("anchor");
    fs::DirBuilder::new().mode(0o700).create(&anchor).unwrap();
    let anchor_s = anchor.to_str().unwrap();
    let vault = path("vault");
    let watch = path("watch");
    let proof = path("proof");
    run(
        &[
            "hd",
            "keygen",
            "--threshold",
            "2",
            "--parties",
            "3",
            "--count",
            "4",
            "--vault-dir",
            &vault,
            "--watch-out",
            &watch,
            "--anchor-dir",
            anchor_s,
            "--allow-single-disk-anchor",
            "--deterministic",
            "--passphrase-env",
            "QSAG_HD_TEST_PASS",
        ],
        true,
    );
    assert!(PathBuf::from(&vault).join("hd-query.budget").is_file());
    assert!(PathBuf::from(&vault).join("hd-query.budget.lock").is_file());
    let snap_budget = fs::read(PathBuf::from(&vault).join("hd-query.budget")).unwrap();

    run(
        &[
            "hd", "derive", "--watch", &watch, "--index", "1", "--out", &proof,
        ],
        true,
    );

    // Export 2-of-3 RssKeyShare256 (QSRSSK01, 268 B) for all 3 custodians without cleartext SK.
    let rss_dir = path("rss-shares");
    run(
        &[
            "hd",
            "export-rss",
            "--vault-dir",
            &vault,
            "--index",
            "1",
            "--proof",
            &proof,
            "--out-dir",
            &rss_dir,
            "--anchor-dir",
            anchor_s,
            "--allow-single-disk-anchor",
            "--passphrase-env",
            "QSAG_HD_TEST_PASS",
        ],
        true,
    );
    for p in 0..3 {
        let share_doc =
            fs::read_to_string(PathBuf::from(&rss_dir).join(format!("child-1-party-{p}.rss.json")))
                .unwrap();
        assert!(share_doc.contains("qsag-hd-rss-child-share-v1"));
        assert!(share_doc.contains("cshake256-iterated-v1"));
    }

    // Export a single custodian's share even with custodian 1 deleted!
    fs::remove_file(PathBuf::from(&vault).join("hd-custodian-1.share")).unwrap();
    let single_rss = path("party0-unenc.rss.json");
    run(
        &[
            "hd",
            "export-rss",
            "--vault-dir",
            &vault,
            "--index",
            "1",
            "--party",
            "0",
            "--secret-out",
            &single_rss,
            "--anchor-dir",
            anchor_s,
            "--allow-single-disk-anchor",
            "--passphrase-env",
            "QSAG_HD_TEST_PASS",
            "--allow-unencrypted",
        ],
        true,
    );
    let unenc = fs::read_to_string(&single_rss).unwrap();
    // "QSRSSK01" in hex is 51535253534b3031 (first 8 bytes of 268-byte RssKeyShare256).
    assert!(unenc.contains("51535253534b3031"), "{unenc}");

    // Roll back QSHDQB05 budget file in place; external anchor detects rollback and fails closed!
    fs::write(PathBuf::from(&vault).join("hd-query.budget"), &snap_budget).unwrap();
    run(
        &[
            "hd",
            "recover",
            "--vault-dir",
            &vault,
            "--signers",
            "0,2",
            "--index",
            "1",
            "--proof",
            &proof,
            "--secret-out",
            &path("rollback.sk"),
            "--anchor-dir",
            anchor_s,
            "--allow-single-disk-anchor",
            "--passphrase-env",
            "QSAG_HD_TEST_PASS",
        ],
        false,
    );
    assert!(!PathBuf::from(path("rollback.sk")).exists());
}
