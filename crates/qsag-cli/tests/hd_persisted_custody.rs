//! Recovery must not open absent custodians or run their DKG state machines.
use std::{fs, path::PathBuf, process::Command};

struct Temp(PathBuf);
impl Drop for Temp {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
fn run(args: &[&str], success: bool) {
    let out = Command::new(env!("CARGO_BIN_EXE_qsag"))
        .args(args)
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
