//! Retired dealer/oracle APIs remain absent from the replacement public interface.
use std::{fs, process::Command};

#[test]
fn default_consumer_cannot_access_retired_oracles() {
    // Keep nested build artifacts inside this checkout, including isolated CI runs.
    let parent = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target");
    fs::create_dir_all(&parent).unwrap();
    let dir = parent.join(format!("credential-gate-{}", std::process::id()));
    fs::create_dir(&dir).unwrap();
    struct Cleanup(std::path::PathBuf);
    impl Drop for Cleanup {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }
    let _cleanup = Cleanup(dir.clone());
    let dependency = env!("CARGO_MANIFEST_DIR").replace('\\', "\\\\");
    fs::write(dir.join("Cargo.toml"), format!(
        "[package]\nname = \"credential-gate-probe\"\nversion = \"0.0.0\"\nedition = \"2024\"\n[workspace]\n[dependencies]\nqsag-cred = {{ path = {dependency:?} }}\n"
    )).unwrap();
    fs::create_dir(dir.join("src")).unwrap();
    fs::write(dir.join("src/main.rs"), r#"
use qsag_cred::voprf::voprf_server_evaluate;
use qsag_cred::voprf_dkg;
use qsag_cred::blind_vc::verify_selective_disclosure;
use qsag_cred::holder_prepare_blind_issuance;
fn main() {}
"#).unwrap();
    let output = Command::new(env!("CARGO"))
        .args(["check", "--offline", "--quiet"])
        .env("CARGO_TARGET_DIR", dir.join("target"))
        .current_dir(&dir).output().unwrap();
    assert!(!output.status.success(), "retired APIs must remain absent");
    let stderr = String::from_utf8_lossy(&output.stderr);
    for symbol in ["voprf", "voprf_dkg", "blind_vc", "holder_prepare_blind_issuance"] {
        assert!(stderr.contains(&format!("unresolved import `qsag_cred::{symbol}")), "{stderr}");
    }
}
