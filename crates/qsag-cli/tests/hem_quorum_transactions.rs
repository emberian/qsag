//! Transaction behaviour of the `hem-jorts-poseidon2` quorum vault commands: one command at
//! a time per vault, and a failed signing attempt that spent a leaf is recorded on disk.

use std::path::PathBuf;
use std::process::{Command, Output, Stdio};

const SEED: &str = "00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff";
const LOCK: &str = "quorum-meta.json.vault.lock";

struct Workdir(PathBuf);

impl Workdir {
    fn new(name: &str) -> Self {
        let dir = std::env::temp_dir().join(format!("qsag-hem-tx-{name}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("seed"), SEED).unwrap();
        Self(dir)
    }
    fn path(&self, name: &str) -> String {
        self.0.join(name).to_str().unwrap().to_string()
    }
    /// A message file holding `text`; the CLI takes messages by path.
    fn msg(&self, text: &str) -> String {
        let path = self.path(&format!("msg-{}", text.replace(' ', "_")));
        std::fs::write(&path, text).unwrap();
        path
    }
    fn read(&self, name: &str) -> String {
        std::fs::read_to_string(self.0.join(name)).unwrap()
    }
}

impl Drop for Workdir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn qsag(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_qsag"))
        .args(args)
        .output()
        .unwrap()
}

#[track_caller]
fn run(args: &[&str], expected_code: i32) -> Output {
    let output = qsag(args);
    assert_eq!(
        output.status.code(),
        Some(expected_code),
        "qsag {args:?}\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    output
}

fn json_member(text: &str, member: &str) -> String {
    let key = format!("\"{member}\": ");
    let rest = &text[text
        .find(&key)
        .unwrap_or_else(|| panic!("no {member} in {text}"))
        + key.len()..];
    let end = rest.find('\n').unwrap_or(rest.len());
    rest[..end]
        .trim_end_matches(',')
        .trim_matches('"')
        .to_string()
}

fn keygen(dir: &Workdir, vault: &str, leaves: &str) {
    run(
        &[
            "quorum",
            "keygen",
            "--scheme",
            "hem-jorts-poseidon2",
            "--threshold",
            "2",
            "--parties",
            "3",
            "--leaves",
            leaves,
            "--seed-file",
            &dir.path("seed"),
            "--vault-dir",
            &dir.path(vault),
            "--public-out",
            &dir.path("pk"),
        ],
        0,
    );
}

fn high_water(dir: &Workdir, vault: &str) -> u64 {
    json_member(
        &dir.read(&format!("{vault}/quorum-meta.json")),
        "high_water_leaf",
    )
    .parse()
    .unwrap()
}

fn vault_files(dir: &Workdir, vault: &str) -> Vec<(String, Vec<u8>)> {
    let mut out: Vec<_> = std::fs::read_dir(dir.0.join(vault))
        .unwrap()
        .map(|e| {
            let e = e.unwrap();
            (
                e.file_name().to_str().unwrap().to_string(),
                std::fs::read(e.path()).unwrap(),
            )
        })
        .collect();
    out.sort();
    out
}

#[test]
fn concurrent_signs_on_one_vault_never_share_a_leaf() {
    let dir = Workdir::new("concurrent");
    keygen(&dir, "vault", "8");
    assert!(dir.0.join("vault").join(LOCK).is_file());

    const WORKERS: usize = 6;
    let children: Vec<_> = (0..WORKERS)
        .map(|i| {
            Command::new(env!("CARGO_BIN_EXE_qsag"))
                .args([
                    "quorum",
                    "sign",
                    "--vault-dir",
                    &dir.path("vault"),
                    "--message",
                    &dir.msg(&format!("message {i}")),
                    "--out",
                    &dir.path(&format!("sig-{i}")),
                ])
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .spawn()
                .unwrap()
        })
        .collect();

    let mut epochs = Vec::new();
    for (i, child) in children.into_iter().enumerate() {
        let output = child.wait_with_output().unwrap();
        let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
        match output.status.code() {
            Some(0) => {
                let sig = dir.read(&format!("sig-{i}"));
                epochs.push(json_member(&sig, "epoch").parse::<u64>().unwrap());
                run(
                    &[
                        "quorum",
                        "verify",
                        "--public",
                        &dir.path("pk"),
                        "--message",
                        &dir.msg(&format!("message {i}")),
                        "--sig",
                        &dir.path(&format!("sig-{i}")),
                    ],
                    0,
                );
            }
            // A command that could not get the vault within the lock timeout gives up
            // without having read or written anything.
            Some(4) => {
                assert!(stderr.contains("vault lock unavailable"), "{stderr}");
                assert!(!dir.0.join(format!("sig-{i}")).exists());
            }
            other => panic!("worker {i} exited {other:?}: {stderr}"),
        }
    }

    assert!(!epochs.is_empty());
    epochs.sort_unstable();
    let expected: Vec<u64> = (0..epochs.len() as u64).collect();
    assert_eq!(epochs, expected, "each signature used its own leaf");
    assert_eq!(high_water(&dir, "vault"), epochs.len() as u64);

    // The vault is still loadable and continues from the recorded high-water mark.
    run(
        &[
            "quorum",
            "sign",
            "--vault-dir",
            &dir.path("vault"),
            "--message",
            &dir.msg("after"),
            "--out",
            &dir.path("sig-after"),
        ],
        0,
    );
    assert_eq!(
        json_member(&dir.read("sig-after"), "epoch"),
        epochs.len().to_string()
    );
}

#[test]
fn commands_wait_for_the_vault_lock_and_refuse_a_vault_without_one() {
    use std::fs::OpenOptions;

    let dir = Workdir::new("lock");
    keygen(&dir, "vault", "4");
    let lock_path = dir.0.join("vault").join(LOCK);
    let before = vault_files(&dir, "vault");

    // While another holder has the vault, sign, refresh and reshare all give up with a
    // state conflict and leave every vault file as it was.
    let held = OpenOptions::new()
        .read(true)
        .write(true)
        .open(&lock_path)
        .unwrap();
    held.lock().unwrap();
    let vault = dir.path("vault");
    let sign = [
        "quorum",
        "sign",
        "--vault-dir",
        &vault,
        "--message",
        &dir.msg("m"),
        "--out",
        &dir.path("sig"),
    ];
    let refresh = ["quorum", "refresh", "--vault-dir", &vault];
    let reshare = [
        "quorum",
        "reshare",
        "--vault-dir",
        &vault,
        "--new-threshold",
        "2",
        "--new-parties",
        "4",
        "--out-vault-dir",
        &dir.path("vault2"),
    ];
    for args in [&sign[..], &refresh[..], &reshare[..]] {
        let output = run(args, 4);
        assert!(
            String::from_utf8_lossy(&output.stderr).contains("vault lock unavailable"),
            "{args:?}"
        );
    }
    assert_eq!(vault_files(&dir, "vault"), before);
    assert!(!dir.0.join("sig").exists());
    assert!(!dir.0.join("vault2").exists());
    drop(held);

    // Released: the same sign command succeeds at the first leaf.
    run(&sign, 0);
    assert_eq!(json_member(&dir.read("sig"), "epoch"), "0");

    // A vault whose lock file is gone, or was replaced by another file, is refused.
    let after_sign = vault_files(&dir, "vault");
    let lock_bytes = std::fs::read(&lock_path).unwrap();
    std::fs::remove_file(&lock_path).unwrap();
    let sign2 = [
        "quorum",
        "sign",
        "--vault-dir",
        &vault,
        "--message",
        &dir.msg("m2"),
        "--out",
        &dir.path("sig2"),
    ];
    run(&sign2, 4);
    run(&refresh, 4);
    assert!(!dir.0.join("sig2").exists());
    std::fs::write(&lock_path, lock_bytes).unwrap();
    assert_eq!(vault_files(&dir, "vault"), after_sign);
}

#[test]
fn reshare_refuses_an_occupied_target_before_touching_the_old_vault() {
    let dir = Workdir::new("reshare-target");
    keygen(&dir, "vault", "2");
    let before = vault_files(&dir, "vault");
    let vault = dir.path("vault");

    // Reshare onto itself, and onto a directory that already holds a vault file.
    std::fs::create_dir(dir.0.join("taken")).unwrap();
    std::fs::write(dir.0.join("taken").join("custodian-3.share"), b"x").unwrap();
    for target in [vault.clone(), dir.path("taken")] {
        run(
            &[
                "quorum",
                "reshare",
                "--vault-dir",
                &vault,
                "--new-threshold",
                "2",
                "--new-parties",
                "4",
                "--out-vault-dir",
                &target,
            ],
            1,
        );
    }
    assert_eq!(vault_files(&dir, "vault"), before);

    // The old vault is still live.
    run(
        &[
            "quorum",
            "sign",
            "--vault-dir",
            &vault,
            "--message",
            &dir.msg("m"),
            "--out",
            &dir.path("sig"),
        ],
        0,
    );
}

#[test]
fn failed_sign_that_spent_a_leaf_is_recorded_and_the_retry_uses_the_next_leaf() {
    let dir = Workdir::new("burn");
    keygen(&dir, "vault", "3");
    let vault = dir.path("vault");

    // Rejected before the latch certifies (one signer of a 2-of-3): nothing changes.
    let before = vault_files(&dir, "vault");
    run(
        &[
            "quorum",
            "sign",
            "--vault-dir",
            &vault,
            "--signers",
            "0",
            "--message",
            &dir.msg("m"),
            "--out",
            &dir.path("sig-short"),
        ],
        4,
    );
    assert_eq!(vault_files(&dir, "vault"), before);

    // Damage custodian 0's share of leaf 0 (first scalar after the 60-byte header).
    let share0 = dir.0.join("vault").join("custodian-0.share");
    let mut bytes = std::fs::read(&share0).unwrap();
    bytes[60] ^= 1;
    std::fs::write(&share0, &bytes).unwrap();

    // Signing certifies leaf 0 for this message and then fails. The leaf is spent on disk.
    let failed = qsag(&[
        "quorum",
        "sign",
        "--vault-dir",
        &vault,
        "--signers",
        "0,1",
        "--message",
        &dir.msg("first"),
        "--out",
        &dir.path("sig-first"),
    ]);
    assert_ne!(failed.status.code(), Some(0));
    assert!(!dir.0.join("sig-first").exists());
    assert_eq!(high_water(&dir, "vault"), 1);

    // Another message cannot be signed at leaf 0 any more; the retry signs at leaf 1.
    run(
        &[
            "quorum",
            "sign",
            "--vault-dir",
            &vault,
            "--signers",
            "0,1",
            "--message",
            &dir.msg("second"),
            "--out",
            &dir.path("sig-second"),
        ],
        0,
    );
    assert_eq!(json_member(&dir.read("sig-second"), "epoch"), "1");
    run(
        &[
            "quorum",
            "verify",
            "--public",
            &dir.path("pk"),
            "--message",
            &dir.msg("second"),
            "--sig",
            &dir.path("sig-second"),
        ],
        0,
    );
    assert_eq!(high_water(&dir, "vault"), 2);
}
