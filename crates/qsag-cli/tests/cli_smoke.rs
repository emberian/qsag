//! End-to-end tests of the `qsag` binary: real subcommands, real files, real exit codes.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const SEED: &str = "00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff";

struct Workdir(PathBuf);

impl Workdir {
    fn new(name: &str) -> Self {
        let dir = std::env::temp_dir().join(format!("qsag-cli-{name}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("seed"), SEED).unwrap();
        std::fs::write(
            dir.join("msg"),
            b"pay 250000 units to the treasury cold wallet\n",
        )
        .unwrap();
        std::fs::write(
            dir.join("other"),
            b"pay 250001 units to the treasury cold wallet\n",
        )
        .unwrap();
        Self(dir)
    }
    fn path(&self, name: &str) -> String {
        self.0.join(name).to_str().unwrap().to_string()
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

fn code(output: &Output) -> i32 {
    output.status.code().expect("qsag exited by signal")
}

#[track_caller]
fn expect(args: &[&str], expected_code: i32) -> String {
    let output = qsag(args);
    assert_eq!(
        code(&output),
        expected_code,
        "qsag {args:?}\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).unwrap()
}

/// Flip one hex digit of the `"signature"` / `"proof"` member of a JSON file.
fn flip_hex_digit(path: &str, member: &str) {
    let text = std::fs::read_to_string(path).unwrap();
    let start = text.find(&format!("\"{member}\": \"")).unwrap() + member.len() + 5;
    let mut bytes = text.into_bytes();
    let at = start + 100;
    bytes[at] = if bytes[at] == b'0' { b'1' } else { b'0' };
    std::fs::write(path, bytes).unwrap();
}

fn keygen(dir: &Workdir, scheme: &str, extra: &[&str]) {
    let (sk, pk, seed) = (dir.path("sk"), dir.path("pk"), dir.path("seed"));
    let mut args = vec![
        "keygen",
        "--scheme",
        scheme,
        "--seed-file",
        &seed,
        "--secret-out",
        &sk,
        "--public-out",
        &pk,
    ];
    args.extend_from_slice(extra);
    expect(&args, 0);
}

#[test]
fn help_info_and_usage_errors() {
    assert!(expect(&["--help"], 0).contains("verify-agg"));
    for command in [
        "info",
        "keygen",
        "sign",
        "verify",
        "addr",
        "aggregate",
        "verify-agg",
        "policy-demo",
        "kat",
    ] {
        assert!(
            !expect(&[command, "--help"], 0).is_empty(),
            "{command} --help"
        );
    }
    let info = expect(&["info", "--json"], 0);
    for needle in [
        "slh-dsa-shake-128s",
        "\"signature_bytes\": 7856",
        "fts-frontier-514",
        "\"signature_bytes\": 514",
        "fts-threshold",
        "agg-jorts-poseidon2",
        "GoldilocksExt4",
        "WHIR",
        "CanopyMultiProof",
    ] {
        assert!(info.contains(needle), "info lacks {needle}");
    }
    assert_eq!(
        info,
        expect(&["info", "--json"], 0),
        "info output must be deterministic"
    );

    expect(&[], 1);
    expect(&["frobnicate"], 1);
    expect(
        &[
            "keygen",
            "--scheme",
            "rsa-512",
            "--secret-out",
            "/dev/null",
            "--public-out",
            "/dev/null",
        ],
        1,
    );
    expect(&["keygen", "--scheme"], 1);
    expect(&["sign", "--secret-key-hex", "00"], 1);
    expect(
        &[
            "verify",
            "--public",
            "/nonexistent/pk",
            "--in",
            "/nonexistent/m",
            "--sig",
            "/nonexistent/s",
        ],
        5,
    );
}

#[test]
fn slh_dsa_keygen_sign_verify_and_tamper() {
    let dir = Workdir::new("slh");
    keygen(&dir, "slh-dsa-shake-128f", &[]);
    let (sk, pk, msg, other, sig) = (
        dir.path("sk"),
        dir.path("pk"),
        dir.path("msg"),
        dir.path("other"),
        dir.path("sig"),
    );
    let public = dir.read("pk");
    assert!(public.contains("\"address\": \"qsp1"));
    assert!(public.contains("\"spki_der\""));
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        assert_eq!(
            std::fs::metadata(Path::new(&sk))
                .unwrap()
                .permissions()
                .mode()
                & 0o777,
            0o600
        );
    }
    // Existing key files are never overwritten.
    let seed = dir.path("seed");
    expect(
        &[
            "keygen",
            "--scheme",
            "slh-dsa-shake-128f",
            "--seed-file",
            &seed,
            "--secret-out",
            &sk,
            "--public-out",
            &pk,
        ],
        5,
    );

    expect(
        &[
            "sign",
            "--secret",
            &sk,
            "--in",
            &msg,
            "--out",
            &sig,
            "--ctx-hex",
            "c0ffee",
            "--deterministic",
        ],
        0,
    );
    assert!(dir.read("sig").contains("\"signature_bytes\": 17088"));
    assert!(
        expect(
            &[
                "verify",
                "--public",
                &pk,
                "--in",
                &msg,
                "--sig",
                &sig,
                "--ctx-hex",
                "c0ffee",
                "--json"
            ],
            0
        )
        .contains("\"valid\": true")
    );
    // Deterministic signing is reproducible.
    let sig2 = dir.path("sig2");
    expect(
        &[
            "sign",
            "--secret",
            &sk,
            "--in",
            &msg,
            "--out",
            &sig2,
            "--ctx-hex",
            "c0ffee",
            "--deterministic",
        ],
        0,
    );
    assert_eq!(dir.read("sig"), dir.read("sig2"));

    // Wrong message, wrong context, and a tampered signature are each refused with exit code 2.
    expect(
        &[
            "verify",
            "--public",
            &pk,
            "--in",
            &other,
            "--sig",
            &sig,
            "--ctx-hex",
            "c0ffee",
        ],
        2,
    );
    expect(&["verify", "--public", &pk, "--in", &msg, "--sig", &sig], 2);
    flip_hex_digit(&sig, "signature");
    expect(
        &[
            "verify",
            "--public",
            &pk,
            "--in",
            &msg,
            "--sig",
            &sig,
            "--ctx-hex",
            "c0ffee",
        ],
        2,
    );

    // The address round-trips; a corrupted address is refused.
    let address = expect(&["addr", "encode", "--public", &pk], 0);
    let address = address.trim();
    assert!(public.contains(address));
    assert!(expect(&["addr", "decode", address, "--hrp", "qsp"], 0).contains("SlhDsa128f"));
    expect(&["addr", "decode", address, "--hrp", "btc"], 2);
    let mut corrupted = address.to_string();
    let last = corrupted.pop().unwrap();
    corrupted.push(if last == 'q' { 'p' } else { 'q' });
    expect(&["addr", "decode", &corrupted], 2);
}

#[test]
fn few_time_key_enforces_its_use_budget_across_invocations() {
    let dir = Workdir::new("fts");
    keygen(&dir, "fts-frontier-1058", &[]);
    let (sk, pk, msg, other) = (
        dir.path("sk"),
        dir.path("pk"),
        dir.path("msg"),
        dir.path("other"),
    );
    let (sig1, sig2, sig3) = (dir.path("sig1"), dir.path("sig2"), dir.path("sig3"));
    expect(&["sign", "--secret", &sk, "--in", &msg, "--out", &sig1], 0);
    assert!(dir.read("sk").contains("\"uses_completed\": 1"));
    expect(
        &["sign", "--secret", &sk, "--in", &other, "--out", &sig2],
        4,
    );
    assert!(!Path::new(&sig2).exists());
    expect(
        &["verify", "--public", &pk, "--in", &msg, "--sig", &sig1],
        0,
    );
    expect(
        &["verify", "--public", &pk, "--in", &other, "--sig", &sig1],
        2,
    );
    // Full256Bit permits one use; repeated exhausted attempts write no signature.
    expect(&["sign", "--secret", &sk, "--in", &msg, "--out", &sig3], 4);
    assert!(!Path::new(&sig3).exists());
    flip_hex_digit(&sig1, "signature");
    expect(
        &["verify", "--public", &pk, "--in", &msg, "--sig", &sig1],
        2,
    );
}

#[test]
fn threshold_few_time_signature_burns_each_epoch_once() {
    let dir = Workdir::new("threshold");
    let (sk, pk, seed) = (dir.path("sk"), dir.path("pk"), dir.path("seed"));
    expect(
        &[
            "keygen",
            "--scheme",
            "fts-threshold",
            "--seed-file",
            &seed,
            "--secret-out",
            &sk,
            "--public-out",
            &pk,
            "--parties",
            "3",
            "--fast-demo",
        ],
        1,
    );
    keygen(
        &dir,
        "fts-threshold",
        &[
            "--parties",
            "3",
            "--fast-demo",
            "--accept-trusted-dealer-demo",
        ],
    );
    let (msg, other, sig) = (dir.path("msg"), dir.path("other"), dir.path("sig"));
    expect(&["sign", "--secret", &sk, "--in", &msg, "--out", &sig], 1);
    expect(
        &[
            "sign",
            "--secret",
            &sk,
            "--in",
            &msg,
            "--out",
            &sig,
            "--accept-trusted-dealer-demo",
        ],
        1,
    );
    expect(
        &[
            "sign",
            "--secret",
            &sk,
            "--in",
            &msg,
            "--out",
            &sig,
            "--epoch",
            "8",
            "--accept-trusted-dealer-demo",
        ],
        1,
    );
    expect(
        &[
            "sign",
            "--secret",
            &sk,
            "--in",
            &msg,
            "--out",
            &sig,
            "--epoch",
            "5",
            "--accept-trusted-dealer-demo",
        ],
        0,
    );
    expect(&["verify", "--public", &pk, "--in", &msg, "--sig", &sig], 0);
    expect(
        &["verify", "--public", &pk, "--in", &other, "--sig", &sig],
        2,
    );
    // The burn journal survives the process: epoch 5 can never sign a second message.
    let again = dir.path("again");
    expect(
        &[
            "sign",
            "--secret",
            &sk,
            "--in",
            &other,
            "--out",
            &again,
            "--epoch",
            "5",
            "--accept-trusted-dealer-demo",
        ],
        4,
    );
    assert!(!Path::new(&again).exists());
    flip_hex_digit(&sig, "signature");
    expect(&["verify", "--public", &pk, "--in", &msg, "--sig", &sig], 2);
}

#[test]
fn aggregate_merge_verify_and_tamper() {
    let dir = Workdir::new("agg");
    let wal = dir.path("wal");
    keygen(
        &dir,
        "agg-jorts-poseidon2",
        &["--validators", "4", "--wal-dir", &wal],
    );
    let (sk, pk, msg, other) = (
        dir.path("sk"),
        dir.path("pk"),
        dir.path("msg"),
        dir.path("other"),
    );
    let (proof_a, proof_b, merged) = (
        dir.path("a.proof"),
        dir.path("b.proof"),
        dir.path("merged.proof"),
    );
    let sign = |signers: &str, epoch: &str, input: &str, out: &str, expected: i32| {
        expect(
            &[
                "aggregate",
                "--secret",
                &sk,
                "--signers",
                signers,
                "--epoch",
                epoch,
                "--wal-dir",
                &wal,
                "--in",
                input,
                "--out",
                out,
                "--deterministic",
            ],
            expected,
        )
    };
    sign("0,2", "0", &msg, &proof_a, 0);
    sign("1,3", "0", &msg, &proof_b, 0);
    assert!(
        expect(
            &[
                "verify-agg",
                "--public",
                &pk,
                "--in",
                &msg,
                "--proof",
                &proof_a,
                "--json"
            ],
            0
        )
        .contains("\"valid\": true")
    );
    expect(
        &[
            "verify-agg",
            "--public",
            &pk,
            "--in",
            &other,
            "--proof",
            &proof_a,
        ],
        2,
    );

    // A validator's epoch is spent: signing a different message at epoch 0 is refused.
    sign("0", "0", &other, &dir.path("equivocation.proof"), 4);
    assert!(!Path::new(&dir.path("equivocation.proof")).exists());
    sign("2,1", "1", &msg, &dir.path("unordered.proof"), 1);
    // A deleted write-ahead log is not treated as an unused key.
    std::fs::remove_file(Path::new(&wal).join("validator-3.wal")).unwrap();
    sign("3", "1", &msg, &dir.path("lost-wal.proof"), 4);

    let pair = format!("{proof_a},{proof_b}");
    let out = expect(
        &[
            "aggregate",
            "--merge",
            &pair,
            "--public",
            &pk,
            "--in",
            &msg,
            "--out",
            &merged,
            "--json",
        ],
        0,
    );
    assert!(out.contains("\"leaf_shards\": 2"));
    assert!(
        expect(
            &[
                "verify-agg",
                "--public",
                &pk,
                "--in",
                &msg,
                "--proof",
                &merged
            ],
            0
        )
        .contains("4 of 4")
    );
    // Overlapping signer sets can not be merged.
    let overlap = format!("{proof_a},{merged}");
    expect(
        &[
            "aggregate",
            "--merge",
            &overlap,
            "--public",
            &pk,
            "--in",
            &msg,
            "--out",
            &dir.path("overlap.proof"),
        ],
        2,
    );

    flip_hex_digit(&merged, "proof");
    expect(
        &[
            "verify-agg",
            "--public",
            &pk,
            "--in",
            &msg,
            "--proof",
            &merged,
        ],
        2,
    );
}

#[test]
fn hybrid_identity_validates_exact_key_encodings() {
    let dir = Workdir::new("hybrid");
    let write = |name: &str, bytes: Vec<u8>| {
        let hex: String = bytes.iter().map(|b| format!("{b:02x}")).collect();
        std::fs::write(dir.0.join(name), hex).unwrap();
        dir.path(name)
    };
    let mut compressed = vec![0x11u8; 33];
    compressed[0] = 0x02;
    let classical = write("classical", compressed.clone());
    let pq = write("pq", vec![0x22u8; 1312]);
    let out = expect(
        &[
            "addr",
            "hybrid",
            "--suite",
            "hybrid-secp256k1-mldsa44",
            "--classical-pk",
            &classical,
            "--pq-pk",
            &pq,
            "--json",
        ],
        0,
    );
    assert!(
        out.contains("HybridConjunctive")
            && out.contains("\"id_commit\"")
            && out.contains("Secp256k1EcdsaCompact")
    );

    compressed[0] = 0x04;
    let uncompressed_tag = write("bad-tag", compressed);
    let short_pq = write("short-pq", vec![0x22u8; 1311]);
    let hybrid = |classical: &str, pq: &str, suite: &str, expected: i32| {
        expect(
            &[
                "addr",
                "hybrid",
                "--suite",
                suite,
                "--classical-pk",
                classical,
                "--pq-pk",
                pq,
            ],
            expected,
        );
    };
    hybrid(&uncompressed_tag, &pq, "hybrid-secp256k1-mldsa44", 2);
    hybrid(&classical, &short_pq, "hybrid-secp256k1-mldsa44", 2);
    hybrid(&classical, &pq, "hybrid-ed25519-mldsa65", 2);
    hybrid(&classical, &pq, "slh-dsa-shake-128s", 1);
}

#[test]
fn policy_demo_and_known_answer_tests() {
    let demo = expect(&["policy-demo", "--json"], 0);
    assert!(demo.contains("\"release_tokens_minted\": 3"));
    assert_eq!(demo.matches("\"matches_expected\": true").count(), 7);
    expect(&["policy-demo", "--scenario", "approved"], 0);
    for denied in [
        "unlisted-recipient",
        "over-single-cap",
        "over-velocity-cap",
        "self-approval",
        "missing-guardian",
        "expired",
    ] {
        expect(&["policy-demo", "--scenario", denied], 3);
    }
    expect(&["policy-demo", "--scenario", "no-such-scenario"], 1);

    let kat = expect(&["kat", "--json"], 0);
    assert!(kat.contains("\"failed\": 0"));
    for group in ["accel", "core", "fts", "agg", "addr", "policy"] {
        assert!(
            kat.contains(&format!("\"crate\": \"{group}\"")),
            "kat lacks {group} checks"
        );
    }
    assert!(!kat.contains("\"pass\": false"));
}

#[test]
fn concurrent_frontier_processes_spend_exactly_once() {
    let dir = Workdir::new("concurrent-vault");
    keygen(&dir, "fts-frontier-514", &[]);
    let barrier = std::sync::Barrier::new(4);
    let mut codes = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..4)
            .map(|i| {
                let barrier = &barrier;
                let dir = &dir;
                scope.spawn(move || {
                    barrier.wait();
                    let output = qsag(&[
                        "sign",
                        "--secret",
                        &dir.path("sk"),
                        "--in",
                        &dir.path("msg"),
                        "--out",
                        &dir.path(&format!("sig{i}")),
                    ]);
                    if code(&output) == 4 {
                        assert!(
                            String::from_utf8_lossy(&output.stderr).contains("UseBudgetExhausted")
                        );
                    }
                    code(&output)
                })
            })
            .collect();
        handles
            .into_iter()
            .map(|h| h.join().unwrap())
            .collect::<Vec<_>>()
    });
    codes.sort();
    assert_eq!(codes, [0, 4, 4, 4]);
}

#[test]
fn vault_rejects_corruption_missing_state_and_overwrite() {
    let dir = Workdir::new("vault-corruption");
    keygen(&dir, "fts-frontier-514", &[]);
    let original = dir.read("sk");
    let sign = || {
        qsag(&[
            "sign",
            "--secret",
            &dir.path("sk"),
            "--in",
            &dir.path("msg"),
            "--out",
            &dir.path("sig"),
        ])
    };
    let modified = original.replace("\"uses_completed\": 0", "\"uses_completed\": 1");
    std::fs::write(dir.path("sk"), modified).unwrap();
    let rejected = sign();
    assert_eq!(code(&rejected), 4);
    assert!(String::from_utf8_lossy(&rejected.stderr).contains("CorruptOrMissingVaultState"));
    let marker = "\"state_mac\": \"";
    let at = original.find(marker).unwrap() + marker.len();
    let mut bad_mac = original.clone().into_bytes();
    bad_mac[at] = if bad_mac[at] == b'0' { b'1' } else { b'0' };
    std::fs::write(dir.path("sk"), bad_mac).unwrap();
    assert_eq!(code(&sign()), 4);
    std::fs::write(dir.path("sk"), &original).unwrap();
    expect(
        &[
            "keygen",
            "--scheme",
            "fts-frontier-514",
            "--secret-out",
            &dir.path("sk"),
            "--public-out",
            &dir.path("pk"),
        ],
        5,
    );
    expect(
        &[
            "keygen",
            "--scheme",
            "fts-frontier-514",
            "--secret-out",
            &dir.path("sk"),
            "--public-out",
            &dir.path("pk"),
            "--force-overwrite",
        ],
        4,
    );
    assert_eq!(dir.read("sk"), original);
    let lock = dir.path("sk.vault.lock");
    let state = std::fs::read(&lock).unwrap();
    let _keep_inode = std::fs::File::open(&lock).unwrap();
    std::fs::remove_file(&lock).unwrap();
    assert_eq!(code(&sign()), 4);
    // Recreating the same bytes under a different inode does not restore enrollment.
    std::fs::write(&lock, state).unwrap();
    assert_eq!(code(&sign()), 4);
    assert!(!dir.0.join("sig").exists());
}

#[test]
fn stateful_seed_enrollments_are_distinct() {
    let dir = Workdir::new("enrollment");
    keygen(&dir, "fts-frontier-514", &[]);
    expect(
        &[
            "keygen",
            "--scheme",
            "fts-frontier-514",
            "--seed-file",
            &dir.path("seed"),
            "--secret-out",
            &dir.path("sk2"),
            "--public-out",
            &dir.path("pk2"),
        ],
        0,
    );
    assert_ne!(dir.read("pk"), dir.read("pk2"));
}

#[test]
fn oversized_files_fail_before_allocation() {
    let dir = Workdir::new("oversized");
    let huge = dir.path("huge");
    std::fs::File::create(&huge)
        .unwrap()
        .set_len(1024 * 1024 * 1024)
        .unwrap();
    expect(
        &[
            "verify",
            "--public",
            &huge,
            "--in",
            &dir.path("msg"),
            "--sig",
            &huge,
        ],
        1,
    );
}

#[cfg(unix)]
#[test]
fn symlinked_vault_lock_is_refused() {
    let dir = Workdir::new("symlink-lock");
    keygen(&dir, "fts-frontier-514", &[]);
    std::fs::rename(dir.path("sk.vault.lock"), dir.path("other-lock")).unwrap();
    std::os::unix::fs::symlink(dir.path("other-lock"), dir.path("sk.vault.lock")).unwrap();
    expect(
        &[
            "sign",
            "--secret",
            &dir.path("sk"),
            "--in",
            &dir.path("msg"),
            "--out",
            &dir.path("sig"),
        ],
        4,
    );
}
