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
    let mut args = args.to_vec();
    // Tests without an anchor directory use disposable keys and say so, as the CLI
    // requires. Anchored invocations run exactly as written.
    let enrolls_custody = match (args.first(), args.get(1), args.get(2)) {
        (Some(&"keygen" | &"sign" | &"aggregate"), _, _) => true,
        (Some(&"quorum"), Some(&"keygen" | &"sign" | &"refresh" | &"reshare"), _) => true,
        (
            Some(&"cred"),
            Some(&"voprf-keygen" | &"voprf-eval" | &"mldsa-keygen" | &"mldsa-sign"),
            _,
        ) => true,
        (Some(&"hd"), Some(&"keygen" | &"recover" | &"export-rss"), _) => true,
        (Some(&"policy"), Some(&"init"), _) => true,
        (Some(&"policy"), Some(&"biscuit"), Some(&"keygen" | &"mint")) => true,
        _ => false,
    };
    let has_anchor = args.iter().any(|a| {
        matches!(
            *a,
            "--anchor-dir"
                | "--anchor-tpm-nv"
                | "--anchor-vmgenid"
                | "--ephemeral-unanchored"
                | "--help"
                | "-h"
        )
    });
    if enrolls_custody && !has_anchor {
        args.push("--ephemeral-unanchored");
    }
    Command::new(env!("CARGO_BIN_EXE_qsag"))
        .args(&args)
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

/// A fresh empty directory for one test to point `TMPDIR` at.
fn dir_for_tmp(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("qsag-cli-{name}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// The value of the first `"member": ...` line of pretty-printed JSON, without its quotes.
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

/// A two-approver custody policy over parties 1, 2 and 3 with party 3 as accounting guardian:
/// 1,000 units per transfer, 1,500 units per window, one allowlisted recipient.
fn write_policy(dir: &Workdir, suite: &str, recipient: &str) -> String {
    let path = dir.path("policy.json");
    std::fs::write(
        &path,
        format!(
            r#"{{
  "format": "qsag-policy-v1",
  "chain_id": 1,
  "suite": "{suite}",
  "recipient_allowlist": ["{recipient}"],
  "max_single_tx_amount": 1000,
  "velocity_window_cap": 1500,
  "valid_not_before_secs": 0,
  "valid_not_after_secs": 4102444800,
  "forbid_initiator_self_approval": true,
  "hardware_guardian_party": 3,
  "quorum_tiers": [
    {{"max_amount_units": 1000, "min_approvers": 2, "require_hardware_guardian": true}}
  ],
  "parties": [1, 2, 3]
}}
"#
        ),
    )
    .unwrap();
    path
}

/// Propose a transfer and return its intent identifier; `message_out` receives the bytes to sign.
#[track_caller]
fn propose(
    ledger: &[&str],
    public: &str,
    payload: &str,
    recipient: &str,
    amount: &str,
    message_out: &str,
) -> String {
    let mut args = vec!["policy", "propose"];
    args.extend_from_slice(ledger);
    args.extend_from_slice(&[
        "--public",
        public,
        "--payload",
        payload,
        "--recipient",
        recipient,
        "--amount",
        amount,
        "--initiator",
        "1",
        "--approvers",
        "2,3",
        "--message-out",
        message_out,
        "--json",
    ]);
    json_member(&expect(&args, 0), "intent_id")
}

#[track_caller]
fn approve(ledger: &[&str], intent: &str, party: &str, expected_code: i32) {
    let mut args = vec!["policy", "approve"];
    args.extend_from_slice(ledger);
    args.extend_from_slice(&["--intent", intent, "--party", party]);
    expect(&args, expected_code);
}

#[track_caller]
fn window_spend(ledger: &[&str]) -> String {
    let mut args = vec!["policy", "status", "--json"];
    args.extend_from_slice(ledger);
    json_member(&expect(&args, 0), "window_spend")
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
        "quorum",
        "aggregate",
        "verify-agg",
        "verify-aggregate",
        "cred",
        "hd",
        "migrate",
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
        "fts-compact-1122",
        "\"signature_bytes\": 1122",
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
    keygen(&dir, "fts-frontier-2338", &[]);
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

// The dealerless height-3 ceremony behind `fts-threshold` takes hours (measured: ~294 OT wire
// messages/s against ~4.6 million OT calls per keygen), so this runs only against a trusted-dealer
// binary: `cargo test --release -p qsag-cli --features test-dealer --test cli_smoke threshold_few_time`.
#[cfg(feature = "test-dealer")]
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

    // `policy` without a subcommand is the same stateless evaluation: it writes nothing,
    // not even under the temporary directory, and it does not take a ledger directory.
    let scratch = dir_for_tmp("stateless-policy");
    for args in [
        &["policy", "--json"][..],
        &["policy", "--ephemeral", "--json"],
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_qsag"))
            .args(args)
            .env("TMPDIR", &scratch)
            .output()
            .unwrap();
        assert_eq!(code(&output), 0);
        assert_eq!(String::from_utf8(output.stdout).unwrap(), demo);
        assert_eq!(std::fs::read_dir(&scratch).unwrap().count(), 0);
    }
    std::fs::remove_dir_all(&scratch).unwrap();
    expect(&["policy", "--scenario", "expired"], 3);
    expect(&["policy", "--ledger-dir", "anywhere"], 1);
    expect(&["policy", "--ephemeral", "--ledger-dir", "anywhere"], 1);
    for verb in ["init", "propose", "approve", "status"] {
        assert!(expect(&["policy", verb, "--help"], 0).contains("--ledger-dir"));
    }

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
    keygen(&dir, "fts-compact-1122", &[]);
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
    keygen(&dir, "fts-compact-1122", &[]);
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
            "fts-compact-1122",
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
            "fts-compact-1122",
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
    keygen(&dir, "fts-compact-1122", &[]);
    expect(
        &[
            "keygen",
            "--scheme",
            "fts-compact-1122",
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
    keygen(&dir, "fts-compact-1122", &[]);
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

#[cfg(unix)]
fn snapshot_dir_files(dir: &Path) -> Vec<(PathBuf, Vec<u8>)> {
    let mut out = Vec::new();
    for entry in std::fs::read_dir(dir).unwrap() {
        let p = entry.unwrap().path();
        if p.is_dir() {
            out.extend(snapshot_dir_files(&p));
        } else {
            out.push((p.clone(), std::fs::read(&p).unwrap()));
        }
    }
    out
}

#[cfg(unix)]
fn restore_dir_files_in_place(snapshot: &[(PathBuf, Vec<u8>)]) {
    use std::io::Write;
    for (p, bytes) in snapshot {
        let mut f = std::fs::OpenOptions::new()
            .write(true)
            .truncate(true)
            .open(p)
            .unwrap();
        f.write_all(bytes).unwrap();
        f.sync_all().unwrap();
    }
}

#[cfg(unix)]
#[test]
fn external_anchor_isolation_and_full_vault_snapshot_rollback_refused() {
    use std::os::unix::fs::DirBuilderExt;
    let dir = Workdir::new("external-anchor-e2e");
    let vault = dir.0.join("vault");
    let anchor = dir.0.join("anchor");
    std::fs::DirBuilder::new()
        .mode(0o700)
        .create(&vault)
        .unwrap();
    std::fs::DirBuilder::new()
        .mode(0o700)
        .create(&anchor)
        .unwrap();
    let vault_s = vault.to_str().unwrap();
    let anchor_s = anchor.to_str().unwrap();
    let sk = vault.join("sk");
    let sk_s = sk.to_str().unwrap();
    let pk = dir.path("pk");

    // 1. `--anchor-dir` equal to `--vault-dir` is refused even with `--allow-single-disk-anchor`.
    expect(
        &[
            "keygen",
            "--scheme",
            "fts-frontier-2338",
            "--secret-out",
            sk_s,
            "--public-out",
            &pk,
            "--anchor-dir",
            vault_s,
            "--vault-dir",
            vault_s,
            "--allow-single-disk-anchor",
        ],
        4,
    );

    // 2. Nested `--anchor-dir` inside `--vault-dir` is refused.
    let nested = vault.join("nested-anchor");
    expect(
        &[
            "keygen",
            "--scheme",
            "fts-frontier-2338",
            "--secret-out",
            sk_s,
            "--public-out",
            &pk,
            "--anchor-dir",
            nested.to_str().unwrap(),
            "--vault-dir",
            vault_s,
            "--allow-single-disk-anchor",
        ],
        4,
    );

    // 3. Same-device `--anchor-dir` without `--allow-single-disk-anchor` is refused.
    expect(
        &[
            "keygen",
            "--scheme",
            "fts-frontier-2338",
            "--secret-out",
            sk_s,
            "--public-out",
            &pk,
            "--anchor-dir",
            anchor_s,
            "--vault-dir",
            vault_s,
        ],
        4,
    );

    // 4. Proper enrollment with `--allow-single-disk-anchor` succeeds.
    expect(
        &[
            "keygen",
            "--scheme",
            "fts-frontier-2338",
            "--secret-out",
            sk_s,
            "--public-out",
            &pk,
            "--anchor-dir",
            anchor_s,
            "--vault-dir",
            vault_s,
            "--allow-single-disk-anchor",
        ],
        0,
    );
    let genesis_snapshot = snapshot_dir_files(&vault);

    // 5. Omitting `--anchor-dir` on an anchored key fails closed with exit 4.
    expect(
        &[
            "sign",
            "--secret",
            sk_s,
            "--in",
            &dir.path("msg"),
            "--out",
            &dir.path("no-anchor.sig"),
        ],
        4,
    );

    // 6. Anchored signing with CeremonyContext flags (`--policy-id-hex`, `--spend-amount`) succeeds.
    let policy_hex = "ab".repeat(32);
    expect(
        &[
            "sign",
            "--secret",
            sk_s,
            "--in",
            &dir.path("msg"),
            "--out",
            &dir.path("sig1"),
            "--anchor-dir",
            anchor_s,
            "--vault-dir",
            vault_s,
            "--allow-single-disk-anchor",
            "--policy-id-hex",
            &policy_hex,
            "--spend-amount",
            "125000",
        ],
        0,
    );
    expect(
        &[
            "verify",
            "--public",
            &pk,
            "--in",
            &dir.path("msg"),
            "--sig",
            &dir.path("sig1"),
        ],
        0,
    );

    // 7. Full in-place block/inode-preserving rollback of `--vault-dir` is refused by `--anchor-dir`!
    restore_dir_files_in_place(&genesis_snapshot);
    expect(
        &[
            "sign",
            "--secret",
            sk_s,
            "--in",
            &dir.path("other"),
            "--out",
            &dir.path("rolled-back.sig"),
            "--anchor-dir",
            anchor_s,
            "--vault-dir",
            vault_s,
            "--allow-single-disk-anchor",
        ],
        4,
    );
    assert!(!dir.0.join("rolled-back.sig").exists());
}

#[cfg(unix)]
#[test]
fn quorum_jorts_2of3_ceremony_context_retry_and_snapshot_rollback() {
    use std::os::unix::fs::DirBuilderExt;
    let dir = Workdir::new("quorum-jorts-e2e");
    let vault = dir.0.join("quorum-vault");
    let anchor = dir.0.join("quorum-anchor");
    std::fs::DirBuilder::new()
        .mode(0o700)
        .create(&vault)
        .unwrap();
    std::fs::DirBuilder::new()
        .mode(0o700)
        .create(&anchor)
        .unwrap();
    let vault_s = vault.to_str().unwrap();
    let anchor_s = anchor.to_str().unwrap();
    let pk = dir.path("quorum.pk");
    let msg = dir.path("msg");
    let other = dir.path("other");
    let policy_a = "11".repeat(32);
    let policy_b = "22".repeat(32);

    // Same-inode `--anchor-dir == --vault-dir` refused on `quorum keygen`.
    expect(
        &[
            "quorum",
            "keygen",
            "--vault-dir",
            vault_s,
            "--public-out",
            &pk,
            "--tree-height",
            "2",
            "--anchor-dir",
            vault_s,
            "--allow-single-disk-anchor",
        ],
        4,
    );

    let keygen_out = expect(
        &[
            "quorum",
            "keygen",
            "--vault-dir",
            vault_s,
            "--public-out",
            &pk,
            "--tree-height",
            "2",
            "--anchor-dir",
            anchor_s,
            "--allow-single-disk-anchor",
            "--json",
        ],
        0,
    );
    assert!(keygen_out.contains("jorts-2of3-sha3"));
    let genesis_snapshot = snapshot_dir_files(&vault);

    // Sign epoch 0 with CeremonyContext (`policy_a`, spend `50000`).
    let sig0 = dir.path("sig0.json");
    expect(
        &[
            "quorum",
            "sign",
            "--vault-dir",
            vault_s,
            "--epoch",
            "0",
            "--in",
            &msg,
            "--out",
            &sig0,
            "--anchor-dir",
            anchor_s,
            "--allow-single-disk-anchor",
            "--policy-id-hex",
            &policy_a,
            "--spend-amount",
            "50000",
            "--json",
        ],
        0,
    );
    assert!(
        expect(
            &[
                "quorum", "verify", "--public", &pk, "--in", &msg, "--sig", &sig0, "--json"
            ],
            0
        )
        .contains("\"valid\": true")
    );
    expect(
        &[
            "quorum", "verify", "--public", &pk, "--in", &other, "--sig", &sig0,
        ],
        2,
    );

    // Re-signing epoch 0 without `--retry` is refused.
    expect(
        &[
            "quorum",
            "sign",
            "--vault-dir",
            vault_s,
            "--epoch",
            "0",
            "--in",
            &msg,
            "--out",
            &dir.path("dup0.json"),
            "--anchor-dir",
            anchor_s,
            "--allow-single-disk-anchor",
            "--policy-id-hex",
            &policy_a,
            "--spend-amount",
            "50000",
        ],
        4,
    );

    // `--retry` with altered policy, altered spend, or altered message is refused!
    expect(
        &[
            "quorum",
            "sign",
            "--vault-dir",
            vault_s,
            "--epoch",
            "0",
            "--in",
            &msg,
            "--out",
            &dir.path("bad-policy.json"),
            "--anchor-dir",
            anchor_s,
            "--allow-single-disk-anchor",
            "--policy-id-hex",
            &policy_b,
            "--spend-amount",
            "50000",
            "--retry",
        ],
        4,
    );
    expect(
        &[
            "quorum",
            "sign",
            "--vault-dir",
            vault_s,
            "--epoch",
            "0",
            "--in",
            &other,
            "--out",
            &dir.path("bad-msg.json"),
            "--anchor-dir",
            anchor_s,
            "--allow-single-disk-anchor",
            "--policy-id-hex",
            &policy_a,
            "--spend-amount",
            "50000",
            "--retry",
        ],
        4,
    );

    // Idempotent `--retry` with the exact persisted `(epoch 0, msg, policy_a, 50000)` succeeds
    // and replays the identical latched signature!
    let retry0 = dir.path("retry0.json");
    expect(
        &[
            "quorum",
            "sign",
            "--vault-dir",
            vault_s,
            "--epoch",
            "0",
            "--in",
            &msg,
            "--out",
            &retry0,
            "--anchor-dir",
            anchor_s,
            "--allow-single-disk-anchor",
            "--policy-id-hex",
            &policy_a,
            "--spend-amount",
            "50000",
            "--retry",
        ],
        0,
    );
    assert_eq!(dir.read("sig0.json"), dir.read("retry0.json"));

    // Advance to epoch 1: epoch 0 is now permanently consumed even under `--retry`.
    let sig1 = dir.path("sig1.json");
    expect(
        &[
            "quorum",
            "sign",
            "--vault-dir",
            vault_s,
            "--epoch",
            "1",
            "--in",
            &other,
            "--out",
            &sig1,
            "--anchor-dir",
            anchor_s,
            "--allow-single-disk-anchor",
            "--policy-id-hex",
            &policy_b,
            "--spend-amount",
            "75000",
        ],
        0,
    );
    expect(
        &[
            "quorum", "verify", "--public", &pk, "--in", &other, "--sig", &sig1,
        ],
        0,
    );
    expect(
        &[
            "quorum",
            "sign",
            "--vault-dir",
            vault_s,
            "--epoch",
            "0",
            "--in",
            &msg,
            "--out",
            &dir.path("consumed0.json"),
            "--anchor-dir",
            anchor_s,
            "--allow-single-disk-anchor",
            "--policy-id-hex",
            &policy_a,
            "--spend-amount",
            "50000",
            "--retry",
        ],
        4,
    );

    // Full in-place snapshot restore of all 3 party vaults + belt WALs + ceremony journals
    // back to genesis is caught and refused by `--anchor-dir`!
    restore_dir_files_in_place(&genesis_snapshot);
    expect(
        &[
            "quorum",
            "sign",
            "--vault-dir",
            vault_s,
            "--epoch",
            "0",
            "--in",
            &other,
            "--out",
            &dir.path("forged-rollback.json"),
            "--anchor-dir",
            anchor_s,
            "--allow-single-disk-anchor",
        ],
        4,
    );
    assert!(!dir.0.join("forged-rollback.json").exists());
}

#[cfg(unix)]
#[test]
fn anchored_committee_aggregate_rejects_full_snapshot_rollback() {
    use std::os::unix::fs::DirBuilderExt;
    let dir = Workdir::new("anchored-agg-e2e");
    let vault = dir.0.join("agg-vault");
    let anchor = dir.0.join("agg-anchor");
    std::fs::DirBuilder::new()
        .mode(0o700)
        .create(&vault)
        .unwrap();
    std::fs::DirBuilder::new()
        .mode(0o700)
        .create(&anchor)
        .unwrap();
    let vault_s = vault.to_str().unwrap();
    let anchor_s = anchor.to_str().unwrap();
    let wal = vault.join("wals");
    let wal_s = wal.to_str().unwrap();
    let sk = vault.join("committee.sk");
    let sk_s = sk.to_str().unwrap();
    let pk = dir.path("committee.pk");

    expect(
        &[
            "keygen",
            "--scheme",
            "agg-jorts-poseidon2",
            "--seed-file",
            &dir.path("seed"),
            "--secret-out",
            sk_s,
            "--public-out",
            &pk,
            "--validators",
            "4",
            "--wal-dir",
            wal_s,
            "--anchor-dir",
            anchor_s,
            "--vault-dir",
            vault_s,
            "--allow-single-disk-anchor",
        ],
        0,
    );
    let genesis_snapshot = snapshot_dir_files(&vault);

    let proof1 = dir.path("proof1.json");
    expect(
        &[
            "aggregate",
            "--secret",
            sk_s,
            "--signers",
            "0,2",
            "--epoch",
            "0",
            "--wal-dir",
            wal_s,
            "--in",
            &dir.path("msg"),
            "--out",
            &proof1,
            "--anchor-dir",
            anchor_s,
            "--vault-dir",
            vault_s,
            "--allow-single-disk-anchor",
            "--policy-id-hex",
            &"cc".repeat(32),
            "--spend-amount",
            "42000",
            "--deterministic",
        ],
        0,
    );
    expect(
        &[
            "verify-agg",
            "--public",
            &pk,
            "--in",
            &dir.path("msg"),
            "--proof",
            &proof1,
        ],
        0,
    );

    // Restore committee secret + ceremony journal + validator WALs in-place and attempt equivocation!
    restore_dir_files_in_place(&genesis_snapshot);
    expect(
        &[
            "aggregate",
            "--secret",
            sk_s,
            "--signers",
            "0,2",
            "--epoch",
            "0",
            "--wal-dir",
            wal_s,
            "--in",
            &dir.path("other"),
            "--out",
            &dir.path("equivocated.json"),
            "--anchor-dir",
            anchor_s,
            "--vault-dir",
            vault_s,
            "--allow-single-disk-anchor",
            "--deterministic",
        ],
        4,
    );
    assert!(!dir.0.join("equivocated.json").exists());
}

#[cfg(unix)]
#[test]
fn policy_ledger_gates_stateless_signing_across_invocations() {
    let dir = Workdir::new("policy-ledger-slh");
    let scheme = "slh-dsa-shake-128f";
    let (payload, msg) = (dir.path("msg"), dir.path("msg"));
    // A recipient to allowlist and a stranger, both with addresses of the pinned suite.
    for name in ["recipient", "stranger"] {
        expect(
            &[
                "keygen",
                "--scheme",
                scheme,
                "--secret-out",
                &dir.path(&format!("{name}.sk")),
                "--public-out",
                &dir.path(&format!("{name}.pk")),
            ],
            0,
        );
    }
    let recipient = json_member(&dir.read("recipient.pk"), "address");
    let stranger = json_member(&dir.read("stranger.pk"), "address");
    let policy = write_policy(&dir, "SlhDsa128f", &recipient);
    let ledger_dir = dir.path("ledger");
    let ledger = ["--ledger-dir", ledger_dir.as_str()];

    // Creating a ledger needs the custody acknowledgement, and never reuses a directory.
    expect(
        &[
            "policy",
            "init",
            "--ledger-dir",
            &ledger_dir,
            "--policy",
            &policy,
        ],
        1,
    );
    assert!(!Path::new(&ledger_dir).exists());
    let created = expect(
        &[
            "policy",
            "init",
            "--ledger-dir",
            &ledger_dir,
            "--policy",
            &policy,
            "--accept-single-host-custody",
            "--json",
        ],
        0,
    );
    let ledger_id = json_member(&created, "ledger_id");
    assert!(created.contains("single-host guard committee"));
    expect(
        &[
            "policy",
            "init",
            "--ledger-dir",
            &ledger_dir,
            "--policy",
            &policy,
            "--accept-single-host-custody",
        ],
        4,
    );
    assert_eq!(window_spend(&ledger), "0");

    // A key enrolled against the ledger refuses to sign outside its gate.
    let (sk, pk) = (dir.path("sk"), dir.path("pk"));
    expect(
        &[
            "keygen",
            "--scheme",
            scheme,
            "--secret-out",
            &sk,
            "--public-out",
            &pk,
            "--policy-ledger-dir",
            &ledger_dir,
        ],
        0,
    );
    assert_eq!(json_member(&dir.read("sk"), "policy_ledger_id"), ledger_id);
    let plain = dir.path("plain.sig");
    expect(&["sign", "--secret", &sk, "--in", &msg, "--out", &plain], 4);
    expect(
        &[
            "sign",
            "--secret",
            &sk,
            "--in",
            &msg,
            "--out",
            &plain,
            "--policy-ledger-dir",
            &ledger_dir,
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
            &plain,
            "--policy-intent",
            &"00".repeat(32),
        ],
        1,
    );

    // Proposals the policy refuses are never recorded.
    let refused = |recipient: &str, amount: &str, initiator: &str, approvers: &str| {
        expect(
            &[
                "policy",
                "propose",
                "--ledger-dir",
                &ledger_dir,
                "--public",
                &pk,
                "--payload",
                &payload,
                "--recipient",
                recipient,
                "--amount",
                amount,
                "--initiator",
                initiator,
                "--approvers",
                approvers,
                "--message-out",
                &dir.path("refused.msg"),
            ],
            3,
        );
        assert!(!Path::new(&dir.path("refused.msg")).exists());
    };
    refused(&stranger, "800", "1", "2,3");
    refused(&recipient, "1001", "1", "2,3");
    refused(&recipient, "800", "2", "2,3");
    refused(&recipient, "800", "3", "1,2");
    assert_eq!(
        std::fs::read_dir(Path::new(&ledger_dir).join("intents"))
            .unwrap()
            .count(),
        0
    );

    let intent_msg = dir.path("intent1.msg");
    let intent = propose(&ledger, &pk, &payload, &recipient, "800", &intent_msg);
    let gated = |input: &str, out: &str, extra: &[&str], expected: i32| {
        let mut args = vec![
            "sign",
            "--secret",
            &sk,
            "--in",
            input,
            "--out",
            out,
            "--policy-ledger-dir",
            &ledger_dir,
            "--policy-intent",
            &intent,
        ];
        args.extend_from_slice(extra);
        let stdout = expect(&args, expected);
        assert_eq!(Path::new(out).exists(), expected == 0, "{out}");
        stdout
    };
    let sig = dir.path("intent1.sig");

    // Unapproved, then half approved: refused in separate invocations, nothing spent.
    gated(&intent_msg, &sig, &[], 3);
    approve(&ledger, &intent, "2", 0);
    gated(&intent_msg, &sig, &[], 3);
    approve(&ledger, &intent, "1", 3);
    approve(&ledger, &intent, "3", 0);
    // Fully approved, but for another message, another context, or with a caller-chosen spend.
    gated(&msg, &sig, &[], 3);
    gated(&intent_msg, &sig, &["--ctx-hex", "aa"], 3);
    assert_eq!(window_spend(&ledger), "0");

    let signed = gated(&intent_msg, &sig, &["--json"], 0);
    assert_eq!(json_member(&signed, "policy_intent"), intent);
    assert_eq!(json_member(&signed, "policy_ledger_id"), ledger_id);
    assert_eq!(json_member(&signed, "spend_amount"), "800");
    expect(
        &[
            "verify",
            "--public",
            &pk,
            "--in",
            &intent_msg,
            "--sig",
            &sig,
        ],
        0,
    );
    assert_eq!(window_spend(&ledger), "800");

    // Replay in a later invocation is refused; an explicit retry re-signs without spending.
    let replay = dir.path("replay.sig");
    gated(&intent_msg, &replay, &[], 3);
    approve(&ledger, &intent, "2", 3);
    gated(&msg, &replay, &["--policy-retry"], 3);
    gated(&intent_msg, &replay, &["--policy-retry"], 0);
    assert_eq!(window_spend(&ledger), "800");

    // The window cap is cumulative across invocations: 800 + 800 is refused, 800 + 700 fits
    // exactly, and then not one unit more.
    refused(&recipient, "800", "1", "2,3");
    let second_msg = dir.path("intent2.msg");
    let second = propose(&ledger, &pk, &payload, &recipient, "700", &second_msg);
    approve(&ledger, &second, "2", 0);
    approve(&ledger, &second, "3", 0);
    let checkpoint = Path::new(&ledger_dir).join("guards").join("committee.ckpt");
    let before_second = std::fs::read(&checkpoint).unwrap();
    let second_sig = dir.path("intent2.sig");
    expect(
        &[
            "sign",
            "--secret",
            &sk,
            "--in",
            &second_msg,
            "--out",
            &second_sig,
            "--policy-ledger-dir",
            &ledger_dir,
            "--policy-intent",
            &second,
        ],
        0,
    );
    assert_eq!(window_spend(&ledger), "1500");
    refused(&recipient, "1", "1", "2,3");

    // Putting the pre-spend checkpoint back does not reopen the window: the generation fence
    // has moved, so the ledger is refused outright until its real state returns.
    let after_second = std::fs::read(&checkpoint).unwrap();
    std::fs::write(&checkpoint, &before_second).unwrap();
    expect(&["policy", "status", "--ledger-dir", &ledger_dir], 4);
    expect(
        &[
            "sign",
            "--secret",
            &sk,
            "--in",
            &second_msg,
            "--out",
            &dir.path("rolled.sig"),
            "--policy-ledger-dir",
            &ledger_dir,
            "--policy-intent",
            &second,
        ],
        4,
    );
    assert!(!Path::new(&dir.path("rolled.sig")).exists());
    std::fs::write(&checkpoint, &after_second).unwrap();
    assert_eq!(window_spend(&ledger), "1500");
    let status = expect(
        &["policy", "status", "--ledger-dir", &ledger_dir, "--json"],
        0,
    );
    assert_eq!(status.matches("\"state\": \"released\"").count(), 2);
}

#[cfg(unix)]
#[test]
fn anchored_policy_ledger_gates_stateful_signing_and_refuses_ledger_rollback() {
    use std::os::unix::fs::DirBuilderExt;
    let dir = Workdir::new("policy-ledger-frontier");
    let anchor = dir.0.join("ledger-anchor");
    std::fs::DirBuilder::new()
        .mode(0o700)
        .create(&anchor)
        .unwrap();
    let anchor_s = anchor.to_str().unwrap();
    let ledger_dir = dir.path("ledger");
    let (sk, pk, payload) = (dir.path("sk"), dir.path("pk"), dir.path("msg"));

    // The ledger must exist before a key can be enrolled against it; the first key is the
    // allowlisted recipient, the second is the gated signer.
    expect(
        &[
            "keygen",
            "--scheme",
            "fts-frontier-2338",
            "--secret-out",
            &dir.path("recipient.sk"),
            "--public-out",
            &dir.path("recipient.pk"),
        ],
        0,
    );
    let recipient = json_member(&dir.read("recipient.pk"), "address");
    let policy = write_policy(&dir, "FrontierSumFts", &recipient);
    // An anchor inside the ledger directory, or on its device without the acknowledgement,
    // is refused and leaves nothing behind.
    let nested = Path::new(&ledger_dir).join("anchor");
    for (anchor_dir, flags) in [
        (
            nested.to_str().unwrap(),
            &["--allow-single-disk-anchor"][..],
        ),
        (anchor_s, &[][..]),
    ] {
        let mut args = vec![
            "policy",
            "init",
            "--ledger-dir",
            &ledger_dir,
            "--policy",
            &policy,
            "--accept-single-host-custody",
            "--anchor-dir",
            anchor_dir,
        ];
        args.extend_from_slice(flags);
        expect(&args, 4);
        let _ = std::fs::remove_dir_all(&ledger_dir);
    }
    expect(
        &[
            "policy",
            "init",
            "--ledger-dir",
            &ledger_dir,
            "--policy",
            &policy,
            "--accept-single-host-custody",
            "--anchor-dir",
            anchor_s,
            "--allow-single-disk-anchor",
        ],
        0,
    );
    let ledger = [
        "--ledger-dir",
        ledger_dir.as_str(),
        "--anchor-dir",
        anchor_s,
        "--allow-single-disk-anchor",
    ];
    let gate = [
        "--policy-ledger-dir",
        ledger_dir.as_str(),
        "--policy-anchor-dir",
        anchor_s,
        "--policy-allow-single-disk-anchor",
    ];
    // An anchored ledger does not open without its anchor.
    expect(&["policy", "status", "--ledger-dir", &ledger_dir], 4);
    assert_eq!(window_spend(&ledger), "0");

    let mut keygen = vec![
        "keygen",
        "--scheme",
        "fts-frontier-2338",
        "--secret-out",
        &sk,
        "--public-out",
        &pk,
    ];
    keygen.extend_from_slice(&gate);
    expect(&keygen, 0);
    expect(
        &[
            "keygen",
            "--scheme",
            "fts-frontier-2338",
            "--secret-out",
            &dir.path("x.sk"),
            "--public-out",
            &dir.path("x.pk"),
            "--policy-ledger-dir",
            &ledger_dir,
        ],
        4,
    );

    let intent_msg = dir.path("intent.msg");
    let intent = propose(&ledger, &pk, &payload, &recipient, "900", &intent_msg);
    let sign = |out: &str, extra: &[&str], expected: i32| {
        let mut args = vec!["sign", "--secret", &sk, "--in", &intent_msg, "--out", out];
        args.extend_from_slice(&gate);
        args.extend_from_slice(&["--policy-intent", &intent]);
        args.extend_from_slice(extra);
        expect(&args, expected)
    };
    let sig = dir.path("intent.sig");

    // Refusals leave the few-time key untouched: no use is burned for an unapproved intent.
    sign(&sig, &[], 3);
    sign(&sig, &["--spend-amount", "1"], 1);
    assert!(dir.read("sk").contains("\"uses_completed\": 0"));
    approve(&ledger, &intent, "2", 0);
    approve(&ledger, &intent, "3", 0);
    let ledger_before = snapshot_dir_files(Path::new(&ledger_dir));
    let key_before = dir.read("sk");

    let signed = sign(&sig, &["--json"], 0);
    assert_eq!(json_member(&signed, "spend_amount"), "900");
    assert_eq!(json_member(&signed, "policy_intent"), intent);
    assert!(dir.read("sk").contains("\"uses_completed\": 1"));
    expect(
        &[
            "verify",
            "--public",
            &pk,
            "--in",
            &intent_msg,
            "--sig",
            &sig,
        ],
        0,
    );
    assert_eq!(window_spend(&ledger), "900");
    // This PQ profile has one signing slot. Exhaustion refuses the retry before
    // policy authorization, and cannot charge the already-spent intent again.
    sign(&dir.path("replay.sig"), &[], 4);
    assert!(!Path::new(&dir.path("replay.sig")).exists());
    assert_eq!(window_spend(&ledger), "900");
    assert!(dir.read("sk").contains("\"uses_completed\": 1"));

    // Restore every file of the ledger directory to its approved-but-unspent state, in
    // place. The external anchor has seen the newer generation: status and signing are
    // refused, and the key does not move.
    let ledger_after = snapshot_dir_files(Path::new(&ledger_dir));
    restore_dir_files_in_place(&ledger_before);
    let mut status = vec!["policy", "status"];
    status.extend_from_slice(&ledger);
    expect(&status, 4);
    sign(&dir.path("rollback.sig"), &[], 4);
    assert!(!Path::new(&dir.path("rollback.sig")).exists());
    assert!(dir.read("sk").contains("\"uses_completed\": 1"));
    assert_ne!(dir.read("sk"), key_before);

    // With its real state back the ledger opens again; the signing slot remains spent.
    restore_dir_files_in_place(&ledger_after);
    assert_eq!(window_spend(&ledger), "900");
    // This PQ profile has one signing slot. Exhaustion refuses the retry before
    // policy authorization, and cannot charge the already-spent intent again.
    sign(&dir.path("replay.sig"), &[], 4);
    assert!(!Path::new(&dir.path("replay.sig")).exists());
    assert_eq!(window_spend(&ledger), "900");
    // A second transfer that would pass the window cap is refused at proposal.
    let mut over = vec!["policy", "propose"];
    over.extend_from_slice(&ledger);
    let over_msg = dir.path("over.msg");
    over.extend_from_slice(&[
        "--public",
        &pk,
        "--payload",
        &payload,
        "--recipient",
        &recipient,
        "--amount",
        "601",
        "--initiator",
        "1",
        "--approvers",
        "2,3",
        "--message-out",
        &over_msg,
    ]);
    expect(&over, 3);
}

#[cfg(unix)]
#[test]
fn policy_ledger_gates_quorum_signing_before_any_epoch_is_latched() {
    use std::os::unix::fs::DirBuilderExt;
    let dir = Workdir::new("policy-ledger-quorum");
    let vault = dir.0.join("quorum-vault");
    std::fs::DirBuilder::new()
        .mode(0o700)
        .create(&vault)
        .unwrap();
    let vault_s = vault.to_str().unwrap();
    let (pk, payload) = (dir.path("quorum.pk"), dir.path("msg"));
    expect(
        &[
            "keygen",
            "--scheme",
            "slh-dsa-shake-128f",
            "--secret-out",
            &dir.path("recipient.sk"),
            "--public-out",
            &dir.path("recipient.pk"),
        ],
        0,
    );
    let recipient = json_member(&dir.read("recipient.pk"), "address");
    let policy = write_policy(&dir, "SlhDsa128f", &recipient);
    let ledger_dir = dir.path("ledger");
    let ledger = ["--ledger-dir", ledger_dir.as_str()];
    expect(
        &[
            "policy",
            "init",
            "--ledger-dir",
            &ledger_dir,
            "--policy",
            &policy,
            "--accept-single-host-custody",
        ],
        0,
    );
    expect(
        &[
            "quorum",
            "keygen",
            "--vault-dir",
            vault_s,
            "--public-out",
            &pk,
            "--tree-height",
            "2",
            "--policy-ledger-dir",
            &ledger_dir,
        ],
        0,
    );
    let intent_msg = dir.path("intent.msg");
    let intent = propose(&ledger, &pk, &payload, &recipient, "1000", &intent_msg);
    let sign = |epoch: &str, input: &str, out: &str, extra: &[&str], expected: i32| {
        let mut args = vec![
            "quorum",
            "sign",
            "--vault-dir",
            vault_s,
            "--epoch",
            epoch,
            "--in",
            input,
            "--out",
            out,
        ];
        args.extend_from_slice(extra);
        expect(&args, expected)
    };
    let gate = [
        "--policy-ledger-dir",
        ledger_dir.as_str(),
        "--policy-intent",
        intent.as_str(),
    ];
    let vault_before = snapshot_dir_files(&vault);
    let sig = dir.path("quorum.sig");

    // Outside the gate, unapproved, wrong message, caller-chosen context: all refused, and
    // not one byte of any party's vault, belt or ceremony journal moves.
    sign("0", &intent_msg, &sig, &[], 4);
    sign("0", &intent_msg, &sig, &gate, 3);
    approve(&ledger, &intent, "2", 0);
    approve(&ledger, &intent, "3", 0);
    sign("0", &payload, &sig, &gate, 3);
    sign(
        "0",
        &intent_msg,
        &sig,
        &[&gate[..], &["--policy-id-hex", &"11".repeat(32)]].concat(),
        1,
    );
    assert!(!Path::new(&sig).exists());
    assert_eq!(snapshot_dir_files(&vault), vault_before);
    assert_eq!(window_spend(&ledger), "0");

    let signed = sign("0", &intent_msg, &sig, &gate, 0);
    assert!(signed.contains("signed quorum epoch 0"));
    let sig_text = dir.read("quorum.sig");
    assert_eq!(json_member(&sig_text, "policy_intent"), intent);
    assert_eq!(json_member(&sig_text, "spend_amount"), "1000");
    expect(
        &[
            "quorum",
            "verify",
            "--public",
            &pk,
            "--in",
            &intent_msg,
            "--sig",
            &sig,
        ],
        0,
    );
    assert_eq!(window_spend(&ledger), "1000");

    // The released intent does not unlock another epoch, and the refusal burns none.
    let vault_after = snapshot_dir_files(&vault);
    let again = dir.path("again.sig");
    sign("1", &intent_msg, &again, &gate, 3);
    assert_eq!(snapshot_dir_files(&vault), vault_after);
    sign(
        "1",
        &intent_msg,
        &again,
        &[&gate[..], &["--policy-retry"]].concat(),
        0,
    );
    expect(
        &[
            "quorum",
            "verify",
            "--public",
            &pk,
            "--in",
            &intent_msg,
            "--sig",
            &again,
        ],
        0,
    );
    assert_eq!(window_spend(&ledger), "1000");
}

#[test]
fn e2e_hem_quorum_switch_2of3_to_3of5_and_untrusted_public_aggregate() {
    let dir = Workdir::new("hem-quorum-agg");
    let (msg, other, seed0, seed1) = (
        dir.path("msg"),
        dir.path("other"),
        dir.path("seed"),
        dir.path("seed1"),
    );
    std::fs::write(
        &seed1,
        "ffeeddccbbaa99887766554433221100ffeeddccbbaa99887766554433221100",
    )
    .unwrap();

    // Validator 0: (2, 3) Hem-compatible threshold quorum -> sign epoch 0 -> switch to (3, 5)
    // under the EXACT same 65-byte validator public key -> proactive refresh -> sign epoch 1!
    let v0_epoch0 = dir.path("v0-2of3");
    let v0_epoch1 = dir.path("v0-3of5");
    let pk0 = dir.path("v0.pk");
    let pk0_after = dir.path("v0-after.pk");
    let v0_sig_early = dir.path("v0-early.sig");
    let v0_sig_consensus = dir.path("v0-consensus.sig");
    let v0_sig_bad = dir.path("v0-bad.sig");

    expect(
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
            "4",
            "--seed-file",
            &seed0,
            "--vault-dir",
            &v0_epoch0,
            "--public-out",
            &pk0,
        ],
        0,
    );
    let pk0_hex_before = json_member(&dir.read("v0.pk"), "validator_public_key");
    let original_latch_seed = json_member(&dir.read("v0-2of3/quorum-meta.json"), "latch_seed");

    expect(
        &[
            "quorum",
            "sign",
            "--vault-dir",
            &v0_epoch0,
            "--signers",
            "0,2",
            "--message",
            &other,
            "--out",
            &v0_sig_early,
        ],
        0,
    );
    expect(
        &[
            "quorum",
            "verify",
            "--public",
            &pk0,
            "--in",
            &other,
            "--sig",
            &v0_sig_early,
        ],
        0,
    );

    // Dynamic (2, 3) -> (3, 5) reshare preserving the 65-byte validator public key!
    expect(
        &[
            "quorum",
            "reshare",
            "--vault-dir",
            &v0_epoch0,
            "--signers",
            "1,2",
            "--new-threshold",
            "3",
            "--new-parties",
            "5",
            "--out-vault-dir",
            &v0_epoch1,
            "--public-out",
            &pk0_after,
            "--deterministic",
        ],
        0,
    );
    assert_eq!(
        json_member(&dir.read("v0-after.pk"), "validator_public_key"),
        pk0_hex_before,
        "dynamic (2,3)->(3,5) quorum switch must preserve the exact 65-byte validator pubkey"
    );

    let reshare_latch_seed = json_member(&dir.read("v0-3of5/quorum-meta.json"), "latch_seed");
    assert_ne!(reshare_latch_seed, original_latch_seed);

    // Proactive security: retired (2, 3) vault is wiped & refused (exit 4), and < 3 signers
    // on the new (3, 5) vault cannot sign (exit 4)!
    expect(
        &[
            "quorum",
            "sign",
            "--vault-dir",
            &v0_epoch0,
            "--signers",
            "0,1",
            "--message",
            &msg,
            "--out",
            &v0_sig_bad,
        ],
        4,
    );
    expect(
        &[
            "quorum",
            "sign",
            "--vault-dir",
            &v0_epoch1,
            "--signers",
            "0,4",
            "--message",
            &msg,
            "--out",
            &v0_sig_bad,
        ],
        4,
    );
    assert!(!Path::new(&v0_sig_bad).exists());

    // Proactive refresh on (3, 5) vault, then sign consensus message at monotone leaf 1
    // using custodians {1, 3, 4}, verifiable against the ORIGINAL pk0 file!
    expect(
        &[
            "quorum",
            "refresh",
            "--vault-dir",
            &v0_epoch1,
            "--deterministic",
        ],
        0,
    );
    let refreshed_latch_seed = json_member(&dir.read("v0-3of5/quorum-meta.json"), "latch_seed");
    assert_ne!(
        refreshed_latch_seed, reshare_latch_seed,
        "refresh must rotate persisted latch authority as well as secret shares"
    );
    expect(
        &[
            "quorum",
            "sign",
            "--vault-dir",
            &v0_epoch1,
            "--signers",
            "1,3,4",
            "--message",
            &msg,
            "--out",
            &v0_sig_consensus,
        ],
        0,
    );
    expect(
        &[
            "quorum",
            "verify",
            "--public",
            &pk0,
            "--in",
            &msg,
            "--sig",
            &v0_sig_consensus,
        ],
        0,
    );

    // Validator 1: independent (2, 3) Hem quorum signs the same consensus message!
    let v1_vault = dir.path("v1-2of3");
    let pk1 = dir.path("v1.pk");
    let v1_sig = dir.path("v1-consensus.sig");
    expect(
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
            "4",
            "--seed-file",
            &seed1,
            "--vault-dir",
            &v1_vault,
            "--public-out",
            &pk1,
        ],
        0,
    );
    expect(
        &[
            "quorum",
            "sign",
            "--vault-dir",
            &v1_vault,
            "--signers",
            "0,2",
            "--message",
            &msg,
            "--out",
            &v1_sig,
        ],
        0,
    );

    // Untrusted public aggregator: ZERO --secret and ZERO --wal-dir!
    let pubkeys_arg = format!("{pk0},{pk1}");
    let sigs_arg = format!("{v0_sig_consensus},{v1_sig}");
    let agg_proof = dir.path("quorum-committee.proof");
    expect(
        &[
            "aggregate",
            "--pubkeys",
            &pubkeys_arg,
            "--sigs",
            &sigs_arg,
            "--message",
            &msg,
            "--out",
            &agg_proof,
        ],
        0,
    );
    let verify_out = expect(
        &[
            "verify-aggregate",
            "--pubkeys",
            &pubkeys_arg,
            "--message",
            &msg,
            "--proof",
            &agg_proof,
            "--json",
        ],
        0,
    );
    assert!(verify_out.contains("\"valid\": true"));

    // Wrong message fails verification with exit code 2.
    expect(
        &[
            "verify-aggregate",
            "--pubkeys",
            &pubkeys_arg,
            "--message",
            &other,
            "--proof",
            &agg_proof,
        ],
        2,
    );
}

#[test]
fn e2e_cred_hd_and_migrate_subcommands() {
    let dir = Workdir::new("cred-hd-migrate");
    let (msg, other) = (dir.path("msg"), dir.path("other"));

    // 1. `qsag cred`: (2, 5) TOPRF + dealerless (2, 3) FIPS 204 threshold ML-DSA-44
    let voprf_vault = dir.path("voprf-vault");
    let voprf_pk = dir.path("voprf.pk");
    let voprf_eval0 = dir.path("voprf-0.json");
    let voprf_replay = dir.path("voprf-replay.json");
    expect(
        &[
            "cred",
            "voprf-keygen",
            "--vault-dir",
            &voprf_vault,
            "--public-out",
            &voprf_pk,
            "--deterministic",
        ],
        0,
    );
    expect(
        &[
            "cred",
            "voprf-eval",
            "--vault-dir",
            &voprf_vault,
            "--public",
            &voprf_pk,
            "--counter",
            "0",
            "--in",
            &msg,
            "--out",
            &voprf_eval0,
            "--deterministic",
        ],
        0,
    );
    // Replaying counter 0 must fail closed with STATE_CONFLICT (exit 4).
    expect(
        &[
            "cred",
            "voprf-eval",
            "--vault-dir",
            &voprf_vault,
            "--public",
            &voprf_pk,
            "--counter",
            "0",
            "--in",
            &other,
            "--out",
            &voprf_replay,
        ],
        4,
    );

    let mldsa_vault = dir.path("mldsa-vault");
    let mldsa_pk = dir.path("mldsa.pk");
    let mldsa_sig = dir.path("mldsa.sig");
    let mldsa_replay = dir.path("mldsa-replay.sig");
    expect(
        &[
            "cred",
            "mldsa-keygen",
            "--threshold",
            "2",
            "--parties",
            "3",
            "--level",
            "44",
            "--vault-dir",
            &mldsa_vault,
            "--public-out",
            &mldsa_pk,
            "--deterministic",
        ],
        0,
    );
    expect(
        &[
            "cred",
            "mldsa-sign",
            "--vault-dir",
            &mldsa_vault,
            "--signers",
            "0,1,2",
            "--epoch",
            "0",
            "--in",
            &msg,
            "--out",
            &mldsa_sig,
            "--deterministic",
        ],
        0,
    );
    expect(
        &[
            "cred",
            "mldsa-verify",
            "--public",
            &mldsa_pk,
            "--in",
            &msg,
            "--sig",
            &mldsa_sig,
        ],
        0,
    );
    // Replaying epoch 0 or signing with < 2t - 1 (= 3) signers fails with exit 4.
    expect(
        &[
            "cred",
            "mldsa-sign",
            "--vault-dir",
            &mldsa_vault,
            "--signers",
            "0,1",
            "--epoch",
            "1",
            "--in",
            &msg,
            "--out",
            &mldsa_replay,
        ],
        4,
    );
    expect(
        &[
            "cred",
            "mldsa-sign",
            "--vault-dir",
            &mldsa_vault,
            "--signers",
            "0,1,2",
            "--epoch",
            "0",
            "--in",
            &other,
            "--out",
            &mldsa_replay,
        ],
        4,
    );
    expect(
        &[
            "cred",
            "mldsa-verify",
            "--public",
            &mldsa_pk,
            "--in",
            &other,
            "--sig",
            &mldsa_sig,
        ],
        2,
    );

    // 2. `qsag hd`: (2, 3) dealerless seed ceremony -> 0-round watch-only derive -> threshold recover -> sign
    let hd_vault = dir.path("hd-vault");
    let hd_watch = dir.path("hd-watch.json");
    let hd_child3 = dir.path("hd-child3.json");
    let hd_child3_sk = dir.path("hd-child3.sk");
    let hd_child3_pk = dir.path("hd-child3.pk");
    let hd_child3_sig = dir.path("hd-child3.sig");
    let hd_bad_sk = dir.path("hd-bad.sk");
    expect(
        &[
            "hd",
            "keygen",
            "--threshold",
            "2",
            "--parties",
            "3",
            "--count",
            "8",
            "--vault-dir",
            &hd_vault,
            "--watch-out",
            &hd_watch,
            "--deterministic",
        ],
        0,
    );
    expect(
        &[
            "hd", "derive", "--watch", &hd_watch, "--index", "3", "--out", &hd_child3,
        ],
        0,
    );
    expect(
        &[
            "hd",
            "verify-child",
            "--watch",
            &hd_watch,
            "--proof",
            &hd_child3,
        ],
        0,
    );
    let target_pq_addr = json_member(&dir.read("hd-child3.json"), "address");

    // 1 custodian (< threshold 2) cannot recover the child signing key (exit 4).
    expect(
        &[
            "hd",
            "recover",
            "--vault-dir",
            &hd_vault,
            "--signers",
            "1",
            "--index",
            "3",
            "--proof",
            &hd_child3,
            "--secret-out",
            &hd_bad_sk,
        ],
        4,
    );
    // Custodians {1, 2} recover child #3 into a vault-enrolled SLH-DSA-SHAKE-128f key!
    expect(
        &[
            "hd",
            "recover",
            "--vault-dir",
            &hd_vault,
            "--signers",
            "1,2",
            "--index",
            "3",
            "--proof",
            &hd_child3,
            "--secret-out",
            &hd_child3_sk,
            "--public-out",
            &hd_child3_pk,
        ],
        0,
    );
    expect(
        &[
            "sign",
            "--secret",
            &hd_child3_sk,
            "--in",
            &msg,
            "--out",
            &hd_child3_sig,
            "--deterministic",
        ],
        0,
    );
    expect(
        &[
            "verify",
            "--public",
            &hd_child3_pk,
            "--in",
            &msg,
            "--sig",
            &hd_child3_sig,
        ],
        0,
    );

    // 3. `qsag migrate`: 438-rep ZKBoo classical-to-PQ migration proof to `target_pq_addr`
    let legacy_key = dir.path("legacy-secp.hex");
    std::fs::write(
        &legacy_key,
        "0000000000000000000000000000000000000000000000000000000000000001\n",
    )
    .unwrap();
    let mig_claim = dir.path("mig-claim.json");
    let mig_proof = dir.path("mig.proof");
    expect(
        &[
            "migrate",
            "commit",
            "--kind",
            "btc-taproot",
            "--legacy-secret",
            &legacy_key,
            "--out",
            &mig_claim,
        ],
        0,
    );
    expect(
        &[
            "migrate",
            "prove",
            "--kind",
            "btc-taproot",
            "--legacy-secret",
            &legacy_key,
            "--target",
            &target_pq_addr,
            "--epoch",
            "42",
            "--out",
            &mig_proof,
            "--deterministic",
        ],
        0,
    );
    expect(
        &[
            "migrate",
            "verify",
            "--proof",
            &mig_proof,
            "--target",
            &target_pq_addr,
            "--epoch",
            "42",
        ],
        0,
    );
    // Wrong epoch or tampered proof fails verification with exit code 2.
    expect(
        &["migrate", "verify", "--proof", &mig_proof, "--epoch", "43"],
        2,
    );
    flip_hex_digit(&mig_proof, "zk_proof");
    expect(&["migrate", "verify", "--proof", &mig_proof], 2);
}

#[test]
fn durable_signing_requires_anchor_or_explicit_ephemeral_flag() {
    let dir = Workdir::new("anchor-required-default");
    keygen(&dir, "fts-compact-1122", &[]);
    let secret = dir.path("sk");
    let message = dir.path("msg");
    let signature = dir.path("refused.sig");
    let journal = format!("{secret}.ceremony");
    let before = std::fs::read(&journal).unwrap();
    // Deliberately bypass the ephemeral test command adapter.
    let output = Command::new(env!("CARGO_BIN_EXE_qsag"))
        .args([
            "sign", "--secret", &secret, "--in", &message, "--out", &signature,
        ])
        .output()
        .unwrap();
    assert_eq!(code(&output), 1);
    assert!(String::from_utf8_lossy(&output.stderr).contains("--ephemeral-unanchored"));
    assert!(!Path::new(&signature).exists());
    assert_eq!(std::fs::read(journal).unwrap(), before);

    // Quorum and policy-ledger enrollment refuse the same default before creating anything,
    // and naming an anchor while waiving it is refused as a contradiction.
    let (vault, ledger, anchor) = (dir.path("quorum"), dir.path("ledger"), dir.path("anchor"));
    let quorum_pk = dir.path("quorum.pk");
    let (frontier_sk, frontier_pk) = (dir.path("anchored.sk"), dir.path("anchored.pk"));
    let (hem_vault, cred_vault, hd_vault, hd_watch, biscuit_sk, biscuit_pk) = (
        dir.path("hem-vault"),
        dir.path("cred-vault"),
        dir.path("hd-vault"),
        dir.path("hd.watch"),
        dir.path("biscuit.sk"),
        dir.path("biscuit.pk"),
    );
    let refusals: [&[&str]; 8] = [
        &[
            "quorum",
            "keygen",
            "--vault-dir",
            &vault,
            "--public-out",
            &quorum_pk,
        ],
        &[
            "quorum",
            "keygen",
            "--scheme",
            "hem-jorts-poseidon2",
            "--vault-dir",
            &hem_vault,
            "--public-out",
            &quorum_pk,
        ],
        &[
            "cred",
            "mldsa-keygen",
            "--vault-dir",
            &cred_vault,
            "--public-out",
            &quorum_pk,
            "--allow-unencrypted",
        ],
        &[
            "cred",
            "voprf-keygen",
            "--vault-dir",
            &cred_vault,
            "--public-out",
            &quorum_pk,
            "--allow-unencrypted",
        ],
        &[
            "hd",
            "keygen",
            "--vault-dir",
            &hd_vault,
            "--watch-out",
            &hd_watch,
            "--allow-unencrypted",
        ],
        &[
            "policy",
            "biscuit",
            "keygen",
            "--secret-out",
            &biscuit_sk,
            "--public-out",
            &biscuit_pk,
            "--allow-unencrypted",
        ],
        &[
            "policy",
            "init",
            "--ledger-dir",
            &ledger,
            "--policy",
            &message,
            "--accept-single-host-custody",
        ],
        &[
            "keygen",
            "--scheme",
            "fts-compact-1122",
            "--secret-out",
            &frontier_sk,
            "--public-out",
            &frontier_pk,
            "--anchor-dir",
            &anchor,
            "--allow-single-disk-anchor",
            "--ephemeral-unanchored",
        ],
    ];
    for args in refusals {
        let output = Command::new(env!("CARGO_BIN_EXE_qsag"))
            .args(args)
            .output()
            .unwrap();
        assert_eq!(code(&output), 1, "{args:?}");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains("--ephemeral-unanchored"),
            "{args:?}: {stderr}"
        );
    }
    for created in [
        &vault,
        &hem_vault,
        &cred_vault,
        &hd_vault,
        &ledger,
        &anchor,
        &quorum_pk,
        &frontier_sk,
        &biscuit_sk,
    ] {
        assert!(!Path::new(created).exists(), "{created}");
    }
}

#[test]
fn e2e_policy_macaroon_attenuation_third_party_discharge_and_refusal() {
    let dir = Workdir::new("policy-macaroon");
    let root_key = dir.path("root.mac.key");
    let tp_key = dir.path("tp.mac.key");
    let tok0 = dir.path("tok0.json");
    let tok1 = dir.path("tok1.json");
    let dis_raw = dir.path("dis_raw.json");
    let dis_bound = dir.path("dis_bound.json");
    let audience = &"aa".repeat(32);
    let resource = &"bb".repeat(32);
    let tp_id = &"cc".repeat(32);
    let huge_amount = "100000000000000000000"; // 10^20 > u64::MAX

    expect(
        &[
            "policy",
            "macaroon",
            "keygen",
            "--out",
            &root_key,
            "--allow-unencrypted",
        ],
        0,
    );
    expect(
        &[
            "policy",
            "macaroon",
            "keygen",
            "--out",
            &tp_key,
            "--allow-unencrypted",
        ],
        0,
    );
    expect(
        &[
            "policy",
            "macaroon",
            "issue",
            "--key",
            &root_key,
            "--audience-hex",
            audience,
            "--resource-hex",
            resource,
            "--actions",
            "7",
            "--third-party-hex",
            tp_id,
            "--out",
            &tok0,
        ],
        0,
    );
    // Attenuate offline with a 128-bit max-amount cap (> u64::MAX).
    expect(
        &[
            "policy",
            "macaroon",
            "attenuate",
            "--in",
            &tok0,
            "--max-amount",
            huge_amount,
            "--expires-at",
            "4102444800",
            "--out",
            &tok1,
        ],
        0,
    );
    // Missing third-party discharge is denied (exit 3).
    expect(
        &[
            "policy",
            "macaroon",
            "verify",
            "--key",
            &root_key,
            "--in",
            &tok1,
            "--audience-hex",
            audience,
            "--resource-hex",
            resource,
            "--actions",
            "3",
            "--amount",
            huge_amount,
            "--now",
            "1700000000",
        ],
        3,
    );
    // Issue third-party discharge and verify unbound discharge is rejected (exit 3).
    expect(
        &[
            "policy",
            "macaroon",
            "issue-discharge",
            "--key",
            &tp_key,
            "--id-hex",
            tp_id,
            "--audience-hex",
            audience,
            "--expires-at",
            "4102444800",
            "--out",
            &dis_raw,
        ],
        0,
    );
    expect(
        &[
            "policy",
            "macaroon",
            "verify",
            "--key",
            &root_key,
            "--in",
            &tok1,
            "--audience-hex",
            audience,
            "--resource-hex",
            resource,
            "--actions",
            "3",
            "--amount",
            huge_amount,
            "--now",
            "1700000000",
            "--discharge",
            &dis_raw,
            "--discharge-key",
            &tp_key,
        ],
        3,
    );
    // Bind discharge to tok1 -> verification succeeds!
    expect(
        &[
            "policy",
            "macaroon",
            "bind-discharge",
            "--parent",
            &tok1,
            "--discharge",
            &dis_raw,
            "--out",
            &dis_bound,
        ],
        0,
    );
    expect(
        &[
            "policy",
            "macaroon",
            "verify",
            "--key",
            &root_key,
            "--in",
            &tok1,
            "--audience-hex",
            audience,
            "--resource-hex",
            resource,
            "--actions",
            "3",
            "--amount",
            huge_amount,
            "--now",
            "1700000000",
            "--discharge",
            &dis_bound,
            "--discharge-key",
            &tp_key,
        ],
        0,
    );
    // Spending 1 unit over the u128 max-amount cap is denied (exit 3).
    expect(
        &[
            "policy",
            "macaroon",
            "verify",
            "--key",
            &root_key,
            "--in",
            &tok1,
            "--audience-hex",
            audience,
            "--resource-hex",
            resource,
            "--actions",
            "3",
            "--amount",
            "100000000000000000001",
            "--now",
            "1700000000",
            "--discharge",
            &dis_bound,
            "--discharge-key",
            &tp_key,
        ],
        3,
    );
}

#[cfg(unix)]
#[test]
fn e2e_policy_biscuit_anchored_mint_attenuate_step_retirement_seal_and_rollback() {
    use std::os::unix::fs::DirBuilderExt;
    let dir = Workdir::new("policy-biscuit");
    let anchor = dir.0.join("biscuit-anchor");
    std::fs::DirBuilder::new()
        .mode(0o700)
        .create(&anchor)
        .unwrap();
    let anchor_s = anchor.to_str().unwrap();
    let auth_sk = dir.path("auth.sk");
    let auth_pk = dir.path("auth.pk");
    let tok0 = dir.path("b0.json");
    let step0 = dir.path("step0.sk");
    let tok1 = dir.path("b1.json");
    let step1 = dir.path("step1.sk");
    let sealed = dir.path("sealed.json");
    let audience = &"12".repeat(32);
    let resource = &"34".repeat(32);

    expect(
        &[
            "policy",
            "biscuit",
            "keygen",
            "--secret-out",
            &auth_sk,
            "--public-out",
            &auth_pk,
            "--tree-height",
            "2",
            "--anchor-dir",
            anchor_s,
            "--allow-single-disk-anchor",
            "--allow-unencrypted",
        ],
        0,
    );
    let sk_before = std::fs::read(&auth_sk).unwrap();
    let lock_before = std::fs::read(format!("{auth_sk}.vault.lock")).unwrap();

    expect(
        &[
            "policy",
            "biscuit",
            "mint",
            "--secret",
            &auth_sk,
            "--audience-hex",
            audience,
            "--resource-hex",
            resource,
            "--actions",
            "15",
            "--token-out",
            &tok0,
            "--step-key-out",
            &step0,
            "--anchor-dir",
            anchor_s,
            "--allow-single-disk-anchor",
        ],
        0,
    );
    // Attenuate consumes step0.sk (single-use retirement)!
    expect(
        &[
            "policy",
            "biscuit",
            "attenuate",
            "--in",
            &tok0,
            "--step-key",
            &step0,
            "--max-amount",
            "50000000000000000000",
            "--token-out",
            &tok1,
            "--step-key-out",
            &step1,
        ],
        0,
    );
    assert!(!Path::new(&step0).exists());
    // Reusing retired step0.sk fails!
    expect(
        &[
            "policy",
            "biscuit",
            "attenuate",
            "--in",
            &tok0,
            "--step-key",
            &step0,
            "--max-amount",
            "99999999999999999999",
            "--token-out",
            &dir.path("forged.json"),
            "--step-key-out",
            &dir.path("forged.sk"),
        ],
        4,
    );

    // Seal with --bind-request and verify publicly!
    expect(
        &[
            "policy",
            "biscuit",
            "seal",
            "--in",
            &tok1,
            "--step-key",
            &step1,
            "--bind-request",
            "--audience-hex",
            audience,
            "--resource-hex",
            resource,
            "--actions",
            "3",
            "--amount",
            "50000000000000000000",
            "--now",
            "1700000000",
            "--out",
            &sealed,
        ],
        0,
    );
    assert!(!Path::new(&step1).exists());
    expect(
        &[
            "policy",
            "biscuit",
            "verify",
            "--public",
            &auth_pk,
            "--in",
            &sealed,
            "--audience-hex",
            audience,
            "--resource-hex",
            resource,
            "--actions",
            "3",
            "--amount",
            "50000000000000000000",
            "--now",
            "1700000000",
        ],
        0,
    );
    // Request mismatch (different amount than bound request) fails verification!
    expect(
        &[
            "policy",
            "biscuit",
            "verify",
            "--public",
            &auth_pk,
            "--in",
            &sealed,
            "--audience-hex",
            audience,
            "--resource-hex",
            resource,
            "--actions",
            "3",
            "--amount",
            "1",
            "--now",
            "1700000000",
        ],
        2,
    );

    // Snapshot rollback of auth.sk + lock is refused by the external anchor!
    std::fs::write(&auth_sk, &sk_before).unwrap();
    std::fs::write(format!("{auth_sk}.vault.lock"), &lock_before).unwrap();
    expect(
        &[
            "policy",
            "biscuit",
            "mint",
            "--secret",
            &auth_sk,
            "--audience-hex",
            audience,
            "--token-out",
            &dir.path("rb.json"),
            "--step-key-out",
            &dir.path("rb.sk"),
            "--anchor-dir",
            anchor_s,
            "--allow-single-disk-anchor",
        ],
        4,
    );
}

#[test]
fn e2e_fts_threshold_persists_reservoirs_and_signs_without_redkg() {
    let dir = Workdir::new("fts-threshold-reservoirs");
    let sk = dir.path("fts.sk");
    let pk = dir.path("fts.pk");
    let msg = dir.path("msg");
    let other = dir.path("other");
    let sig0 = dir.path("sig0");
    let sig1 = dir.path("sig1");

    expect(
        &[
            "keygen",
            "--scheme",
            "fts-threshold",
            "--fast-demo",
            "--tree-height",
            "2",
            "--secret-out",
            &sk,
            "--public-out",
            &pk,
        ],
        0,
    );
    for p in 0..3 {
        assert!(Path::new(&format!("{sk}.party-{p}.reservoir")).is_file());
        assert!(Path::new(&format!("{sk}.party-{p}.reservoir.lock")).is_file());
    }
    expect(
        &["sign", "--secret", &sk, "--in", &msg, "--out", &sig0],
        0,
    );
    expect(
        &["verify", "--public", &pk, "--in", &msg, "--sig", &sig0],
        0,
    );
    expect(
        &["sign", "--secret", &sk, "--in", &other, "--out", &sig1],
        0,
    );
    expect(
        &["verify", "--public", &pk, "--in", &other, "--sig", &sig1],
        0,
    );

    // Corrupting a persisted party reservoir sidecar fails closed before signing.
    let res0 = format!("{sk}.party-0.reservoir");
    let mut raw = std::fs::read(&res0).unwrap();
    let mid = raw.len() / 2;
    raw[mid] ^= 0x55;
    std::fs::write(&res0, &raw).unwrap();
    expect(
        &[
            "sign",
            "--secret",
            &sk,
            "--in",
            &msg,
            "--out",
            &dir.path("corrupt.sig"),
        ],
        4,
    );
    assert!(!Path::new(&dir.path("corrupt.sig")).exists());
}

#[test]
fn e2e_policy_ledger_u128_amount_above_u64_max() {
    let dir = Workdir::new("policy-u128");
    let (sk, pk, payload) = (dir.path("sk"), dir.path("pk"), dir.path("msg"));
    expect(
        &[
            "keygen",
            "--scheme",
            "fts-frontier-2338",
            "--secret-out",
            &dir.path("recipient.sk"),
            "--public-out",
            &dir.path("recipient.pk"),
        ],
        0,
    );
    let recipient = json_member(&dir.read("recipient.pk"), "address");
    let policy_path = dir.path("policy-u128.json");
    // 2 * 10^20 single tx cap, 3 * 10^20 window cap (well above u64::MAX = 18_446_744_073_709_551_615).
    std::fs::write(
        &policy_path,
        format!(
            r#"{{
  "format": "qsag-policy-v1",
  "chain_id": 1,
  "suite": "FrontierSumFts",
  "recipient_allowlist": ["{recipient}"],
  "max_single_tx_amount": 200000000000000000000,
  "velocity_window_cap": 300000000000000000000,
  "valid_not_before_secs": 0,
  "valid_not_after_secs": 4102444800,
  "forbid_initiator_self_approval": true,
  "hardware_guardian_party": 3,
  "quorum_tiers": [
    {{"max_amount_units": 200000000000000000000, "min_approvers": 2, "require_hardware_guardian": true}}
  ],
  "parties": [1, 2, 3]
}}
"#
        ),
    )
    .unwrap();
    let ledger_dir = dir.path("ledger");
    expect(
        &[
            "policy",
            "init",
            "--ledger-dir",
            &ledger_dir,
            "--policy",
            &policy_path,
            "--accept-single-host-custody",
        ],
        0,
    );
    expect(
        &[
            "keygen",
            "--scheme",
            "fts-frontier-2338",
            "--secret-out",
            &sk,
            "--public-out",
            &pk,
            "--policy-ledger-dir",
            &ledger_dir,
        ],
        0,
    );
    let ledger = ["--ledger-dir", ledger_dir.as_str()];
    let intent_msg = dir.path("intent.msg");
    let huge = "100000000000000000000";
    let intent = propose(&ledger, &pk, &payload, &recipient, huge, &intent_msg);
    approve(&ledger, &intent, "2", 0);
    approve(&ledger, &intent, "3", 0);
    let sig = dir.path("huge.sig");
    let signed = expect(
        &[
            "sign",
            "--secret",
            &sk,
            "--in",
            &intent_msg,
            "--out",
            &sig,
            "--policy-ledger-dir",
            &ledger_dir,
            "--policy-intent",
            &intent,
            "--json",
        ],
        0,
    );
    assert_eq!(json_member(&signed, "spend_amount"), huge);
    assert_eq!(window_spend(&ledger), huge);
}
