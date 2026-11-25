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
    let enrolls_custody = matches!(
        (args.first(), args.get(1), args.get(2)),
        (Some(&"keygen" | &"sign" | &"aggregate"), _, _)
            | (
                Some(&"quorum"),
                Some(&"keygen" | &"sign" | &"refresh" | &"reshare"),
                _
            )
            | (
                Some(&"cred"),
                Some(&"voprf-keygen" | &"voprf-eval" | &"mldsa-keygen" | &"mldsa-sign"),
                _
            )
            | (Some(&"hd"), Some(&"keygen" | &"recover" | &"export-rss"), _)
            | (Some(&"policy"), Some(&"init"), _)
            | (
                Some(&"policy"),
                Some(&"biscuit"),
                Some(&"keygen" | &"mint" | &"verify")
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
    for args in [
        &["verify-agg"][..],
        &["verify-agg", "--min-signers", "0"][..],
    ] {
        let rejected = qsag(args);
        assert_eq!(code(&rejected), 1);
        assert!(String::from_utf8_lossy(&rejected.stderr).contains("--min-signers"));
    }
    let dir = Workdir::new("test-entropy-policy");
    for (command, subcommand, output) in [
        ("hd", "keygen", "--watch-out"),
        ("cred", "voprf-keygen", "--public-out"),
        ("cred", "mldsa-keygen", "--public-out"),
    ] {
        let vault = dir.path("vault");
        let public = dir.path("public");
        let mut args = vec![
            command,
            subcommand,
            "--deterministic-test-only",
            "--vault-dir",
            &vault,
            output,
            &public,
        ];
        let refused = qsag(&args);
        assert!(!refused.status.success());
        assert!(String::from_utf8_lossy(&refused.stderr).contains("--allow-unencrypted"));
        let anchor = dir.path("anchor");
        args.extend(["--allow-unencrypted", "--anchor-dir", &anchor]);
        let refused = qsag(&args);
        assert!(!refused.status.success());
        assert!(String::from_utf8_lossy(&refused.stderr).contains("--deterministic-test-only"));
        assert!(!Path::new(&vault).exists());
    }
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
        "fts-frontier-2338",
        "agg-jorts-poseidon2",
        "QuinticFp5",
        "WHIR",
        "QSAGHQM2",
        "qsag-migration-proof-v2",
        "\"kind\": \"btc-hash160\"",
        "\"kind\": \"eth-eoa\"",
        "\"kind\": \"ed25519\"",
        "\"kind\": \"bip32-secp256k1\"",
        "\"kind\": \"ironwood\"",
        "\"kind\": \"orchard\"",
        "\"kind\": \"sapling\"",
        "\"kind\": \"zcash-transparent\"",
    ] {
        assert!(info.contains(needle), "info lacks {needle}");
    }
    assert!(!info.contains("fts-threshold"));
    assert_eq!(
        info,
        expect(&["info", "--json"], 0),
        "info output must be deterministic"
    );

    expect(&[], 1);
    expect(&["frobnicate"], 1);
    let migrate_help = expect(&["migrate", "--help"], 0);
    for needle in [
        "claim",
        "prove",
        "verify",
        "registry",
        "btc-hash160",
        "bip32-secp256k1",
    ] {
        assert!(
            migrate_help.contains(needle),
            "migrate --help lacks {needle}"
        );
    }
    for sub in [
        &["claim"][..],
        &["commit"],
        &["prove"],
        &["verify"],
        &["registry"],
        &["registry", "init"],
        &["registry", "register"],
        &["registry", "enroll"],
        &["registry", "finalize"],
        &["registry", "lookup"],
    ] {
        let mut args = vec!["migrate"];
        args.extend_from_slice(sub);
        args.push("--help");
        assert!(!expect(&args, 0).is_empty(), "{args:?}");
    }
    expect(&["migrate"], 1);
    expect(&["migrate", "frobnicate"], 1);
    expect(&["migrate", "registry"], 1);
    expect(&["migrate", "registry", "frobnicate"], 1);
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
    let initial_key = dir.read("sk");
    for unavailable in [&pk, &dir.path("missing/out")] {
        expect(
            &["sign", "--secret", &sk, "--in", &msg, "--out", unavailable],
            5,
        );
        assert_eq!(dir.read("sk"), initial_key);
    }
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
fn aggregate_quintic_verify_and_tamper() {
    let dir = Workdir::new("agg");
    let wal = dir.path("wal");
    let pass = dir.path("pass");
    std::fs::write(&pass, b"sealed committee password").unwrap();
    keygen(
        &dir,
        "agg-jorts-poseidon2",
        &[
            "--validators",
            "4",
            "--wal-dir",
            &wal,
            "--passphrase-file",
            &pass,
        ],
    );
    let (sk, pk, msg, other) = (
        dir.path("sk"),
        dir.path("pk"),
        dir.path("msg"),
        dir.path("other"),
    );
    let (proof_a, proof_b, full_proof) = (
        dir.path("a.proof"),
        dir.path("b.proof"),
        dir.path("full.proof"),
    );
    let sign = |signers: &str, epoch: &str, input: &str, out: &str, expected: i32| {
        expect(
            &[
                "aggregate",
                "--secret",
                &sk,
                "--passphrase-file",
                &pass,
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
    expect(
        &[
            "verify-agg",
            "--min-signers",
            "2",
            "--hem-profile",
            "quintic-gl24",
            "--public",
            &pk,
            "--in",
            &msg,
            "--proof",
            &proof_a,
        ],
        2,
    );

    expect(
        &[
            "verify-agg",
            "--min-signers",
            "3",
            "--public",
            &pk,
            "--in",
            &msg,
            "--proof",
            &proof_a,
        ],
        2,
    );
    expect(
        &[
            "verify-agg",
            "--min-signers",
            "2",
            "--public",
            &pk,
            "--in",
            &msg,
            "--proof",
            &proof_a,
        ],
        0,
    );
    assert!(
        expect(
            &[
                "verify-agg",
                "--allow-any-subset",
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
            "--allow-any-subset",
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

    // Epoch 1 full-committee Quintic Fp5 (`QSAGHQM2`) proof across all 4 validators.
    sign("0,1,2,3", "1", &msg, &full_proof, 0);
    assert!(
        expect(
            &[
                "verify-agg",
                "--allow-any-subset",
                "--public",
                &pk,
                "--in",
                &msg,
                "--proof",
                &full_proof
            ],
            0
        )
        .contains("4 of 4")
    );
    // Retired `--merge` flag must be rejected as an unknown option.
    expect(
        &[
            "aggregate",
            "--merge",
            &format!("{proof_a},{proof_b}"),
            "--public",
            &pk,
            "--in",
            &msg,
            "--out",
            &dir.path("retired-merge.proof"),
        ],
        1,
    );

    // A deleted write-ahead log is not treated as an unused key.
    std::fs::remove_file(Path::new(&wal).join("validator-3.wal")).unwrap();
    sign("3", "2", &msg, &dir.path("lost-wal.proof"), 4);

    flip_hex_digit(&full_proof, "proof");
    expect(
        &[
            "verify-agg",
            "--allow-any-subset",
            "--public",
            &pk,
            "--in",
            &msg,
            "--proof",
            &full_proof,
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

/// Restore the custody bytes of a vault in place: every inode is kept, and the anchor
/// `.lock` sidecars and VMGENID `.target` files are not touched at all. A vault's own
/// `.vault.lock` holds its state MAC, so its contents are part of the old state.
#[cfg(target_os = "linux")]
fn restore_custody_bytes_in_place(snapshot: &[(PathBuf, Vec<u8>)]) {
    let custody: Vec<_> = snapshot
        .iter()
        .filter(|(path, _)| {
            path.to_string_lossy().ends_with(".vault.lock")
                || !matches!(
                    path.extension().and_then(|s| s.to_str()),
                    Some("lock" | "target")
                )
        })
        .cloned()
        .collect();
    restore_dir_files_in_place(&custody);
}

// A VM generation id changes when the hypervisor restores or clones the whole VM. It
// does not change when the guest's files are put back in place, and the VMGENID seal
// lives on the disk being restored. Before `--anchor-vmgenid` stopped counting as an
// anchor, the first half of this test enrolled with it alone, signed epoch 0, restored
// the vault bytes in place and signed epoch 0 again for a different message: two valid
// signatures from one one-time leaf.
#[cfg(target_os = "linux")]
#[test]
fn vmgenid_alone_is_refused_and_in_place_restore_cannot_respend_a_leaf() {
    use std::os::unix::fs::{DirBuilderExt, MetadataExt};
    let dir = Workdir::new("vmgenid-in-place");
    let private = |path: &Path| {
        std::fs::DirBuilder::new().mode(0o700).create(path).unwrap();
    };
    let vault = dir.0.join("vault");
    private(&vault);
    let vault_s = vault.to_str().unwrap();
    let pk = dir.path("pk");
    let keygen = |vault: &str, pk: &str, anchor: &[&str]| {
        let mut args = vec![
            "quorum",
            "keygen",
            "--vault-dir",
            vault,
            "--public-out",
            pk,
            "--tree-height",
            "1",
        ];
        args.extend_from_slice(anchor);
        qsag(&args)
    };
    let sign = |vault: &str, message: &str, output: &str, anchor: &[&str]| {
        let mut args = vec![
            "quorum",
            "sign",
            "--vault-dir",
            vault,
            "--epoch",
            "0",
            "--in",
            message,
            "--out",
            output,
        ];
        args.extend_from_slice(anchor);
        qsag(&args)
    };
    let verify = |pk: &str, message: &str, sig: &str| {
        expect(
            &[
                "quorum", "verify", "--public", pk, "--in", message, "--sig", sig,
            ],
            0,
        );
    };
    let stderr = |output: &Output| String::from_utf8_lossy(&output.stderr).into_owned();

    // 1. VMGENID on its own.
    let enrolled = keygen(vault_s, &pk, &["--anchor-vmgenid"]);
    if code(&enrolled) == 0 {
        let genesis = snapshot_dir_files(&vault);
        let first = dir.path("first.sig");
        let second = dir.path("second.sig");
        let signed = sign(vault_s, &dir.path("msg"), &first, &["--anchor-vmgenid"]);
        assert_eq!(code(&signed), 0, "{}", stderr(&signed));
        let identity = |path: &Path| {
            let meta = std::fs::metadata(path).unwrap();
            (meta.dev(), meta.ino())
        };
        let inodes: Vec<_> = genesis.iter().map(|(path, _)| identity(path)).collect();
        restore_custody_bytes_in_place(&genesis);
        let after: Vec<_> = genesis.iter().map(|(path, _)| identity(path)).collect();
        assert_eq!(inodes, after);
        let resigned = sign(vault_s, &dir.path("other"), &second, &["--anchor-vmgenid"]);
        if code(&resigned) == 0 {
            verify(&pk, &dir.path("msg"), &first);
            verify(&pk, &dir.path("other"), &second);
            panic!(
                "VMGENID-only vault reopened its restored state: two valid epoch-0 signatures over different messages"
            );
        }
        panic!(
            "--anchor-vmgenid alone was accepted as a rollback anchor: {}",
            stderr(&resigned)
        );
    }
    assert_eq!(code(&enrolled), 1, "{}", stderr(&enrolled));
    assert!(
        stderr(&enrolled).contains("snapshot/clone detection only"),
        "{}",
        stderr(&enrolled)
    );
    assert!(!Path::new(&pk).exists());
    assert_eq!(std::fs::read_dir(&vault).unwrap().count(), 0);

    // 2. A directory anchor on the vault's own device is restored by the same restore;
    //    the single-disk waiver does not turn VMGENID into the monotone half.
    let same_disk = dir.0.join("anchor");
    private(&same_disk);
    let refused = keygen(
        vault_s,
        &pk,
        &[
            "--anchor-vmgenid",
            "--anchor-dir",
            same_disk.to_str().unwrap(),
            "--allow-single-disk-anchor",
        ],
    );
    assert_eq!(code(&refused), 4, "{}", stderr(&refused));
    assert!(
        stderr(&refused).contains("snapshot/clone detection only"),
        "{}",
        stderr(&refused)
    );
    assert!(!Path::new(&pk).exists());

    // 3. With a directory anchor on another device the same in-place restore is refused.
    let shm = Path::new("/dev/shm");
    if !shm.is_dir()
        || std::fs::metadata(shm).unwrap().dev() == std::fs::metadata(&vault).unwrap().dev()
    {
        eprintln!("no second filesystem device for the disjoint-anchor half of this test");
        return;
    }
    let disjoint = shm.join(format!("qsag-cli-vmgenid-anchor-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&disjoint);
    private(&disjoint);
    struct Cleanup(PathBuf);
    impl Drop for Cleanup {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }
    let _cleanup = Cleanup(disjoint.clone());
    let vault2 = dir.0.join("vault2");
    private(&vault2);
    let vault2_s = vault2.to_str().unwrap();
    let pk2 = dir.path("pk2");
    let anchored = [
        "--anchor-vmgenid",
        "--anchor-dir",
        disjoint.to_str().unwrap(),
    ];
    let enrolled = keygen(vault2_s, &pk2, &anchored);
    assert_eq!(code(&enrolled), 0, "{}", stderr(&enrolled));
    let genesis = snapshot_dir_files(&vault2);
    let first = dir.path("anchored-first.sig");
    let second = dir.path("anchored-second.sig");
    let signed = sign(vault2_s, &dir.path("msg"), &first, &anchored);
    assert_eq!(code(&signed), 0, "{}", stderr(&signed));
    verify(&pk2, &dir.path("msg"), &first);
    restore_custody_bytes_in_place(&genesis);
    let resigned = sign(vault2_s, &dir.path("other"), &second, &anchored);
    assert_eq!(code(&resigned), 4, "{}", stderr(&resigned));
    assert!(!Path::new(&second).exists());
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
            "--allow-any-subset",
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
            "--allow-any-subset",
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
            "--allow-any-subset",
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
fn e2e_cred_and_hd_subcommands() {
    let dir = Workdir::new("cred-hd");
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
            "--deterministic-test-only",
            "--allow-unencrypted",
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
            "--deterministic-test-only",
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
            "--deterministic-test-only",
            "--allow-unencrypted",
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
            "--context-hex",
            "abcd",
            "--deterministic-test-only",
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
            "--context-hex",
            "abcd",
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
        2,
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
            "--context-hex",
            "abce",
        ],
        2,
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
            "--context-hex",
            "abcd",
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
            "--deterministic-test-only",
            "--allow-unencrypted",
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

    expect(&["policy", "macaroon", "keygen", "--out", &root_key], 0);
    expect(&["policy", "macaroon", "keygen", "--out", &tp_key], 0);
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
    // A macaroon is a reusable bearer grant: verification keeps no state, so the same
    // token and discharge verify again, and the output says so instead of implying
    // that the grant was spent.
    let again = expect(
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
            "--json",
        ],
        0,
    );
    assert_eq!(json_member(&again, "valid"), "true");
    assert_eq!(json_member(&again, "consumed"), "false");
    assert_eq!(json_member(&again, "reusable"), "true");
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
    let vault_dir = dir.0.join("biscuit-vault");
    std::fs::DirBuilder::new()
        .mode(0o700)
        .create(&vault_dir)
        .unwrap();
    let auth_sk = vault_dir.join("auth.sk").to_str().unwrap().to_string();
    let auth_pk = dir.path("auth.pk");
    let tok0 = dir.path("b0.json");
    let step0 = dir.path("step0.sk");
    let tok1 = dir.path("b1.json");
    let step1 = dir.path("step1.sk");
    let sealed = dir.path("sealed.json");
    let seal_store = dir.path("seal-ledger");
    let intent_digest = &"56".repeat(32);
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
    assert!(
        std::fs::read_to_string(&step0)
            .unwrap()
            .contains("\"retired\": true")
    );
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
            "--intent-digest-hex",
            intent_digest,
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
    assert!(
        std::fs::read_to_string(&step1)
            .unwrap()
            .contains("\"retired\": true")
    );
    let verify_args = [
        "policy",
        "biscuit",
        "verify",
        "--intent-digest-hex",
        intent_digest,
        "--seal-store",
        &seal_store,
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
    ];
    let mut first_verify = verify_args.to_vec();
    first_verify.push("--create-seal-store");
    expect(&first_verify, 0);
    // A new CLI process reopening the same ledger must refuse the same seal.
    expect(&verify_args, 3);
    // Request mismatch (different amount than bound request) fails verification!
    expect(
        &[
            "policy",
            "biscuit",
            "verify",
            "--intent-digest-hex",
            intent_digest,
            "--seal-store",
            &seal_store,
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
fn retired_threshold_scheme_is_refused_before_creating_custody_files() {
    let dir = Workdir::new("retired-threshold");
    let sk = dir.path("fts.sk");
    let pk = dir.path("fts.pk");
    expect(
        &[
            "keygen",
            "--scheme",
            "fts-threshold",
            "--secret-out",
            &sk,
            "--public-out",
            &pk,
        ],
        1,
    );
    assert!(!Path::new(&sk).exists());
    assert!(!Path::new(&pk).exists());
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

#[cfg(unix)]
#[test]
fn passphrase_biscuit_authority_survives_multiple_anchored_mints() {
    use std::os::unix::fs::DirBuilderExt;
    let dir = Workdir::new("sealed-biscuit-mints");
    for name in ["vault", "anchor"] {
        std::fs::DirBuilder::new()
            .mode(0o700)
            .create(dir.path(name))
            .unwrap();
    }
    let sk = dir.path("vault/authority.sk");
    let pk = dir.path("authority.pk");
    let anchor = dir.path("anchor");
    let pass = dir.path("pass");
    std::fs::write(&pass, b"correct biscuit password").unwrap();
    let audience = "12".repeat(32);
    let resource = "34".repeat(32);
    expect(
        &[
            "policy",
            "biscuit",
            "keygen",
            "--secret-out",
            &sk,
            "--public-out",
            &pk,
            "--tree-height",
            "2",
            "--passphrase-file",
            &pass,
            "--anchor-dir",
            &anchor,
            "--allow-single-disk-anchor",
        ],
        0,
    );
    let mut seen_salts = std::collections::BTreeSet::new();
    let mut seen_tags = std::collections::BTreeSet::new();
    seen_salts.insert(json_member(&std::fs::read_to_string(&sk).unwrap(), "salt"));
    seen_tags.insert(json_member(
        &std::fs::read_to_string(&sk).unwrap(),
        "envelope_tag",
    ));
    for mint in 0..3 {
        let token = dir.path(&format!("token-{mint}"));
        let step = dir.path(&format!("step-{mint}"));
        let sealed = dir.path(&format!("sealed-{mint}"));
        let seal_store = dir.path(&format!("seal-store-{mint}"));
        let args = [
            "policy",
            "biscuit",
            "mint",
            "--secret",
            &sk,
            "--audience-hex",
            &audience,
            "--resource-hex",
            &resource,
            "--token-out",
            &token,
            "--step-key-out",
            &step,
            "--passphrase-file",
            &pass,
            "--anchor-dir",
            &anchor,
            "--allow-single-disk-anchor",
        ];
        let before = std::fs::read(&sk).unwrap();
        // Omitting passphrase must fail closed without advancing vault or anchor.
        expect(
            &[
                "policy",
                "biscuit",
                "mint",
                "--secret",
                &sk,
                "--audience-hex",
                &audience,
                "--resource-hex",
                &resource,
                "--token-out",
                &token,
                "--step-key-out",
                &step,
                "--anchor-dir",
                &anchor,
                "--allow-single-disk-anchor",
            ],
            1,
        );
        assert_eq!(std::fs::read(&sk).unwrap(), before);
        // Pre-existing --token-out must fail preflight before burning a leaf.
        std::fs::write(&token, b"occupied").unwrap();
        expect(&args, 1);
        assert_eq!(std::fs::read(&sk).unwrap(), before);
        std::fs::remove_file(&token).unwrap();
        // Wrong passphrase must fail closed without advancing vault or anchor.
        std::fs::write(&pass, b"wrong password").unwrap();
        expect(&args, 1);
        assert_eq!(std::fs::read(&sk).unwrap(), before);
        assert!(!Path::new(&token).exists());
        std::fs::write(&pass, b"correct biscuit password").unwrap();
        expect(&args, 0);
        let updated = std::fs::read_to_string(&sk).unwrap();
        assert!(updated.contains(&format!("\"uses_completed\": {}", mint + 1)));
        for field in ["envelope", "salt", "envelope_tag"] {
            assert_eq!(updated.matches(&format!("\"{field}\":")).count(), 1);
        }
        assert!(seen_salts.insert(json_member(&updated, "salt")));
        assert!(seen_tags.insert(json_member(&updated, "envelope_tag")));
        expect(
            &[
                "policy",
                "biscuit",
                "seal",
                "--in",
                &token,
                "--step-key",
                &step,
                "--out",
                &sealed,
            ],
            0,
        );
        expect(
            &[
                "policy",
                "biscuit",
                "verify",
                "--public",
                &pk,
                "--in",
                &sealed,
                "--audience-hex",
                &audience,
                "--resource-hex",
                &resource,
                "--seal-store",
                &seal_store,
                "--create-seal-store",
            ],
            0,
        );
    }
}

// A seal consumed after a backup of the verifier's seal store must stay consumed when
// the backup is put back. Without an anchor the restored store accepts it again.
#[cfg(unix)]
#[test]
fn biscuit_seal_store_anchor_refuses_a_restored_store() {
    use std::os::unix::fs::DirBuilderExt;
    let dir = Workdir::new("seal-store-rollback");
    let private = |name: &str| {
        std::fs::DirBuilder::new()
            .mode(0o700)
            .create(dir.path(name))
            .unwrap();
        dir.path(name)
    };
    let sk = dir.path("authority.sk");
    let pk = dir.path("authority.pk");
    let audience = "12".repeat(32);
    let resource = "34".repeat(32);
    expect(
        &[
            "policy",
            "biscuit",
            "keygen",
            "--secret-out",
            &sk,
            "--public-out",
            &pk,
            "--tree-height",
            "2",
        ],
        0,
    );
    let seal = |n: usize| {
        let token = dir.path(&format!("token-{n}"));
        let step = dir.path(&format!("step-{n}"));
        let sealed = dir.path(&format!("sealed-{n}"));
        expect(
            &[
                "policy",
                "biscuit",
                "mint",
                "--secret",
                &sk,
                "--audience-hex",
                &audience,
                "--resource-hex",
                &resource,
                "--token-out",
                &token,
                "--step-key-out",
                &step,
            ],
            0,
        );
        expect(
            &[
                "policy",
                "biscuit",
                "seal",
                "--in",
                &token,
                "--step-key",
                &step,
                "--out",
                &sealed,
            ],
            0,
        );
        sealed
    };
    let verify = |sealed: &str, store: &str, extra: &[&str]| {
        let mut args = vec![
            "policy",
            "biscuit",
            "verify",
            "--public",
            &pk,
            "--in",
            sealed,
            "--audience-hex",
            &audience,
            "--resource-hex",
            &resource,
            "--seal-store",
            store,
        ];
        args.extend_from_slice(extra);
        qsag(&args)
    };
    let stderr = |output: &Output| String::from_utf8_lossy(&output.stderr).into_owned();

    for anchored in [false, true] {
        let store_dir = private(if anchored {
            "anchored-store"
        } else {
            "bare-store"
        });
        let store = format!("{store_dir}/seals");
        let anchor_dir = private(if anchored {
            "anchor-a"
        } else {
            "anchor-unused"
        });
        let anchor: Vec<&str> = if anchored {
            vec!["--anchor-dir", &anchor_dir, "--allow-single-disk-anchor"]
        } else {
            vec!["--ephemeral-unanchored"]
        };
        let with = |extra: &[&'static str]| -> Vec<&str> {
            anchor
                .iter()
                .copied()
                .chain(extra.iter().copied())
                .collect()
        };
        let (first, second) = (
            seal(usize::from(anchored) * 2),
            seal(usize::from(anchored) * 2 + 1),
        );

        let created = verify(&first, &store, &with(&["--create-seal-store"]));
        assert_eq!(code(&created), 0, "{}", stderr(&created));
        let backup = snapshot_dir_files(Path::new(&store_dir));
        let accepted = verify(&second, &store, &with(&[]));
        assert_eq!(code(&accepted), 0, "{}", stderr(&accepted));
        let replayed = verify(&second, &store, &with(&[]));
        assert_eq!(code(&replayed), 3, "{}", stderr(&replayed));
        let current = snapshot_dir_files(Path::new(&store_dir));

        // The store directory goes back to the backup, every inode kept.
        restore_dir_files_in_place(&backup);
        let after_restore = verify(&second, &store, &with(&[]));
        if anchored {
            assert_eq!(code(&after_restore), 4, "{}", stderr(&after_restore));
            assert!(
                stderr(&after_restore).contains("rollback"),
                "{}",
                stderr(&after_restore)
            );
            // The anchor requirement cannot be dropped to get around it.
            let waived = verify(&second, &store, &["--ephemeral-unanchored"]);
            assert_eq!(code(&waived), 4, "{}", stderr(&waived));
            assert!(stderr(&waived).contains("must be opened with it"));
            // The current store still opens and still refuses the consumed seals.
            restore_dir_files_in_place(&current);
            for sealed in [&first, &second] {
                let refused = verify(sealed, &store, &with(&[]));
                assert_eq!(code(&refused), 3, "{}", stderr(&refused));
            }
        } else {
            // No anchor: the consumed seal is accepted a second time.
            assert_eq!(code(&after_restore), 0, "{}", stderr(&after_restore));
            // And an unanchored store cannot be claimed to be anchored afterwards.
            let claimed = verify(
                &first,
                &store,
                &["--anchor-dir", &anchor_dir, "--allow-single-disk-anchor"],
            );
            assert_eq!(code(&claimed), 4, "{}", stderr(&claimed));
            assert!(stderr(&claimed).contains("without an external anchor"));
        }
    }
    // Neither an anchor nor the waiver: the command refuses to pick for the operator.
    let output = Command::new(env!("CARGO_BIN_EXE_qsag"))
        .args([
            "policy",
            "biscuit",
            "verify",
            "--public",
            &pk,
            "--in",
            &dir.path("sealed-3"),
            "--audience-hex",
            &audience,
            "--resource-hex",
            &resource,
            "--seal-store",
            &dir.path("undecided"),
            "--create-seal-store",
        ])
        .output()
        .unwrap();
    assert_eq!(code(&output), 1, "{}", stderr(&output));
    assert!(!Path::new(&dir.path("undecided")).exists());
}

/// secp256k1 secret key 1: public key `G`.
const SECP_KEY_ONE: &str = "0000000000000000000000000000000000000000000000000000000000000001";

/// A post-quantum address to migrate to: the address of a fresh SLH-DSA key.
fn migration_target(dir: &Workdir, name: &str) -> String {
    let public = dir.path(&format!("{name}.pk"));
    expect(
        &[
            "keygen",
            "--scheme",
            "slh-dsa-shake-128s",
            "--secret-out",
            &dir.path(&format!("{name}.sk")),
            "--public-out",
            &public,
        ],
        0,
    );
    json_member(&std::fs::read_to_string(public).unwrap(), "address")
}

/// `migrate prove` of `kind` for the secret in `secret` to `target` at `epoch`, in the
/// default domain unless `extra` names one. Returns the proof path.
fn migrate_prove(
    dir: &Workdir,
    out: &str,
    kind: &str,
    secret: &str,
    target: &str,
    epoch: &str,
    extra: &[&str],
) -> String {
    let out = dir.path(out);
    let mut args = vec![
        "migrate",
        "prove",
        "--kind",
        kind,
        "--legacy-secret",
        secret,
        "--target",
        target,
        "--epoch",
        epoch,
        "--out",
        &out,
        "--deterministic",
    ];
    args.extend_from_slice(extra);
    expect(&args, 0);
    out
}

#[test]
fn migrate_every_statement_kind_claims_proves_and_verifies() {
    let dir = Workdir::new("migrate-kinds");
    let target = migration_target(&dir, "target");
    let write = |name: &str, contents: &str| {
        let path = dir.path(name);
        std::fs::write(&path, contents).unwrap();
        path
    };
    let secp = write("secp.hex", &format!("{SECP_KEY_ONE}\n"));
    // RFC 8032 section 7.1, test 1.
    let ed = write(
        "ed.hex",
        "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
    );
    // BIP-32 test vector 1.
    let seed = write("seed.hex", "000102030405060708090a0b0c0d0e0f");

    // (kind as typed, canonical kind, secret, path, member holding the legacy value, value)
    type Case<'a> = (&'a str, &'a str, &'a str, Option<&'a str>, &'a str, &'a str);
    let cases: [Case; 6] = [
        (
            "btc-p2wpkh",
            "btc-hash160",
            &secp,
            None,
            "legacy_hash160",
            "751e76e8199196d454941c45d1b3a323f1433bd6",
        ),
        (
            "btc-p2pkh",
            "btc-hash160",
            &secp,
            None,
            "legacy_hash160",
            "751e76e8199196d454941c45d1b3a323f1433bd6",
        ),
        (
            "eth-eoa",
            "eth-eoa",
            &secp,
            None,
            "legacy_address",
            "7e5f4552091a69125d5dfcb7b8c2659029395bdf",
        ),
        (
            "ed25519",
            "ed25519",
            &ed,
            None,
            "legacy_public_key",
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a",
        ),
        (
            "bip32-secp256k1",
            "bip32-secp256k1",
            &seed,
            Some("m/0'/1"),
            "legacy_hash160",
            "bef5a2f9a56a94aab12459f72ad9cf8cf19c7bbe",
        ),
        (
            "bip32",
            "bip32-secp256k1",
            &seed,
            Some("m/0h"),
            "legacy_hash160",
            "5c1bd648ed23aa5fd50ba52b2457c11e9e80a6a7",
        ),
    ];
    for (index, (kind, canonical, secret, path, member, value)) in cases.into_iter().enumerate() {
        let claim = dir.path(&format!("claim-{index}.json"));
        let proof = dir.path(&format!("proof-{index}.json"));
        let statement = |command: &'static str, out: &str| {
            let mut args = vec![
                "migrate",
                command,
                "--kind",
                kind,
                "--legacy-secret",
                secret,
                "--target",
                target.as_str(),
                "--epoch",
                "42",
                "--out",
                out,
            ];
            if let Some(path) = path {
                args.extend(["--path", path]);
            }
            expect(&args, 0)
        };
        statement("claim", &claim);
        let claim_text = std::fs::read_to_string(&claim).unwrap();
        assert_eq!(
            json_member(&claim_text, "format"),
            "qsag-migration-claim-v2"
        );
        assert_eq!(json_member(&claim_text, "kind"), canonical, "{kind}");
        assert_eq!(json_member(&claim_text, member), value, "{kind}");
        assert_eq!(json_member(&claim_text, "target_pq_address"), target);
        assert_eq!(json_member(&claim_text, "epoch"), "42");
        assert_eq!(
            json_member(&claim_text, "key_exposure"),
            if canonical.starts_with("btc") || canonical == "eth-eoa" {
                "hidden"
            } else {
                "revealed"
            },
            "{kind}"
        );

        statement("prove", &proof);
        let proof_text = std::fs::read_to_string(&proof).unwrap();
        assert_eq!(
            json_member(&proof_text, "format"),
            "qsag-migration-proof-v2"
        );
        // The proof file states the claim's statement, byte for byte.
        for shared in [
            "statement",
            "nullifier",
            "legacy_id",
            "pq_commitment",
            member,
        ] {
            assert_eq!(
                json_member(&proof_text, shared),
                json_member(&claim_text, shared),
                "{kind} {shared}"
            );
        }
        let proof_bytes: usize = json_member(&proof_text, "proof_bytes").parse().unwrap();
        assert!(
            (300_000..2_000_000).contains(&proof_bytes),
            "{kind}: {proof_bytes} proof bytes"
        );
        assert!(proof_text.len() < proof_bytes * 4 / 3 + 4096, "{kind}");

        let verified = expect(
            &[
                "migrate", "verify", "--proof", &proof, "--epoch", "42", "--target", &target,
                "--json",
            ],
            0,
        );
        assert_eq!(json_member(&verified, "valid"), "true");
        assert_eq!(json_member(&verified, member), value, "{kind}");
    }
    // The nullifier is per on-chain credential: the two spellings of the HASH160 kind
    // agree, and the Ethereum address of the same key has its own.
    let nullifier = |index: usize| {
        json_member(
            &std::fs::read_to_string(dir.path(&format!("claim-{index}.json"))).unwrap(),
            "nullifier",
        )
    };
    assert_eq!(nullifier(0), nullifier(1));
    assert_ne!(nullifier(0), nullifier(2));
    assert_ne!(nullifier(0), nullifier(3));
    assert_ne!(nullifier(4), nullifier(5));

    // Options that do not fit the kind, and inputs that are not valid secrets.
    let out = dir.path("refused.json");
    let refused = |args: &[&str], needle: &str| {
        let mut full = vec!["migrate", "claim", "--out", &out, "--epoch", "1"];
        full.extend_from_slice(args);
        let output = qsag(&full);
        let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
        assert_eq!(code(&output), 1, "{args:?}: {stderr}");
        assert!(stderr.contains(needle), "{args:?}: {stderr}");
        assert!(!Path::new(&out).exists(), "{args:?}");
    };
    let t = target.as_str();
    refused(
        &[
            "--kind",
            "btc-p2wsh",
            "--legacy-secret",
            &secp,
            "--target",
            t,
        ],
        "unsupported --kind",
    );
    refused(
        &[
            "--kind",
            "btc-p2wpkh",
            "--legacy-secret",
            &secp,
            "--target",
            t,
            "--path",
            "m/0",
        ],
        "--path does not apply",
    );
    refused(
        &["--kind", "bip32", "--legacy-secret", &seed, "--target", t],
        "requires --path",
    );
    refused(
        &[
            "--kind",
            "bip32",
            "--legacy-secret",
            &seed,
            "--target",
            t,
            "--path",
            "44'/0'",
        ],
        "not a BIP-32 path",
    );
    // A 16-byte seed is not a 32-byte key, and a 32-byte raw file is not a hex seed.
    refused(
        &["--kind", "eth-eoa", "--legacy-secret", &seed, "--target", t],
        "must be 32 bytes",
    );
    let raw = dir.path("raw.bin");
    std::fs::write(&raw, [0xa5u8; 32]).unwrap();
    refused(
        &[
            "--kind",
            "bip32",
            "--legacy-secret",
            &raw,
            "--target",
            t,
            "--path",
            "m",
        ],
        "must be hex",
    );
    let zero = write("zero.hex", &"00".repeat(32));
    refused(
        &[
            "--kind",
            "btc-p2wpkh",
            "--legacy-secret",
            &zero,
            "--target",
            t,
        ],
        "not a valid btc-hash160 secret",
    );
    refused(
        &[
            "--kind",
            "btc-p2wpkh",
            "--legacy-secret",
            &secp,
            "--target",
            "qsp1notanaddress",
        ],
        "invalid --target",
    );
    // A raw 32-byte key file is read as the key itself.
    expect(
        &[
            "migrate",
            "claim",
            "--kind",
            "ed25519",
            "--legacy-secret",
            &raw,
            "--target",
            t,
            "--epoch",
            "1",
        ],
        0,
    );
}

/// The statement options beyond the kind: an extended-key root, a hidden path, a Taproot
/// script tree and BIP32-Ed25519. Each is claimed, proved and verified against a published
/// vector or against the same key reached the plain way.
#[test]
fn migrate_roots_hidden_paths_script_trees_and_bip32_ed25519() {
    let dir = Workdir::new("migrate-options");
    let target = migration_target(&dir, "target");
    let write = |name: &str, contents: &str| {
        let path = dir.path(name);
        std::fs::write(&path, contents).unwrap();
        path
    };
    // BIP-32 test vector 1: the seed, and the extended private key of chain m/0'.
    let seed = write("seed.hex", "000102030405060708090a0b0c0d0e0f");
    let xprv = write(
        "account.xprv",
        "xprv9uHRZZhk6KAJC1avXpDAp4MDc3sQKNxDiPvvkX8Br5ngLNv1TxvUxt4cV1rGL5hj6KCesnDYUhd7oWgT11eZG7XnxHrnYeSvkzY7d2bhkJ7\n",
    );
    // BIP-341 wallet test vectors, keyPathSpending input 1 (a script tree).
    let taproot = write(
        "taproot.hex",
        "1e4da49f6aaf4e5cd175fe08a32bb5cb4863d963921255f33d3bc31e1343907f",
    );
    // `D1` of rust-ed25519-bip32; its hardened child 0 is `D1_H0`.
    let cardano = write(
        "cardano.hex",
        "f8a29231ee38d6c5bf715d5bac21c750577aa3798b22d79d65bf97d6fadea15a\
         dcd1ee1abdf78bd4be64731a12deb94d3671784112eb6f364b871851fd1c9a24\
         7384db9ad6003bbd08b3b1ddc0d07a597293ff85e961bf252b331262eddfad0d",
    );
    // m/0'/1 of test vector 1, as in `migrate_every_statement_kind_claims_proves_and_verifies`.
    const CHILD_HASH160: &str = "bef5a2f9a56a94aab12459f72ad9cf8cf19c7bbe";

    // (name, kind, secret, extra options, member, value, members present, members absent)
    type Case<'a> = (
        &'a str,
        &'a str,
        &'a str,
        Vec<&'a str>,
        &'a str,
        &'a str,
        Vec<(&'a str, &'a str)>,
        Vec<&'a str>,
    );
    let cases: Vec<Case> = vec![
        (
            "extended",
            "bip32-secp256k1",
            &xprv,
            vec!["--root", "extended-key", "--path", "m/1"],
            "legacy_hash160",
            CHILD_HASH160,
            vec![("bip32_root", "extended-key"), ("derivation_path", "m/1")],
            vec!["hidden_path_max_depth"],
        ),
        (
            "hidden",
            "bip32-secp256k1",
            &seed,
            vec!["--path", "m/0'/1", "--hidden-path-depth", "2"],
            "legacy_hash160",
            CHILD_HASH160,
            vec![("hidden_path_max_depth", "2")],
            vec!["derivation_path", "bip32_root"],
        ),
        (
            "tree",
            "btc-taproot-tree",
            &taproot,
            vec![
                "--merkle-root",
                "5b75adecf53548f3ec6ad7d78383bf84cc57b55a3127c72b9a2481752dd88b21",
            ],
            "legacy_output_key",
            "147c9c57132f6e7ecddba9800bb0c4449251c92a1e60371ee77557b6620f3ea3",
            vec![("key_exposure", "hidden")],
            vec!["derivation_path", "merkle_root"],
        ),
        (
            "cardano",
            "cardano-ed25519",
            &cardano,
            vec!["--path", "m/0'"],
            "legacy_public_key",
            "9c99845ae0a60881decf7874b94ad02e7540628b588f8b4305d668cc53986978",
            vec![("kind", "bip32-ed25519"), ("derivation_path", "m/0'")],
            vec!["bip32_root"],
        ),
    ];
    for (name, kind, secret, extra, member, value, present, absent) in cases {
        let claim = dir.path(&format!("{name}-claim.json"));
        let mut args = vec![
            "migrate",
            "claim",
            "--kind",
            kind,
            "--legacy-secret",
            secret,
            "--target",
            target.as_str(),
            "--epoch",
            "42",
            "--out",
            &claim,
        ];
        args.extend_from_slice(&extra);
        expect(&args, 0);
        let claim_text = std::fs::read_to_string(&claim).unwrap();
        assert_eq!(json_member(&claim_text, member), value, "{name}");
        for (member, value) in present {
            assert_eq!(json_member(&claim_text, member), value, "{name}");
        }
        for member in absent {
            assert!(
                !claim_text.contains(&format!("\"{member}\"")),
                "{name} {member}"
            );
        }
        // The merkle root is a witness: it is not in the claim.
        assert!(!claim_text.contains("5b75adecf535"), "{name}");

        let proof = migrate_prove(
            &dir,
            &format!("{name}-proof.json"),
            kind,
            secret,
            &target,
            "42",
            &extra,
        );
        let proof_text = std::fs::read_to_string(&proof).unwrap();
        assert_eq!(
            json_member(&proof_text, "statement"),
            json_member(&claim_text, "statement"),
            "{name}"
        );
        let verified = expect(
            &[
                "migrate", "verify", "--proof", &proof, "--epoch", "42", "--target", &target,
                "--json",
            ],
            0,
        );
        assert_eq!(json_member(&verified, "valid"), "true", "{name}");
        assert_eq!(json_member(&verified, member), value, "{name}");
    }
    // The hidden-path statement does not name the path: another path of the same depth
    // bound gives a statement of the same shape and a different credential.
    let statement_of = |name: &str| {
        json_member(
            &std::fs::read_to_string(dir.path(&format!("{name}-claim.json"))).unwrap(),
            "statement",
        )
    };
    let other = dir.path("hidden-other.json");
    expect(
        &[
            "migrate",
            "claim",
            "--kind",
            "bip32",
            "--legacy-secret",
            &seed,
            "--target",
            &target,
            "--epoch",
            "42",
            "--path",
            "m/0'",
            "--hidden-path-depth",
            "2",
            "--out",
            &other,
        ],
        0,
    );
    let other_statement = json_member(&std::fs::read_to_string(&other).unwrap(), "statement");
    assert_eq!(other_statement.len(), statement_of("hidden").len());
    assert_ne!(other_statement, statement_of("hidden"));

    let out = dir.path("refused.json");
    let refused = |args: &[&str], needle: &str| {
        let mut full = vec![
            "migrate",
            "claim",
            "--out",
            &out,
            "--epoch",
            "1",
            "--target",
            target.as_str(),
        ];
        full.extend_from_slice(args);
        let output = qsag(&full);
        let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
        assert_eq!(code(&output), 1, "{args:?}: {stderr}");
        assert!(stderr.contains(needle), "{args:?}: {stderr}");
        assert!(!Path::new(&out).exists(), "{args:?}");
    };
    let root = "5b75adecf53548f3ec6ad7d78383bf84cc57b55a3127c72b9a2481752dd88b21";
    refused(
        &["--kind", "btc-taproot-tree", "--legacy-secret", &taproot],
        "requires --merkle-root",
    );
    refused(
        &[
            "--kind",
            "btc-taproot",
            "--legacy-secret",
            &taproot,
            "--merkle-root",
            root,
        ],
        "--merkle-root does not apply",
    );
    refused(
        &[
            "--kind",
            "eth-eoa",
            "--legacy-secret",
            &taproot,
            "--root",
            "extended-key",
        ],
        "applies to BIP-32",
    );
    refused(
        &[
            "--kind",
            "bip32",
            "--legacy-secret",
            &seed,
            "--path",
            "m/1",
            "--root",
            "xpub",
        ],
        "is not 'seed' or 'extended-key'",
    );
    refused(
        &[
            "--kind",
            "bip32",
            "--legacy-secret",
            &seed,
            "--path",
            "m/0'/1",
            "--hidden-path-depth",
            "1",
        ],
        "longer than --hidden-path-depth",
    );
    refused(
        &[
            "--kind",
            "cardano-ed25519",
            "--legacy-secret",
            &cardano,
            "--path",
            "m/0'",
            "--hidden-path-depth",
            "2",
        ],
        "applies to BIP-32",
    );
    // A seed is not an extended key, and a damaged xprv fails its checksum.
    refused(
        &[
            "--kind",
            "bip32",
            "--legacy-secret",
            &seed,
            "--path",
            "m/1",
            "--root",
            "extended-key",
        ],
        "extended private key must be",
    );
    let damaged = write(
        "damaged.xprv",
        "xprv9uHRZZhk6KAJC1avXpDAp4MDc3sQKNxDiPvvkX8Br5ngLNv1TxvUxt4cV1rGL5hj6KCesnDYUhd7oWgT11eZG7XnxHrnYeSvkzY7d2bhkJ8",
    );
    refused(
        &[
            "--kind",
            "bip32",
            "--legacy-secret",
            &damaged,
            "--path",
            "m/1",
            "--root",
            "extended-key",
        ],
        "checksum mismatch",
    );
}

#[test]
fn migrate_verify_refuses_wrong_target_epoch_domain_and_altered_files() {
    let dir = Workdir::new("migrate-verify");
    let target = migration_target(&dir, "target");
    let other_target = migration_target(&dir, "other-target");
    let secp = dir.path("secp.hex");
    std::fs::write(&secp, SECP_KEY_ONE).unwrap();
    let domain = "42".repeat(32);
    let proof = migrate_prove(
        &dir,
        "proof.json",
        "eth-eoa",
        &secp,
        &target,
        "42",
        &["--domain-hex", &domain],
    );
    let verify = |file: &str, epoch: &str, extra: &[&str], expected: i32, needle: &str| {
        let mut args = vec!["migrate", "verify", "--proof", file, "--epoch", epoch];
        args.extend_from_slice(extra);
        let output = qsag(&args);
        let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
        assert_eq!(code(&output), expected, "{args:?}: {stderr}");
        assert!(stderr.contains(needle), "{args:?}: {stderr}");
    };
    let in_domain = ["--domain-hex", domain.as_str()];
    verify(&proof, "42", &in_domain, 0, "");
    verify(
        &proof,
        "42",
        &["--domain-hex", &domain, "--target", &target],
        0,
        "",
    );
    // The verifier names the epoch; there is no default.
    let output = qsag(&[
        "migrate",
        "verify",
        "--proof",
        &proof,
        "--domain-hex",
        &domain,
    ]);
    assert_eq!(code(&output), 1);
    verify(&proof, "43", &in_domain, 2, "epoch");
    // The default domain is not the proof's, nor is any other.
    verify(&proof, "42", &[], 2, "another migration domain");
    verify(
        &proof,
        "42",
        &["--domain-hex", &"43".repeat(32)],
        2,
        "another migration domain",
    );
    verify(
        &proof,
        "42",
        &["--domain-hex", &domain, "--target", &other_target],
        2,
        "another target",
    );

    let original = std::fs::read_to_string(&proof).unwrap();
    let altered = dir.path("altered.json");
    let write_altered = |text: String| {
        assert_ne!(text, original);
        std::fs::write(&altered, text).unwrap();
    };
    // A changed proof body.
    std::fs::write(&altered, &original).unwrap();
    flip_hex_digit(&altered, "proof");
    assert_ne!(std::fs::read_to_string(&altered).unwrap(), original);
    verify(&altered, "42", &in_domain, 2, "");
    // A rendered member that no longer matches the statement: the epoch, the target.
    write_altered(original.replace("\"epoch\": 42", "\"epoch\": 43"));
    verify(&altered, "43", &in_domain, 2, "\"epoch\" does not match");
    write_altered(original.replace(&target, &other_target));
    verify(&altered, "42", &in_domain, 2, "commits to");
    // A statement for another epoch with its rendering made consistent: the proof is
    // bound to the original statement and fails.
    let other_epoch = migrate_prove(
        &dir,
        "epoch-43.json",
        "eth-eoa",
        &secp,
        &target,
        "43",
        &["--domain-hex", &domain],
    );
    let other_epoch = std::fs::read_to_string(other_epoch).unwrap();
    let proof_member = |text: &str| json_member(text, "proof");
    write_altered(
        other_epoch
            .replace(&proof_member(&other_epoch), &proof_member(&original))
            .replace(
                &format!(
                    "\"proof_bytes\": {}",
                    json_member(&other_epoch, "proof_bytes")
                ),
                &format!("\"proof_bytes\": {}", json_member(&original, "proof_bytes")),
            ),
    );
    verify(&altered, "43", &in_domain, 2, "verification failed");
    // Trailing proof bytes, a length that lies, an extra member, another format.
    let body = proof_member(&original);
    write_altered(original.replace(&body, &format!("{body}AAAA")));
    verify(&altered, "42", &in_domain, 2, "");
    let length = json_member(&original, "proof_bytes");
    write_altered(original.replace(&format!("\"proof_bytes\": {length}"), "\"proof_bytes\": 1"));
    verify(&altered, "42", &in_domain, 2, "proof_bytes");
    write_altered(original.replace("\"kind\":", "\"note\": \"x\",\n  \"kind\":"));
    verify(&altered, "42", &in_domain, 2, "unexpected member");
    write_altered(original.replace("qsag-migration-proof-v2", "qsag-migration-proof-v1"));
    verify(
        &altered,
        "42",
        &in_domain,
        2,
        "not a qsag-migration-proof-v2",
    );
    // A proof padded far beyond any proof of the statement is refused by its size.
    write_altered(original.replace(&body, &"A".repeat(4 * body.len())));
    verify(&altered, "42", &in_domain, 2, "larger than any proof");
    // A claim file is not a proof.
    let claim = dir.path("claim.json");
    expect(
        &[
            "migrate",
            "claim",
            "--kind",
            "eth-eoa",
            "--legacy-secret",
            &secp,
            "--target",
            &target,
            "--epoch",
            "42",
            "--domain-hex",
            &domain,
            "--out",
            &claim,
        ],
        0,
    );
    verify(&claim, "42", &in_domain, 2, "not a qsag-migration-proof-v2");
    // `prove` never overwrites.
    let output = qsag(&[
        "migrate",
        "prove",
        "--kind",
        "eth-eoa",
        "--legacy-secret",
        &secp,
        "--target",
        &target,
        "--epoch",
        "42",
        "--out",
        &proof,
    ]);
    assert_eq!(code(&output), 5);
    assert_eq!(std::fs::read_to_string(&proof).unwrap(), original);
}

#[test]
fn migrate_registry_records_each_credential_once() {
    let dir = Workdir::new("migrate-registry");
    let target = migration_target(&dir, "target");
    let other_target = migration_target(&dir, "other-target");
    let key = |name: &str, hex: &str| {
        let path = dir.path(name);
        std::fs::write(&path, hex).unwrap();
        path
    };
    let first = key("first.hex", SECP_KEY_ONE);
    let second = key("second.hex", &format!("{}02", "00".repeat(31)));
    let third = key("third.hex", &format!("{}03", "00".repeat(31)));
    let registry = dir.path("registry");
    let reg = ["--registry-dir", registry.as_str()];

    // Creation names its rollback protection or waives it, in a fresh directory.
    expect(
        &["migrate", "registry", "init", "--registry-dir", &registry],
        1,
    );
    assert!(!Path::new(&registry).exists());
    expect(
        &[
            "migrate",
            "registry",
            "init",
            "--registry-dir",
            &registry,
            "--ephemeral-unanchored",
        ],
        0,
    );
    expect(
        &[
            "migrate",
            "registry",
            "init",
            "--registry-dir",
            &registry,
            "--ephemeral-unanchored",
        ],
        4,
    );

    let run = |args: &[&str], expected: i32| -> String {
        let mut full = args.to_vec();
        full.extend_from_slice(&reg);
        full.push("--json");
        expect(&full, expected)
    };
    let lookup =
        |selector: &str, value: &str| run(&["migrate", "registry", "lookup", selector, value], 0);

    let proof = migrate_prove(&dir, "first.json", "btc-p2wpkh", &first, &target, "7", &[]);
    let proof_text = std::fs::read_to_string(&proof).unwrap();
    let nullifier = json_member(&proof_text, "nullifier");
    let legacy_id = json_member(&proof_text, "legacy_id");
    assert_eq!(
        json_member(&lookup("--statement", &proof), "status"),
        "absent"
    );

    // A proof that does not verify registers nothing.
    let bad = dir.path("bad.json");
    std::fs::write(&bad, &proof_text).unwrap();
    flip_hex_digit(&bad, "proof");
    run(
        &[
            "migrate",
            "verify",
            "--register",
            "--proof",
            &bad,
            "--epoch",
            "7",
        ],
        2,
    );
    run(
        &[
            "migrate",
            "verify",
            "--register",
            "--proof",
            &proof,
            "--epoch",
            "8",
        ],
        2,
    );
    assert_eq!(
        json_member(&lookup("--nullifier", &nullifier), "status"),
        "absent"
    );
    // `--register` needs a registry, and registry options need `--register`.
    expect(
        &[
            "migrate",
            "verify",
            "--register",
            "--proof",
            &proof,
            "--epoch",
            "7",
        ],
        1,
    );
    expect(
        &[
            "migrate",
            "verify",
            "--proof",
            &proof,
            "--epoch",
            "7",
            "--registry-dir",
            &registry,
        ],
        1,
    );

    // Verify and register in one step; the same proof again is accepted and writes nothing.
    let receipt = run(
        &[
            "migrate",
            "verify",
            "--register",
            "--proof",
            &proof,
            "--epoch",
            "7",
        ],
        0,
    );
    assert_eq!(json_member(&receipt, "status"), "finalized");
    assert_eq!(json_member(&receipt, "appended"), "true");
    let checkpoint = json_member(&receipt, "checkpoint");
    assert!(checkpoint.starts_with("1:"), "{checkpoint}");
    let again = run(
        &[
            "migrate", "registry", "register", "--proof", &proof, "--epoch", "7",
        ],
        0,
    );
    assert_eq!(json_member(&again, "status"), "finalized");
    assert_eq!(json_member(&again, "appended"), "false");
    assert_eq!(json_member(&again, "checkpoint"), checkpoint);
    for (selector, value) in [
        ("--nullifier", nullifier.as_str()),
        ("--legacy-id", legacy_id.as_str()),
        ("--statement", proof.as_str()),
    ] {
        let found = lookup(selector, value);
        assert_eq!(json_member(&found, "status"), "finalized", "{selector}");
        assert_eq!(json_member(&found, "nullifier"), nullifier, "{selector}");
        assert_eq!(
            json_member(&found, "pq_commitment"),
            json_member(&proof_text, "pq_commitment"),
            "{selector}"
        );
    }

    // The same credential to another target, at another epoch or in another domain: each
    // proof is valid and each is refused with exit code 4. (Another statement kind for the
    // same credential is refused the same way; `hem::registry` tests that. Another
    // credential of the same key, such as its Ethereum address, is a separate migration.)
    let domain = "42".repeat(32);
    for (name, kind, target, epoch, extra) in [
        ("retarget.json", "btc-p2wpkh", &other_target, "7", &[][..]),
        ("later.json", "btc-p2wpkh", &target, "8", &[][..]),
        (
            "domain.json",
            "btc-p2wpkh",
            &target,
            "7",
            &["--domain-hex", domain.as_str()][..],
        ),
    ] {
        let conflicting = migrate_prove(&dir, name, kind, &first, target, epoch, extra);
        let mut verify = vec![
            "migrate",
            "verify",
            "--proof",
            &conflicting,
            "--epoch",
            epoch,
        ];
        verify.extend_from_slice(extra);
        expect(&verify, 0);
        verify.push("--register");
        let output = {
            let mut full = verify.clone();
            full.extend_from_slice(&reg);
            qsag(&full)
        };
        let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
        assert_eq!(code(&output), 4, "{name}: {stderr}");
        assert!(
            stderr.contains("bound to a different record") || stderr.contains("already migrated"),
            "{name}: {stderr}"
        );
    }
    // Nothing moved: same checkpoint, same binding.
    let found = lookup("--nullifier", &nullifier);
    assert_eq!(json_member(&found, "checkpoint"), checkpoint);
    assert_eq!(
        json_member(&found, "pq_commitment"),
        json_member(&proof_text, "pq_commitment")
    );

    // Enrol, then finalize. Finalizing what was never enrolled is refused.
    let enrolled = migrate_prove(&dir, "second.json", "eth-eoa", &second, &target, "7", &[]);
    let unknown = migrate_prove(&dir, "third.json", "eth-eoa", &third, &target, "7", &[]);
    run(
        &[
            "migrate", "registry", "finalize", "--proof", &unknown, "--epoch", "7",
        ],
        4,
    );
    let receipt = run(
        &[
            "migrate", "registry", "enroll", "--proof", &enrolled, "--epoch", "7",
        ],
        0,
    );
    assert_eq!(json_member(&receipt, "status"), "enrolled");
    assert_eq!(json_member(&receipt, "appended"), "true");
    assert_eq!(
        json_member(&lookup("--statement", &enrolled), "status"),
        "enrolled"
    );
    let receipt = run(
        &[
            "migrate", "registry", "enroll", "--proof", &enrolled, "--epoch", "7",
        ],
        0,
    );
    assert_eq!(json_member(&receipt, "appended"), "false");
    // An enrolment already reserves the credential against another target.
    let displaced = migrate_prove(
        &dir,
        "displace.json",
        "eth-eoa",
        &second,
        &other_target,
        "7",
        &[],
    );
    run(
        &[
            "migrate", "registry", "register", "--proof", &displaced, "--epoch", "7",
        ],
        4,
    );
    run(
        &[
            "migrate", "registry", "finalize", "--proof", &displaced, "--epoch", "7",
        ],
        4,
    );
    let receipt = run(
        &[
            "migrate", "registry", "finalize", "--proof", &enrolled, "--epoch", "7",
        ],
        0,
    );
    assert_eq!(json_member(&receipt, "status"), "finalized");
    assert_eq!(json_member(&receipt, "appended"), "true");
    assert_eq!(
        json_member(&lookup("--statement", &enrolled), "status"),
        "finalized"
    );
    assert_eq!(
        json_member(&lookup("--statement", &unknown), "status"),
        "absent"
    );

    // A proof file above a megabyte (BIP-32, five levels) registers and is found again.
    let seed = key("seed.hex", "000102030405060708090a0b0c0d0e0f");
    let deep = migrate_prove(
        &dir,
        "deep.json",
        "bip32",
        &seed,
        &target,
        "7",
        &["--path", "m/44'/0'/0'/0/0"],
    );
    assert!(std::fs::metadata(&deep).unwrap().len() > 500_000);
    run(
        &[
            "migrate", "registry", "register", "--proof", &deep, "--epoch", "7",
        ],
        0,
    );
    let found = lookup("--statement", &deep);
    assert_eq!(json_member(&found, "status"), "finalized");
    assert_eq!(json_member(&found, "key_exposure"), "revealed");

    // A sealed registry key needs its passphrase.
    let sealed = dir.path("sealed-registry");
    let pass = dir.path("pass");
    std::fs::write(&pass, "correct horse battery staple").unwrap();
    expect(
        &[
            "migrate",
            "registry",
            "init",
            "--registry-dir",
            &sealed,
            "--ephemeral-unanchored",
            "--passphrase-file",
            &pass,
        ],
        0,
    );
    let sealed_args = [
        "migrate",
        "registry",
        "register",
        "--registry-dir",
        &sealed,
        "--proof",
        &proof,
        "--epoch",
        "7",
    ];
    assert_ne!(code(&qsag(&sealed_args)), 0);
    let mut with_pass = sealed_args.to_vec();
    with_pass.extend(["--passphrase-file", pass.as_str()]);
    expect(&with_pass, 0);
}

#[cfg(unix)]
#[test]
fn migrate_registry_rollback_is_refused_with_an_anchor_or_a_retained_checkpoint() {
    use std::os::unix::fs::DirBuilderExt;
    let dir = Workdir::new("migrate-registry-rollback");
    let target = migration_target(&dir, "target");
    let other_target = migration_target(&dir, "other-target");
    let first = dir.path("first.hex");
    std::fs::write(&first, SECP_KEY_ONE).unwrap();
    let second = dir.path("second.hex");
    std::fs::write(&second, format!("{}02", "00".repeat(31))).unwrap();
    let proof_a = migrate_prove(&dir, "a.json", "btc-p2wpkh", &first, &target, "7", &[]);
    let proof_b = migrate_prove(&dir, "b.json", "btc-p2wpkh", &second, &target, "7", &[]);
    // The double migration a rollback is for: the first key again, to another address.
    let proof_a2 = migrate_prove(
        &dir,
        "a2.json",
        "btc-p2wpkh",
        &first,
        &other_target,
        "7",
        &[],
    );
    let register = |registry: &[&str], proof: &str, expected: i32| -> String {
        let mut args = vec![
            "migrate",
            "verify",
            "--register",
            "--proof",
            proof,
            "--epoch",
            "7",
            "--json",
        ];
        args.extend_from_slice(registry);
        expect(&args, expected)
    };
    let lookup = |registry: &[&str], proof: &str, expected: i32| -> String {
        let mut args = vec![
            "migrate",
            "registry",
            "lookup",
            "--statement",
            proof,
            "--json",
        ];
        args.extend_from_slice(registry);
        expect(&args, expected)
    };

    // With an anchor.
    let anchor = dir.0.join("registry-anchor");
    std::fs::DirBuilder::new()
        .mode(0o700)
        .create(&anchor)
        .unwrap();
    let anchor = anchor.to_str().unwrap();
    let anchored_dir = dir.path("anchored");
    // An anchor on the registry's device needs the acknowledgement.
    expect(
        &[
            "migrate",
            "registry",
            "init",
            "--registry-dir",
            &anchored_dir,
            "--anchor-dir",
            anchor,
        ],
        4,
    );
    let _ = std::fs::remove_dir_all(&anchored_dir);
    let anchored = [
        "--registry-dir",
        anchored_dir.as_str(),
        "--anchor-dir",
        anchor,
        "--allow-single-disk-anchor",
    ];
    let mut init = vec!["migrate", "registry", "init"];
    init.extend_from_slice(&anchored);
    expect(&init, 0);
    // An anchored registry does not open without its anchor.
    lookup(&["--registry-dir", &anchored_dir], &proof_a, 4);
    register(&anchored, &proof_a, 0);
    let before_b = snapshot_dir_files(Path::new(&anchored_dir));
    register(&anchored, &proof_b, 0);
    assert_eq!(
        json_member(&lookup(&anchored, &proof_b, 0), "status"),
        "finalized"
    );
    restore_dir_files_in_place(&before_b);
    // The log is one record behind the anchor: nothing opens, nothing registers.
    lookup(&anchored, &proof_a, 4);
    register(&anchored, &proof_b, 4);
    register(&anchored, &proof_a2, 4);
    // Rolled back to before the first migration as well.
    let after_init: Vec<_> = before_b
        .iter()
        .filter(|(path, _)| !path.to_string_lossy().ends_with("registry.log"))
        .cloned()
        .collect();
    restore_dir_files_in_place(&after_init);
    register(&anchored, &proof_a2, 4);

    // Without an anchor, a retained checkpoint is the defence.
    let plain_dir = dir.path("plain");
    let plain = ["--registry-dir", plain_dir.as_str()];
    expect(
        &[
            "migrate",
            "registry",
            "init",
            "--registry-dir",
            &plain_dir,
            "--ephemeral-unanchored",
        ],
        0,
    );
    let checkpoint_a = json_member(&register(&plain, &proof_a, 0), "checkpoint");
    let before_b = snapshot_dir_files(Path::new(&plain_dir));
    let checkpoint_b = json_member(&register(&plain, &proof_b, 0), "checkpoint");
    assert_ne!(checkpoint_a, checkpoint_b);
    let at_least = |checkpoint: &str| {
        vec![
            "--registry-dir".to_string(),
            plain_dir.clone(),
            "--min-checkpoint".to_string(),
            checkpoint.to_string(),
        ]
    };
    let with = |checkpoint: &str, proof: &str, expected: i32| {
        let options = at_least(checkpoint);
        let options: Vec<&str> = options.iter().map(String::as_str).collect();
        lookup(&options, proof, expected)
    };
    with(&checkpoint_a, &proof_b, 0);
    with(&checkpoint_b, &proof_b, 0);
    restore_dir_files_in_place(&before_b);
    // The restored log is a valid earlier state: it opens, and has forgotten the second
    // migration. Only the retained checkpoint tells.
    assert_eq!(
        json_member(&lookup(&plain, &proof_b, 0), "status"),
        "absent"
    );
    with(&checkpoint_a, &proof_b, 0);
    with(&checkpoint_b, &proof_b, 4);
    // A checkpoint of the right length and the wrong tip is refused too.
    let forged = format!("1:{}", "00".repeat(32));
    with(&forged, &proof_a, 4);
    // The anchor and the checkpoint are alternatives.
    let mut both = anchored.to_vec();
    both.extend(["--min-checkpoint", checkpoint_a.as_str()]);
    lookup(&both, &proof_a, 1);
}

#[test]
fn migration_rejects_sealed_or_damaged_envelope_legacy_seeds() {
    let dir = Workdir::new("migration-sealed-seed");
    let target = migration_target(&dir, "target");
    let key = dir.path("legacy.json");
    let output = dir.path("claim.json");
    let claim = |kind: &str| {
        let mut args = vec![
            "migrate",
            "claim",
            "--kind",
            kind,
            "--legacy-secret",
            &key,
            "--target",
            &target,
            "--epoch",
            "1",
            "--out",
            &output,
        ];
        if kind == "bip32" {
            args.extend(["--path", "m/0'"]);
        }
        let rejected = qsag(&args);
        assert_eq!(code(&rejected), 1, "{kind}");
        assert!(!Path::new(&output).exists(), "{kind}");
        String::from_utf8_lossy(&rejected.stderr).into_owned()
    };
    for header in [
        "envelope",
        "salt",
        "envelope_tag",
        "envelope_salt",
        "envelope_nonce",
    ] {
        for kind in ["btc-p2wpkh", "ed25519", "bip32"] {
            std::fs::write(&key, format!("{{\"seed\":\"{SEED}\",\"{header}\":\"00\"}}")).unwrap();
            assert!(
                claim(kind).contains("sealed legacy keys"),
                "{kind} {header}"
            );
            let short_json = format!("{{\"{header}\":0}}");
            std::fs::write(&key, format!("{short_json:<32}")).unwrap();
            assert!(
                claim(kind).contains("sealed legacy keys"),
                "{kind} {header}"
            );
        }
    }
    // A 32-byte malformed JSON object must never be treated as 32 raw key bytes.
    let malformed_32b = format!("{:<32}", "{\"seed\":\"0011\"}");
    assert_eq!(malformed_32b.len(), 32);
    std::fs::write(&key, malformed_32b).unwrap();
    assert!(claim("btc-p2wpkh").contains("must be 32 bytes"));
    // An unsealed JSON seed is accepted.
    std::fs::write(&key, format!("{{\"seed\":\"{SEED}\"}}")).unwrap();
    expect(
        &[
            "migrate",
            "claim",
            "--kind",
            "ed25519",
            "--legacy-secret",
            &key,
            "--target",
            &target,
            "--epoch",
            "1",
            "--out",
            &output,
        ],
        0,
    );
}

#[test]
fn hd_rejects_threshold_truncation_before_enrollment() {
    let dir = Workdir::new("hd-threshold-overflow");
    let vault = dir.path("vault");
    let watch = dir.path("watch.json");
    expect(
        &[
            "hd",
            "keygen",
            "--threshold",
            "65538",
            "--parties",
            "3",
            "--count",
            "2",
            "--vault-dir",
            &vault,
            "--watch-out",
            &watch,
            "--deterministic-test-only",
            "--allow-unencrypted",
        ],
        1,
    );
    assert!(!Path::new(&watch).exists());
    assert!(!Path::new(&vault).exists());
}

#[cfg(unix)]
#[test]
fn enrollment_preflights_party_files_before_external_anchor_provisioning() {
    use std::os::unix::fs::DirBuilderExt;
    let dir = Workdir::new("preflight-party-files");
    for name in [
        "hd",
        "mldsa-share",
        "mldsa-burn",
        "mldsa-burn-lock",
        "voprf-rss",
        "voprf-spdz",
        "anchor",
    ] {
        std::fs::DirBuilder::new()
            .mode(0o700)
            .create(dir.path(name))
            .unwrap();
    }
    let anchor = dir.path("anchor");
    for (vault_name, filename, command, subcommand, parties) in [
        ("hd", "hd-custodian-0.share", "hd", "keygen", "3"),
        (
            "mldsa-share",
            "mldsa-party-0.share",
            "cred",
            "mldsa-keygen",
            "3",
        ),
        (
            "mldsa-burn",
            "mldsa-party-0.burn",
            "cred",
            "mldsa-keygen",
            "3",
        ),
        (
            "mldsa-burn-lock",
            "mldsa-party-0.burn.lock",
            "cred",
            "mldsa-keygen",
            "3",
        ),
        (
            "voprf-rss",
            "voprf-party-0.share",
            "cred",
            "voprf-keygen",
            "5",
        ),
        (
            "voprf-spdz",
            "voprf-counter-0.json",
            "cred",
            "voprf-keygen",
            "3",
        ),
    ] {
        let vault = dir.path(vault_name);
        let occupied = Path::new(&vault).join(filename);
        std::fs::write(&occupied, b"existing custody artifact").unwrap();
        let mut args = vec![
            command,
            subcommand,
            "--vault-dir",
            &vault,
            "--threshold",
            "2",
            "--parties",
            parties,
            "--allow-unencrypted",
            "--anchor-dir",
            &anchor,
            "--allow-single-disk-anchor",
        ];
        let public = dir.path(&format!("{vault_name}.public"));
        if command == "hd" {
            args.extend(["--count", "2", "--watch-out", &public]);
        } else {
            args.extend(["--public-out", &public]);
        }
        let output = qsag(&args);
        assert_eq!(
            code(&output),
            1,
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(String::from_utf8_lossy(&output.stderr).contains("already exists"));
        assert_eq!(
            std::fs::read(&occupied).unwrap(),
            b"existing custody artifact"
        );
        assert_eq!(std::fs::read_dir(&anchor).unwrap().count(), 0);
    }
}

#[test]
fn migrate_zcash_transparent_orchard_and_ironwood_claim_prove_verify_and_register() {
    let dir = Workdir::new("migrate-zcash");
    let target = migration_target(&dir, "target");
    let write = |name: &str, contents: &str| {
        let path = dir.path(name);
        std::fs::write(&path, contents).unwrap();
        path
    };
    let secp = write("secp.hex", &format!("{SECP_KEY_ONE}\n"));
    let orchard_sk = write("orchard.hex", &"21".repeat(32));
    let ironwood_json = write(
        "ironwood.json",
        &format!(
            "{{\n  \"spending_key\": \"{}\",\n  \"alpha\": \"09{}\",\n  \"value\": 125000000,\n  \"rho\": \"07{}\",\n  \"rseed\": \"{}\"\n}}\n",
            "41".repeat(32),
            "00".repeat(31),
            "00".repeat(31),
            "55".repeat(32),
        ),
    );

    let registry = dir.path("zcash-registry");
    expect(
        &[
            "migrate",
            "registry",
            "init",
            "--registry-dir",
            &registry,
            "--ephemeral-unanchored",
        ],
        0,
    );

    for (alias, canonical, secret, member) in [
        (
            "zip2007-t1",
            "zcash-transparent",
            secp.as_str(),
            "legacy_zcash_address",
        ),
        (
            "orchard",
            "orchard",
            orchard_sk.as_str(),
            "legacy_orchard_address",
        ),
        ("zip2005", "ironwood", ironwood_json.as_str(), "anchor"),
    ] {
        let claim = dir.path(&format!("{canonical}-claim.json"));
        expect(
            &[
                "migrate",
                "claim",
                "--kind",
                alias,
                "--legacy-secret",
                secret,
                "--target",
                &target,
                "--epoch",
                "99",
                "--out",
                &claim,
            ],
            0,
        );
        let claim_text = std::fs::read_to_string(&claim).unwrap();
        assert_eq!(json_member(&claim_text, "kind"), canonical);
        assert_eq!(json_member(&claim_text, "key_exposure"), "hidden");
        assert!(!json_member(&claim_text, member).is_empty());

        let proof = migrate_prove(
            &dir,
            &format!("{canonical}-proof.json"),
            alias,
            secret,
            &target,
            "99",
            &[],
        );
        let proof_text = std::fs::read_to_string(&proof).unwrap();
        assert_eq!(json_member(&proof_text, "regime"), "TurboShakeJohnson400");
        assert_eq!(
            json_member(&proof_text, "statement"),
            json_member(&claim_text, "statement")
        );

        let verified = expect(
            &[
                "migrate",
                "verify",
                "--register",
                "--registry-dir",
                &registry,
                "--proof",
                &proof,
                "--epoch",
                "99",
                "--target",
                &target,
                "--json",
            ],
            0,
        );
        assert_eq!(json_member(&verified, "valid"), "true");
        assert_eq!(json_member(&verified, "status"), "finalized");
        assert_eq!(json_member(&verified, "appended"), "true");
    }

    // Sapling claim & help check (`sapling` / `zcash-sapling`)
    let sapling_sk = write("sapling.hex", &"31".repeat(32));
    let sapling_claim = dir.path("sapling-claim.json");
    expect(
        &[
            "migrate",
            "claim",
            "--kind",
            "zcash-sapling",
            "--legacy-secret",
            &sapling_sk,
            "--target",
            &target,
            "--epoch",
            "99",
            "--out",
            &sapling_claim,
        ],
        0,
    );
    let sapling_claim_text = std::fs::read_to_string(&sapling_claim).unwrap();
    assert_eq!(json_member(&sapling_claim_text, "kind"), "sapling");
    assert!(!json_member(&sapling_claim_text, "legacy_sapling_address").is_empty());
}

#[test]
fn quintic_public_cli_roundtrip() {
    use qsag_agg::sig::digest4_to_bytes;
    use qsag_agg::{AggSigProfile, FsWalEpochSink, ValidatorKeypair};

    let dir = Workdir::new("quintic-public");
    let mut kp = ValidatorKeypair::keygen_deterministic(AggSigProfile::JortsPoseidon2, &[7; 32], 0);
    let (mut wal, _) = FsWalEpochSink::create_new_for_fresh_key(
        dir.path("validator.wal"),
        &digest4_to_bytes(&kp.pk.pk_root),
        [8; 32],
    )
    .unwrap();
    let msg = dir.path("msg");
    let pk = dir.path("pk");
    let signature = dir.path("signature");
    let proof = dir.path("aggregate");
    let sig = kp
        .sign_stateful(&std::fs::read(&msg).unwrap(), 0, &mut wal)
        .unwrap();
    std::fs::write(&pk, kp.pk.to_bytes()).unwrap();
    std::fs::write(&signature, sig.to_bytes()).unwrap();
    expect(
        &[
            "aggregate",
            "--pubkeys",
            &pk,
            "--signers",
            "0",
            "--sigs",
            &signature,
            "--message",
            &msg,
            "--hem-profile",
            "quintic-turbo",
            "--out",
            &proof,
        ],
        0,
    );
    let verify = |message: &str, profile: &str, code| {
        expect(
            &[
                "verify-aggregate",
                "--allow-any-subset",
                "--pubkeys",
                &pk,
                "--message",
                message,
                "--proof",
                &proof,
                "--hem-profile",
                profile,
            ],
            code,
        );
    };
    verify(&msg, "quintic-turbo", 0);
    verify(&dir.path("other"), "quintic-turbo", 2);
    verify(&msg, "quintic-gl24", 2);
    flip_hex_digit(&proof, "proof");
    verify(&msg, "quintic-turbo", 2);
}
