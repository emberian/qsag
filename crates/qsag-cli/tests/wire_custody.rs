//! Production binary, three independent processes and one anchor/journal per share.
#![forbid(unsafe_code)]
#![cfg(unix)]
use qsag_accel::CpuReferenceBackend;
use qsag_core::cnf_rss::CnfRssKeyShare256;
use qsag_fts::{
    FrontierDpTable, FrontierFtsProfile, FrontierFtsPublicKey, FrontierFtsSignature,
    verify_frontier_fts,
};
use qsag_fts::{FrontierFtsSigningKey, FsWalFtsEpochLatch};
use std::{
    fs,
    net::TcpListener,
    os::unix::fs::PermissionsExt,
    path::{Path, PathBuf},
    process::{Command, Stdio},
};

struct Temp(PathBuf);
impl Drop for Temp {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
fn run(root: &Path, scheme: &str, op: &str, peers: &str, nonce: u8, expected: bool) {
    let mut children = Vec::new();
    for i in 0..3 {
        let mut cmd = Command::new(env!("CARGO_BIN_EXE_qsag"));
        cmd.args([
            "quorum",
            "wire",
            op,
            "--deployment-id",
            &"68".repeat(32),
            "--profile",
            scheme,
            "--vault-dir",
        ])
        .arg(root.join(format!("custodian-{i}")))
        .arg("--anchor-dir")
        .arg(root.join(format!("anchor-{i}")))
        .arg("--allow-single-disk-anchor");
        if op != "init" {
            cmd.args([
                "--session",
                &format!("{nonce:02x}").repeat(32),
                "--peers",
                peers,
            ]);
            if op == "dkg" {
                cmd.args(["--threshold", "2", "--party", &i.to_string()]);
            } else {
                cmd.arg("--out").arg(root.join(format!("{op}-{nonce}-{i}")));
            }
        }
        if op == "sign" {
            cmd.arg("--in").arg(root.join("message"));
        }
        children.push(cmd.stderr(Stdio::piped()).spawn().unwrap());
    }
    let results: Vec<_> = children
        .into_iter()
        .map(|p| p.wait_with_output().unwrap())
        .collect();
    for r in results {
        assert_eq!(
            r.status.success(),
            expected,
            "{scheme} {op}: {}",
            String::from_utf8_lossy(&r.stderr)
        );
        if !expected {
            assert!(
                String::from_utf8_lossy(&r.stderr).contains("journal"),
                "{:?}",
                r
            );
        }
    }
}
fn exercise(profile: FrontierFtsProfile, name: &str) {
    let root = Temp(std::env::temp_dir().join(
        format!("qsag-wire-{name}-{}-{}",std::process::id(),
        std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()),
    ));
    fs::create_dir(&root.0).unwrap();
    for i in 0..3 {
        let vault = root.0.join(format!("custodian-{i}"));
        fs::create_dir(&vault).unwrap();
        fs::set_permissions(&vault, fs::Permissions::from_mode(0o700)).unwrap();
        let links: Vec<_> = (0..3)
            .map(|j| {
                if i == j {
                    [0; 32]
                } else {
                    [1 + 3 * i.min(j) + i.max(j); 32]
                }
            })
            .collect();
        fs::write(vault.join("links"), links.as_flattened()).unwrap();
    }
    let reserve: Vec<_> = (0..3)
        .map(|_| TcpListener::bind("127.0.0.1:0").unwrap())
        .collect();
    let addresses = reserve
        .iter()
        .map(|l| l.local_addr().unwrap().to_string())
        .collect::<Vec<_>>()
        .join(",");
    drop(reserve);
    let missing = Command::new(env!("CARGO_BIN_EXE_qsag"))
        .args(["quorum", "wire", "init", "--vault-dir"])
        .arg(root.0.join("custodian-0"))
        .output()
        .unwrap();
    assert!(!missing.status.success());
    assert!(String::from_utf8_lossy(&missing.stderr).contains("requires --anchor-dir"));
    assert!(!root.0.join("custodian-0/sessions").exists());
    fs::write(root.0.join("message"), b"release").unwrap();
    run(&root.0, name, "dkg", &addresses, 4, true);
    let seed =
        CnfRssKeyShare256::from_secret_bytes(&fs::read(root.0.join("custodian-0/share")).unwrap())
            .unwrap()
            .pk_seed;
    run(&root.0, name, "init", &addresses, 0, true);
    run(&root.0, name, "public", &addresses, 1, true);
    run(&root.0, name, "sign", &addresses, 2, true);
    let public = fs::read(root.0.join("public-1-0")).unwrap();
    assert_eq!(public.len(), 64);
    assert_eq!(&public[..32], &seed);
    let pk = FrontierFtsPublicKey {
        profile,
        pk_seed: seed,
        root: public[32..].to_vec(),
    };
    let sig = fs::read(root.0.join("sign-2-0")).unwrap();
    for i in 1..3 {
        assert_eq!(
            public,
            fs::read(root.0.join(format!("public-1-{i}"))).unwrap()
        );
        assert_eq!(sig, fs::read(root.0.join(format!("sign-2-{i}"))).unwrap());
    }
    assert_eq!(sig.len(), profile.signature_bytes());
    let decoded = FrontierFtsSignature::from_bytes(profile, &sig).unwrap();
    let dp = FrontierDpTable::build(profile);
    verify_frontier_fts(&pk, &dp, b"release", &decoded).unwrap();
    assert!(verify_frontier_fts(&pk, &dp, b"other", &decoded).is_err());
    // Test-only clear oracle. Each CLI process was given one vault.
    let shares: Vec<_> = (0..3)
        .map(|i| {
            CnfRssKeyShare256::from_secret_bytes(
                &fs::read(root.0.join(format!("custodian-{i}/share"))).unwrap(),
            )
            .unwrap()
        })
        .collect();
    let (mut sk, mut prf) = ([0; 32], [0; 32]);
    for slot in 0..shares[0].config().total_slots() {
        let (x, y, _) = shares.iter().find_map(|s| s.held_slot(slot)).unwrap();
        for i in 0..32 {
            sk[i] ^= x[i];
            prf[i] ^= y[i];
        }
    }
    let clear = FrontierFtsSigningKey::keygen(profile, sk, prf, seed, true, &CpuReferenceBackend);
    assert_eq!(clear.pk.root, pk.root);
    let wal =
        FsWalFtsEpochLatch::create(root.0.join("oracle-wal"), clear.wal_key(), [18; 32]).unwrap();
    let mut clear = clear.attach_wal(Box::new(wal)).unwrap();
    assert_eq!(
        sig,
        clear
            .sign(&dp, b"release", &[2; 32])
            .unwrap()
            .to_bytes(profile)
    );
    run(&root.0, name, "sign", &addresses, 3, false);
    assert!(!root.0.join("sign-3-0").exists());
}
#[test]
fn production_frontier_wire_ceremonies() {
    exercise(FrontierFtsProfile::Full256Bit, "Full256Bit");
    exercise(FrontierFtsProfile::Compact1122, "Compact1122");
}
