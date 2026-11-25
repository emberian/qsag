//! A single custodian's migration commands.
use super::*;
use qsag_core::field::tower::{TowerGf256, eval_poly_gf256};
use qsag_core::wipe::SecretBuffer;
use qsag_migrate::hem::collab::{
    self, CustodyInput,
    engine::{Engine, Preprocessing},
    net::{Framed, StreamLink, connect_tcp_stream_mesh},
    prep::PrepDemand,
};
use std::net::{SocketAddr, TcpStream};
use std::time::Duration;

const HELP:&str = "\
qsag migrate collab split-secret --secret FILE --threshold K --parties N --out-dir DIR
qsag migrate collab prep --party I --peers ADDRS --links FILE --deployment-id HEX32 --session HEX32
    (--claim FILE [--secret-bytes N] | --triples T --randoms R) --out TAPE [--timeout-ms MS]
qsag migrate collab prove --party I --peers ADDRS --links FILE --deployment-id HEX32 --session HEX32
    --claim FILE (--xor-share FILE | --shamir-share FILE --custodian-id ID --quorum IDS)
    [--prep-tape TAPE] [--path m/...] [--merkle-root HEX32]
    [--anchor-dir DIR [--allow-single-disk-anchor] | --ephemeral-unanchored] --out PROOF [--json] [--timeout-ms MS]

Party positions and Shamir custodian IDs start at zero. ADDRS and IDS are comma-separated in party order.
Each host's links file contains N consecutive 32-byte pairwise PSKs in that order (own slot unused).
Use fresh sessions and private randomness. Preprocessing tapes are sealed to this party, deployment
and session. Keep the private .migration-key file alongside the links file. Proving removes the tape
and records its consumption locally. --anchor-dir additionally records it in an external anchor.
";

fn number(text: &str, name: &str) -> Result<usize, CliError> {
    text.parse()
        .map_err(|_| CliError::usage(format!("invalid {name}")))
}
fn needed_number(args: &Args, name: &str) -> Result<usize, CliError> {
    number(args.require(name)?, name)
}
fn failure(e: collab::ThresholdError) -> CliError {
    CliError::verify(format!("custodian protocol failed: {e:?}"))
}

fn split(args: &Args) -> Result<(), CliError> {
    let k = needed_number(args, "threshold")?;
    let n = needed_number(args, "parties")?;
    if !(2..=n).contains(&k) || k > 64 || n > 255 {
        return Err(CliError::usage(
            "require 2 <= threshold <= 64 and threshold <= parties <= 255",
        ));
    }
    let dir = args.require("out-dir")?;
    // Prefer raw when its length is exactly 32, including a raw key consisting entirely of ASCII hex.
    let raw = read_bounded_file(args.require("secret")?, MAX_KEY_FILE_BYTES)?;
    let secret = if raw.len() == 32 {
        raw
    } else {
        drop(raw);
        read_legacy_secret(args.require("secret")?, SecretForm::Key32)?
    };
    let mut shares = SecretBuffer(vec![[0u8; 32]; n]);
    let mut coeffs = SecretBuffer(vec![TowerGf256(0); k]);
    let mut rng = qsag_core::preprocessing::PartyPrivateRng::from_seed(
        os_random_32()?,
        b"QSAG.CLI.MIGRATE.SHAMIR/v1",
    );
    for (i, byte) in secret.iter().enumerate() {
        coeffs[0] = TowerGf256(*byte);
        for c in &mut coeffs[1..] {
            rng.fill_bytes(std::slice::from_mut(&mut c.0));
        }
        for (p, share) in shares.iter_mut().enumerate() {
            share[i] = eval_poly_gf256(&coeffs, TowerGf256((p + 1) as u8)).0;
        }
    }
    drop((secret, coeffs, rng));
    private_dir(dir, true)?;
    let mut written = Vec::new();
    for (i, share) in shares.iter().enumerate() {
        let path = format!("{dir}/share-{i}.bin");
        if let Err(e) = write_new(&path, share, true) {
            for own in written {
                std::fs::remove_file(own)
                    .map_err(|e| CliError::io("removing incomplete split", e))?;
            }
            return Err(e);
        }
        written.push(path);
    }
    println!("Wrote {n} shares to {dir}. Any {k} reconstruct the key.");
    Ok(())
}

struct Mesh<'a> {
    me: usize,
    peers: Vec<SocketAddr>,
    links: &'a str,
    deployment: [u8; 32],
    session: [u8; 32],
    timeout: Duration,
}

impl<'a> Mesh<'a> {
    fn parse(args: &'a Args) -> Result<Self, CliError> {
        let me = needed_number(args, "party")?;
        let peers: Vec<SocketAddr> = args
            .require("peers")?
            .split(',')
            .map(|p| {
                p.parse()
                    .map_err(|_| CliError::usage("invalid peer socket address"))
            })
            .collect::<Result<_, _>>()?;
        if !(2..=64).contains(&peers.len())
            || me >= peers.len()
            || peers
                .iter()
                .enumerate()
                .any(|(i, p)| p.port() == 0 || peers[..i].contains(p))
        {
            return Err(CliError::usage(
                "expected 2 to 64 distinct peer addresses and a valid party index",
            ));
        }
        let ms = args
            .get("timeout-ms")
            .unwrap_or("120000")
            .parse()
            .map_err(|_| CliError::usage("invalid timeout-ms"))?;
        if ms == 0 {
            return Err(CliError::usage("timeout must be positive"));
        }
        Ok(Self {
            me,
            peers,
            links: args.require("links")?,
            deployment: from_hex_exact(args.require("deployment-id")?, "deployment-id")?,
            session: from_hex_exact(args.require("session")?, "session")?,
            timeout: Duration::from_millis(ms),
        })
    }

    fn connect(&self, purpose: &[u8]) -> Result<Framed<StreamLink<TcpStream>>, CliError> {
        let bytes = read_bounded_file(self.links, (32 * self.peers.len()) as u64)?;
        if bytes.len() != 32 * self.peers.len() {
            return Err(CliError::input(
                "links must contain one 32-byte key per roster position",
            ));
        }
        let seed = Secret32::new(os_random_32()?);
        let keys = bytes.as_chunks::<32>().0.to_vec();
        let sid = cshake256_framed_32(b"QSAG.CLI.MIGRATE.MESH/v1", &[&self.session, purpose]);
        connect_tcp_stream_mesh(
            self.deployment,
            sid,
            self.me,
            &self.peers,
            keys,
            *seed,
            self.timeout,
        )
        .map_err(|e| CliError::io("connecting custodian mesh", e))
    }

    fn binding(&self) -> [u8; 32] {
        cshake256_framed_32(
            b"QSAG.CLI.MIGRATE.CUSTODIAN/v1",
            &[
                &self.deployment,
                &self.session,
                &[self.me as u8, self.peers.len() as u8],
            ],
        )
    }

    fn local_key(&self, create: bool) -> Result<Secret32, CliError> {
        let path = format!("{}.migration-key", self.links);
        if create
            && !std::path::Path::new(&path)
                .try_exists()
                .map_err(|e| CliError::io("inspecting migration key", e))?
        {
            let fresh = Secret32::new(os_random_32()?);
            write_new(&path, &*fresh, true)?;
            return Ok(fresh);
        }
        let raw = read_bounded_file(&path, 32)?;
        Ok(Secret32::new(raw.as_slice().try_into().map_err(|_| {
            CliError::input("invalid migration key length")
        })?))
    }
}

fn claim(args: &Args) -> Result<LoadedStatement, CliError> {
    let doc = read_document(args.require("claim")?)?.map_err(CliError::input)?;
    let loaded = load_statement(&doc, CLAIM_FORMAT, &[]).map_err(CliError::input)?;
    if !matches!(loaded.statement, Statement::Ownership(_)) {
        return Err(CliError::input(
            "collaborative proving requires an ownership claim",
        ));
    }
    Ok(loaded)
}

fn crypt(bytes: &mut [u8], key: &Secret32, binding: &[u8; 32], nonce: &[u8; 32]) {
    use qsag_accel::keccak::{finalize_cshake256, init_cshake256};
    let mut xof = init_cshake256(b"", b"QSAG.CLI.MIGRATE.TAPE.STREAM/v1");
    for frame in [&key.0, binding, nonce] {
        xof.absorb(frame);
    }
    finalize_cshake256(&mut xof, true);
    let mut mask = SecretBuffer([0u8; 136 * 16]);
    for chunk in bytes.chunks_mut(mask.len()) {
        xof.squeeze(&mut mask[..chunk.len()]);
        for (v, m) in chunk.iter_mut().zip(mask.iter()) {
            *v ^= *m;
        }
    }
}

fn tape_tag(key: &Secret32, binding: &[u8; 32], nonce: &[u8; 32], ct: &[u8]) -> [u8; 32] {
    cshake256_framed_32(
        b"QSAG.CLI.MIGRATE.TAPE.TAG/v1",
        &[&key.0, binding, nonce, ct],
    )
}

fn save_tape(
    mesh: &Mesh<'_>,
    key: &Secret32,
    tape: Preprocessing,
    path: &str,
) -> Result<(), CliError> {
    let nonce = os_random_32()?;
    let binding = mesh.binding();
    let mut bytes = tape.to_secret_bytes();
    drop(tape);
    crypt(&mut bytes, key, &binding, &nonce);
    let tag = tape_tag(key, &binding, &nonce, &bytes);
    bytes.extend_from_slice(&nonce);
    bytes.extend_from_slice(&tag);
    write_new(path, &bytes, true)
}

fn open_tape(
    mesh: &Mesh<'_>,
    key: &Secret32,
    path: &str,
    demand: &PrepDemand,
) -> Result<Preprocessing, CliError> {
    let len = Preprocessing::secret_byte_len(demand.triples, demand.randoms)
        .and_then(|l| l.checked_add(64))
        .ok_or_else(|| CliError::input("tape size overflow"))?;
    let mut raw = read_bounded_file(path, len as u64)?;
    if raw.len() != len {
        return Err(CliError::input("tape length differs from claim demand"));
    }
    let (ct, footer) = raw.split_at_mut(len - 64);
    let nonce = footer[..32].try_into().unwrap();
    let binding = mesh.binding();
    let tag = tape_tag(key, &binding, nonce, ct);
    if !qsag_asm::ct_eq_32(&tag, footer[32..].try_into().unwrap()) {
        return Err(CliError::verify("tape authentication failed"));
    }
    crypt(ct, key, &binding, nonce);
    let tape = Preprocessing::from_secret_bytes(ct)
        .filter(|t| t.triples.len() == demand.triples && t.randoms.len() == demand.randoms)
        .ok_or_else(|| CliError::input("invalid preprocessing tape"))?;
    Ok(tape)
}

fn output_path(args: &Args) -> Result<&str, CliError> {
    let path = args.require("out")?;
    match std::fs::symlink_metadata(path) {
        Ok(_) => Err(CliError::input(format!("output already exists: {path}"))),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(path),
        Err(e) => Err(CliError::io("inspecting output path", e)),
    }
}

fn prep(args: &Args) -> Result<(), CliError> {
    let mesh = Mesh::parse(args)?;
    let path = output_path(args)?;
    let demand = if args.get("claim").is_some() {
        if args.get("triples").is_some() || args.get("randoms").is_some() {
            return Err(CliError::usage("choose a claim or explicit counts"));
        }
        let loaded = claim(args)?;
        let Statement::Ownership(s) = &loaded.statement else {
            unreachable!()
        };
        let default_len = match &s.source {
            KeySource::Bip32 {
                root: Bip32Root::ExtendedKey,
                ..
            } => 64,
            KeySource::Bip32Ed25519 { .. } => 96,
            _ => 32,
        };
        let secret_bytes = args
            .get("secret-bytes")
            .map(|v| number(v, "secret-bytes"))
            .transpose()?
            .unwrap_or(default_len);
        let root = [0; 32];
        qsag_migrate::hem::relations::ownership_auxiliary_inputs(
            s,
            secret_bytes,
            &[],
            (s.lock == Lock::TaprootScriptTree).then_some(&root),
        )
        .ok_or_else(|| CliError::input("secret byte count does not fit the claim"))?;
        collab::ownership_prep_demand(s, REGIME, mesh.peers.len(), secret_bytes).map_err(failure)?
    } else {
        if args.get("secret-bytes").is_some() {
            return Err(CliError::usage("--secret-bytes requires --claim"));
        }
        PrepDemand {
            triples: needed_number(args, "triples")?,
            randoms: needed_number(args, "randoms")?,
        }
    };
    let key = mesh.local_key(true)?;
    let mut net = mesh.connect(b"prepare")?;
    let seed = Secret32::new(os_random_32()?);
    let tape = collab::prepare_party(&mut net, &mesh.session, &seed, &demand).map_err(failure)?;
    save_tape(&mesh, &key, tape, path)?;
    println!(
        "Wrote {} triples and {} randoms for party {} to {path}",
        demand.triples, demand.randoms, mesh.me
    );
    Ok(())
}

fn share(args: &Args, mesh: &Mesh<'_>) -> Result<(ZeroizingBuf, String), CliError> {
    match (args.get("xor-share"), args.get("shamir-share")) {
        (Some(p), None) if args.get("quorum").is_none() && args.get("custodian-id").is_none() => {
            Ok((read_bounded_file(p, 96)?, p.into()))
        }
        (None, Some(p)) => {
            let id = needed_number(args, "custodian-id")?;
            let ids: Vec<_> = args
                .require("quorum")?
                .split(',')
                .map(|v| number(v, "quorum ID"))
                .collect::<Result<_, _>>()?;
            if ids.len() != mesh.peers.len() || ids[mesh.me] != id {
                return Err(CliError::input(
                    "quorum must match peer order and custodian ID",
                ));
            }
            let raw = read_bounded_file(p, 96)?;
            let xor = collab::custody::xor_share_from_shamir(&ids, id, &raw)
                .ok_or_else(|| CliError::input("invalid Shamir quorum"))?;
            Ok((ZeroizingBuf::new(xor), p.into()))
        }
        _ => Err(CliError::usage(
            "choose --xor-share or --shamir-share with --custodian-id and --quorum",
        )),
    }
}

fn prove(args: &Args) -> Result<(), CliError> {
    let mesh = Mesh::parse(args)?;
    let out = output_path(args)?;
    let loaded = claim(args)?;
    let Statement::Ownership(s) = &loaded.statement else {
        unreachable!()
    };
    let (xor, custody_path) = share(args, &mesh)?;
    let path = args
        .get("path")
        .map(parse_path)
        .transpose()?
        .unwrap_or_default();
    let path = if let Some(fixed) = public_path(&s.source) {
        if args.get("path").is_some() && path != fixed {
            return Err(CliError::input("derivation path differs from the claim"));
        }
        Vec::new()
    } else {
        path
    };
    let root = args
        .get("merkle-root")
        .map(|r| from_hex_exact(r, "merkle-root"))
        .transpose()?;
    qsag_migrate::hem::relations::ownership_auxiliary_inputs(s, xor.len(), &path, root.as_ref())
        .ok_or_else(|| {
            CliError::input("share length, derivation path or script tree does not fit claim")
        })?;
    let input = CustodyInput {
        xor_share: &xor,
        path: &path,
        merkle_root: root.as_ref(),
    };
    let config = AnchorConfig::from_args(args)?;
    crate::anchor::require_anchor_or_waiver(
        config.is_some(),
        args.flag("ephemeral-unanchored"),
        "anchor-dir",
    )?;
    let tape_path = args.get("prep-tape");
    let key = if tape_path.is_some() || config.is_some() {
        Some(mesh.local_key(tape_path.is_none())?)
    } else {
        None
    };
    let tape = tape_path
        .map(|p| {
            let demand = collab::ownership_prep_demand(s, REGIME, mesh.peers.len(), xor.len())
                .map_err(failure)?;
            open_tape(&mesh, key.as_ref().unwrap(), p, &demand)
        })
        .transpose()?;
    let net = mesh.connect(if tape.is_some() {
        b"prove tape"
    } else {
        b"prepare and prove"
    })?;
    let anchor = config
        .map(|cfg| {
            let mut files = vec![mesh.links, custody_path.as_str()];
            files.extend(tape_path);
            let mac = Secret32::new(cshake256_framed_32(
                b"QSAG.CLI.MIGRATE.ANCHOR/v1",
                &[&key.as_ref().unwrap().0, &mesh.binding()],
            ));
            // Each party/session receives a fresh single-use slot. A restart cannot take
            // the current generation from storage and bless an old copy of the tape.
            FsExternalMountAnchor::provision_fresh(
                &cfg,
                &files,
                &[],
                "migration_custodian",
                mesh.binding(),
                *mac,
            )
        })
        .transpose()?;
    let seed = Secret32::new(os_random_32()?);
    let proof = if let (Some(tape), Some(p)) = (tape, tape_path) {
        // A durable exclusive receipt also rejects copies and concurrent consumers.
        let receipt = format!("{}.burn-{}", mesh.links, to_hex(&tape.tape_id()));
        write_new(&receipt, &mesh.binding(), true)?;
        std::fs::remove_file(p).map_err(|e| CliError::io("consuming preprocessing tape", e))?;
        crate::cli::sync_parent(p)?;
        let mut e = match &anchor {
            Some(a) => Engine::new_anchored(net, tape, &mesh.session, &seed, a, None),
            None => Engine::new_ephemeral(net, tape, &mesh.session, &seed),
        }
        .map_err(|e| failure(collab::ThresholdError::Mpc(e)))?;
        collab::checked_ownership(&mut e, s, REGIME, input)
    } else if let Some(a) = &anchor {
        collab::prove_ownership_party_over_wire_anchored(
            net,
            &mesh.session,
            &seed,
            a,
            None,
            s,
            REGIME,
            input,
        )
    } else {
        collab::prove_ownership_party_over_wire(net, &mesh.session, &seed, s, REGIME, input)
    }
    .map_err(failure)?;
    let bytes = proof.to_bytes();
    write_proof_document(&loaded, &bytes, out)?;
    if args.flag("json") {
        print!(
            "{}",
            Json::object(vec![
                ("proof_file", Json::str(out)),
                ("proof_bytes", Json::num(bytes.len()))
            ])
            .to_pretty()
        );
    } else {
        println!(
            "Proved {} with {} custodians -> {out}",
            summary(&loaded),
            mesh.peers.len()
        );
    }
    Ok(())
}

pub(super) fn run(raw: &[String]) -> Result<(), CliError> {
    let Some((cmd, rest)) = raw.split_first() else {
        return Err(CliError::usage(HELP));
    };
    if matches!(cmd.as_str(), "help" | "--help" | "-h") || rest == ["--help"] {
        print!("{HELP}");
        return Ok(());
    }
    let mut options = vec![
        "party",
        "peers",
        "links",
        "deployment-id",
        "session",
        "out",
        "timeout-ms",
    ];
    let flags = match cmd.as_str() {
        "split-secret" => {
            options = vec!["secret", "threshold", "parties", "out-dir"];
            &[][..]
        }
        "prep" => {
            options.extend(["claim", "secret-bytes", "triples", "randoms"]);
            &[][..]
        }
        "prove" => {
            options.extend([
                "claim",
                "xor-share",
                "shamir-share",
                "custodian-id",
                "quorum",
                "prep-tape",
                "path",
                "merkle-root",
                "anchor-dir",
            ]);
            &["ephemeral-unanchored", "allow-single-disk-anchor", "json"][..]
        }
        _ => return Err(CliError::usage(HELP)),
    };
    let args = Args::parse(rest, &options, flags)?;
    args.no_positionals()?;
    match cmd.as_str() {
        "split-secret" => split(&args),
        "prep" => prep(&args),
        _ => prove(&args),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use qsag_agg::field::Goldilocks as F;
    use qsag_migrate::hem::collab::engine::Sb;
    use std::net::TcpListener;

    struct Files(String);
    impl Files {
        fn new() -> Self {
            let dir = std::env::temp_dir().join(format!(
                "qsag-migration-{}",
                to_hex(&os_random_32().unwrap())
            ));
            let dir = dir.to_str().unwrap().to_owned();
            private_dir(&dir, true).unwrap();
            Self(dir)
        }
    }
    impl Drop for Files {
        fn drop(&mut self) {
            std::fs::remove_dir_all(&self.0).unwrap();
        }
    }

    fn args(words: &[&str]) -> Vec<String> {
        words.iter().map(|s| s.to_string()).collect()
    }
    fn invoke(words: &[&str]) {
        super::super::run(&args(words)).unwrap();
    }

    struct Hosts {
        files: Files,
        peers: String,
    }
    impl Hosts {
        fn new() -> Self {
            let files = Files::new();
            let sockets: Vec<_> = (0..3)
                .map(|_| TcpListener::bind("127.0.0.1:0").unwrap())
                .collect();
            let peers = sockets
                .iter()
                .map(|s| s.local_addr().unwrap().to_string())
                .collect::<Vec<_>>()
                .join(",");
            private_dir(&format!("{}/custody", files.0), true).unwrap();
            for p in 0..3 {
                let keys: Vec<_> = (0..3).flat_map(|q| [1 + p + q; 32]).collect();
                write_new(&format!("{}/custody/links-{p}", files.0), &keys, true).unwrap();
            }
            Self { files, peers }
        }

        fn mesh(&self, p: usize) -> Mesh<'_> {
            Mesh {
                me: p,
                peers: self.peers.split(',').map(|p| p.parse().unwrap()).collect(),
                links: "",
                deployment: [11; 32],
                session: [12; 32],
                timeout: Duration::from_secs(300),
            }
        }
        fn links(&self, p: usize) -> String {
            format!("{}/custody/links-{p}", self.files.0)
        }
        fn tape(&self, p: usize) -> String {
            format!("{}/custody/tape-{p}", self.files.0)
        }

        fn run(&self, cmd: &str, extra: impl Fn(usize) -> Vec<String> + Sync) {
            std::thread::scope(|scope| {
                for p in 0..3 {
                    let mut argv = args(&[
                        "collab",
                        cmd,
                        "--party",
                        &p.to_string(),
                        "--peers",
                        &self.peers,
                        "--links",
                        &self.links(p),
                        "--deployment-id",
                        &to_hex(&[11; 32]),
                        "--session",
                        &to_hex(&[12; 32]),
                        "--timeout-ms",
                        "300000",
                    ]);
                    argv.extend(extra(p));
                    scope.spawn(move || super::super::run(&argv).unwrap());
                }
            });
        }
    }

    #[test]
    fn single_prover_ownership_encodings_still_verify() {
        let witness = OwnershipWitness::secp256k1_key(&[11; 32]);
        let statement = OwnershipStatement::derive(
            Lock::P2pkh,
            KeySource::Secp256k1Key,
            &witness,
            [5; 32],
            [6; 32],
            7,
        )
        .unwrap();
        let proof = prove_ownership(&statement, &witness, REGIME, &[17; 32]).unwrap();
        let statement = Statement::Ownership(statement);
        assert_eq!(
            verify_statement_bytes(&statement, &proof.to_bytes()),
            Some(true)
        );
        let mut raw = proof.proof.to_bytes();
        assert_eq!(verify_statement_bytes(&statement, &raw), Some(true));
        raw.pop();
        assert_eq!(verify_statement_bytes(&statement, &raw), None);
    }

    #[test]
    fn tcp_prep_writes_private_authenticated_tapes() {
        let hosts = Hosts::new();
        hosts.run("prep", |p| {
            args(&[
                "--triples",
                "16",
                "--randoms",
                "32",
                "--out",
                &hosts.tape(p),
            ])
        });
        let mut tapes = Vec::new();
        for p in 0..3 {
            let links = hosts.links(p);
            let mesh = Mesh {
                links: &links,
                ..hosts.mesh(p)
            };
            let path = hosts.tape(p);
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                assert_eq!(
                    std::fs::metadata(&path).unwrap().permissions().mode() & 0o777,
                    0o600
                );
            }
            let key = mesh.local_key(false).unwrap();
            let demand = PrepDemand {
                triples: 16,
                randoms: 32,
            };
            tapes.push(open_tape(&mesh, &key, &path, &demand).unwrap());
            let mut bytes = std::fs::read(&path).unwrap();
            bytes[8] ^= 0x80;
            std::fs::write(&path, bytes).unwrap();
            assert!(open_tape(&mesh, &key, &path, &demand).is_err());
        }
        let keys = tapes.iter().fold([F::ZERO; 2], |mut k, t| {
            k[0] += t.key[0];
            k[1] += t.key[1];
            k
        });
        let sum = |shares: [Sb; 3]| {
            let value = shares.iter().fold(F::ZERO, |s, x| s + x.v);
            for (k, alpha) in keys.iter().enumerate() {
                assert_eq!(
                    shares.iter().fold(F::ZERO, |s, x| s + x.m[k]),
                    *alpha * value
                );
            }
            value
        };
        for i in 0..16 {
            let [a, b, c] =
                std::array::from_fn(|j| sum(std::array::from_fn(|p| tapes[p].triples[i][j])));
            assert_eq!(a * b, c);
        }
        for i in 0..32 {
            sum(std::array::from_fn(|p| tapes[p].randoms[i]));
        }
    }

    // Known-answer offline tapes for exercising the online CLI with a full-size
    // ownership circuit. These public fixture correlations are exclusively for tests.
    fn fixture_tape(p: usize, demand: PrepDemand) -> Preprocessing {
        let alpha = [
            F::from_u64_reduced(17 + p as u64),
            F::from_u64_reduced(29 + p as u64),
        ];
        let share = |v: F, i: usize| {
            let mask = F::from_u64_reduced(1 + i as u64);
            let value = match p {
                0 => v - mask - mask,
                _ => mask,
            };
            Sb {
                v: value,
                m: [alpha[0] * v, alpha[1] * v],
            }
        };
        Preprocessing {
            key: alpha,
            triples: (0..demand.triples)
                .map(|i| {
                    let a = F::from_u64_reduced(i as u64 + 13);
                    let b = F::from_u64_reduced(i as u64 + 41);
                    [
                        share(a, 3 * i),
                        share(b, 3 * i + 1),
                        share(a * b, 3 * i + 2),
                    ]
                })
                .collect(),
            randoms: (0..demand.randoms)
                .map(|i| {
                    // Mask openings in witness generation need nonzero, independently
                    // distributed field elements (including nonsquares).
                    let raw = cshake256_framed_32(
                        b"QSAG.CLI.MIGRATE.TEST.RANDOM/v1",
                        &[&(i as u64).to_le_bytes()],
                    );
                    share(
                        F::from_u64_reduced(u64::from_le_bytes(raw[..8].try_into().unwrap())),
                        i,
                    )
                })
                .collect(),
        }
    }

    #[test]
    fn tcp_shamir_ownership_proof_verifies_and_registers() {
        let hosts = Hosts::new();
        let dir = &hosts.files.0;
        let (secret, claim_path, shares, registry) = (
            format!("{dir}/key"),
            format!("{dir}/claim"),
            format!("{dir}/shares"),
            format!("{dir}/registry"),
        );
        let target = qsag_addr::QsagAddress::from_pubkey_cshake256(
            "qsp",
            qsag_addr::WitnessSuiteTag::MlDsa65,
            qsag_addr::KeyIdentityKind::SingleOrThreshold,
            &[9; 32],
        )
        .unwrap()
        .encode()
        .unwrap();
        write_new(&secret, &[13; 32], true).unwrap();
        invoke(&[
            "claim",
            "--kind",
            "btc-hash160",
            "--legacy-secret",
            &secret,
            "--epoch",
            "7",
            "--target",
            &target,
            "--out",
            &claim_path,
        ]);
        invoke(&[
            "collab",
            "split-secret",
            "--secret",
            &secret,
            "--threshold",
            "2",
            "--parties",
            "3",
            "--out-dir",
            &shares,
        ]);
        let doc = read_document(&claim_path).unwrap().unwrap();
        let loaded = load_statement(&doc, CLAIM_FORMAT, &[]).unwrap();
        let Statement::Ownership(s) = loaded.statement else {
            panic!("ownership claim")
        };
        let demand = collab::ownership_prep_demand(&s, REGIME, 3, 32).unwrap();
        for p in 0..3 {
            let links = hosts.links(p);
            let mesh = Mesh {
                links: &links,
                ..hosts.mesh(p)
            };
            save_tape(
                &mesh,
                &mesh.local_key(true).unwrap(),
                fixture_tape(p, demand),
                &hosts.tape(p),
            )
            .unwrap();
        }
        hosts.run("prove", |p| {
            args(&[
                "--claim",
                &claim_path,
                "--shamir-share",
                &format!("{shares}/share-{p}.bin"),
                "--custodian-id",
                &p.to_string(),
                "--quorum",
                "0,1,2",
                "--prep-tape",
                &hosts.tape(p),
                "--anchor-dir",
                &format!("{dir}/anchor-{p}"),
                "--allow-single-disk-anchor",
                "--out",
                &format!("{dir}/proof-{p}"),
            ])
        });
        let proof = format!("{dir}/proof-0");
        let expected = std::fs::read(&proof).unwrap();
        for p in 0..3 {
            assert_eq!(std::fs::read(format!("{dir}/proof-{p}")).unwrap(), expected);
            assert!(!std::path::Path::new(&hosts.tape(p)).exists());
        }
        invoke(&[
            "verify", "--epoch", "7", "--target", &target, "--proof", &proof,
        ]);
        invoke(&[
            "registry",
            "init",
            "--registry-dir",
            &registry,
            "--ephemeral-unanchored",
        ]);
        invoke(&[
            "registry",
            "register",
            "--registry-dir",
            &registry,
            "--proof",
            &proof,
            "--epoch",
            "7",
        ]);
    }
}
