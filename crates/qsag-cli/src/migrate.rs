//! Zero-knowledge classical-to-PQ ownership migration CLI (`qsag migrate`),
//! backed by [`qsag_migrate`] (`438`-repetition mixed-domain ZKBoo proofs with
//! `< 2^-256` classical soundness error and `> 2^128` quantum Grover cost).
//!
//! Subcommands:
//! - `commit` — Compute the canonical classical legacy commitment (`btc-p2wpkh`,
//!              `btc-taproot`, `eth-eoa`, or `ed25519-slip10`) without revealing the key.
//! - `prove`  — Produce a self-contained zero-knowledge migration proof binding a legacy
//!              spending key to a target Bech32m post-quantum `QsagAddress`, epoch anchor,
//!              and replay-preventing nullifier.
//! - `verify` — Verify a zero-knowledge migration proof against its statement, expected
//!              epoch, and optional expected target address / campaign domain.

use qsag_accel::CpuReferenceBackend;
use qsag_accel::keccak::cshake256_framed_32;
use qsag_addr::QsagAddress;
use qsag_migrate::zk_engine::PartyView;
use qsag_migrate::{
    LegacyCommitmentKind, LegacyOwnershipWitness, MIT_REPETITIONS, MigrateError, MigrationRequest,
    MigrationStatement, MigrationZkProof, OpenedRepetitionView, prove_migration_in_domain,
    verify_migration_proof,
};

use crate::cli::{
    Args, CliError, MAX_KEY_FILE_BYTES, MAX_SIG_PROOF_BYTES, Secret32, os_random_32,
    read_bounded_file, write_new,
};
use crate::codec::{Json, from_hex, from_hex_exact, to_hex};

const MIGRATE_HELP: &str = "\
qsag migrate <subcommand> [options]

Zero-knowledge classical-to-post-quantum ownership migration (438-rep mixed-domain ZKBoo):
  commit  derive the public legacy commitment (btc-p2wpkh | btc-taproot | eth-eoa | ed25519-slip10)
  prove   generate a zero-knowledge migration proof to a target post-quantum Bech32m address
  verify  verify a zero-knowledge migration proof and emit its replay nullifier
";

const MIGRATE_CLAIM_FORMAT: &str = "qsag-migration-claim-v1";
const MIGRATE_PROOF_FORMAT: &str = "qsag-migration-proof-v1";
const DEFAULT_DOMAIN_LABEL: &[u8] = b"QSAG.CLI.MIGRATE.DEFAULT_DOMAIN.V1";
const PROOF_WIRE_MAGIC: &[u8; 8] = b"QSAGMIGP";
/// Migration ZKBoo proofs across 438 repetitions encode to ~1.5-4 MB hex JSON.
const MAX_MIGRATION_PROOF_FILE_BYTES: u64 = 16 * 1024 * 1024;

fn ensure_absent(path: &str) -> Result<(), CliError> {
    match std::fs::symlink_metadata(path) {
        Ok(_) => Err(CliError::usage(format!("{path} already exists"))),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(e) => Err(CliError::io(format_args!("inspecting {path}"), e)),
    }
}

fn default_migration_domain() -> [u8; 32] {
    cshake256_framed_32(DEFAULT_DOMAIN_LABEL, &[b"qsag-mainnet-migration-v1"])
}

fn parse_domain(spec: Option<&str>) -> Result<[u8; 32], CliError> {
    match spec {
        Some(hex_str) => from_hex_exact::<32>(hex_str, "--domain-hex"),
        None => Ok(default_migration_domain()),
    }
}

/// Read a 32-byte classical spending key from either:
/// 1. Raw 32-byte binary secret file,
/// 2. 64-character hex secret file, or
/// 3. `qsag-secret-key-v1` JSON file with a `"seed"` field.
fn read_legacy_secret_32(path: &str) -> Result<Secret32, CliError> {
    let raw = read_bounded_file(path, MAX_KEY_FILE_BYTES)?;
    if raw.0.len() == 32 {
        let mut out = Secret32([0u8; 32]);
        out.0.copy_from_slice(&raw.0);
        return Ok(out);
    }
    let text = std::str::from_utf8(&raw.0).map_err(|_| {
        CliError::input(format!(
            "{path} must be 32 raw bytes, 64 hex chars, or a JSON secret file"
        ))
    })?;
    let trimmed = text.trim();
    if trimmed.starts_with('{') {
        let json = Json::parse(trimmed)?;
        let seed_buf = json.field_hex("seed")?;
        if seed_buf.0.len() != 32 {
            return Err(CliError::input("JSON legacy key \"seed\" must be 32 bytes"));
        }
        let mut out = Secret32([0u8; 32]);
        out.0.copy_from_slice(&seed_buf.0);
        return Ok(out);
    }
    let hex_str = trimmed.strip_prefix("0x").unwrap_or(trimmed);
    let decoded = from_hex(hex_str)?;
    if decoded.0.len() != 32 {
        return Err(CliError::input(format!(
            "{path} must decode to exactly 32 bytes (got {})",
            decoded.0.len()
        )));
    }
    let mut out = Secret32([0u8; 32]);
    out.0.copy_from_slice(&decoded.0);
    Ok(out)
}

fn compute_legacy_commitment(
    witness: &LegacyOwnershipWitness,
    kind_name: &str,
) -> Result<(LegacyCommitmentKind, &'static str), CliError> {
    match kind_name {
        "btc-p2wpkh" | "bitcoin-hash160" => witness
            .compute_bitcoin_hash160()
            .map(|k| (k, "btc-p2wpkh"))
            .ok_or_else(|| CliError::input("legacy secret is not a valid nonzero secp256k1 scalar")),
        "btc-taproot" | "bitcoin-taproot" => witness
            .compute_taproot_tweaked_xonly()
            .map(|k| (k, "btc-taproot"))
            .ok_or_else(|| CliError::input("legacy secret is not a valid nonzero secp256k1 scalar")),
        "eth-eoa" | "ethereum-keccak20" => witness
            .compute_ethereum_keccak20()
            .map(|k| (k, "eth-eoa"))
            .ok_or_else(|| CliError::input("legacy secret is not a valid nonzero secp256k1 scalar")),
        "ed25519-slip10" | "slip0010-ed25519" => {
            Ok((witness.compute_slip0010_commitment(), "ed25519-slip10"))
        }
        other => Err(CliError::usage(format!(
            "unsupported --kind '{other}' (expected btc-p2wpkh, btc-taproot, eth-eoa, or ed25519-slip10)"
        ))),
    }
}

fn encode_legacy_kind(kind: &LegacyCommitmentKind) -> (&'static str, Vec<u8>) {
    match kind {
        LegacyCommitmentKind::BitcoinHash160(h20) => ("btc-p2wpkh", h20.to_vec()),
        LegacyCommitmentKind::BitcoinTaprootXOnly(x32) => ("btc-taproot", x32.to_vec()),
        LegacyCommitmentKind::EthereumKeccak20(k20) => ("eth-eoa", k20.to_vec()),
        LegacyCommitmentKind::Slip0010Ed25519(pk32) => ("ed25519-slip10", pk32.to_vec()),
    }
}

fn decode_legacy_kind(kind_name: &str, hex_value: &str) -> Result<LegacyCommitmentKind, CliError> {
    match kind_name {
        "btc-p2wpkh" => Ok(LegacyCommitmentKind::BitcoinHash160(from_hex_exact::<20>(
            hex_value,
            "btc-p2wpkh commitment",
        )?)),
        "btc-taproot" => Ok(LegacyCommitmentKind::BitcoinTaprootXOnly(
            from_hex_exact::<32>(hex_value, "btc-taproot commitment")?,
        )),
        "eth-eoa" => Ok(LegacyCommitmentKind::EthereumKeccak20(
            from_hex_exact::<20>(hex_value, "eth-eoa commitment")?,
        )),
        "ed25519-slip10" => Ok(LegacyCommitmentKind::Slip0010Ed25519(from_hex_exact::<32>(
            hex_value,
            "ed25519-slip10 commitment",
        )?)),
        other => Err(CliError::input(format!(
            "unsupported legacy_kind '{other}' in proof"
        ))),
    }
}

fn limbs4_to_bytes(limbs: &[u64; 4]) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (i, &w) in limbs.iter().enumerate() {
        out[i * 8..(i + 1) * 8].copy_from_slice(&w.to_le_bytes());
    }
    out
}

fn bytes_to_limbs4(bytes: &[u8; 32]) -> [u64; 4] {
    core::array::from_fn(|i| {
        u64::from_le_bytes(bytes[i * 8..(i + 1) * 8].try_into().unwrap_or([0; 8]))
    })
}

fn put_u32_framed(out: &mut Vec<u8>, slice: &[u8]) -> Result<(), CliError> {
    let len = u32::try_from(slice.len())
        .map_err(|_| CliError::input("proof field exceeds u32 framing bound"))?;
    out.extend_from_slice(&len.to_le_bytes());
    out.extend_from_slice(slice);
    Ok(())
}

fn take_exact<'a>(cursor: &mut &'a [u8], len: usize) -> Result<&'a [u8], CliError> {
    if cursor.len() < len {
        return Err(CliError::verify("truncated migration ZK proof wire payload"));
    }
    let (head, tail) = cursor.split_at(len);
    *cursor = tail;
    Ok(head)
}

fn take_u32_framed(cursor: &mut &[u8]) -> Result<Vec<u8>, CliError> {
    let len_bytes = take_exact(cursor, 4)?;
    let len = u32::from_le_bytes(len_bytes.try_into().unwrap_or([0; 4])) as usize;
    if len > 256 * 1024 {
        return Err(CliError::verify("oversized repetition field in migration proof"));
    }
    Ok(take_exact(cursor, len)?.to_vec())
}

fn encode_zk_proof_wire(proof: &MigrationZkProof) -> Result<Vec<u8>, CliError> {
    let mut out = Vec::with_capacity(512 * 1024);
    out.extend_from_slice(PROOF_WIRE_MAGIC);
    out.extend_from_slice(&proof.views_merkle_root);
    let rep_count = u32::try_from(proof.repetitions.len())
        .map_err(|_| CliError::input("invalid repetition count"))?;
    out.extend_from_slice(&rep_count.to_le_bytes());
    for rep in &proof.repetitions {
        out.push(rep.opened_e);
        for pv in &rep.pair {
            out.extend_from_slice(&pv.seed);
            put_u32_framed(&mut out, &pv.inputs)?;
            put_u32_framed(&mut out, &pv.products)?;
            put_u32_framed(&mut out, &pv.outputs)?;
        }
        out.extend_from_slice(&rep.hidden_party_commit);
        put_u32_framed(&mut out, &rep.hidden_outputs)?;
    }
    Ok(out)
}

fn decode_zk_proof_wire(bytes: &[u8]) -> Result<MigrationZkProof, CliError> {
    let mut cur = bytes;
    let magic = take_exact(&mut cur, 8)?;
    if magic != PROOF_WIRE_MAGIC {
        return Err(CliError::verify("invalid migration ZK proof wire magic"));
    }
    let mut views_merkle_root = [0u8; 32];
    views_merkle_root.copy_from_slice(take_exact(&mut cur, 32)?);
    let rep_count =
        u32::from_le_bytes(take_exact(&mut cur, 4)?.try_into().unwrap_or([0; 4])) as usize;
    if rep_count != MIT_REPETITIONS {
        return Err(CliError::verify(format!(
            "invalid repetition count {rep_count} (expected {MIT_REPETITIONS})"
        )));
    }
    let mut repetitions = Vec::with_capacity(rep_count);
    for _ in 0..rep_count {
        let opened_e = take_exact(&mut cur, 1)?[0];
        let mut p0_seed = [0u8; 32];
        p0_seed.copy_from_slice(take_exact(&mut cur, 32)?);
        let p0 = PartyView {
            seed: p0_seed,
            inputs: take_u32_framed(&mut cur)?,
            products: take_u32_framed(&mut cur)?,
            outputs: take_u32_framed(&mut cur)?,
        };
        let mut p1_seed = [0u8; 32];
        p1_seed.copy_from_slice(take_exact(&mut cur, 32)?);
        let p1 = PartyView {
            seed: p1_seed,
            inputs: take_u32_framed(&mut cur)?,
            products: take_u32_framed(&mut cur)?,
            outputs: take_u32_framed(&mut cur)?,
        };
        let mut hidden_party_commit = [0u8; 32];
        hidden_party_commit.copy_from_slice(take_exact(&mut cur, 32)?);
        let hidden_outputs = take_u32_framed(&mut cur)?;
        repetitions.push(OpenedRepetitionView {
            opened_e,
            pair: [p0, p1],
            hidden_party_commit,
            hidden_outputs,
        });
    }
    if !cur.is_empty() {
        return Err(CliError::verify(
            "trailing unauthenticated bytes in migration ZK proof",
        ));
    }
    Ok(MigrationZkProof {
        views_merkle_root,
        repetitions,
    })
}

fn map_migrate_err(err: MigrateError) -> CliError {
    match err {
        MigrateError::WitnessMismatchWithLegacyCommitment
        | MigrateError::InvalidSharingParameters => {
            CliError::input(format!("migration witness error: {err:?}"))
        }
        MigrateError::EntropyUnavailable => {
            CliError::new(crate::cli::exit::IO, "entropy unavailable for migration proof")
        }
        other => CliError::verify(format!("migration ZK proof verification failed: {other:?}")),
    }
}

fn commit(raw: &[String]) -> Result<(), CliError> {
    let args = Args::parse(
        raw,
        &["kind", "legacy-secret", "domain-hex", "out"],
        &["json", "help"],
    )?;
    if args.flag("help") {
        println!(
            "qsag migrate commit --kind <btc-p2wpkh|btc-taproot|eth-eoa|ed25519-slip10> --legacy-secret <path> [--domain-hex <64-hex>] [--out <path>] [--json]"
        );
        return Ok(());
    }
    args.no_positionals()?;
    let kind_arg = args.require("kind")?;
    let secret_path = args.require("legacy-secret")?;
    let domain = parse_domain(args.get("domain-hex"))?;
    if let Some(out) = args.get("out") {
        ensure_absent(out)?;
    }

    let secret = read_legacy_secret_32(secret_path)?;
    let witness = LegacyOwnershipWitness::from_raw_secret(secret.0);
    let (kind, canonical_name) = compute_legacy_commitment(&witness, kind_arg)?;
    let nullifier = witness
        .compute_nullifier(&kind, &domain)
        .ok_or_else(|| CliError::input("failed to derive migration nullifier"))?;
    let (_, commitment_bytes) = encode_legacy_kind(&kind);
    let nullifier_bytes = limbs4_to_bytes(&nullifier);

    let doc = Json::object(vec![
        ("format", Json::str(MIGRATE_CLAIM_FORMAT)),
        ("legacy_kind", Json::str(canonical_name)),
        ("legacy_commitment", Json::hex(&commitment_bytes)),
        ("migration_domain", Json::hex(&domain)),
        ("migration_nullifier", Json::hex(&nullifier_bytes)),
    ]);
    if let Some(out) = args.get("out") {
        write_new(out, doc.to_pretty().as_bytes(), false)?;
    }
    if args.flag("json") {
        print!("{}", doc.to_pretty());
    } else {
        println!(
            "{canonical_name} commitment {} (nullifier {})",
            to_hex(&commitment_bytes),
            to_hex(&nullifier_bytes)
        );
    }
    Ok(())
}

fn prove(raw: &[String]) -> Result<(), CliError> {
    let args = Args::parse(
        raw,
        &["kind", "legacy-secret", "target", "epoch", "domain-hex", "out"],
        &["deterministic", "json", "help"],
    )?;
    if args.flag("help") {
        println!(
            "qsag migrate prove --kind <btc-p2wpkh|btc-taproot|eth-eoa|ed25519-slip10> --legacy-secret <path> --target <bech32m_addr> --epoch <n> [--domain-hex <64-hex>] --out <path> [--deterministic] [--json]"
        );
        return Ok(());
    }
    args.no_positionals()?;
    let kind_arg = args.require("kind")?;
    let secret_path = args.require("legacy-secret")?;
    let target_str = args.require("target")?;
    let epoch = args
        .get_u64("epoch")?
        .ok_or_else(|| CliError::usage("missing required option --epoch <n>"))?;
    let domain = parse_domain(args.get("domain-hex"))?;
    let out_path = args.require("out")?;
    ensure_absent(out_path)?;

    let target_addr = QsagAddress::decode(target_str)
        .map_err(|e| CliError::usage(format!("invalid --target Bech32m address: {e:?}")))?;
    let canonical_target = target_addr
        .encode()
        .map_err(|e| CliError::usage(format!("encoding target address failed: {e:?}")))?;

    let secret = read_legacy_secret_32(secret_path)?;
    let witness = LegacyOwnershipWitness::from_raw_secret(secret.0);
    let (legacy_kind, canonical_kind) = compute_legacy_commitment(&witness, kind_arg)?;
    let (_, commitment_bytes) = encode_legacy_kind(&legacy_kind);

    let entropy = Secret32(if args.flag("deterministic") {
        cshake256_framed_32(
            b"QSAG.CLI.MIGRATE.DET.ENTROPY.V1",
            &[
                &secret.0,
                &domain,
                canonical_target.as_bytes(),
                &epoch.to_le_bytes(),
            ],
        )
    } else {
        os_random_32()?
    });

    let request = MigrationRequest {
        legacy: legacy_kind,
        target: target_addr,
        epoch,
        domain,
    };
    let accel = CpuReferenceBackend::new();
    let (statement, zk_proof) =
        prove_migration_in_domain(&witness, request, entropy.0, &accel).map_err(map_migrate_err)?;
    verify_migration_proof(&statement, &zk_proof, &domain, epoch).map_err(map_migrate_err)?;

    let wire_bytes = encode_zk_proof_wire(&zk_proof)?;
    let nullifier_bytes = limbs4_to_bytes(&statement.migration_nullifier);
    let anchor_bytes = limbs4_to_bytes(&statement.witness_anchor);

    let doc = Json::object(vec![
        ("format", Json::str(MIGRATE_PROOF_FORMAT)),
        ("legacy_kind", Json::str(canonical_kind)),
        ("legacy_commitment", Json::hex(&commitment_bytes)),
        ("target_pq_address", Json::str(&canonical_target)),
        ("epoch_anchor", Json::num(statement.epoch_anchor)),
        ("migration_domain", Json::hex(&statement.migration_domain)),
        ("migration_nullifier", Json::hex(&nullifier_bytes)),
        ("witness_anchor", Json::hex(&anchor_bytes)),
        ("repetitions", Json::num(zk_proof.repetitions.len())),
        ("views_merkle_root", Json::hex(&zk_proof.views_merkle_root)),
        ("zk_proof", Json::hex(&wire_bytes)),
    ]);
    write_new(out_path, doc.to_pretty().as_bytes(), false)?;

    if args.flag("json") {
        let report = Json::object(vec![
            ("operation", Json::str("migrate-prove")),
            ("legacy_kind", Json::str(canonical_kind)),
            ("legacy_commitment", Json::hex(&commitment_bytes)),
            ("target_pq_address", Json::str(&canonical_target)),
            ("epoch_anchor", Json::num(epoch)),
            ("migration_nullifier", Json::hex(&nullifier_bytes)),
            ("proof_wire_bytes", Json::num(wire_bytes.len())),
            ("proof_file", Json::str(out_path)),
        ]);
        print!("{}", report.to_pretty());
    } else {
        println!(
            "generated {canonical_kind} -> {canonical_target} ZK migration proof at epoch {epoch} ({} B wire, nullifier {}) -> {out_path}",
            wire_bytes.len(),
            to_hex(&nullifier_bytes)
        );
    }
    Ok(())
}

fn verify(raw: &[String]) -> Result<(), CliError> {
    let args = Args::parse(
        raw,
        &["proof", "target", "epoch", "domain-hex", "legacy-commitment"],
        &["json", "help"],
    )?;
    if args.flag("help") {
        println!(
            "qsag migrate verify --proof <path> [--target <bech32m_addr>] [--epoch <n>] [--domain-hex <64-hex>] [--legacy-commitment <hex>] [--json]"
        );
        return Ok(());
    }
    args.no_positionals()?;
    let proof_path = args.require("proof")?;
    let raw_file = read_bounded_file(proof_path, MAX_MIGRATION_PROOF_FILE_BYTES.max(MAX_SIG_PROOF_BYTES))?;
    let text = std::str::from_utf8(&raw_file.0)
        .map_err(|_| CliError::verify("migration proof file is not valid UTF-8"))?;
    let json = Json::parse(text)
        .map_err(|e| CliError::verify(format!("malformed migration proof JSON: {e}")))?;
    if json.field_str("format").map_err(|e| CliError::verify(e.message))? != MIGRATE_PROOF_FORMAT {
        return Err(CliError::verify(format!(
            "{proof_path} is not a {MIGRATE_PROOF_FORMAT} file"
        )));
    }

    let legacy_kind_str = json
        .field_str("legacy_kind")
        .map_err(|e| CliError::verify(e.message))?;
    let legacy_comm_hex = json
        .field_str("legacy_commitment")
        .map_err(|e| CliError::verify(e.message))?;
    if let Some(expected_comm) = args.get("legacy-commitment") {
        let a = from_hex(expected_comm)?;
        let b = from_hex(legacy_comm_hex)?;
        if a.0 != b.0 {
            return Err(CliError::verify(
                "legacy_commitment does not match --legacy-commitment",
            ));
        }
    }
    let legacy_commitment = decode_legacy_kind(legacy_kind_str, legacy_comm_hex)
        .map_err(|e| CliError::verify(e.message))?;

    let target_str = json
        .field_str("target_pq_address")
        .map_err(|e| CliError::verify(e.message))?;
    let target_pq_address = QsagAddress::decode(target_str)
        .map_err(|e| CliError::verify(format!("invalid target_pq_address in proof: {e:?}")))?;
    if let Some(expected_target_str) = args.get("target") {
        let expected_target = QsagAddress::decode(expected_target_str)
            .map_err(|e| CliError::usage(format!("invalid --target Bech32m address: {e:?}")))?;
        if target_pq_address != expected_target {
            return Err(CliError::verify(
                "proof target_pq_address does not match expected --target",
            ));
        }
    }

    let statement_epoch = json
        .field_u64("epoch_anchor")
        .map_err(|e| CliError::verify(e.message))?;
    let expected_epoch = args.get_u64("epoch")?.unwrap_or(statement_epoch);

    let statement_domain = from_hex_exact::<32>(
        json.field_str("migration_domain")
            .map_err(|e| CliError::verify(e.message))?,
        "migration_domain",
    )
    .map_err(|e| CliError::verify(e.message))?;
    let expected_domain = match args.get("domain-hex") {
        Some(h) => from_hex_exact::<32>(h, "--domain-hex")?,
        None => statement_domain,
    };

    let nullifier_bytes = from_hex_exact::<32>(
        json.field_str("migration_nullifier")
            .map_err(|e| CliError::verify(e.message))?,
        "migration_nullifier",
    )
    .map_err(|e| CliError::verify(e.message))?;
    let anchor_bytes = from_hex_exact::<32>(
        json.field_str("witness_anchor")
            .map_err(|e| CliError::verify(e.message))?,
        "witness_anchor",
    )
    .map_err(|e| CliError::verify(e.message))?;

    let wire_hex = json
        .field_str("zk_proof")
        .map_err(|e| CliError::verify(e.message))?;
    let wire_bytes = from_hex(wire_hex)
        .map_err(|e| CliError::verify(format!("invalid zk_proof hex: {e}")))?;
    let zk_proof = decode_zk_proof_wire(&wire_bytes.0)?;

    let header_root = from_hex_exact::<32>(
        json.field_str("views_merkle_root")
            .map_err(|e| CliError::verify(e.message))?,
        "views_merkle_root",
    )
    .map_err(|e| CliError::verify(e.message))?;
    if zk_proof.views_merkle_root != header_root {
        return Err(CliError::verify(
            "views_merkle_root header does not match wire proof",
        ));
    }

    let statement = MigrationStatement {
        legacy_commitment,
        target_pq_address,
        epoch_anchor: statement_epoch,
        migration_domain: statement_domain,
        migration_nullifier: bytes_to_limbs4(&nullifier_bytes),
        witness_anchor: bytes_to_limbs4(&anchor_bytes),
    };

    verify_migration_proof(&statement, &zk_proof, &expected_domain, expected_epoch)
        .map_err(map_migrate_err)?;

    if args.flag("json") {
        let report = Json::object(vec![
            ("valid", Json::Bool(true)),
            ("legacy_kind", Json::str(legacy_kind_str)),
            ("legacy_commitment", Json::str(legacy_comm_hex)),
            ("target_pq_address", Json::str(target_str)),
            ("epoch_anchor", Json::num(statement_epoch)),
            ("migration_nullifier", Json::hex(&nullifier_bytes)),
        ]);
        print!("{}", report.to_pretty());
    } else {
        println!(
            "valid ({legacy_kind_str} -> {target_str}, epoch {statement_epoch}, nullifier {})",
            to_hex(&nullifier_bytes)
        );
    }
    Ok(())
}

pub fn run(raw: &[String]) -> Result<(), CliError> {
    let Some((sub, rest)) = raw.split_first() else {
        print!("{MIGRATE_HELP}");
        return Err(CliError::usage("migrate requires a subcommand (try --help)"));
    };
    match sub.as_str() {
        "--help" | "-h" | "help" => {
            print!("{MIGRATE_HELP}");
            Ok(())
        }
        "commit" => commit(rest),
        "prove" => prove(rest),
        "verify" => verify(rest),
        other => Err(CliError::usage(format!(
            "unknown migrate subcommand '{other}' (expected commit, prove, or verify)"
        ))),
    }
}
