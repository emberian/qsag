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
    Args, CliError, MAX_KEY_FILE_BYTES, Secret32, os_random_32, read_bounded_file, write_new,
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

// Size contract of a `qsag-migration-proof-v1` file, shared by `prove` and `verify`.
//
// The `zk_proof` wire payload is
//   magic (8) | views_merkle_root (32) | repetition count (4, always `MIT_REPETITIONS`) |
//   per repetition: opened_e (1) | 2 x [seed (32) | inputs | products | outputs] |
//                   hidden_party_commit (32) | hidden_outputs
// where each named field is a little-endian u32 length followed by that many bytes. The field
// lengths are fixed by the ownership circuit of the legacy kind, which the verifier replays
// exactly; the caps below only bound what is read before that check. Measured per repetition
// (inputs, products, outputs): btc-p2wpkh (288, 81424, 85), eth-eoa (288, 80480, 85),
// btc-taproot (288, 75680, 98), ed25519-slip10 (288, 65600, 97), i.e. 57.9 to 71.7 MB of wire.
const WIRE_HEADER_BYTES: u64 = 8 + 32 + 4;
const WIRE_REP_FIXED_BYTES: u64 = 1 + 2 * 32 + 32;
const WIRE_LEN_PREFIX_BYTES: u64 = 4;
const MAX_VIEW_INPUT_BYTES: usize = 1024;
const MAX_VIEW_PRODUCT_BYTES: usize = 128 * 1024;
const MAX_VIEW_OUTPUT_BYTES: usize = 1024;

const fn checked(value: Option<u64>) -> u64 {
    match value {
        Some(v) => v,
        None => panic!("migration proof size bound overflows u64"),
    }
}

/// Largest wire payload the schema admits: every framed field at its cap.
const MAX_PROOF_WIRE_BYTES: u64 = {
    let inputs = checked(WIRE_LEN_PREFIX_BYTES.checked_add(MAX_VIEW_INPUT_BYTES as u64));
    let products = checked(WIRE_LEN_PREFIX_BYTES.checked_add(MAX_VIEW_PRODUCT_BYTES as u64));
    let outputs = checked(WIRE_LEN_PREFIX_BYTES.checked_add(MAX_VIEW_OUTPUT_BYTES as u64));
    // Two opened views carry inputs, products and outputs; the hidden view only its outputs.
    let mut rep = WIRE_REP_FIXED_BYTES;
    rep = checked(rep.checked_add(checked(inputs.checked_mul(2))));
    rep = checked(rep.checked_add(checked(products.checked_mul(2))));
    rep = checked(rep.checked_add(checked(outputs.checked_mul(3))));
    checked(WIRE_HEADER_BYTES.checked_add(checked(rep.checked_mul(MIT_REPETITIONS as u64))))
};
/// Everything in the JSON document other than the hex of the wire payload: eleven short
/// members (hashes, the Bech32m address, a u64 epoch) and their punctuation. `prove` writes
/// under 700 bytes of it.
const MAX_PROOF_ENVELOPE_BYTES: u64 = 4096;
/// Largest proof file `verify` reads and `prove` writes: the wire payload in hex plus the
/// envelope (about 223 MiB; files written today are 116 to 144 MB).
const MAX_MIGRATION_PROOF_FILE_BYTES: u64 = checked(
    checked(MAX_PROOF_WIRE_BYTES.checked_mul(2)).checked_add(MAX_PROOF_ENVELOPE_BYTES),
);
// The wire payload must be addressable on the host before it is decoded into memory.
const _: () = assert!(MAX_MIGRATION_PROOF_FILE_BYTES <= usize::MAX as u64);

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

fn put_u32_framed(out: &mut Vec<u8>, slice: &[u8], max_len: usize) -> Result<(), CliError> {
    if slice.len() > max_len {
        return Err(CliError::input(format!(
            "migration proof field of {} bytes exceeds its {max_len}-byte wire bound",
            slice.len()
        )));
    }
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

/// Read one length-prefixed field. The claimed length is checked against the field's cap and
/// then against the bytes actually present, so nothing is allocated for a forged length.
fn take_u32_framed(cursor: &mut &[u8], max_len: usize) -> Result<Vec<u8>, CliError> {
    let len_bytes = take_exact(cursor, 4)?;
    let len = usize::try_from(u32::from_le_bytes(len_bytes.try_into().unwrap_or([0; 4])))
        .map_err(|_| CliError::verify("oversized repetition field in migration proof"))?;
    if len > max_len {
        return Err(CliError::verify("oversized repetition field in migration proof"));
    }
    Ok(take_exact(cursor, len)?.to_vec())
}

fn take_party_view(cursor: &mut &[u8]) -> Result<PartyView, CliError> {
    let mut seed = [0u8; 32];
    seed.copy_from_slice(take_exact(cursor, 32)?);
    Ok(PartyView {
        seed,
        inputs: take_u32_framed(cursor, MAX_VIEW_INPUT_BYTES)?,
        products: take_u32_framed(cursor, MAX_VIEW_PRODUCT_BYTES)?,
        outputs: take_u32_framed(cursor, MAX_VIEW_OUTPUT_BYTES)?,
    })
}

fn encode_zk_proof_wire(proof: &MigrationZkProof) -> Result<Vec<u8>, CliError> {
    let mut out = Vec::new();
    out.extend_from_slice(PROOF_WIRE_MAGIC);
    out.extend_from_slice(&proof.views_merkle_root);
    if proof.repetitions.len() != MIT_REPETITIONS {
        return Err(CliError::input("invalid repetition count"));
    }
    let rep_count = u32::try_from(proof.repetitions.len())
        .map_err(|_| CliError::input("invalid repetition count"))?;
    out.extend_from_slice(&rep_count.to_le_bytes());
    for rep in &proof.repetitions {
        out.push(rep.opened_e);
        for pv in &rep.pair {
            out.extend_from_slice(&pv.seed);
            put_u32_framed(&mut out, &pv.inputs, MAX_VIEW_INPUT_BYTES)?;
            put_u32_framed(&mut out, &pv.products, MAX_VIEW_PRODUCT_BYTES)?;
            put_u32_framed(&mut out, &pv.outputs, MAX_VIEW_OUTPUT_BYTES)?;
        }
        out.extend_from_slice(&rep.hidden_party_commit);
        put_u32_framed(&mut out, &rep.hidden_outputs, MAX_VIEW_OUTPUT_BYTES)?;
    }
    debug_assert!(out.len() as u64 <= MAX_PROOF_WIRE_BYTES);
    Ok(out)
}

fn decode_zk_proof_wire(bytes: &[u8]) -> Result<MigrationZkProof, CliError> {
    if !u64::try_from(bytes.len()).is_ok_and(|len| len <= MAX_PROOF_WIRE_BYTES) {
        return Err(CliError::verify("oversized migration ZK proof wire payload"));
    }
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
        let p0 = take_party_view(&mut cur)?;
        let p1 = take_party_view(&mut cur)?;
        let mut hidden_party_commit = [0u8; 32];
        hidden_party_commit.copy_from_slice(take_exact(&mut cur, 32)?);
        let hidden_outputs = take_u32_framed(&mut cur, MAX_VIEW_OUTPUT_BYTES)?;
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
    let encoded = doc.to_pretty();
    // Never write a proof that `verify` would refuse to read.
    if !u64::try_from(encoded.len()).is_ok_and(|len| len <= MAX_MIGRATION_PROOF_FILE_BYTES) {
        return Err(CliError::input(format!(
            "encoded migration proof is {} bytes, above the {MAX_MIGRATION_PROOF_FILE_BYTES}-byte file bound",
            encoded.len()
        )));
    }
    write_new(out_path, encoded.as_bytes(), false)?;

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
    let raw_file = read_bounded_file(proof_path, MAX_MIGRATION_PROOF_FILE_BYTES)?;
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
    if !u64::try_from(wire_hex.len())
        .is_ok_and(|len| len <= checked(MAX_PROOF_WIRE_BYTES.checked_mul(2)))
    {
        return Err(CliError::verify("oversized migration ZK proof wire payload"));
    }
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

#[cfg(test)]
mod tests {
    use super::*;

    fn view(inputs: usize, products: usize, outputs: usize) -> PartyView {
        PartyView {
            seed: [7; 32],
            inputs: vec![1; inputs],
            products: vec![2; products],
            outputs: vec![3; outputs],
        }
    }

    fn proof(inputs: usize, products: usize, outputs: usize) -> MigrationZkProof {
        MigrationZkProof {
            views_merkle_root: [9; 32],
            repetitions: (0..MIT_REPETITIONS)
                .map(|rep| OpenedRepetitionView {
                    opened_e: (rep % 3) as u8,
                    pair: [
                        view(inputs, products, outputs),
                        view(inputs, products, outputs),
                    ],
                    hidden_party_commit: [5; 32],
                    hidden_outputs: vec![4; outputs],
                })
                .collect(),
        }
    }

    fn wire_len(inputs: u64, products: u64, outputs: u64) -> u64 {
        44 + 438 * (97 + 7 * 4 + 2 * inputs + 2 * products + 3 * outputs)
    }

    #[test]
    fn size_bounds_follow_the_wire_schema_and_cover_every_legacy_kind() {
        assert_eq!(MIT_REPETITIONS, 438);
        assert_eq!(MAX_PROOF_WIRE_BYTES, wire_len(1024, 128 * 1024, 1024));
        assert_eq!(MAX_PROOF_WIRE_BYTES, 117_116_426);
        assert_eq!(MAX_MIGRATION_PROOF_FILE_BYTES, 2 * 117_116_426 + 4096);
        // (inputs, products, outputs, wire bytes) written by `migrate prove` for each kind.
        for (inputs, products, outputs, wire) in [
            (288, 81_424, 85, 71_746_196u64), // btc-p2wpkh
            (288, 80_480, 85, 70_919_252),    // eth-eoa
            (288, 75_680, 98, 66_731_534),    // btc-taproot
            (288, 65_600, 97, 57_900_140),    // ed25519-slip10
        ] {
            assert_eq!(wire_len(inputs, products, outputs), wire);
            assert!(inputs as usize <= MAX_VIEW_INPUT_BYTES);
            assert!(products as usize <= MAX_VIEW_PRODUCT_BYTES);
            assert!(outputs as usize <= MAX_VIEW_OUTPUT_BYTES);
            assert!(2 * wire + MAX_PROOF_ENVELOPE_BYTES <= MAX_MIGRATION_PROOF_FILE_BYTES);
        }
    }

    #[test]
    fn wire_codec_accepts_the_bound_exactly_and_rejects_anything_larger() {
        let full = proof(
            MAX_VIEW_INPUT_BYTES,
            MAX_VIEW_PRODUCT_BYTES,
            MAX_VIEW_OUTPUT_BYTES,
        );
        let wire = encode_zk_proof_wire(&full).unwrap();
        assert_eq!(wire.len() as u64, MAX_PROOF_WIRE_BYTES);
        assert!(decode_zk_proof_wire(&wire).unwrap() == full);
        drop(full);

        let mut padded = wire;
        padded.push(0);
        let err = decode_zk_proof_wire(&padded).unwrap_err();
        assert_eq!(err.code, crate::cli::exit::VERIFY_FAILED);
        assert!(err.message.contains("oversized"), "{}", err.message);
        drop(padded);

        for (inputs, products, outputs) in [
            (MAX_VIEW_INPUT_BYTES + 1, 0, 0),
            (0, MAX_VIEW_PRODUCT_BYTES + 1, 0),
            (0, 0, MAX_VIEW_OUTPUT_BYTES + 1),
        ] {
            let err = encode_zk_proof_wire(&proof(inputs, products, outputs)).unwrap_err();
            assert!(err.message.contains("wire bound"), "{}", err.message);
        }
    }

    #[test]
    fn wire_decoder_rejects_forged_lengths_truncation_trailing_bytes_and_bad_headers() {
        let small = proof(3, 5, 2);
        let wire = encode_zk_proof_wire(&small).unwrap();
        assert_eq!(wire.len() as u64, wire_len(3, 5, 2));
        assert!(decode_zk_proof_wire(&wire).unwrap() == small);

        let rejects = |bytes: &[u8], what: &str| {
            let err = decode_zk_proof_wire(bytes).unwrap_err();
            assert_eq!(err.code, crate::cli::exit::VERIFY_FAILED, "{what}");
            assert!(err.message.contains(what), "{what}: {}", err.message);
        };
        // Offsets inside the first repetition: opened_e at 44, first seed at 45, then the
        // inputs / products / outputs length prefixes of the first opened view.
        let inputs_len_at = 44 + 1 + 32;
        let products_len_at = inputs_len_at + 4 + 3;
        let outputs_len_at = products_len_at + 4 + 5;
        for (offset, cap) in [
            (inputs_len_at, MAX_VIEW_INPUT_BYTES),
            (products_len_at, MAX_VIEW_PRODUCT_BYTES),
            (outputs_len_at, MAX_VIEW_OUTPUT_BYTES),
        ] {
            for claimed in [cap as u32 + 1, u32::MAX] {
                let mut forged = wire.clone();
                forged[offset..offset + 4].copy_from_slice(&claimed.to_le_bytes());
                rejects(&forged, "oversized repetition field");
            }
            // A length within the cap but beyond the bytes present is a truncation.
            let mut short = wire[..offset + 4].to_vec();
            short[offset..offset + 4].copy_from_slice(&(cap as u32).to_le_bytes());
            rejects(&short, "truncated");
        }
        rejects(&wire[..wire.len() - 1], "truncated");
        rejects(&wire[..43], "truncated");
        rejects(&[], "truncated");
        let mut trailing = wire.clone();
        trailing.push(0);
        rejects(&trailing, "trailing");
        let mut magic = wire.clone();
        magic[0] ^= 1;
        rejects(&magic, "magic");
        for count in [0u32, 437, 439, u32::MAX] {
            let mut reps = wire.clone();
            reps[40..44].copy_from_slice(&count.to_le_bytes());
            rejects(&reps, "invalid repetition count");
        }
    }
}
