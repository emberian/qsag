//! `aggregate` and `verify-agg`: succinct K-to-1 aggregation of committee signatures.

use qsag_agg::sig::digest4_to_bytes;
use qsag_agg::{
    AggSigProfile, FsWalEpochSink, QsagAggregateProof, SignerBitmap, SigningMode, ValidatorKeypair,
    ValidatorPublicKey, aggregate_signatures, compute_committee_root, merge_aggregates,
    verify_aggregate, verify_individual_signature,
};

use crate::cli::{Args, CliError, os_random_32, read_input, write_new};
use crate::codec::{Json, from_hex_exact};
use crate::keys::{PUBLIC_FORMAT, SECRET_FORMAT, derive, load_json, scheme_of};
use crate::schemes::Scheme;

pub const PROOF_FORMAT: &str = "qsag-aggregate-proof-v1";

/// Deterministic validator keypair `index` of a committee seed.
pub fn validator(seed: &[u8; 32], index: u32) -> ValidatorKeypair {
    ValidatorKeypair::keygen_deterministic(
        AggSigProfile::JortsPoseidon2,
        &derive(seed, format!("committee validator {index}").as_bytes()),
        index,
    )
}

fn wal_path(wal_dir: &str, index: u32) -> std::path::PathBuf {
    std::path::Path::new(wal_dir).join(format!("validator-{index}.wal"))
}

fn wal_mac_key(seed: &[u8; 32], index: u32) -> [u8; 32] {
    derive(seed, format!("wal mac {index}").as_bytes())
}

/// Enroll a fresh committee: create every validator's epoch write-ahead log exactly once.
/// Signing later only ever recovers these logs; a missing log is never treated as an unused key.
pub fn enroll_committee(seed: &[u8; 32], validators: u32, wal_dir: &str) -> Result<(), CliError> {
    std::fs::create_dir_all(wal_dir)
        .map_err(|e| CliError::io(format_args!("creating {wal_dir}"), e))?;
    for index in 0..validators {
        let root = digest4_to_bytes(&validator(seed, index).pk.pk_root);
        FsWalEpochSink::create_new_for_fresh_key(
            wal_path(wal_dir, index),
            &root,
            wal_mac_key(seed, index),
        )
        .map_err(|e| {
            CliError::state(format!(
                "validator {index}: write-ahead log already exists or can not be created: {e:?}"
            ))
        })?;
    }
    Ok(())
}

pub fn committee_from_json(keys: &[Json]) -> Result<Vec<ValidatorPublicKey>, CliError> {
    keys.iter()
        .map(|key| {
            let bytes: [u8; 65] =
                from_hex_exact(key.as_str().unwrap_or(""), "validator public key")?;
            ValidatorPublicKey::from_bytes_canonical(&bytes)
                .ok_or_else(|| CliError::input("validator public key is not canonical"))
        })
        .collect()
}

fn load_committee(path: &str) -> Result<Vec<ValidatorPublicKey>, CliError> {
    let public = load_json(path, PUBLIC_FORMAT)?;
    if scheme_of(&public)? != Scheme::AggCommittee {
        return Err(CliError::usage(format!(
            "{path} is not a committee public key file"
        )));
    }
    let keys = public
        .get("validators")
        .and_then(Json::as_array)
        .ok_or_else(|| CliError::input("missing validators"))?;
    let committee = committee_from_json(keys)?;
    if *public.field_hex("committee_root")? != compute_committee_root(&committee) {
        return Err(CliError::input(
            "committee_root does not match the listed validators",
        ));
    }
    Ok(committee)
}

fn load_proof(path: &str) -> Result<QsagAggregateProof, CliError> {
    let file = load_json(path, PROOF_FORMAT)?;
    QsagAggregateProof::from_bytes_canonical(&file.field_hex("proof")?)
        .map_err(|e| CliError::verify(format!("{path}: malformed aggregate proof: {e:?}")))
}

fn proof_file(committee: &[ValidatorPublicKey], proof: &QsagAggregateProof) -> Json {
    let bytes = proof.to_bytes();
    let signers = proof.bitmap().active_indices();
    Json::object(vec![
        ("format", Json::str(PROOF_FORMAT)),
        ("scheme", Json::str(Scheme::AggCommittee.name())),
        (
            "committee_root",
            Json::hex(&compute_committee_root(committee)),
        ),
        (
            "signers",
            Json::Array(signers.iter().map(Json::num).collect()),
        ),
        ("leaf_shards", Json::num(proof.num_leaf_shards())),
        ("proof_bytes", Json::num(bytes.len())),
        (
            "raw_signature_bytes",
            Json::num(signers.len() * AggSigProfile::JortsPoseidon2.raw_signature_bytes()),
        ),
        ("proof", Json::hex(&bytes)),
    ])
}

const AGGREGATE_HELP: &str = "\
qsag aggregate --secret <committee> --signers <i,j,..> --epoch <n> --wal-dir <dir> --in <file|-> --out <path>
qsag aggregate --merge <proofA,proofB> --public <committee> --in <file|-> --out <path>

First form: the listed validators of a committee key (from `qsag keygen --scheme
agg-jorts-poseidon2`) each sign the message at the given one-time epoch, and the signatures
are aggregated into one proof. Each validator's epoch is persisted to its write-ahead log in
--wal-dir (created by keygen) before it signs; an epoch never signs two different messages.

Second form: merge two verified proofs over disjoint signer sets into one.

  --deterministic     derive the proof blinding seed from the inputs instead of OS entropy
  --json              print the proof file contents to standard output as well
";

pub fn aggregate(raw: &[String]) -> Result<(), CliError> {
    let args = Args::parse(
        raw,
        &[
            "secret",
            "public",
            "signers",
            "epoch",
            "wal-dir",
            "merge",
            "in",
            "out",
            "passphrase-env",
            "passphrase-file",
        ],
        &["deterministic", "json", "help"],
    )?;
    if args.flag("help") {
        print!("{AGGREGATE_HELP}");
        return Ok(());
    }
    args.no_positionals()?;
    let message = read_input(args.require("in")?)?;
    let out_path = args.require("out")?;
    let mode = SigningMode::SharedMessage(&message);

    let (committee, proof) = if let Some(pair) = args.get("merge") {
        let committee = load_committee(args.require("public")?)?;
        let (a, b) = pair
            .split_once(',')
            .ok_or_else(|| CliError::usage("--merge takes two comma-separated proof files"))?;
        let merged = merge_aggregates(&committee, &mode, &load_proof(a)?, &load_proof(b)?)
            .map_err(|e| CliError::verify(format!("merge refused: {e:?}")))?;
        (committee, merged)
    } else {
        let secret_path = args.require("secret")?;
        let mut vault = crate::vault::Vault::acquire(secret_path, false)?;
        let mut secret = load_json(secret_path, SECRET_FORMAT)?;
        let passphrase = crate::envelope::passphrase(&args)?;
        let opened = crate::envelope::open(&secret, passphrase.as_deref())?;
        vault.set_key_material(&opened)?;
        vault.authenticate(&secret)?;
        if scheme_of(&secret)? != Scheme::AggCommittee {
            return Err(CliError::usage("--secret must be a committee key file"));
        }
        let seed = crate::codec::from_hex_secret32(opened.field_str("seed")?, "seed")?;
        let size = secret.field_u64("validators")? as u32;
        let epoch = args
            .get_u64("epoch")?
            .ok_or_else(|| CliError::usage("missing required option --epoch"))?;
        let epoch = u32::try_from(epoch).map_err(|_| CliError::usage("--epoch out of range"))?;
        let wal_dir = args.require("wal-dir")?;
        let mut signers = Vec::new();
        for part in args.require("signers")?.split(',') {
            let index: usize = part
                .trim()
                .parse()
                .map_err(|_| CliError::usage("--signers must be comma-separated indices"))?;
            if index >= size as usize || signers.last().is_some_and(|&last| index <= last) {
                return Err(CliError::usage(
                    "--signers must be strictly ascending indices below the committee size",
                ));
            }
            signers.push(index);
        }
        let committee: Vec<ValidatorPublicKey> =
            (0..size).map(|i| validator(&seed, i).pk).collect();
        let bitmap = SignerBitmap::from_active_indices(size, &signers)
            .ok_or_else(|| CliError::usage("invalid signer set"))?;
        vault.reserve(secret_path, &mut secret)?;
        let mut signatures = Vec::with_capacity(signers.len());
        for &index in &signers {
            let mut keypair = validator(&seed, index as u32);
            let root = digest4_to_bytes(&keypair.pk.pk_root);
            let refused = |what: String| {
                CliError::state(format!(
                    "validator {index} can not sign at epoch {epoch}: {what}"
                ))
            };
            let (mut wal, recovered) = FsWalEpochSink::open_or_recover(
                wal_path(wal_dir, index as u32),
                &root,
                wal_mac_key(&seed, index as u32),
            )
            .map_err(|e| {
                refused(format!(
                    "write-ahead log missing, locked, or not authentic: {e:?}"
                ))
            })?;
            if let Some((next_unused, latched, mu)) = recovered {
                keypair
                    .restore_from_wal(next_unused, latched, mu)
                    .map_err(|e| refused(format!("{e:?}")))?;
            }
            let signature = keypair
                .sign_stateful_with_wal(&message, epoch, &mut wal)
                .map_err(|e| refused(format!("{e:?}")))?;
            if !verify_individual_signature(&committee[index], &message, &signature) {
                return Err(CliError::verify(format!(
                    "validator {index} produced an invalid signature"
                )));
            }
            signatures.push(signature);
        }
        let blinding = if args.flag("deterministic") {
            derive(
                &seed,
                &[b"blinding", &epoch.to_be_bytes()[..], &message].concat(),
            )
        } else {
            os_random_32()?
        };
        let proof = aggregate_signatures(&committee, &bitmap, &mode, &signatures, blinding)
            .map_err(|e| CliError::verify(format!("aggregation failed: {e:?}")))?;
        (committee, proof)
    };
    if !verify_aggregate(&committee, &mode, &proof) {
        return Err(CliError::verify("the produced aggregate does not verify"));
    }
    let file = proof_file(&committee, &proof);
    write_new(out_path, file.to_pretty().as_bytes(), false)?;
    if args.flag("json") {
        print!("{}", file.to_pretty());
    } else {
        println!(
            "wrote {out_path}: {} signers, {} proof bytes (raw signatures: {} bytes)",
            proof.num_signers(),
            file.field_u64("proof_bytes")?,
            file.field_u64("raw_signature_bytes")?
        );
    }
    Ok(())
}

const VERIFY_AGG_HELP: &str = "\
qsag verify-agg --public <committee> --in <file|-> --proof <path> [--json]

Verify an aggregate proof against a committee and message. Exit code 0 means valid; exit code 2
means invalid. The signer set is read from the proof and reported.
";

pub fn verify_agg(raw: &[String]) -> Result<(), CliError> {
    let args = Args::parse(raw, &["public", "in", "proof"], &["json", "help"])?;
    if args.flag("help") {
        print!("{VERIFY_AGG_HELP}");
        return Ok(());
    }
    args.no_positionals()?;
    let committee = load_committee(args.require("public")?)?;
    let message = read_input(args.require("in")?)?;
    let proof = load_proof(args.require("proof")?)?;
    let valid = verify_aggregate(&committee, &SigningMode::SharedMessage(&message), &proof);
    let signers = proof.bitmap().active_indices();
    if args.flag("json") {
        let verdict = Json::object(vec![
            ("valid", Json::Bool(valid)),
            (
                "signers",
                Json::Array(signers.iter().map(Json::num).collect()),
            ),
            ("committee_size", Json::num(committee.len())),
        ]);
        print!("{}", verdict.to_pretty());
    } else if valid {
        println!(
            "aggregate valid: {} of {} validators signed: {signers:?}",
            signers.len(),
            committee.len()
        );
    } else {
        println!("aggregate INVALID");
    }
    if valid {
        Ok(())
    } else {
        Err(CliError::verify("aggregate verification failed"))
    }
}
