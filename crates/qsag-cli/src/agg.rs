//! `aggregate` and `verify-agg`: succinct K-to-1 aggregation of committee signatures.

use qsag_accel::keccak::cshake256_framed_32;
use qsag_agg::sig::digest4_to_bytes;
use qsag_agg::{
    AggSigProfile, FsWalEpochSink, HemAggregatedProof, SignerBitmap, SigningMode, ValidatorKeypair,
    ValidatorPublicKey, ValidatorSignature, aggregate_signatures, compute_committee_root,
    merge_aggregates, verify_aggregate, verify_individual_signature,
};
use qsag_core::ceremony_journal::{CeremonyContext, CeremonyReservation, FsCeremonyJournal};
use std::collections::HashMap;

use crate::cli::{
    Args, CliError, MAX_KEY_FILE_BYTES, MAX_SIG_PROOF_BYTES, Secret32, os_random_32,
    read_bounded_file, read_input, write_new,
};
use crate::codec::{Json, from_hex_exact};
use crate::keys::{PUBLIC_FORMAT, SECRET_FORMAT, derive, derive_secret, load_json, scheme_of};
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
    crate::cli::private_dir(wal_dir, true)?;
    for index in 0..validators {
        let root = digest4_to_bytes(&validator(seed, index).pk.pk_root);
        let mac = Secret32::new(wal_mac_key(seed, index));
        FsWalEpochSink::create_new_for_fresh_key(wal_path(wal_dir, index), &root, mac.0).map_err(
            |e| {
                CliError::state(format!(
                    "validator {index}: write-ahead log already exists or can not be created: {e:?}"
                ))
            },
        )?;
    }
    Ok(())
}

/// Provision the committee's ceremony reservation journal and optional external anchors.
pub fn enroll_committee_ceremony(
    secret_path: &str,
    seed: &[u8; 32],
    validators: u32,
    wal_dir: &str,
    committee_root: [u8; 32],
    anchor_cfg: Option<&crate::anchor::AnchorConfig>,
) -> Result<(qsag_core::LedgerCheckpoint, Option<[u8; 24]>), CliError> {
    let ceremony_path = format!("{secret_path}.ceremony");
    let ceremony_mac = derive_secret(seed, b"committee ceremony journal mac");
    let (journal, ceremony_seal) = if let Some(cfg) = anchor_cfg {
        cfg.validate_isolation(&[secret_path], &[wal_dir], true)?;
        for index in 0..validators {
            let root = digest4_to_bytes(&validator(seed, index).pk.pk_root);
            let anchor_mac =
                derive_secret(seed, format!("agg validator anchor {index}").as_bytes());
            let val_anchor = crate::anchor::FsExternalMountAnchor::provision_fresh(
                cfg,
                &[secret_path],
                &[wal_dir],
                "agg_wal",
                root,
                anchor_mac.0,
            )?;
            val_anchor.advance_floor(b"agg_wal", 0)?;
        }
        let ceremony_anchor_mac = derive_secret(seed, b"committee ceremony anchor mac");
        let ceremony_anchor = crate::anchor::FsExternalMountAnchor::provision_fresh(
            cfg,
            &[secret_path],
            &[wal_dir],
            "agg_ceremony",
            committee_root,
            ceremony_anchor_mac.0,
        )?;
        let seal = ceremony_anchor.lock_identity_seal();
        let j = FsCeremonyJournal::create_new_anchored(
            ceremony_path,
            committee_root,
            ceremony_mac.0,
            Box::new(ceremony_anchor),
        )
        .map_err(|e| CliError::io("creating anchored committee ceremony journal", e))?;
        (j, Some(seal))
    } else {
        let j = FsCeremonyJournal::create_new(ceremony_path, committee_root, ceremony_mac.0)
            .map_err(|e| CliError::io("creating committee ceremony journal", e))?;
        (j, None)
    };
    Ok((journal.checkpoint(), ceremony_seal))
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

/// Load a validator roster from either a single `agg-jorts-poseidon2` committee file OR a
/// comma-separated list of individual 65-byte validator / `hem-jorts-poseidon2` quorum public keys.
pub fn load_public_validators(spec: &str) -> Result<Vec<ValidatorPublicKey>, CliError> {
    let parts: Vec<&str> = spec
        .split(',')
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .collect();
    if parts.is_empty() {
        return Err(CliError::usage("--pubkeys / --public must not be empty"));
    }
    let mut out = Vec::with_capacity(parts.len());
    for path in parts {
        let raw = read_bounded_file(path, MAX_KEY_FILE_BYTES)?;
        if let Ok(bytes) = <&[u8; 65]>::try_from(raw.0.as_slice()) {
            let pk = ValidatorPublicKey::from_bytes_canonical(bytes)
                .ok_or_else(|| CliError::input(format!("{path}: non-canonical 65B public key")))?;
            out.push(pk);
            continue;
        }
        let text = std::str::from_utf8(&raw.0)
            .map_err(|_| CliError::input(format!("{path} is not UTF-8")))?;
        let json = Json::parse(text)?;
        if let Some(vals) = json.get("validators").and_then(Json::as_array) {
            out.extend(load_committee(path).or_else(|_| committee_from_json(vals))?);
        } else if let Some(pk_hex) = json
            .get("validator_public_key")
            .or_else(|| json.get("public_key"))
            .and_then(Json::as_str)
        {
            let bytes: [u8; 65] = from_hex_exact(pk_hex, "validator_public_key")?;
            let pk = ValidatorPublicKey::from_bytes_canonical(&bytes).ok_or_else(|| {
                CliError::input(format!("{path}: validator public key is not canonical"))
            })?;
            out.push(pk);
        } else {
            return Err(CliError::usage(format!(
                "{path} is not a committee or JortsPoseidon2 validator/quorum public key file"
            )));
        }
    }
    if out.is_empty() {
        return Err(CliError::usage("validator committee must not be empty"));
    }
    Ok(out)
}

/// Load a standalone `JortsPoseidon2` signature from raw canonical bytes or a JSON signature file
/// (`qsag-quorum-signature-v1` / `qsag-signature-v1`).
fn load_validator_signature(
    path: &str,
) -> Result<(ValidatorSignature, Option<ValidatorPublicKey>), CliError> {
    let raw = read_bounded_file(path, MAX_SIG_PROOF_BYTES)?;
    if raw.0.len() == AggSigProfile::JortsPoseidon2.raw_signature_bytes() {
        return ValidatorSignature::from_bytes_canonical(AggSigProfile::JortsPoseidon2, &raw.0)
            .map(|sig| (sig, None))
            .map_err(|_| CliError::verify(format!("{path}: non-canonical JortsPoseidon2 sig")));
    }
    let text =
        std::str::from_utf8(&raw.0).map_err(|_| CliError::input(format!("{path} is not UTF-8")))?;
    let json = Json::parse(text)?;
    let author = match json.get("validator_public_key").and_then(Json::as_str) {
        Some(hex) => Some(
            ValidatorPublicKey::from_bytes_canonical(&from_hex_exact::<65>(
                hex,
                "validator_public_key",
            )?)
            .ok_or_else(|| CliError::input("non-canonical signature author key"))?,
        ),
        None => None,
    };
    let sig_bytes = json.field_hex("signature")?;
    ValidatorSignature::from_bytes_canonical(AggSigProfile::JortsPoseidon2, &sig_bytes)
        .map(|sig| (sig, author))
        .map_err(|_| CliError::verify(format!("{path}: non-canonical JortsPoseidon2 signature")))
}

fn resolve_signature_authors(
    committee: &[ValidatorPublicKey],
    message: &[u8],
    loaded_sigs: Vec<(ValidatorSignature, Option<ValidatorPublicKey>)>,
    sig_paths: &[&str],
) -> Result<(Vec<usize>, Vec<ValidatorSignature>), CliError> {
    let mut authors = HashMap::with_capacity(committee.len());
    for (idx, pk) in committee.iter().enumerate() {
        if authors.insert(*pk, idx).is_some() {
            return Err(CliError::usage("committee contains duplicate public keys"));
        }
    }
    let mut ordered = vec![None; committee.len()];
    for (pos, (sig, author)) in loaded_sigs.into_iter().enumerate() {
        let author = author.ok_or_else(|| CliError::usage(format!(
            "{} has no validator_public_key metadata; supply --signers for raw or legacy signatures",
            sig_paths[pos]
        )))?;
        let idx = *authors.get(&author).ok_or_else(|| {
            CliError::verify(format!(
                "{} identifies a public key outside the committee",
                sig_paths[pos]
            ))
        })?;
        if ordered[idx].is_some() {
            return Err(CliError::verify(format!(
                "duplicate signature author {idx}"
            )));
        }
        if !verify_individual_signature(&committee[idx], message, &sig) {
            return Err(CliError::verify(format!(
                "signature for validator {idx} failed individual verification"
            )));
        }
        ordered[idx] = Some(sig);
    }
    Ok(ordered
        .into_iter()
        .enumerate()
        .filter_map(|(idx, sig)| sig.map(|sig| (idx, sig)))
        .unzip())
}

fn load_proof(path: &str) -> Result<HemAggregatedProof, CliError> {
    let file = load_json(path, PROOF_FORMAT)?;
    HemAggregatedProof::from_bytes_canonical(&file.field_hex("proof")?)
        .map_err(|e| CliError::verify(format!("{path}: malformed aggregate proof: {e:?}")))
}

fn proof_file(committee: &[ValidatorPublicKey], proof: &HemAggregatedProof) -> Json {
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
qsag aggregate --pubkeys <pk1,pk2,..|committee> --sigs <sig1,sig2,..> [--signers <i,j,..>] --message <file|-> --out <path>
qsag aggregate --merge <proofA,proofB> --public <committee|pk1,pk2,..> --in <file|-> --out <path>
qsag aggregate --secret <committee> --signers <i,j,..> --epoch <n> --wal-dir <dir> --in <file|-> --out <path>

First form (untrusted public aggregator — zero secret keys!): aggregate pre-existing
JortsPoseidon2 signatures (from `qsag quorum sign --scheme hem-jorts-poseidon2` or
individual validators) using ONLY public keys, signatures, and the message.
Without --signers, each JSON signature must include validator_public_key.
Raw and legacy signature files require explicit --signers.

Second form: merge two verified proofs over disjoint signer sets into one.

Third form: committee-vault demo signing + aggregation backed by per-validator FsWalEpochSink.

  --deterministic     derive the proof blinding seed from the inputs instead of OS entropy
  --anchor-dir <dir>  verify and advance external monotone anchors before releasing proof
  --vault-dir <dir>   explicit local custody directory verified disjoint from --anchor-dir
  --ephemeral-unanchored  allow disposable committee signing without rollback protection
  --allow-single-disk-anchor  permit --anchor-dir on the same filesystem device (distinct inode)
  --policy-id-hex <hex>  32-byte policy identifier committed into CeremonyContext
  --spend-amount <n>  spend amount committed into CeremonyContext (default: 0)
  --json              print the proof file contents to standard output as well
";

pub fn aggregate(raw: &[String]) -> Result<(), CliError> {
    let args = Args::parse(
        raw,
        &[
            "secret",
            "public",
            "pubkeys",
            "sigs",
            "signers",
            "epoch",
            "wal-dir",
            "merge",
            "in",
            "message",
            "out",
            "passphrase-env",
            "passphrase-file",
            "anchor-dir",
            "vault-dir",
            "anchor-tpm-nv",
            "anchor-tpm-device",
            "anchor-tpm-auth-env",
            "policy-id-hex",
            "spend-amount",
        ],
        &[
            "deterministic",
            "json",
            "help",
            "allow-single-disk-anchor",
            "anchor-vmgenid",
            "anchor-vmgenid-strict",
            "ephemeral-unanchored",
        ],
    )?;
    if args.flag("help") {
        print!("{AGGREGATE_HELP}");
        return Ok(());
    }
    args.no_positionals()?;
    let anchor_cfg = crate::anchor::AnchorConfig::from_args(&args)?;
    let base_context = crate::anchor::parse_ceremony_context(&args, 0)?;
    if args.get("in").is_some() && args.get("message").is_some() {
        return Err(CliError::usage("pass either --message or --in, not both"));
    }
    if args.get("public").is_some() && args.get("pubkeys").is_some() {
        return Err(CliError::usage(
            "pass either --pubkeys or --public, not both",
        ));
    }
    let msg_arg = args
        .get("message")
        .or_else(|| args.get("in"))
        .ok_or_else(|| CliError::usage("missing required option --message (or --in)"))?;
    let message = read_input(msg_arg)?;
    let out_path = args.require("out")?;
    let mode = SigningMode::SharedMessage(&message);

    let (committee, proof) = if let Some(pair) = args.get("merge") {
        if args.get("secret").is_some() || args.get("sigs").is_some() {
            return Err(CliError::usage(
                "--merge cannot be combined with --secret or --sigs",
            ));
        }
        if anchor_cfg.is_some()
            || args.get("policy-id-hex").is_some()
            || args.get("spend-amount").is_some()
        {
            return Err(CliError::usage(
                "ceremony anchor and policy options do not apply to --merge",
            ));
        }
        let pub_arg = args
            .get("pubkeys")
            .or_else(|| args.get("public"))
            .ok_or_else(|| CliError::usage("missing required option --pubkeys (or --public)"))?;
        let committee = load_public_validators(pub_arg)?;
        let (a, b) = pair
            .split_once(',')
            .ok_or_else(|| CliError::usage("--merge takes two comma-separated proof files"))?;
        let merged = merge_aggregates(&committee, &mode, &load_proof(a)?, &load_proof(b)?)
            .map_err(|e| CliError::verify(format!("merge refused: {e:?}")))?;
        (committee, merged)
    } else if let Some(sigs_spec) = args.get("sigs") {
        if args.get("secret").is_some()
            || args.get("wal-dir").is_some()
            || args.get("epoch").is_some()
            || anchor_cfg.is_some()
            || args.get("policy-id-hex").is_some()
            || args.get("spend-amount").is_some()
        {
            return Err(CliError::usage(
                "untrusted public aggregation (--sigs) uses only public inputs (--pubkeys, --sigs, --message) and never accepts --secret, --wal-dir, or ceremony flags",
            ));
        }
        let pub_arg = args
            .get("pubkeys")
            .or_else(|| args.get("public"))
            .ok_or_else(|| {
                CliError::usage("public aggregation requires --pubkeys (or --public)")
            })?;
        let committee = load_public_validators(pub_arg)?;
        let size = u32::try_from(committee.len())
            .map_err(|_| CliError::usage("committee size exceeds u32::MAX"))?;

        let sig_paths: Vec<&str> = sigs_spec
            .split(',')
            .map(str::trim)
            .filter(|s| !s.is_empty())
            .collect();
        if sig_paths.is_empty() {
            return Err(CliError::usage(
                "--sigs must list at least one signature file",
            ));
        }
        let mut loaded_sigs = Vec::with_capacity(sig_paths.len());
        for p in &sig_paths {
            loaded_sigs.push(load_validator_signature(p)?);
        }

        let (signers, ordered_sigs): (Vec<usize>, Vec<ValidatorSignature>) =
            if let Some(signers_spec) = args.get("signers") {
                let mut indices = Vec::new();
                for part in signers_spec.split(',') {
                    let idx: usize = part.trim().parse().map_err(|_| {
                        CliError::usage("--signers must be comma-separated indices")
                    })?;
                    if idx >= committee.len() || indices.last().is_some_and(|&last| idx <= last) {
                        return Err(CliError::usage(
                            "--signers must be strictly ascending indices below the committee size",
                        ));
                    }
                    indices.push(idx);
                }
                if indices.len() != loaded_sigs.len() {
                    return Err(CliError::usage("--signers count must match --sigs count"));
                }
                for (&idx, (sig, author)) in indices.iter().zip(&loaded_sigs) {
                    if author.is_some_and(|pk| pk != committee[idx])
                        || !verify_individual_signature(&committee[idx], &message, sig)
                    {
                        return Err(CliError::verify(format!(
                            "signature for validator {idx} failed individual verification"
                        )));
                    }
                }
                (
                    indices,
                    loaded_sigs.into_iter().map(|(sig, _)| sig).collect(),
                )
            } else {
                resolve_signature_authors(&committee, &message, loaded_sigs, &sig_paths)?
            };

        let bitmap = SignerBitmap::from_active_indices(size, &signers)
            .ok_or_else(|| CliError::usage("invalid signer set"))?;
        let committee_root = compute_committee_root(&committee);
        let blinding = if args.flag("deterministic") {
            let mut sig_digest_acc = [0u8; 32];
            for s in &ordered_sigs {
                sig_digest_acc = cshake256_framed_32(
                    b"QSAG.CLI.PUBLIC_AGG.SIG_ACC.V1",
                    &[&sig_digest_acc, &s.to_bytes()],
                );
            }
            cshake256_framed_32(
                b"QSAG.CLI.PUBLIC_AGG.BLINDING.V1",
                &[&committee_root, &sig_digest_acc, &message],
            )
        } else {
            os_random_32()?
        };
        let proof = aggregate_signatures(&committee, &bitmap, &mode, &ordered_sigs, blinding)
            .map_err(|e| CliError::verify(format!("aggregation failed: {e:?}")))?;
        (committee, proof)
    } else {
        crate::keys::require_stateful_anchor(
            Scheme::AggCommittee,
            anchor_cfg.as_ref(),
            args.flag("ephemeral-unanchored"),
        )?;
        let secret_path = args.require("secret")?;
        let mut vault = crate::vault::Vault::acquire(secret_path, false)?;
        let mut secret = load_json(secret_path, SECRET_FORMAT)?;
        let passphrase = crate::envelope::passphrase(&args)?;
        let opened = crate::envelope::open(&secret, passphrase.as_deref().map(Vec::as_slice))?;
        vault.set_key_material(&opened);
        vault.authenticate(&secret)?;
        if scheme_of(&secret)? != Scheme::AggCommittee {
            return Err(CliError::usage("--secret must be a committee key file"));
        }
        crate::anchor::enforce_anchor_requirement(&secret, anchor_cfg.as_ref())?;
        let seed = opened.seed()?;
        let size = secret.field_u64("validators")? as u32;
        let epoch = args
            .get_u64("epoch")?
            .ok_or_else(|| CliError::usage("missing required option --epoch"))?;
        let epoch = u32::try_from(epoch).map_err(|_| CliError::usage("--epoch out of range"))?;
        let wal_dir = args.require("wal-dir")?;
        crate::cli::private_dir(wal_dir, false)?;
        if let Some(cfg) = &anchor_cfg {
            cfg.validate_isolation(&[secret_path], &[wal_dir], false)?;
        }
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
        let committee_root = compute_committee_root(&committee);
        let bitmap = SignerBitmap::from_active_indices(size, &signers)
            .ok_or_else(|| CliError::usage("invalid signer set"))?;

        let retained_ceremony_ckpt = crate::vault::read_ceremony_checkpoint(&secret)?;
        let ceremony_mac = derive_secret(&seed, b"committee ceremony journal mac");
        let ceremony_path = format!("{secret_path}.ceremony");
        let mut ceremony_journal = if let Some(cfg) = &anchor_cfg {
            let ceremony_anchor_mac = derive_secret(&seed, b"committee ceremony anchor mac");
            let ceremony_anchor = crate::anchor::FsExternalMountAnchor::open_existing(
                cfg,
                &[secret_path],
                &[wal_dir],
                "agg_ceremony",
                committee_root,
                ceremony_anchor_mac.0,
            )?;
            ceremony_anchor.verify_expected_seal(&secret, "anchor_ceremony_seal")?;
            let j = FsCeremonyJournal::open_existing_anchored(
                ceremony_path,
                committee_root,
                ceremony_mac.0,
                Box::new(ceremony_anchor),
            )
            .map_err(|_| CliError::state("CorruptOrRolledBackCeremonyJournal"))?;
            let j_ckpt = j.checkpoint();
            if j_ckpt.generation < retained_ceremony_ckpt.generation
                || (j_ckpt.generation == retained_ceremony_ckpt.generation
                    && !qsag_accel::ct::ct_eq_bytes(&j_ckpt.tag, &retained_ceremony_ckpt.tag))
            {
                return Err(CliError::state("CorruptOrRolledBackCeremonyJournal"));
            }
            j
        } else {
            FsCeremonyJournal::open_existing_at_least(
                ceremony_path,
                committee_root,
                ceremony_mac.0,
                retained_ceremony_ckpt,
            )
            .map_err(|_| CliError::state("CorruptOrRolledBackCeremonyJournal"))?
        };

        let mut prepared_validators = Vec::with_capacity(signers.len());
        for &index in &signers {
            let mut keypair = validator(&seed, index as u32);
            let root = digest4_to_bytes(&keypair.pk.pk_root);
            let refused = |what: String| {
                CliError::state(format!(
                    "validator {index} can not sign at epoch {epoch}: {what}"
                ))
            };
            let mac = Secret32::new(wal_mac_key(&seed, index as u32));
            let (wal, recovered) =
                FsWalEpochSink::open_or_recover(wal_path(wal_dir, index as u32), &root, mac.0)
                    .map_err(|e| {
                        refused(format!(
                            "write-ahead log missing, locked, or not authentic: {e:?}"
                        ))
                    })?;
            let val_anchor = if let Some(cfg) = &anchor_cfg {
                let anchor_mac =
                    derive_secret(&seed, format!("agg validator anchor {index}").as_bytes());
                let val_anchor = crate::anchor::FsExternalMountAnchor::open_existing(
                    cfg,
                    &[secret_path],
                    &[wal_dir],
                    "agg_wal",
                    root,
                    anchor_mac.0,
                )?;
                let observed_floor =
                    recovered.map_or(0u64, |(next_unused, _, _)| u64::from(next_unused));
                val_anchor.verify_floor_at_least(b"agg_wal", observed_floor)?;
                Some(val_anchor)
            } else {
                None
            };
            if let Some((next_unused, latched, mu)) = recovered {
                keypair
                    .restore_from_wal(next_unused, latched, mu)
                    .map_err(|e| refused(format!("{e:?}")))?;
            }
            prepared_validators.push((index, keypair, wal, val_anchor));
        }

        let cursor = ceremony_journal.checkpoint().generation;
        let mut signer_bytes = Vec::with_capacity(signers.len() * 4);
        for &idx in &signers {
            signer_bytes.extend_from_slice(&(idx as u32).to_be_bytes());
        }
        let binding = cshake256_framed_32(
            b"QSAG.CLI.AGG.BINDING.V1",
            &[
                &committee_root,
                &cursor.to_be_bytes(),
                &epoch.to_be_bytes(),
                &signer_bytes,
            ],
        );
        let ceremony_id =
            cshake256_framed_32(b"QSAG.CLI.AGG.CEREMONY.V1", &[&seed.0, &binding, &message]);
        let context = CeremonyContext {
            policy_id: base_context.policy_id,
            spend_amount: base_context.spend_amount,
            mpc_nonce_epoch: cursor,
        };
        let permit = ceremony_journal
            .persist_with_context(
                CeremonyReservation {
                    ceremony_id,
                    key_id: committee_root,
                    epoch_or_codeword: binding,
                    seed_burn_cursor: cursor,
                    hedge_generation: cursor,
                },
                None,
                false,
                context,
            )
            .map_err(|_| CliError::state("CorruptOrRolledBackCeremonyJournal"))?;
        ceremony_journal
            .consume_release_with_context(permit, context)
            .map_err(|_| CliError::state("CorruptOrRolledBackCeremonyJournal"))?;
        crate::vault::record_ceremony_checkpoint(&mut secret, ceremony_journal.checkpoint());
        vault.reserve(secret_path, &mut secret)?;

        let mut signatures = Vec::with_capacity(signers.len());
        for (index, mut keypair, mut wal, val_anchor) in prepared_validators {
            let refused = |what: String| {
                CliError::state(format!(
                    "validator {index} can not sign at epoch {epoch}: {what}"
                ))
            };
            if let Some(val_anchor) = &val_anchor {
                val_anchor.advance_floor(b"agg_wal", u64::from(epoch).saturating_add(1))?;
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
qsag verify-aggregate --pubkeys <pk1,pk2,..|committee> --message <file|-> --proof <path> [--json]
qsag verify-agg       --public  <committee|pk1,pk2,..> --in      <file|-> --proof <path> [--json]

Verify an aggregate proof against public keys and a message. Exit code 0 means valid; exit code 2
means invalid. The signer set is read from the proof and reported.
";

pub fn verify_agg(raw: &[String]) -> Result<(), CliError> {
    let args = Args::parse(
        raw,
        &["public", "pubkeys", "in", "message", "proof"],
        &["json", "help"],
    )?;
    if args.flag("help") {
        print!("{VERIFY_AGG_HELP}");
        return Ok(());
    }
    args.no_positionals()?;
    if args.get("public").is_some() && args.get("pubkeys").is_some() {
        return Err(CliError::usage(
            "pass either --pubkeys or --public, not both",
        ));
    }
    if args.get("in").is_some() && args.get("message").is_some() {
        return Err(CliError::usage("pass either --message or --in, not both"));
    }
    let pub_arg = args
        .get("pubkeys")
        .or_else(|| args.get("public"))
        .ok_or_else(|| CliError::usage("missing required option --pubkeys (or --public)"))?;
    let msg_arg = args
        .get("message")
        .or_else(|| args.get("in"))
        .ok_or_else(|| CliError::usage("missing required option --message (or --in)"))?;
    let committee = load_public_validators(pub_arg)?;
    let message = read_input(msg_arg)?;
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

#[cfg(all(test, unix))]
mod tests {
    use super::*;
    use std::os::unix::fs::PermissionsExt;

    #[test]
    fn indexed_authorship_requires_matching_verified_metadata() {
        use qsag_agg::sig::{EpochWalSink, SigError, WalEpochState};
        #[derive(Default)]
        struct TestWal(Option<WalEpochState>);
        impl EpochWalSink for TestWal {
            fn recovered_state(&self, _: &[u8; 32]) -> Result<Option<WalEpochState>, SigError> {
                Ok(self.0)
            }
            fn persist_latched_epoch(
                &mut self,
                _: &[u8; 32],
                next: u32,
                epoch: u32,
                mu: &[u8; 32],
            ) -> Result<(), SigError> {
                self.0 = Some((next, epoch, *mu));
                Ok(())
            }
        }
        let mut a = validator(&[3; 32], 0);
        let mut b = validator(&[4; 32], 1);
        let message = b"indexed authorship";
        let sa = a
            .sign_stateful(message, 0, &mut TestWal::default())
            .unwrap();
        let sb = b
            .sign_stateful(message, 0, &mut TestWal::default())
            .unwrap();
        let committee = [a.pk, b.pk];
        let (indices, signatures) = resolve_signature_authors(
            &committee,
            message,
            vec![(sb.clone(), Some(b.pk)), (sa.clone(), Some(a.pk))],
            &["b", "a"],
        )
        .unwrap();
        assert_eq!(indices, [0, 1]);
        assert_eq!(signatures, [sa.clone(), sb]);
        assert!(
            resolve_signature_authors(
                &committee,
                message,
                vec![(sa.clone(), Some(b.pk))],
                &["wrong"]
            )
            .is_err()
        );
        assert!(
            resolve_signature_authors(&committee, message, vec![(sa.clone(), None)], &["raw"])
                .is_err()
        );
        assert!(
            resolve_signature_authors(
                &[b.pk],
                message,
                vec![(sa.clone(), Some(a.pk))],
                &["unknown"]
            )
            .is_err()
        );
        assert!(
            resolve_signature_authors(
                &committee,
                message,
                vec![(sa.clone(), Some(a.pk)), (sa.clone(), Some(a.pk))],
                &["a", "a"]
            )
            .is_err()
        );
        assert!(
            resolve_signature_authors(
                &[a.pk, a.pk],
                message,
                vec![(sa, Some(a.pk))],
                &["duplicate"]
            )
            .is_err()
        );
    }

    #[test]
    fn enrollment_keeps_validator_logs_in_an_owner_only_directory() {
        let root = std::env::temp_dir().join(format!(
            "qsag-wal-dir-{}",
            crate::codec::to_hex(&os_random_32().unwrap())
        ));
        std::fs::create_dir(&root).unwrap();
        let path = |name: &str| root.join(name).to_str().unwrap().to_owned();
        let mode = |name: &str| std::fs::metadata(path(name)).unwrap().permissions().mode() & 0o777;

        enroll_committee(&[7; 32], 1, &path("committee/wal")).unwrap();
        assert_eq!(mode("committee"), 0o700);
        assert_eq!(mode("committee/wal"), 0o700);
        assert!(root.join("committee/wal/validator-0.wal").is_file());

        // A directory other users can list is refused before any log is created in it.
        std::fs::create_dir(path("shared")).unwrap();
        std::fs::set_permissions(path("shared"), std::fs::Permissions::from_mode(0o755)).unwrap();
        assert!(enroll_committee(&[7; 32], 1, &path("shared")).is_err());
        assert_eq!(std::fs::read_dir(path("shared")).unwrap().count(), 0);
        assert_eq!(mode("shared"), 0o755);
        std::fs::remove_dir_all(root).unwrap();
    }
}
