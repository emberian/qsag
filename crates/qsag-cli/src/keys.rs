//! `keygen`, `sign`, and `verify`.

use qsag_accel::CpuReferenceBackend;
use qsag_accel::keccak::{cshake256_framed_32, cshake256_framed_xof};
use qsag_addr::{KeyIdentityKind, QsagAddress};
use qsag_core::ceremony_journal::{CeremonyReservation, FsCeremonyJournal};
use qsag_core::fips205::{
    Fips205Params, SlhPublicKey, SlhSecretKey, slh_keygen_from_seed, slh_sign, slh_verify,
};
use qsag_core::pcg_dense::{FsSeedBurnTracker, SeedBurnError, SeedBurnTracker};
use qsag_fts::{
    FrontierDpTable, FrontierFtsError, FrontierFtsProfile, FrontierFtsPublicKey,
    FrontierFtsSignature, FrontierFtsSigningKey, FsWalFtsEpochLatch, ParallelSeededError,
    ParallelSeededPublicKey, ParallelSeededSignature, ParallelSeededThresholdSetup,
    verify_frontier_fts, verify_parallel_seeded_fts,
};

use crate::cli::{
    Args, CliError, MAX_KEY_FILE_BYTES, MAX_SIG_PROOF_BYTES, Secret32, ZeroizingBuf, os_random_32,
    read_bounded_file, read_input, write_new,
};
use crate::codec::{Json, from_hex_exact, from_hex_secret32};
use crate::schemes::{Scheme, THRESHOLD_FTS_PARAMS};

pub const SECRET_FORMAT: &str = "qsag-secret-key-v1";
pub const PUBLIC_FORMAT: &str = "qsag-public-key-v1";
pub const SIGNATURE_FORMAT: &str = "qsag-signature-v1";

/// Domain-separated 32-byte subkey of a key file's master seed.
pub fn derive(seed: &[u8; 32], label: &[u8]) -> [u8; 32] {
    cshake256_framed_32(b"QSAG.CLI.DERIVE.V1", &[seed, label])
}

pub fn load_json(path: &str, format: &str) -> Result<Json, CliError> {
    let limit = if format == SECRET_FORMAT || format == PUBLIC_FORMAT {
        MAX_KEY_FILE_BYTES
    } else {
        MAX_SIG_PROOF_BYTES
    };
    let bytes = read_bounded_file(path, limit)?;
    let json = Json::parse(
        std::str::from_utf8(&bytes.0).map_err(|_| CliError::input("input is not UTF-8"))?,
    )?;
    if json.field_str("format")? != format {
        return Err(CliError::input(format!("{path} is not a {format} file")));
    }
    Ok(json)
}

pub fn scheme_of(json: &Json) -> Result<Scheme, CliError> {
    Scheme::by_name(json.field_str("scheme")?)
}

fn frontier_key(profile: qsag_fts::FrontierFtsProfile, seed: &[u8; 32]) -> FrontierFtsSigningKey {
    FrontierFtsSigningKey::keygen(
        profile,
        derive(seed, b"frontier sk_seed"),
        derive(seed, b"frontier sk_prf"),
        derive(seed, b"frontier pk_seed"),
        true,
        &CpuReferenceBackend,
    )
}

fn threshold_setup(
    seed: &[u8; 32],
    parties: u64,
    params: qsag_fts::ParallelSeededParams,
) -> Result<ParallelSeededThresholdSetup, CliError> {
    ParallelSeededThresholdSetup::trusted_dealer_setup_for_testing(
        params,
        parties as usize,
        derive(seed, b"threshold dealer entropy"),
        derive(seed, b"threshold pk_seed"),
        &CpuReferenceBackend,
    )
    .map_err(|e| CliError::usage(format!("threshold setup failed: {e:?}")))
}

fn threshold_params(file: &Json) -> Result<qsag_fts::ParallelSeededParams, CliError> {
    let height = file.field_u64("tree_height")?;
    if height != 3 && height != 10 { return Err(CliError::input("unsupported threshold tree height")); }
    Ok(qsag_fts::ParallelSeededParams { tree_height: height as usize, ..THRESHOLD_FTS_PARAMS })
}

fn threshold_public_bytes(pk: &ParallelSeededPublicKey) -> Vec<u8> {
    let mut out = pk.pk_seed_bytes.to_vec();
    for limb in pk.merkle_root {
        out.extend_from_slice(&limb.to_le_bytes());
    }
    out
}

fn burn_journal_path(secret_path: &str) -> String {
    format!("{secret_path}.burn")
}

fn ceremony_journal_path(secret_path: &str) -> String {
    format!("{secret_path}.ceremony")
}

fn seed_burn_ledger_path(secret_path: &str) -> String {
    format!("{secret_path}.seedburn")
}

fn provision_stateful_seed_burn_ledger(
    secret_path: &str,
    key_id: [u8; 32],
    seed: &[u8; 32],
) -> Result<qsag_core::LedgerCheckpoint, CliError> {
    FsCeremonyJournal::create_new(
        ceremony_journal_path(secret_path),
        key_id,
        derive(seed, b"ceremony journal mac"),
    )
    .map_err(|e| CliError::io("creating ceremony reservation journal", e))?;
    let seed_burns = FsSeedBurnTracker::provision_genesis(
        seed_burn_ledger_path(secret_path),
        derive(seed, b"seed burn ledger mac"),
    )
    .map_err(|_| CliError::state("creating seed burn ledger failed"))?;
    Ok(seed_burns.checkpoint())
}

fn burn_stateful_ceremony_with_checkpoint(
    secret_path: &str,
    secret_json: &mut Json,
    key_id: [u8; 32],
    seed: &[u8; 32],
    ceremony_id: [u8; 32],
    seed_burn_id: [u8; 32],
    already_burned_msg: impl FnOnce() -> String,
) -> Result<(), CliError> {
    let retained_ckpt = crate::vault::read_ledger_checkpoint(secret_json)?;
    let mut ceremony_journal = FsCeremonyJournal::open_existing(
        ceremony_journal_path(secret_path),
        key_id,
        derive(seed, b"ceremony journal mac"),
    )
    .map_err(|_| CliError::state("CorruptOrRolledBackCeremonyJournal"))?;
    let mut seed_burns = FsSeedBurnTracker::open_existing(
        seed_burn_ledger_path(secret_path),
        derive(seed, b"seed burn ledger mac"),
        retained_ckpt,
    )
    .map_err(|_| CliError::state("CorruptOrRolledBackLedgerCheckpoint"))?;
    if seed_burns
        .is_burned(&seed_burn_id)
        .map_err(|_| CliError::state("CorruptOrRolledBackLedgerCheckpoint"))?
    {
        return Err(CliError::state(already_burned_msg()));
    }
    let cursor = seed_burns
        .checkpoint()
        .generation
        .checked_add(1)
        .ok_or_else(crate::vault::corrupt)?;
    let permit = ceremony_journal
        .persist_before_release(CeremonyReservation {
            ceremony_id,
            key_id,
            epoch_or_codeword: seed_burn_id,
            seed_burn_cursor: cursor,
            hedge_generation: cursor,
        })
        .map_err(|_| CliError::state("CorruptOrRolledBackCeremonyJournal"))?;
    seed_burns
        .authorize_release(&ceremony_journal, permit)
        .map_err(|_| CliError::state("CorruptOrRolledBackLedgerCheckpoint"))?;
    seed_burns
        .begin_expansion(&ceremony_id, &seed_burn_id)
        .map_err(|_| CliError::state("CorruptOrRolledBackLedgerCheckpoint"))?;
    seed_burns.burn(&seed_burn_id).map_err(|e| match e {
        SeedBurnError::AlreadyBurned => CliError::state(already_burned_msg()),
        SeedBurnError::Io => CliError::state("CorruptOrRolledBackLedgerCheckpoint"),
    })?;
    crate::vault::record_ledger_checkpoint(secret_json, seed_burns.checkpoint());
    Ok(())
}

const KEYGEN_HELP: &str = "\
qsag keygen --scheme <name> --secret-out <path> --public-out <path> [options]

Generate a key pair. Output files are created new unless --force-overwrite is supplied.
The secret file is created with owner-only permissions.

  --passphrase-env <VAR> / --passphrase-file <PATH>  seal secret material (file bytes used verbatim)
                        omission preserves legacy unencrypted key files for existing scripts
  --accept-trusted-dealer-demo  acknowledge local single-seed threshold demo custody
  --scheme <name>       one of the schemes listed by `qsag info`
  --seed-file <path>    file holding 32 bytes of hex to derive the key from (default: OS entropy)
  --deterministic-test-only  allow reproducible stateful seed enrollment (UNSAFE for custody)
  --force-overwrite     replace an authenticated stateless vault; stateful overwrite is refused
  --hrp <hrp>           address human-readable part (default: qsp)
  --fast-demo          fts-threshold only: use an eight-epoch demonstration tree
  --parties <n>         fts-threshold: number of signing parties, 2..=16 (default: 3)
  --validators <k>      agg-jorts-poseidon2: committee size, 1..=64 (default: 8)
  --wal-dir <dir>       agg-jorts-poseidon2: directory in which each validator's epoch
                        write-ahead log is created (required for that scheme)
  --json                print the public key file contents to standard output as well
";

pub fn keygen(raw: &[String]) -> Result<(), CliError> {
    let args = Args::parse(
        raw,
        &[
            "scheme",
            "secret-out",
            "public-out",
            "seed-file",
            "hrp",
            "parties",
            "validators",
            "wal-dir",
            "passphrase-env",
            "passphrase-file",
        ],
        &["json", "help", "deterministic-test-only", "force-overwrite", "fast-demo", "accept-trusted-dealer-demo"],
    )?;
    if args.flag("help") {
        print!("{KEYGEN_HELP}");
        return Ok(());
    }
    args.no_positionals()?;
    let scheme = Scheme::by_name(args.require("scheme")?)?;
    require_dealer_acceptance(scheme, &args)?;
    let passphrase = crate::envelope::passphrase(&args)?;
    if matches!(scheme, Scheme::AggCommittee) && passphrase.is_some() {
        return Err(CliError::usage("committee envelope support is unavailable"));
    }
    let secret_out = args.require("secret-out")?;
    let public_out = args.require("public-out")?;
    let force = args.flag("force-overwrite");
    // Stateful identities cannot safely be reset in place, even with --force-overwrite.
    if force && !matches!(scheme, Scheme::Slh(_)) {
        return Err(CliError::state(
            "stateful vault overwrite refused; enroll a fresh key at a new path",
        ));
    }
    let existing = std::fs::symlink_metadata(secret_out).is_ok();
    let mut vault = crate::vault::Vault::acquire(secret_out, !(force && existing))?;
    if force && existing {
        let old = load_json(secret_out, SECRET_FORMAT)?;
        let opened = crate::envelope::open(&old, passphrase.as_deref())?;
        vault.set_key_material(&opened)?;
        vault.authenticate(&old)?;
        if !matches!(scheme_of(&old)?, Scheme::Slh(_)) {
            return Err(CliError::state("stateful vault overwrite refused"));
        }
    }
    let hrp = args.get("hrp").unwrap_or("qsp");
    let seed = Secret32(match args.get("seed-file") {
        Some(path) => {
            let text = read_bounded_file(path, MAX_KEY_FILE_BYTES)?;
            from_hex_exact(
                std::str::from_utf8(&text.0).map_err(|_| CliError::input("invalid seed text"))?,
                "seed",
            )?
        }
        None => os_random_32()?,
    });
    let entropy = Secret32(os_random_32()?);
    let nonce = &entropy[..16];
    let seed = if !matches!(scheme, Scheme::Slh(_)) && !args.flag("deterministic-test-only") {
        Secret32(cshake256_framed_32(
            b"QSAG.CLI.ENROLL.V1",
            &[&seed[..], nonce],
        ))
    } else {
        seed
    };
    let scheme_name = scheme.name();
    let mut secret = vec![
        ("format", Json::str(SECRET_FORMAT)),
        ("scheme", Json::str(scheme_name.clone())),
        ("enrollment_nonce", Json::hex(nonce)),
        ("uses_completed", Json::num(0)),
    ];
    let mut public = vec![
        ("format", Json::str(PUBLIC_FORMAT)),
        ("scheme", Json::str(scheme_name)),
    ];

    let public_key: Vec<u8> = match scheme {
        Scheme::Slh(params) => {
            let (sk, pk) = slh_keygen_from_seed(&params, &seed[..])
                .map_err(|e| CliError::usage(e.to_string()))?;
            let raw_key = ZeroizingBuf(sk.to_bytes());
            secret.push(("secret_key", Json::hex(&raw_key.0)));
            public.push((
                "spki_der",
                Json::hex(
                    &pk.to_spki_der(&params)
                        .map_err(|e| CliError::usage(e.to_string()))?,
                ),
            ));
            pk.to_bytes()
        }
        Scheme::Frontier(profile) => {
            let key = frontier_key(profile, &seed);
            FsWalFtsEpochLatch::create(burn_journal_path(secret_out), key.wal_key(), derive(&seed, b"burn journal mac"))
                .map_err(|e| CliError::io("creating frontier use journal", e))?;
            let ckpt = provision_stateful_seed_burn_ledger(secret_out, key.wal_key(), &seed)?;
            secret.push(("ledger_checkpoint_gen", Json::num(ckpt.generation)));
            secret.push(("ledger_checkpoint_tag", Json::hex(&ckpt.tag)));
            secret.push(("seed", Json::hex(&seed[..])));
            [&key.pk.pk_seed[..], &key.pk.root].concat()
        }
        Scheme::ThresholdFts => {
            secret.push((
                "custody_model",
                Json::str("trusted-dealer-demo; not distributed DKG"),
            ));
            public.push((
                "custody_model",
                Json::str("trusted-dealer-demo; not distributed DKG"),
            ));
            let parties = args.get_u64("parties")?.unwrap_or(3);
            if !(2..=16).contains(&parties) {
                return Err(CliError::usage("--parties must be between 2 and 16"));
            }
            let params = qsag_fts::ParallelSeededParams { tree_height: if args.flag("fast-demo") { 3 } else { 10 }, ..THRESHOLD_FTS_PARAMS };
            secret.push(("tree_height", Json::num(params.tree_height)));
            public.push(("tree_height", Json::num(params.tree_height)));
            let setup = threshold_setup(&seed, parties, params)?;
            FsWalFtsEpochLatch::create(
                burn_journal_path(secret_out),
                setup.pk.pk_seed_bytes,
                derive(&seed, b"burn journal mac"),
            )
            .map_err(|e| CliError::io("creating the epoch burn journal", e))?;
            let ckpt =
                provision_stateful_seed_burn_ledger(secret_out, setup.pk.pk_seed_bytes, &seed)?;
            secret.push(("ledger_checkpoint_gen", Json::num(ckpt.generation)));
            secret.push(("ledger_checkpoint_tag", Json::hex(&ckpt.tag)));
            secret.push(("seed", Json::hex(&seed[..])));
            secret.push(("parties", Json::num(parties)));
            public.push(("parties", Json::num(parties)));
            public.push((
                "epochs",
                Json::num(1u32 << params.tree_height),
            ));
            threshold_public_bytes(&setup.pk)
        }
        Scheme::AggCommittee => {
            let validators = args.get_u64("validators")?.unwrap_or(8);
            if !(1..=64).contains(&validators) {
                return Err(CliError::usage("--validators must be between 1 and 64"));
            }
            let wal_dir = args
                .get("wal-dir")
                .ok_or_else(|| CliError::usage("agg-jorts-poseidon2 requires --wal-dir"))?;
            crate::agg::enroll_committee(&seed, validators as u32, wal_dir)?;
            let keys: Vec<Json> = (0..validators as u32)
                .map(|i| Json::hex(&crate::agg::validator(&seed, i).pk.to_bytes()))
                .collect();
            secret.push(("seed", Json::hex(&seed[..])));
            secret.push(("validators", Json::num(validators)));
            let root = qsag_agg::compute_committee_root(&crate::agg::committee_from_json(&keys)?);
            public.push(("committee_root", Json::hex(&root)));
            public.push(("validators", Json::Array(keys)));
            Vec::new()
        }
    };
    if let Some(tag) = scheme.suite_tag() {
        let address = QsagAddress::from_pubkey_cshake256(
            hrp,
            tag,
            KeyIdentityKind::SingleOrThreshold,
            &public_key,
        )
        .and_then(|a| a.encode())
        .map_err(|e| CliError::usage(format!("address encoding failed: {e:?}")))?;
        public.push(("public_key", Json::hex(&public_key)));
        public.push(("address", Json::str(address)));
    }
    let public = Json::object(public);
    let mut secret = Json::object(secret);
    vault.set_key_material(&secret)?;
    if let Some(pass) = &passphrase { crate::envelope::seal(&mut secret, pass)?; }
    vault.bind(&mut secret)?;
    vault.prepare(&mut secret)?;
    let encoded = ZeroizingBuf(secret.to_pretty().into_bytes());
    if force && existing {
        crate::cli::replace_secret(public_out, public.to_pretty().as_bytes())?;
        vault.seal(&mut secret)?;
        crate::cli::replace_secret(secret_out, &encoded.0)?;
    } else {
        vault.seal(&mut secret)?;
        write_new(secret_out, &encoded.0, true)?;
        write_new(public_out, public.to_pretty().as_bytes(), false)?;
    }
    if args.flag("json") {
        print!("{}", public.to_pretty());
    } else {
        println!("wrote {secret_out} (secret) and {public_out} (public)");
    }
    Ok(())
}

const SIGN_HELP: &str = "\
qsag sign --secret <path> --in <file|-> --out <path> [options]

Sign a message file (or standard input with `-`). The signature file is created new.
Stateful schemes persist their advanced state before the signature is written.

  --ctx-hex <hex>     SLH-DSA context string, at most 255 bytes (default: empty)
  --epoch <n>         fts-threshold: the one-time epoch to spend (required for that scheme)
  --deterministic     use no fresh randomness: the same inputs give the same signature
  --passphrase-env <VAR> / --passphrase-file <PATH>  unlock sealed secret material
  --accept-trusted-dealer-demo  acknowledge local single-seed threshold demo custody
  --json              print the signature file contents to standard output as well
";

fn verify_slh_before_release(
    params: &Fips205Params,
    sk: &SlhSecretKey,
    message: &[u8],
    ctx: &[u8],
    candidate: &[u8],
    reference: &[u8],
) -> Result<(), CliError> {
    if !qsag_accel::ct::ct_eq_bytes(candidate, reference)
        || !slh_verify(params, message, candidate, ctx, &sk.public_key())
    {
        return Err(CliError::verify(
            "verify-before-release aborted faulted SLH-DSA signature",
        ));
    }
    Ok(())
}

fn verify_frontier_bytes_before_release(
    pk: &FrontierFtsPublicKey,
    dp: &FrontierDpTable,
    profile: FrontierFtsProfile,
    message: &[u8],
    bytes: &[u8],
) -> Result<(), CliError> {
    let parsed = FrontierFtsSignature::from_bytes(profile, bytes).map_err(|_| {
        CliError::verify("verify-before-release aborted malformed Frontier signature")
    })?;
    if verify_frontier_fts(pk, dp, message, &parsed).is_err() {
        return Err(CliError::verify(
            "verify-before-release aborted faulted Frontier signature",
        ));
    }
    Ok(())
}

fn verify_threshold_fts_bytes_before_release(
    pk: &ParallelSeededPublicKey,
    expected_epoch: u32,
    message: &[u8],
    bytes: &[u8],
) -> Result<(), CliError> {
    let parsed = ParallelSeededSignature::from_bytes_canonical(&pk.params, bytes).map_err(|_| {
        CliError::verify("verify-before-release aborted malformed threshold signature")
    })?;
    if parsed.epoch != expected_epoch
        || verify_parallel_seeded_fts(pk, message, &parsed, &CpuReferenceBackend).is_err()
    {
        return Err(CliError::verify(
            "verify-before-release aborted faulted threshold signature",
        ));
    }
    Ok(())
}

pub fn sign(raw: &[String]) -> Result<(), CliError> {
    sign_inner(raw, None)
}

fn sign_inner(raw: &[String], fault_byte: Option<(usize, u8)>) -> Result<(), CliError> {
    let args = Args::parse(
        raw,
        &["secret", "in", "out", "ctx-hex", "epoch", "passphrase-env", "passphrase-file"],
        &["deterministic", "json", "help", "accept-trusted-dealer-demo"],
    )?;
    if args.flag("help") {
        print!("{SIGN_HELP}");
        return Ok(());
    }
    args.no_positionals()?;
    let secret_path = args.require("secret")?;
    let out_path = args.require("out")?;
    let message = read_input(args.require("in")?)?;
    let mut vault = crate::vault::Vault::acquire(secret_path, false)?;
    let mut secret = load_json(secret_path, SECRET_FORMAT)?;
    let scheme = scheme_of(&secret)?;
    require_dealer_acceptance(scheme, &args)?;
    let passphrase = crate::envelope::passphrase(&args)?;
    let opened = crate::envelope::open(&secret, passphrase.as_deref())?;
    vault.set_key_material(&opened)?;
    vault.authenticate(&secret)?;
    let ctx = crate::codec::from_hex(args.get("ctx-hex").unwrap_or(""))?;
    if !matches!(scheme, Scheme::Slh(_)) && !ctx.is_empty() {
        return Err(CliError::usage("--ctx-hex applies only to SLH-DSA schemes"));
    }
    let fresh = if args.flag("deterministic") {
        None
    } else {
        Some(Secret32(os_random_32()?))
    };
    let mut extra: Vec<(&str, Json)> = Vec::new();

    let signature: Vec<u8> = match scheme {
        Scheme::Slh(params) => {
            let raw_key = opened.field_hex("secret_key")?;
            let sk = SlhSecretKey::from_bytes_for_params(&params, &raw_key.0)
                .map_err(|e| CliError::input(format!("secret key: {e}")))?;
            let hedged = fresh.as_ref().map(|entropy| {
                let mut out = Secret32([0u8; 32]);
                cshake256_framed_xof(
                    b"QSAG.CLI.SLH.HEDGE.V1",
                    &[
                        &entropy.0,
                        sk.sk_prf_slice(),
                        sk.pk_seed_slice(),
                        &ctx,
                        &message,
                    ],
                    &mut out.0,
                );
                out
            });
            let opt_rand = hedged.as_ref().map(|h| &h.0[..params.n]);
            let mut candidate = slh_sign(&params, &message, &ctx, &sk, opt_rand)
                .map_err(|e| CliError::usage(format!("signing failed: {e}")))?;
            if let Some((idx, mask)) = fault_byte
                && let Some(slot) = candidate.get_mut(idx)
            {
                *slot ^= mask;
            }
            let reference = slh_sign(&params, &message, &ctx, &sk, opt_rand)
                .map_err(|e| CliError::usage(format!("signing failed: {e}")))?;
            verify_slh_before_release(&params, &sk, &message, &ctx, &candidate, &reference)?;
            candidate
        }
        Scheme::Frontier(profile) => {
            let seed = from_hex_secret32(opened.field_str("seed")?, "seed")?;
            let used = u8::try_from(secret.field_u64("uses_completed")?)
                .map_err(|_| CliError::input("uses_completed out of range"))?;
            let exhausted =
                |e: FrontierFtsError| CliError::state(format!("key can not sign again: {e:?}"));
            let mut key = frontier_key(profile, &seed)
                .resume_at(used)
                .map_err(exhausted)?;
            if key.uses_remaining() == 0 {
                return Err(exhausted(FrontierFtsError::UseBudgetExhausted));
            }
            let mut hedged = Secret32([0u8; 32]);
            if let Some(entropy) = &fresh {
                cshake256_framed_xof(
                    b"QSAG.CLI.FRONTIER.HEDGE.V1",
                    &[&entropy.0, &seed.0, &[used], &message],
                    &mut hedged.0,
                );
            }
            let ceremony_id = cshake256_framed_32(
                b"QSAG.CLI.FRONTIER.CEREMONY.V1",
                &[&seed.0, &key.wal_key(), &[used], &hedged.0, &message],
            );
            let use_seed_id = cshake256_framed_32(
                b"QSAG.CLI.FRONTIER.USE_SEED.V1",
                &[&seed.0, &key.wal_key(), &[used]],
            );
            // Verify retained LedgerCheckpoint against durable_ledger, burn this use's seed,
            // and seal the new LedgerCheckpoint + advanced counter into the vault BEFORE signing.
            burn_stateful_ceremony_with_checkpoint(
                secret_path,
                &mut secret,
                key.wal_key(),
                &seed.0,
                ceremony_id,
                use_seed_id,
                || format!("key can not sign again: {:?}", FrontierFtsError::UseBudgetExhausted),
            )?;
            vault.reserve(secret_path, &mut secret)?;
            let wal = FsWalFtsEpochLatch::open(
                burn_journal_path(secret_path),
                key.wal_key(),
                derive(&seed, b"burn journal mac"),
            )
            .map_err(|e| CliError::io("recovering frontier use journal", e))?;
            key = key.attach_wal(Box::new(wal)).map_err(exhausted)?;
            let dp = FrontierDpTable::build(profile);
            let sig = key.sign(&dp, &message, &hedged.0).map_err(exhausted)?;
            extra.push(("uses_remaining", Json::num(key.uses_remaining())));
            let mut bytes = sig.to_bytes(profile);
            if let Some((idx, mask)) = fault_byte
                && let Some(slot) = bytes.get_mut(idx)
            {
                *slot ^= mask;
            }
            verify_frontier_bytes_before_release(&key.pk, &dp, profile, &message, &bytes)?;
            bytes
        }
        Scheme::ThresholdFts => {
            let seed = from_hex_secret32(opened.field_str("seed")?, "seed")?;
            let epoch = args
                .get_u64("epoch")?
                .ok_or_else(|| CliError::usage("fts-threshold requires --epoch"))?;
            let params = threshold_params(&secret)?;
            if epoch >> params.tree_height != 0 {
                return Err(CliError::usage(format!(
                    "--epoch must be below {}",
                    1u32 << params.tree_height
                )));
            }
            let mut setup = threshold_setup(&seed, secret.field_u64("parties")?, params)?;
            let mut journal = FsWalFtsEpochLatch::open(
                burn_journal_path(secret_path),
                setup.pk.pk_seed_bytes,
                derive(&seed, b"burn journal mac"),
            )
            .map_err(|e| CliError::state(format!("epoch burn journal unavailable: {e}")))?;
            let mut session = Secret32([0u8; 32]);
            match &fresh {
                Some(entropy) => cshake256_framed_xof(
                    b"QSAG.CLI.SESSION.HEDGE.V1",
                    &[&entropy.0, &seed.0, &epoch.to_be_bytes(), &message],
                    &mut session.0,
                ),
                None => {
                    session.0 = cshake256_framed_32(
                        b"QSAG.CLI.SESSION.V1",
                        &[&seed.0, &epoch.to_be_bytes(), &message],
                    );
                }
            }
            let ceremony_id = cshake256_framed_32(
                b"QSAG.CLI.THRESHOLD.CEREMONY.V1",
                &[
                    &seed.0,
                    &setup.pk.pk_seed_bytes,
                    &epoch.to_be_bytes(),
                    &session.0,
                    &message,
                ],
            );
            let epoch_seed_id = cshake256_framed_32(
                b"QSAG.CLI.THRESHOLD.EPOCH_SEED.V1",
                &[&seed.0, &setup.pk.pk_seed_bytes, &epoch.to_be_bytes()],
            );
            // Verify retained LedgerCheckpoint against durable_ledger, burn the epoch seed,
            // and seal the ratcheted LedgerCheckpoint into the vault BEFORE threshold signing.
            burn_stateful_ceremony_with_checkpoint(
                secret_path,
                &mut secret,
                setup.pk.pk_seed_bytes,
                &seed.0,
                ceremony_id,
                epoch_seed_id,
                || format!("epoch {epoch} was already spent"),
            )?;
            vault.reserve(secret_path, &mut secret)?;
            let sig = setup
                .threshold_sign(
                    epoch as u32,
                    &message,
                    session.0,
                    &mut journal,
                    &CpuReferenceBackend,
                )
                .map_err(|e| match e {
                    ParallelSeededError::PersistenceFailed
                    | ParallelSeededError::EpochUseBudgetExhausted => {
                        CliError::state(format!("epoch {epoch} was already spent"))
                    }
                    other => CliError::usage(format!("threshold signing failed: {other:?}")),
                })?;
            extra.push(("epoch", Json::num(epoch)));
            let mut bytes = sig.to_bytes();
            if let Some((idx, mask)) = fault_byte
                && let Some(slot) = bytes.get_mut(idx)
            {
                *slot ^= mask;
            }
            verify_threshold_fts_bytes_before_release(&setup.pk, epoch as u32, &message, &bytes)?;
            bytes
        }
        Scheme::AggCommittee => {
            return Err(CliError::usage(
                "committee keys sign through `qsag aggregate`",
            ));
        }
    };

    let mut members = vec![
        ("format", Json::str(SIGNATURE_FORMAT)),
        ("scheme", Json::str(scheme.name())),
    ];
    members.extend(extra);
    members.push(("signature_bytes", Json::num(signature.len())));
    members.push(("signature", Json::hex(&signature)));
    let file = Json::object(members);
    write_new(out_path, file.to_pretty().as_bytes(), false)?;
    if args.flag("json") {
        print!("{}", file.to_pretty());
    } else {
        println!("wrote {out_path} ({} signature bytes)", signature.len());
    }
    Ok(())
}

const VERIFY_HELP: &str = "\
qsag verify --public <path> --in <file|-> --sig <path> [options]

Verify a signature. Exit code 0 means valid; exit code 2 means invalid.

  --ctx-hex <hex>     SLH-DSA context string the signer used (default: empty)
  --json              print the verdict as JSON
";

pub fn verify(raw: &[String]) -> Result<(), CliError> {
    let args = Args::parse(raw, &["public", "in", "sig", "ctx-hex"], &["json", "help"])?;
    if args.flag("help") {
        print!("{VERIFY_HELP}");
        return Ok(());
    }
    args.no_positionals()?;
    let public = load_json(args.require("public")?, PUBLIC_FORMAT)?;
    let sig_file = load_json(args.require("sig")?, SIGNATURE_FORMAT)?;
    let message = read_input(args.require("in")?)?;
    let scheme = scheme_of(&public)?;
    if scheme_of(&sig_file)? != scheme {
        return Err(CliError::verify(
            "signature was made under a different scheme than the public key",
        ));
    }
    let ctx = crate::codec::from_hex(args.get("ctx-hex").unwrap_or(""))?;
    let signature = sig_file.field_hex("signature")?;

    let valid = match scheme {
        Scheme::Slh(params) => {
            let pk = SlhPublicKey::from_bytes_for_params(&params, &public.field_hex("public_key")?)
                .map_err(|e| CliError::input(format!("public key: {e}")))?;
            slh_verify(&params, &message, &signature, &ctx, &pk)
        }
        Scheme::Frontier(profile) => {
            let bytes = public.field_hex("public_key")?;
            if bytes.len() != 32 + profile.params().node_bytes {
                return Err(CliError::input(
                    "public key has the wrong length for its scheme",
                ));
            }
            let mut pk_seed = [0u8; 32];
            pk_seed.copy_from_slice(&bytes[..32]);
            let pk = FrontierFtsPublicKey {
                profile,
                pk_seed,
                root: bytes[32..].to_vec(),
            };
            FrontierFtsSignature::from_bytes(profile, &signature)
                .and_then(|sig| {
                    verify_frontier_fts(&pk, &FrontierDpTable::build(profile), &message, &sig)
                })
                .is_ok()
        }
        Scheme::ThresholdFts => {
            let bytes: [u8; 64] = from_hex_exact(public.field_str("public_key")?, "public key")?;
            let mut pk_seed_bytes = [0u8; 32];
            pk_seed_bytes.copy_from_slice(&bytes[..32]);
            let mut merkle_root = [0u64; 4];
            for (limb, raw) in merkle_root.iter_mut().zip(bytes[32..].as_chunks::<8>().0) {
                *limb = u64::from_le_bytes(*raw);
            }
            let pk = ParallelSeededPublicKey {
                params: threshold_params(&public)?,
                pk_seed_bytes,
                pk_seed_limbs: qsag_accel::poseidon2::poseidon2_hash_limbs(
                    0x5345_4544_3536_5633,
                    &qsag_accel::goldilocks::pack_bytes32_to_limbs56(&pk_seed_bytes),
                ),
                merkle_root,
            };
            ParallelSeededSignature::from_bytes_canonical(&pk.params, &signature)
                .and_then(|sig| {
                    verify_parallel_seeded_fts(&pk, &message, &sig, &CpuReferenceBackend)
                })
                .is_ok()
        }
        Scheme::AggCommittee => {
            return Err(CliError::usage(
                "aggregate proofs are verified with `qsag verify-agg`",
            ));
        }
    };
    if args.flag("json") {
        print!(
            "{}",
            Json::object(vec![
                ("scheme", Json::str(scheme.name())),
                ("valid", Json::Bool(valid))
            ])
            .to_pretty()
        );
    } else {
        println!(
            "{}",
            if valid {
                "signature valid"
            } else {
                "signature INVALID"
            }
        );
    }
    if valid {
        Ok(())
    } else {
        Err(CliError::verify("signature verification failed"))
    }
}

/// Public key bytes and scheme of a public key file, for the address subcommand.
pub fn public_key_of(path: &str) -> Result<(Scheme, Vec<u8>), CliError> {
    let public = load_json(path, PUBLIC_FORMAT)?;
    Ok((scheme_of(&public)?, public.field_hex("public_key")?.to_vec()))
}

#[cfg(test)]
mod vault_tests {
    use super::*;

    #[test]
    fn interrupted_reservation_fails_closed() {
        let dir = std::env::temp_dir().join(format!(
            "qsag-interrupted-vault-{}",
            crate::codec::to_hex(&os_random_32().unwrap())
        ));
        std::fs::create_dir(&dir).unwrap();
        let path = |s: &str| dir.join(s).to_str().unwrap().to_owned();
        keygen(&[
            "--scheme".into(),
            "fts-frontier-514".into(),
            "--secret-out".into(),
            path("sk"),
            "--public-out".into(),
            path("pk"),
        ])
        .unwrap();
        {
            let mut vault = crate::vault::Vault::acquire(&path("sk"), false).unwrap();
            let mut secret = load_json(&path("sk"), SECRET_FORMAT).unwrap();
            vault.authenticate(&secret).unwrap();
            crate::vault::set(&mut secret, "uses_completed", Json::num(1));
            // Simulate a crash after companion sync, before secret replacement.
            vault.seal(&mut secret).unwrap();
        }
        std::fs::write(path("msg"), b"must not sign").unwrap();
        let error = sign(&[
            "--secret".into(),
            path("sk"),
            "--in".into(),
            path("msg"),
            "--out".into(),
            path("sig"),
        ])
        .unwrap_err();
        assert_eq!(error.message, "CorruptOrMissingVaultState");
        assert!(!dir.join("sig").exists());
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn concurrent_threads_spend_frontier_once() {
        let dir = std::env::temp_dir().join(format!(
            "qsag-thread-vault-{}-{}",
            std::process::id(),
            crate::codec::to_hex(&os_random_32().unwrap())
        ));
        std::fs::create_dir(&dir).unwrap();
        let path = |s: &str| dir.join(s).to_str().unwrap().to_owned();
        std::fs::write(path("msg"), b"concurrent signing").unwrap();
        keygen(&[
            "--scheme".into(),
            "fts-frontier-514".into(),
            "--secret-out".into(),
            path("sk"),
            "--public-out".into(),
            path("pk"),
        ])
        .unwrap();
        let barrier = std::sync::Barrier::new(4);
        let mut outcomes = std::thread::scope(|scope| {
            let handles: Vec<_> = (0..4)
                .map(|i| {
                    let path = &path;
                    let barrier = &barrier;
                    scope.spawn(move || {
                        barrier.wait();
                        match sign(&[
                            "--secret".into(),
                            path("sk"),
                            "--in".into(),
                            path("msg"),
                            "--out".into(),
                            path(&format!("sig{i}")),
                        ]) {
                            Ok(()) => 0,
                            Err(e) => {
                                assert!(e.message.contains("UseBudgetExhausted"), "{e}");
                                e.code
                            }
                        }
                    })
                })
                .collect();
            handles
                .into_iter()
                .map(|h| h.join().unwrap())
                .collect::<Vec<_>>()
        });
        outcomes.sort();
        assert_eq!(outcomes, [0, 4, 4, 4]);
        std::fs::remove_dir_all(dir).unwrap();
    }
}

fn require_dealer_acceptance(scheme: Scheme, args: &Args) -> Result<(), CliError> {
    if matches!(scheme, Scheme::ThresholdFts) && !args.flag("accept-trusted-dealer-demo") {
        return Err(CliError::usage("fts-threshold requires --accept-trusted-dealer-demo: one local seed holds all shares; this is not distributed DKG custody"));
    }
    Ok(())
}
#[cfg(test)]
mod custody_tests {
    use super::*;
    #[test]
    fn sealed_frontier_roundtrip_preserves_ciphertext_on_reservation() {
        let dir = std::env::temp_dir().join(format!("qsag-sealed-{}", crate::codec::to_hex(&os_random_32().unwrap())));
        std::fs::create_dir(&dir).unwrap();
        let path = |name: &str| dir.join(name).to_str().unwrap().to_owned();
        std::fs::write(path("pass"), b"a test passphrase").unwrap();
        std::fs::write(path("msg"), b"sealed custody").unwrap();
        keygen(&["--scheme".into(), "fts-frontier-514".into(), "--secret-out".into(), path("sk"), "--public-out".into(), path("pk"), "--passphrase-file".into(), path("pass")]).unwrap();
        let before = load_json(&path("sk"), SECRET_FORMAT).unwrap();
        let command = ["--secret".into(), path("sk"), "--in".into(), path("msg"), "--out".into(), path("sig"), "--passphrase-file".into(), path("pass")];
        std::fs::write(path("pass"), b"wrong passphrase").unwrap();
        assert!(sign(&command).is_err());
        assert_eq!(load_json(&path("sk"), SECRET_FORMAT).unwrap().field_u64("uses_completed").unwrap(), 0);
        std::fs::write(path("pass"), b"a test passphrase").unwrap();
        sign(&command).unwrap();
        let after = load_json(&path("sk"), SECRET_FORMAT).unwrap();
        assert_eq!(before.field_str("seed").unwrap(), after.field_str("seed").unwrap());
        assert_eq!(after.field_u64("uses_completed").unwrap(), 1);
        verify(&["--public".into(), path("pk"), "--in".into(), path("msg"), "--sig".into(), path("sig")]).unwrap();
        std::fs::remove_dir_all(dir).unwrap();
    }
    #[test]
    fn public_replace_failure_preserves_old_secret_and_vault() {
        let dir = std::env::temp_dir().join(format!("qsag-overwrite-{}", crate::codec::to_hex(&os_random_32().unwrap())));
        std::fs::create_dir(&dir).unwrap();
        let path = |name: &str| dir.join(name).to_str().unwrap().to_owned();
        let mut args = vec!["--scheme".into(), "slh-dsa-shake-128s".into(), "--secret-out".into(), path("sk"), "--public-out".into(), path("pk")];
        keygen(&args).unwrap();
        let original = std::fs::read(path("sk")).unwrap();
        std::fs::remove_file(path("pk")).unwrap();
        std::fs::create_dir(path("pk")).unwrap();
        args.push("--force-overwrite".into());
        assert!(keygen(&args).is_err());
        assert_eq!(original, std::fs::read(path("sk")).unwrap());
        let mut vault = crate::vault::Vault::acquire(&path("sk"), false).unwrap();
        vault.authenticate(&load_json(&path("sk"), SECRET_FORMAT).unwrap()).unwrap();
        drop(vault);
        std::fs::remove_dir_all(dir).unwrap();
    }
    #[test]
    fn accepted_threshold_demo_signs_and_rejects_epoch_reuse() {
        let dir = std::env::temp_dir().join(format!("qsag-threshold-demo-{}", crate::codec::to_hex(&os_random_32().unwrap())));
        std::fs::create_dir(&dir).unwrap();
        let path = |name: &str| dir.join(name).to_str().unwrap().to_owned();
        std::fs::write(path("msg"), b"explicit demo").unwrap();
        keygen(&["--scheme".into(), "fts-threshold".into(), "--accept-trusted-dealer-demo".into(), "--fast-demo".into(), "--secret-out".into(), path("sk"), "--public-out".into(), path("pk")]).unwrap();
        let mut args = vec!["--secret".into(), path("sk"), "--in".into(), path("msg"), "--out".into(), path("sig"), "--epoch".into(), "5".into()];
        assert!(sign(&args).is_err());
        args.push("--accept-trusted-dealer-demo".into());
        sign(&args).unwrap();
        verify(&["--public".into(), path("pk"), "--in".into(), path("msg"), "--sig".into(), path("sig")]).unwrap();
        assert_eq!(sign(&args).unwrap_err().code, 4);
        std::fs::remove_dir_all(dir).unwrap();
    }
    #[test]
    fn threshold_requires_explicit_acceptance() {
        let args = Args::parse(&[], &[], &["accept-trusted-dealer-demo"]).unwrap();
        assert!(require_dealer_acceptance(Scheme::ThresholdFts, &args).is_err());
        let args = Args::parse(&["--accept-trusted-dealer-demo".into()], &[], &["accept-trusted-dealer-demo"]).unwrap();
        assert!(require_dealer_acceptance(Scheme::ThresholdFts, &args).is_ok());
    }

    #[test]
    fn verify_before_release_blocks_bitflips_and_consistent_grafts_across_all_schemes() {
        let dir = std::env::temp_dir().join(format!(
            "qsag-vbr-{}",
            crate::codec::to_hex(&os_random_32().unwrap())
        ));
        std::fs::create_dir(&dir).unwrap();
        let path = |name: &str| dir.join(name).to_str().unwrap().to_owned();
        std::fs::write(path("msg"), b"castelnovi-martinelli-prest guard").unwrap();

        // 1. SLH-DSA: blocks both signature bit-flips and self-consistent randomizer/subtree grafts.
        keygen(&[
            "--scheme".into(),
            "slh-dsa-shake-128f".into(),
            "--secret-out".into(),
            path("slh.sk"),
            "--public-out".into(),
            path("slh.pk"),
        ])
        .unwrap();
        let slh_err = sign_inner(
            &[
                "--secret".into(),
                path("slh.sk"),
                "--in".into(),
                path("msg"),
                "--out".into(),
                path("slh.sig"),
            ],
            Some((64, 0x01)),
        )
        .unwrap_err();
        assert_eq!(slh_err.code, 2);
        assert!(!dir.join("slh.sig").exists());

        let slh_secret = load_json(&path("slh.sk"), SECRET_FORMAT).unwrap();
        let params = match Scheme::by_name("slh-dsa-shake-128f").unwrap() {
            Scheme::Slh(p) => p,
            _ => unreachable!(),
        };
        let sk = SlhSecretKey::from_bytes_for_params(
            &params,
            &slh_secret.field_hex("secret_key").unwrap().0,
        )
        .unwrap();
        let ref_sig = slh_sign(&params, b"msg", b"", &sk, Some(&[0x11; 16])).unwrap();
        let grafted_valid_sig = slh_sign(&params, b"msg", b"", &sk, Some(&[0x22; 16])).unwrap();
        assert!(slh_verify(
            &params,
            b"msg",
            &grafted_valid_sig,
            b"",
            &sk.public_key()
        ));
        assert!(
            verify_slh_before_release(&params, &sk, b"msg", b"", &grafted_valid_sig, &ref_sig)
                .is_err()
        );

        // 2. Frontier FTS: faulted signature never touches disk, while the use slot stays burned.
        keygen(&[
            "--scheme".into(),
            "fts-frontier-514".into(),
            "--secret-out".into(),
            path("fr.sk"),
            "--public-out".into(),
            path("fr.pk"),
        ])
        .unwrap();
        let fr_err = sign_inner(
            &[
                "--secret".into(),
                path("fr.sk"),
                "--in".into(),
                path("msg"),
                "--out".into(),
                path("fr.sig"),
            ],
            Some((24, 0x04)),
        )
        .unwrap_err();
        assert_eq!(fr_err.code, 2);
        assert!(!dir.join("fr.sig").exists());
        assert_eq!(
            load_json(&path("fr.sk"), SECRET_FORMAT)
                .unwrap()
                .field_u64("uses_completed")
                .unwrap(),
            1
        );

        // 3. Threshold FTS: faulted signature never touches disk, while the epoch stays burned.
        keygen(&[
            "--scheme".into(),
            "fts-threshold".into(),
            "--accept-trusted-dealer-demo".into(),
            "--fast-demo".into(),
            "--secret-out".into(),
            path("th.sk"),
            "--public-out".into(),
            path("th.pk"),
        ])
        .unwrap();
        let th_args = [
            "--secret".into(),
            path("th.sk"),
            "--in".into(),
            path("msg"),
            "--out".into(),
            path("th.sig"),
            "--epoch".into(),
            "2".into(),
            "--accept-trusted-dealer-demo".into(),
        ];
        let th_err = sign_inner(&th_args, Some((40, 0x80))).unwrap_err();
        assert_eq!(th_err.code, 2);
        assert!(!dir.join("th.sig").exists());
        assert_eq!(sign(&th_args).unwrap_err().code, 4);

        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn cli_retains_ledger_checkpoint_and_rejects_durable_ledger_slot_rollback() {
        let dir = std::env::temp_dir().join(format!(
            "qsag-cli-ckpt-rollback-{}",
            crate::codec::to_hex(&os_random_32().unwrap())
        ));
        std::fs::create_dir(&dir).unwrap();
        let path = |name: &str| dir.join(name).to_str().unwrap().to_owned();
        std::fs::write(path("msg"), b"ledger checkpoint anti-rollback").unwrap();

        keygen(&[
            "--scheme".into(),
            "fts-threshold".into(),
            "--accept-trusted-dealer-demo".into(),
            "--fast-demo".into(),
            "--secret-out".into(),
            path("th.sk"),
            "--public-out".into(),
            path("th.pk"),
        ])
        .unwrap();

        let genesis_secret = load_json(&path("th.sk"), SECRET_FORMAT).unwrap();
        assert_eq!(
            genesis_secret.field_u64("ledger_checkpoint_gen").unwrap(),
            0
        );
        let slot_a_gen0 = std::fs::read(path("th.sk.seedburn.slot_a")).unwrap();
        let slot_b_gen0 = std::fs::read(path("th.sk.seedburn.slot_b")).unwrap();

        // Spend epoch 1: ratchets `ledger_checkpoint_gen` to 1 inside `th.sk` + `th.sk.vault.lock`.
        sign(&[
            "--secret".into(),
            path("th.sk"),
            "--in".into(),
            path("msg"),
            "--out".into(),
            path("sig1"),
            "--epoch".into(),
            "1",
            "--accept-trusted-dealer-demo".into(),
        ])
        .unwrap();
        let after_one = load_json(&path("th.sk"), SECRET_FORMAT).unwrap();
        assert_eq!(after_one.field_u64("ledger_checkpoint_gen").unwrap(), 1);

        // Adversarial rollback: overwrite both `.slot_a` and `.slot_b` of `th.sk.seedburn`
        // with the pre-spend generation-0 snapshots while the vault retains generation 1.
        std::fs::write(path("th.sk.seedburn.slot_a"), &slot_a_gen0).unwrap();
        std::fs::write(path("th.sk.seedburn.slot_b"), &slot_b_gen0).unwrap();

        // Attempting to sign (even at a fresh epoch 2!) MUST fail closed on checkpoint mismatch!
        let rollback_err = sign(&[
            "--secret".into(),
            path("th.sk"),
            "--in".into(),
            path("msg"),
            "--out".into(),
            path("sig2"),
            "--epoch".into(),
            "2",
            "--accept-trusted-dealer-demo".into(),
        ])
        .unwrap_err();
        assert_eq!(rollback_err.code, 4);
        assert!(
            rollback_err
                .message
                .contains("CorruptOrRolledBackLedgerCheckpoint"),
            "{rollback_err}"
        );
        assert!(!dir.join("sig2").exists());

        std::fs::remove_dir_all(dir).unwrap();
    }
}
