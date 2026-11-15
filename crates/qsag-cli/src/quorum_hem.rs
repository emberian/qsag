//! Dynamic `(t, n)` Shamir quorum-switching CLI ceremonies (`--scheme hem-jorts-poseidon2`)
//! backed by [`qsag_quorum::hem_quorum::HemDynamicShamirQuorum`].
//!
//! Produces canonical 65-byte [`qsag_agg::ValidatorPublicKey`]s and 4,328-byte
//! [`qsag_agg::ValidatorSignature`]s accepted directly by untrusted public `qsag aggregate`
//! and `qsag verify-aggregate` (`BciksJohnsonQrom128`), while supporting proactive share
//! refresh (`qsag quorum refresh`) and `(t, n) -> (t', n')` roster/threshold switching
//! (`qsag quorum reshare`) without changing the validator public key.

use std::path::Path;

use qsag_accel::keccak::cshake256_framed_32;
use qsag_agg::{
    AggSigProfile, ValidatorPublicKey, ValidatorSignature, verify_individual_signature,
};
use qsag_quorum::hem_quorum::{
    HEM_JORTS_MAX_LEAVES, HEM_JORTS_PK_BYTES, HEM_JORTS_SIG_BYTES, HemDynamicShamirQuorum,
    HemJortsPublicKey, HemJortsSignature, HemQuorumError, HemQuorumPublicDirectory,
    HemShamirCustodianShare, verify_hem_jorts_signature,
};

use crate::cli::{
    Args, CliError, MAX_KEY_FILE_BYTES, MAX_SIG_PROOF_BYTES, Secret32, ZeroizingBuf, os_random_32,
    private_dir, read_bounded_file, read_input, read_text, replace_secret, write_new,
};
use crate::codec::{Json, from_hex_exact};
use crate::quorum::PUBLIC_FORMAT;

pub const HEM_SCHEME_NAME: &str = "hem-jorts-poseidon2";
const HEM_META_FORMAT: &str = "qsag-hem-quorum-meta-v1";
const SIG_FORMAT: &str = "qsag-quorum-signature-v1";

pub const HEM_REFRESH_HELP: &str = "\
qsag quorum refresh --vault-dir <dir> [--deterministic] [--json]

Execute proactive share refresh (Π_refresh) across all (t, n) custodians in --vault-dir,
advancing quorum_epoch and overwriting custodian share files in place while preserving
the exact 65-byte validator public key and monotone leaf high-water mark.
";

pub const HEM_RESHARE_HELP: &str = "\
qsag quorum reshare --vault-dir <old_dir> [--signers <i,j,..>] --new-threshold <t'> --new-parties <n'> --out-vault-dir <new_dir> [--public-out <path>] [--deterministic] [--json]

Execute dynamic (t, n) -> (t', n') quorum-switching (Π_reshare) using >= t custodians from
--vault-dir, writing the new (t', n') custodian vault into --out-vault-dir WITHOUT changing
the 65-byte validator public key, and permanently invalidating/wiping the retired vault.
";

fn meta_path(vault_dir: &str) -> String {
    Path::new(vault_dir)
        .join("quorum-meta.json")
        .to_string_lossy()
        .into_owned()
}

fn directory_path(vault_dir: &str) -> String {
    Path::new(vault_dir)
        .join("directory.bin")
        .to_string_lossy()
        .into_owned()
}

fn share_path(vault_dir: &str, party: usize) -> String {
    Path::new(vault_dir)
        .join(format!("custodian-{party}.share"))
        .to_string_lossy()
        .into_owned()
}

pub fn is_hem_vault(vault_dir: &str) -> bool {
    Path::new(&meta_path(vault_dir)).exists()
}

fn ensure_absent(path: &str) -> Result<(), CliError> {
    match std::fs::symlink_metadata(path) {
        Ok(_) => Err(CliError::usage(format!("{path} already exists"))),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(e) => Err(CliError::io(format_args!("inspecting {path}"), e)),
    }
}

fn parse_party_list(spec: &str, flag_name: &str, n: usize) -> Result<Vec<usize>, CliError> {
    let mut out = Vec::new();
    for part in spec.split(',') {
        let trimmed = part.trim();
        if trimmed.is_empty() {
            continue;
        }
        let idx: usize = trimmed
            .parse()
            .map_err(|_| CliError::usage(format!("--{flag_name} must be comma-separated indices")))?;
        if idx >= n {
            return Err(CliError::usage(format!(
                "--{flag_name} index {idx} out of range (parties = {n})"
            )));
        }
        if out.contains(&idx) {
            return Err(CliError::usage(format!(
                "duplicate party index {idx} in --{flag_name}"
            )));
        }
        out.push(idx);
    }
    if out.is_empty() {
        return Err(CliError::usage(format!("--{flag_name} must not be empty")));
    }
    Ok(out)
}

fn map_quorum_err(err: HemQuorumError) -> CliError {
    match err {
        HemQuorumError::InvalidQuorum { t, n } => {
            CliError::usage(format!("invalid quorum parameters (t={t}, n={n})"))
        }
        HemQuorumError::InvalidActiveLeaves { active_leaves } => {
            CliError::usage(format!("invalid active leaves ({active_leaves})"))
        }
        HemQuorumError::PartyOutOfRange { party, n } => {
            CliError::usage(format!("party {party} out of range for n={n}"))
        }
        HemQuorumError::DuplicateParty { party } => {
            CliError::usage(format!("duplicate party {party}"))
        }
        HemQuorumError::NotEnoughSigners { have, need } => {
            CliError::state(format!("NotEnoughSigners: have {have}, need {need}"))
        }
        HemQuorumError::ShareInvalidated { party } => {
            CliError::state(format!("ShareInvalidated: party {party} was retired"))
        }
        HemQuorumError::QuorumEpochMismatch {
            expected,
            got,
            party,
        } => CliError::state(format!(
            "QuorumEpochMismatch on party {party}: expected {expected}, got {got}"
        )),
        HemQuorumError::LeafExhausted | HemQuorumError::LatchRefused => {
            CliError::state(format!("quorum monotone leaf latch refused: {err}"))
        }
        other => CliError::verify(format!("quorum verification error: {other}")),
    }
}

fn write_public_json(
    pk: &HemJortsPublicKey,
    t: usize,
    n: usize,
    quorum_epoch: u64,
    active_leaves: usize,
) -> Json {
    let pk_bytes = pk.to_bytes();
    Json::object(vec![
        ("format", Json::str(PUBLIC_FORMAT)),
        ("scheme", Json::str(HEM_SCHEME_NAME)),
        (
            "custody_model",
            Json::str("dynamic-shamir-hem-jorts-poseidon2"),
        ),
        ("threshold", Json::num(t)),
        ("parties", Json::num(n)),
        ("quorum_epoch", Json::num(quorum_epoch)),
        ("active_leaves", Json::num(active_leaves)),
        ("public_key_bytes", Json::num(HEM_JORTS_PK_BYTES)),
        ("validator_public_key", Json::hex(&pk_bytes)),
    ])
}

fn write_vault_state(
    vault_dir: &str,
    quorum: &HemDynamicShamirQuorum,
    latch_seed: &[u8; 32],
    create_fresh: bool,
) -> Result<(), CliError> {
    let (t, n) = quorum.threshold_and_size();
    let pk_bytes = quorum.public_key().to_bytes();
    let dir_bytes = quorum.public_directory().to_bytes();
    let dir_digest = cshake256_framed_32(b"QSAG.CLI.HEM.DIR_DIGEST.V1", &[&dir_bytes]);

    let meta = Json::object(vec![
        ("format", Json::str(HEM_META_FORMAT)),
        ("scheme", Json::str(HEM_SCHEME_NAME)),
        ("threshold", Json::num(t)),
        ("parties", Json::num(n)),
        ("quorum_epoch", Json::num(quorum.quorum_epoch())),
        ("high_water_leaf", Json::num(quorum.high_water_leaf())),
        (
            "active_leaves",
            Json::num(quorum.public_directory().active_leaves),
        ),
        ("invalidated", Json::Bool(false)),
        ("validator_public_key", Json::hex(&pk_bytes)),
        ("directory_digest", Json::hex(&dir_digest)),
        ("latch_seed", Json::hex(latch_seed)),
    ]);

    if create_fresh {
        private_dir(vault_dir, true)?;
        let mp = meta_path(vault_dir);
        let dp = directory_path(vault_dir);
        ensure_absent(&mp)?;
        ensure_absent(&dp)?;
        for p in 0..n {
            ensure_absent(&share_path(vault_dir, p))?;
        }
        write_new(&dp, &dir_bytes, false)?;
        for (p, sh) in quorum.custodian_shares().iter().enumerate() {
            let raw = ZeroizingBuf(sh.to_vault_bytes().map_err(map_quorum_err)?);
            write_new(&share_path(vault_dir, p), &raw.0, true)?;
        }
        write_new(&mp, meta.to_pretty().as_bytes(), true)?;
    } else {
        private_dir(vault_dir, false)?;
        for (p, sh) in quorum.custodian_shares().iter().enumerate() {
            let raw = ZeroizingBuf(sh.to_vault_bytes().map_err(map_quorum_err)?);
            replace_secret(&share_path(vault_dir, p), &raw.0)?;
        }
        replace_secret(&meta_path(vault_dir), meta.to_pretty().as_bytes())?;
    }
    Ok(())
}

fn load_vault_state(vault_dir: &str) -> Result<(HemDynamicShamirQuorum, Secret32), CliError> {
    private_dir(vault_dir, false)?;
    let mp = meta_path(vault_dir);
    let meta_text = read_text(&mp)?;
    let meta = Json::parse(&meta_text)?;
    if meta.field_str("format")? != HEM_META_FORMAT || meta.field_str("scheme")? != HEM_SCHEME_NAME
    {
        return Err(CliError::state("CorruptHemQuorumMeta"));
    }
    if meta
        .get("invalidated")
        .and_then(Json::as_bool)
        .unwrap_or(false)
    {
        return Err(CliError::state(
            "ShareInvalidated: this quorum vault was retired by a dynamic reshare",
        ));
    }
    let t = meta.field_u64("threshold")? as usize;
    let n = meta.field_u64("parties")? as usize;
    let expected_qe = meta.field_u64("quorum_epoch")?;
    let expected_hw = meta.field_u64("high_water_leaf")? as usize;
    let expected_pk: [u8; HEM_JORTS_PK_BYTES] = from_hex_exact(
        meta.field_str("validator_public_key")?,
        "validator_public_key",
    )?;
    let expected_dir_digest: [u8; 32] =
        from_hex_exact(meta.field_str("directory_digest")?, "directory_digest")?;
    let latch_seed = Secret32(from_hex_exact(meta.field_str("latch_seed")?, "latch_seed")?);

    let dir_raw = read_bounded_file(&directory_path(vault_dir), 16 * 1024 * 1024)?;
    let actual_dir_digest = cshake256_framed_32(b"QSAG.CLI.HEM.DIR_DIGEST.V1", &[&dir_raw.0]);
    if !qsag_accel::ct::ct_eq_bytes(&actual_dir_digest, &expected_dir_digest) {
        return Err(CliError::state("HemQuorumDirectoryDigestMismatch"));
    }
    let public_dir =
        HemQuorumPublicDirectory::from_bytes_canonical(&dir_raw.0).map_err(map_quorum_err)?;
    if public_dir.pk.to_bytes() != expected_pk {
        return Err(CliError::state("HemQuorumPublicKeyMismatch"));
    }

    let mut shares = Vec::with_capacity(n);
    for p in 0..n {
        let raw = read_bounded_file(&share_path(vault_dir, p), 16 * 1024 * 1024)?;
        let sh = HemShamirCustodianShare::from_vault_bytes(&raw.0).map_err(map_quorum_err)?;
        shares.push(sh);
    }

    let quorum = HemDynamicShamirQuorum::from_persisted_shares(public_dir, shares, latch_seed.0)
        .map_err(map_quorum_err)?;
    if quorum.quorum_epoch() != expected_qe
        || quorum.high_water_leaf() != expected_hw
        || quorum.threshold_and_size() != (t, n)
    {
        return Err(CliError::state("HemQuorumHeaderStateMismatch"));
    }
    Ok((quorum, latch_seed))
}

fn retire_and_wipe_vault_on_disk(vault_dir: &str) -> Result<(), CliError> {
    let mp = meta_path(vault_dir);
    let meta_text = read_text(&mp)?;
    let meta = Json::parse(&meta_text)?;
    let n = meta.field_u64("parties")? as usize;
    for p in 0..n {
        let sp = share_path(vault_dir, p);
        if let Ok(md) = std::fs::symlink_metadata(&sp) {
            let zeros = vec![0u8; md.len() as usize];
            replace_secret(&sp, &zeros)?;
        }
    }
    let retired = Json::object(vec![
        ("format", Json::str(HEM_META_FORMAT)),
        ("scheme", Json::str(HEM_SCHEME_NAME)),
        ("threshold", Json::num(meta.field_u64("threshold")?)),
        ("parties", Json::num(n)),
        ("quorum_epoch", Json::num(meta.field_u64("quorum_epoch")?)),
        (
            "high_water_leaf",
            Json::num(meta.field_u64("high_water_leaf")?),
        ),
        ("active_leaves", Json::num(meta.field_u64("active_leaves")?)),
        ("invalidated", Json::Bool(true)),
        (
            "validator_public_key",
            Json::str(meta.field_str("validator_public_key")?),
        ),
        (
            "directory_digest",
            Json::str(meta.field_str("directory_digest")?),
        ),
        ("latch_seed", Json::hex(&[0u8; 32])),
    ]);
    replace_secret(&mp, retired.to_pretty().as_bytes())
}

pub fn keygen(args: &Args) -> Result<(), CliError> {
    let vault_dir = args.require("vault-dir")?;
    let public_out = args.require("public-out")?;
    ensure_absent(public_out)?;

    let t = args.get_u64("threshold")?.unwrap_or(2) as usize;
    let n = args.get_u64("parties")?.unwrap_or(3) as usize;
    let active_leaves = args.get_u64("leaves")?.unwrap_or(8) as usize;
    if t < 2 || t > n || n > 64 {
        return Err(CliError::usage(
            "--threshold must be >= 2 and <= --parties (<= 64)",
        ));
    }
    if active_leaves == 0 || active_leaves > HEM_JORTS_MAX_LEAVES {
        return Err(CliError::usage(format!(
            "--leaves must be between 1 and {HEM_JORTS_MAX_LEAVES}"
        )));
    }

    let ceremony_seed = if let Some(seed_file) = args.get("seed-file") {
        let raw = read_bounded_file(seed_file, MAX_KEY_FILE_BYTES)?;
        if raw.0.len() < 32 {
            return Err(CliError::usage("--seed-file must hold at least 32 bytes"));
        }
        Secret32(cshake256_framed_32(
            b"QSAG.CLI.HEM.QUORUM.SEED_FILE.V1",
            &[&raw.0],
        ))
    } else {
        Secret32(os_random_32()?)
    };
    let latch_seed = Secret32(cshake256_framed_32(
        b"QSAG.CLI.HEM.QUORUM.LATCH_SEED.V1",
        &[&ceremony_seed.0],
    ));

    let quorum = HemDynamicShamirQuorum::stage(ceremony_seed.0, t, n, active_leaves)
        .map_err(map_quorum_err)?;
    write_vault_state(vault_dir, &quorum, &latch_seed.0, true)?;

    let public = write_public_json(&quorum.public_key(), t, n, 0, active_leaves);
    write_new(public_out, public.to_pretty().as_bytes(), false)?;

    if args.flag("json") {
        print!("{}", public.to_pretty());
    } else {
        println!(
            "enrolled ({t}, {n}) {HEM_SCHEME_NAME} quorum ({active_leaves} leaves) in {vault_dir} -> {public_out}"
        );
    }
    Ok(())
}

pub fn sign(args: &Args) -> Result<(), CliError> {
    let vault_dir = args.require("vault-dir")?;
    let out_path = args.require("out")?;
    ensure_absent(out_path)?;
    if args.get("in").is_some() && args.get("message").is_some() {
        return Err(CliError::usage("pass either --message or --in, not both"));
    }
    let msg_arg = args
        .get("message")
        .or_else(|| args.get("in"))
        .ok_or_else(|| CliError::usage("missing required option --message (or --in)"))?;
    let message = read_input(msg_arg)?;

    let (mut quorum, latch_seed) = load_vault_state(vault_dir)?;
    let (t, n) = quorum.threshold_and_size();

    let signers = match args.get("signers") {
        Some(s) => parse_party_list(s, "signers", n)?,
        None => (0..t).collect(),
    };
    let ackers = match args.get("ackers") {
        Some(a) => parse_party_list(a, "ackers", n)?,
        None => (0..n).collect(),
    };
    if let Some(req_epoch) = args.get_u64("epoch")?
        && req_epoch != quorum.high_water_leaf() as u64
    {
        return Err(CliError::state(format!(
            "requested --epoch {req_epoch} does not match monotone high-water leaf {}",
            quorum.high_water_leaf()
        )));
    }

    let (leaf_epoch, sig) = quorum
        .sign_quorum(&signers, &ackers, &message)
        .map_err(map_quorum_err)?;

    // Persist burned leaf high-water mark to all custodian shares BEFORE releasing signature
    write_vault_state(vault_dir, &quorum, &latch_seed.0, false)?;

    let pk = quorum.public_key();
    let pk_bytes = pk.to_bytes();
    let sig_bytes = sig.to_bytes();
    let agg_pk = ValidatorPublicKey::from_bytes_canonical(&pk_bytes)
        .ok_or_else(|| CliError::verify("quorum public key failed canonical Hem decode"))?;
    let agg_sig =
        ValidatorSignature::from_bytes_canonical(AggSigProfile::JortsPoseidon2, &sig_bytes)
            .ok_or_else(|| CliError::verify("quorum signature failed canonical Hem decode"))?;
    if !verify_hem_jorts_signature(&pk, &message, &sig)
        || !verify_individual_signature(&agg_pk, &message, &agg_sig)
    {
        return Err(CliError::verify(
            "verify-before-release rejected Hem quorum signature",
        ));
    }

    let sig_json = Json::object(vec![
        ("format", Json::str(SIG_FORMAT)),
        ("scheme", Json::str(HEM_SCHEME_NAME)),
        ("epoch", Json::num(leaf_epoch)),
        ("quorum_epoch", Json::num(quorum.quorum_epoch())),
        ("threshold", Json::num(t)),
        ("parties", Json::num(n)),
        ("validator_public_key", Json::hex(&pk_bytes)),
        ("signature_bytes", Json::num(HEM_JORTS_SIG_BYTES)),
        ("signature", Json::hex(&sig_bytes)),
    ]);
    write_new(out_path, sig_json.to_pretty().as_bytes(), false)?;

    if args.flag("json") {
        let report = Json::object(vec![
            ("scheme", Json::str(HEM_SCHEME_NAME)),
            ("epoch", Json::num(leaf_epoch)),
            ("quorum_epoch", Json::num(quorum.quorum_epoch())),
            ("signature_bytes", Json::num(HEM_JORTS_SIG_BYTES)),
            ("out", Json::str(out_path)),
        ]);
        print!("{}", report.to_pretty());
    } else {
        println!(
            "signed {HEM_SCHEME_NAME} leaf epoch {leaf_epoch} (quorum_epoch {}, {} bytes) -> {out_path}",
            quorum.quorum_epoch(),
            HEM_JORTS_SIG_BYTES
        );
    }
    Ok(())
}

pub fn refresh(raw: &[String]) -> Result<(), CliError> {
    let args = Args::parse(raw, &["vault-dir"], &["deterministic", "json", "help"])?;
    if args.flag("help") {
        print!("{HEM_REFRESH_HELP}");
        return Ok(());
    }
    args.no_positionals()?;
    let vault_dir = args.require("vault-dir")?;
    let (mut quorum, latch_seed) = load_vault_state(vault_dir)?;
    let pk_before = quorum.public_key();
    let sid = if args.flag("deterministic") {
        cshake256_framed_32(
            b"QSAG.CLI.HEM.REFRESH.DET.V1",
            &[
                &pk_before.to_bytes(),
                &quorum.quorum_epoch().to_le_bytes(),
                &latch_seed.0,
            ],
        )
    } else {
        os_random_32()?
    };

    quorum.proactive_refresh(sid).map_err(map_quorum_err)?;
    if quorum.public_key() != pk_before {
        return Err(CliError::verify("proactive refresh mutated validator pubkey"));
    }
    write_vault_state(vault_dir, &quorum, &latch_seed.0, false)?;

    let (t, n) = quorum.threshold_and_size();
    if args.flag("json") {
        let report = Json::object(vec![
            ("scheme", Json::str(HEM_SCHEME_NAME)),
            ("threshold", Json::num(t)),
            ("parties", Json::num(n)),
            ("quorum_epoch", Json::num(quorum.quorum_epoch())),
            ("high_water_leaf", Json::num(quorum.high_water_leaf())),
            ("validator_public_key", Json::hex(&pk_before.to_bytes())),
        ]);
        print!("{}", report.to_pretty());
    } else {
        println!(
            "refreshed ({t}, {n}) {HEM_SCHEME_NAME} shares in {vault_dir} -> quorum_epoch {}",
            quorum.quorum_epoch()
        );
    }
    Ok(())
}

pub fn reshare(raw: &[String]) -> Result<(), CliError> {
    let args = Args::parse(
        raw,
        &[
            "vault-dir",
            "signers",
            "new-threshold",
            "new-parties",
            "out-vault-dir",
            "public-out",
        ],
        &["deterministic", "json", "help"],
    )?;
    if args.flag("help") {
        print!("{HEM_RESHARE_HELP}");
        return Ok(());
    }
    args.no_positionals()?;
    let old_vault_dir = args.require("vault-dir")?;
    let new_vault_dir = args.require("out-vault-dir")?;
    let new_t = args
        .get_u64("new-threshold")?
        .ok_or_else(|| CliError::usage("missing required option --new-threshold"))?
        as usize;
    let new_n = args
        .get_u64("new-parties")?
        .ok_or_else(|| CliError::usage("missing required option --new-parties"))?
        as usize;
    if let Some(pub_out) = args.get("public-out") {
        ensure_absent(pub_out)?;
    }

    let (mut quorum, old_latch_seed) = load_vault_state(old_vault_dir)?;
    let (old_t, old_n) = quorum.threshold_and_size();
    let old_signers = match args.get("signers") {
        Some(s) => parse_party_list(s, "signers", old_n)?,
        None => (0..old_t).collect(),
    };
    let pk_before = quorum.public_key();
    let sid = if args.flag("deterministic") {
        cshake256_framed_32(
            b"QSAG.CLI.HEM.RESHARE.DET.V1",
            &[
                &pk_before.to_bytes(),
                &quorum.quorum_epoch().to_le_bytes(),
                &(new_t as u64).to_le_bytes(),
                &(new_n as u64).to_le_bytes(),
                &old_latch_seed.0,
            ],
        )
    } else {
        os_random_32()?
    };
    let new_latch_seed = Secret32(cshake256_framed_32(
        b"QSAG.CLI.HEM.RESHARE.NEW_LATCH.V1",
        &[&old_latch_seed.0, &sid],
    ));

    quorum
        .reshare_quorum(sid, &old_signers, new_t, new_n)
        .map_err(map_quorum_err)?;
    if quorum.public_key() != pk_before {
        return Err(CliError::verify(
            "dynamic reshare mutated validator public key",
        ));
    }

    // Write the new `(new_t, new_n)` vault first, then wipe & retire the old `(old_t, old_n)` vault!
    write_vault_state(new_vault_dir, &quorum, &new_latch_seed.0, true)?;
    retire_and_wipe_vault_on_disk(old_vault_dir)?;

    if let Some(pub_out) = args.get("public-out") {
        let public = write_public_json(
            &pk_before,
            new_t,
            new_n,
            quorum.quorum_epoch(),
            quorum.public_directory().active_leaves,
        );
        write_new(pub_out, public.to_pretty().as_bytes(), false)?;
    }

    if args.flag("json") {
        let report = Json::object(vec![
            ("scheme", Json::str(HEM_SCHEME_NAME)),
            ("old_threshold", Json::num(old_t)),
            ("old_parties", Json::num(old_n)),
            ("new_threshold", Json::num(new_t)),
            ("new_parties", Json::num(new_n)),
            ("quorum_epoch", Json::num(quorum.quorum_epoch())),
            ("high_water_leaf", Json::num(quorum.high_water_leaf())),
            ("validator_public_key", Json::hex(&pk_before.to_bytes())),
            ("out_vault_dir", Json::str(new_vault_dir)),
        ]);
        print!("{}", report.to_pretty());
    } else {
        println!(
            "reshared ({old_t}, {old_n}) -> ({new_t}, {new_n}) {HEM_SCHEME_NAME} (quorum_epoch {}, pubkey preserved) -> {new_vault_dir}",
            quorum.quorum_epoch()
        );
    }
    Ok(())
}

pub fn verify(pub_json: &Json, message: &[u8], sig_path: &str, json_flag: bool) -> Result<(), CliError> {
    let pk_bytes: [u8; HEM_JORTS_PK_BYTES] = from_hex_exact(
        pub_json.field_str("validator_public_key")?,
        "validator_public_key",
    )?;
    let pk = HemJortsPublicKey::from_bytes_canonical(&pk_bytes)
        .ok_or_else(|| CliError::input("non-canonical Hem quorum public key"))?;

    let sig_raw = read_bounded_file(sig_path, MAX_SIG_PROOF_BYTES)?;
    let sig_str = std::str::from_utf8(&sig_raw.0)
        .map_err(|_| CliError::input(format!("{sig_path} is not UTF-8 text")))?;
    let sig_json = Json::parse(sig_str)?;
    if sig_json.field_str("format")? != SIG_FORMAT
        || sig_json.field_str("scheme")? != HEM_SCHEME_NAME
    {
        return Err(CliError::input("unexpected Hem quorum signature format"));
    }
    let sig_bytes = sig_json.field_hex("signature")?;
    let sig = HemJortsSignature::from_bytes_canonical(&sig_bytes)
        .ok_or_else(|| CliError::verify("non-canonical Hem quorum signature"))?;
    if u64::from(sig.leaf_idx) != sig_json.field_u64("epoch")? {
        return Err(CliError::verify("quorum signature epoch header mismatch"));
    }
    if !verify_hem_jorts_signature(&pk, message, &sig) {
        return Err(CliError::verify("quorum signature verification failed"));
    }

    if json_flag {
        let report = Json::object(vec![
            ("valid", Json::Bool(true)),
            ("scheme", Json::str(HEM_SCHEME_NAME)),
            ("epoch", Json::num(sig.leaf_idx)),
        ]);
        print!("{}", report.to_pretty());
    } else {
        println!("VALID ({HEM_SCHEME_NAME}, epoch {})", sig.leaf_idx);
    }
    Ok(())
}
