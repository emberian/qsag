//! Dealerless hardened post-quantum HD inventory & watch-only child derivation CLI
//! (`qsag hd`), backed by [`qsag_hd`].
//!
//! Subcommands:
//! - `keygen` — 3-round dealerless subset-seed ceremony (`SeedCeremonyRound1..3`) +
//!   corroborated `SLH-DSA-SHAKE-128f` batch inventory commitment.
//! - `derive` — `0`-round watch-only Bech32m deposit address + Poseidon2 Merkle proof
//!   derivation (`0` secret keys touched).
//! - `verify-child` — Verify an [`InventoryChildProof`] against the watch-only master root.
//! - `recover` — Threshold `t`-of-`n` custodian child seed recovery verified against the
//!   enrolled child public key, outputting a `qsag sign`-ready secret key file.

use std::path::Path;

use qsag_accel::CpuReferenceBackend;
use qsag_accel::keccak::cshake256_framed_32;
use qsag_addr::QsagAddress;
use qsag_core::fips205::{Fips205Params, slh_keygen_from_seed};
use qsag_hd::{
    CommitteeConfig, CustodianSeeds, CustodianSet, HdError, InventoryChildProof,
    InventoryMasterPublicKey, InventoryPartyShareVault, MAX_CUSTODIANS, SeedCeremonyRound1,
    SeedConfirmation, SeedContributionCommit, SeedPrivateDelivery, WatchOnlyInventoryTable,
    commit_inventory_public_keys, derive_inventory_vault, enroll_child_signing_seed_quorum,
    recover_child_signing_seed, verify_inventory_child_proof,
};

use crate::cli::{
    Args, CliError, MAX_KEY_FILE_BYTES, MAX_SIG_PROOF_BYTES, Secret32, ZeroizingBuf, os_random_32,
    private_dir, read_bounded_file, write_new,
};
use crate::codec::{Json, from_hex_exact, to_hex, to_hex_zeroizing};
use crate::keys::SECRET_FORMAT;

const HD_HELP: &str = "\
qsag hd <subcommand> [options]

Dealerless post-quantum SLH-DSA-SHAKE-128f HD inventory & 0-round watch-only derivation:
  keygen        run 3-round dealerless subset-seed ceremony and emit watch-only inventory
  derive        derive a watch-only Bech32m child address + Poseidon2 Merkle opening (0 secrets)
  verify-child  verify a derived child address and Poseidon2 opening against the watch-only file
  recover       reconstruct a child SLH-DSA-SHAKE-128f signing key from >= t custodian shares
";

const HD_META_FORMAT: &str = "qsag-hd-vault-meta-v1";
const HD_WATCH_FORMAT: &str = "qsag-hd-watch-inventory-v1";
const HD_PROOF_FORMAT: &str = "qsag-hd-child-proof-v1";

fn ensure_absent(path: &str) -> Result<(), CliError> {
    match std::fs::symlink_metadata(path) {
        Ok(_) => Err(CliError::usage(format!("{path} already exists"))),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(e) => Err(CliError::io(format_args!("inspecting {path}"), e)),
    }
}

fn load_json_checked(path: &str, expected_format: &str, max_bytes: u64) -> Result<Json, CliError> {
    let bytes = read_bounded_file(path, max_bytes)?;
    let text = std::str::from_utf8(&bytes.0)
        .map_err(|_| CliError::input(format!("{path} is not UTF-8")))?;
    let json = Json::parse(text)?;
    if json.field_str("format")? != expected_format {
        return Err(CliError::input(format!(
            "{path} is not a {expected_format} file"
        )));
    }
    Ok(json)
}

fn hd_meta_path(vault_dir: &str) -> String {
    Path::new(vault_dir)
        .join("hd-meta.json")
        .to_string_lossy()
        .into_owned()
}

fn hd_seed_path(vault_dir: &str, party: usize) -> String {
    Path::new(vault_dir)
        .join(format!("hd-custodian-{party}.seed"))
        .to_string_lossy()
        .into_owned()
}

fn map_hd_err(err: HdError) -> CliError {
    match err {
        HdError::InvalidBatchSize
        | HdError::ChildIndexOutOfBounds
        | HdError::UnsupportedCommittee
        | HdError::DuplicateOrZeroEvalPoint
        | HdError::AddressCodecError(_) => CliError::usage(format!("HD parameter error: {err:?}")),
        HdError::InvalidThresholdParameters
        | HdError::DerivationBudgetExceeded { .. }
        | HdError::EvaluationBudgetExceeded
        | HdError::DurableBudgetRequired
        | HdError::BudgetStorageFailed => {
            CliError::state(format!("HD threshold/custody requirement unmet: {err:?}"))
        }
        other => CliError::verify(format!("HD verification/ceremony failed: {other:?}")),
    }
}

fn build_committee(
    threshold: usize,
    parties: usize,
    label: [u8; 32],
) -> Result<CommitteeConfig, CliError> {
    if parties == 0 || parties > MAX_CUSTODIANS {
        return Err(CliError::usage(format!(
            "--parties must be in 1..={MAX_CUSTODIANS}"
        )));
    }
    let members: Vec<(u16, u32)> = (0..parties).map(|i| (i as u16, (i + 1) as u32)).collect();
    CommitteeConfig::new(threshold as u16, &members, label).map_err(|_| {
        CliError::usage(format!(
            "unsupported committee ({threshold}, {parties}): honest-majority requires n >= 2t - 1 and 1 <= t <= n <= {MAX_CUSTODIANS}"
        ))
    })
}

fn run_dealerless_seed_ceremony(
    config: &CommitteeConfig,
    entropies: &[Secret32],
) -> Result<(Vec<CustodianSeeds>, Vec<ZeroizingBuf>), CliError> {
    let members = config.members();
    let mut round1_states = Vec::with_capacity(members.len());
    let mut commits = Vec::with_capacity(members.len());
    for (&(id, _), ent) in members.iter().zip(entropies) {
        let (r1, commit) = SeedCeremonyRound1::begin(config, id, ent.0).map_err(map_hd_err)?;
        round1_states.push(r1);
        commits.push(commit);
    }

    let mut round2_states = Vec::with_capacity(members.len());
    let mut all_deliveries: Vec<SeedPrivateDelivery> = Vec::new();
    for r1 in round1_states {
        let (r2, deliveries) = r1.freeze(&commits).map_err(map_hd_err)?;
        round2_states.push(r2);
        all_deliveries.extend(deliveries);
    }

    let mut inboxes: Vec<Vec<SeedPrivateDelivery>> =
        (0..members.len()).map(|_| Vec::new()).collect();
    for delivery in all_deliveries {
        let pos = members
            .iter()
            .position(|&(id, _)| id == delivery.to)
            .ok_or_else(|| CliError::verify("unknown recipient in HD seed delivery"))?;
        inboxes[pos].push(delivery);
    }

    let mut bundles = Vec::with_capacity(members.len());
    for (index, inbox) in inboxes.iter().enumerate() {
        let mut bytes = ZeroizingBuf(b"QSAGHDL1".to_vec());
        bytes.0.extend_from_slice(&entropies[index].0);
        for commit in &commits {
            bytes.0.extend_from_slice(&commit.party_id.to_be_bytes());
            bytes
                .0
                .extend_from_slice(&(commit.digests.len() as u32).to_be_bytes());
            for (subset, digest) in &commit.digests {
                bytes.0.extend_from_slice(&subset.to_be_bytes());
                bytes.0.extend_from_slice(digest);
            }
        }
        bytes
            .0
            .extend_from_slice(&(inbox.len() as u32).to_be_bytes());
        for delivery in inbox {
            bytes.0.extend_from_slice(&delivery.from.to_be_bytes());
            bytes.0.extend_from_slice(&delivery.to.to_be_bytes());
            bytes
                .0
                .extend_from_slice(&(delivery.openings.len() as u32).to_be_bytes());
            for opening in &delivery.openings {
                bytes.0.extend_from_slice(&opening.subset.to_be_bytes());
                bytes.0.extend_from_slice(&opening.contribution);
                bytes.0.extend_from_slice(&opening.salt);
            }
        }
        bundles.push(bytes);
    }
    let mut round3_states = Vec::with_capacity(members.len());
    let mut confirmations = Vec::with_capacity(members.len());
    for (r2, inbox) in round2_states.into_iter().zip(inboxes) {
        let (r3, confirm) = r2.receive(inbox).map_err(map_hd_err)?;
        round3_states.push(r3);
        confirmations.push(confirm);
    }

    for bytes in &mut bundles {
        for confirmation in &confirmations {
            bytes
                .0
                .extend_from_slice(&confirmation.party_id.to_be_bytes());
            bytes
                .0
                .extend_from_slice(&(confirmation.tags.len() as u32).to_be_bytes());
            for (subset, tag) in &confirmation.tags {
                bytes.0.extend_from_slice(&subset.to_be_bytes());
                bytes.0.extend_from_slice(tag);
            }
        }
    }
    let seeds = round3_states
        .into_iter()
        .map(|r3| r3.confirm(&confirmations).map_err(map_hd_err))
        .collect::<Result<_, _>>()?;
    Ok((seeds, bundles))
}

const HD_SHARE_FORMAT: &str = "qsag-hd-custodian-local-v1";
fn hd_share_path(dir: &str, party: usize) -> String {
    Path::new(dir)
        .join(format!("hd-custodian-{party}.share"))
        .to_string_lossy()
        .into_owned()
}

/// Rehydrate exactly one custodian by validating its own stored private deliveries and
/// public ceremony transcript. No network round, peer entropy, or n-party DKG is run.
fn restore_custodian(
    config: &CommitteeConfig,
    party: u16,
    bytes: &[u8],
) -> Result<CustodianSeeds, CliError> {
    struct Reader<'a>(&'a [u8]);
    impl Reader<'_> {
        fn take<const N: usize>(&mut self) -> Result<[u8; N], CliError> {
            let (head, rest) = self
                .0
                .split_at_checked(N)
                .ok_or_else(|| CliError::input("truncated HD custody bundle"))?;
            self.0 = rest;
            head.try_into()
                .map_err(|_| CliError::input("invalid HD custody bundle"))
        }
        fn count(&mut self, width: usize) -> Result<usize, CliError> {
            let count = u32::from_be_bytes(self.take()?) as usize;
            if count > self.0.len() / width {
                return Err(CliError::input("invalid HD custody count"));
            }
            Ok(count)
        }
        fn subset(&mut self) -> Result<CustodianSet, CliError> {
            let mut words = [0u64; 4];
            for word in words.iter_mut().rev() {
                *word = u64::from_be_bytes(self.take()?);
            }
            Ok(CustodianSet(words))
        }
        fn tags(&mut self) -> Result<Vec<(CustodianSet, [u8; 32])>, CliError> {
            let count = self.count(64)?;
            (0..count)
                .map(|_| Ok((self.subset()?, self.take()?)))
                .collect()
        }
    }
    let mut r = Reader(bytes);
    if &r.take::<8>()? != b"QSAGHDL1" {
        return Err(CliError::input("invalid HD custody magic"));
    }
    let entropy = Secret32(r.take()?);
    let mut commits = Vec::with_capacity(config.members().len());
    for _ in config.members() {
        commits.push(SeedContributionCommit {
            party_id: u16::from_be_bytes(r.take()?),
            digests: r.tags()?,
        });
    }
    let count = r.count(8)?;
    if count + 1 != config.members().len() {
        return Err(CliError::input("invalid HD custody roster"));
    }
    let mut deliveries = Vec::with_capacity(count);
    for _ in 0..count {
        let from = u16::from_be_bytes(r.take()?);
        let to = u16::from_be_bytes(r.take()?);
        let count = r.count(96)?;
        let mut openings = Vec::with_capacity(count);
        for _ in 0..count {
            openings.push(qsag_hd::seeds::SeedOpening {
                subset: r.subset()?,
                contribution: r.take()?,
                salt: r.take()?,
            });
        }
        deliveries.push(SeedPrivateDelivery { from, to, openings });
    }
    let mut confirmations = Vec::with_capacity(config.members().len());
    for _ in config.members() {
        confirmations.push(SeedConfirmation {
            party_id: u16::from_be_bytes(r.take()?),
            tags: r.tags()?,
        });
    }
    if !r.0.is_empty() {
        return Err(CliError::input("trailing HD custody data"));
    }
    let (r1, _) = SeedCeremonyRound1::begin(config, party, entropy.0).map_err(map_hd_err)?;
    let (r2, outgoing) = r1.freeze(&commits).map_err(map_hd_err)?;
    drop(outgoing);
    let (r3, _) = r2.receive(deliveries).map_err(map_hd_err)?;
    r3.confirm(&confirmations).map_err(map_hd_err)
}

fn limbs4_to_json(limbs: &[u64; 4]) -> Json {
    let mut bytes = [0u8; 32];
    for (i, &w) in limbs.iter().enumerate() {
        bytes[i * 8..(i + 1) * 8].copy_from_slice(&w.to_le_bytes());
    }
    Json::hex(&bytes)
}

fn json_to_limbs4(hex_str: &str, what: &str) -> Result<[u64; 4], CliError> {
    let raw = from_hex_exact::<32>(hex_str, what)?;
    Ok(core::array::from_fn(|i| {
        u64::from_le_bytes(raw[i * 8..(i + 1) * 8].try_into().unwrap_or([0; 8]))
    }))
}

fn load_watch_table(path: &str) -> Result<WatchOnlyInventoryTable, CliError> {
    let json = load_json_checked(path, HD_WATCH_FORMAT, MAX_SIG_PROOF_BYTES)?;
    let expected_root = from_hex_exact::<32>(json.field_str("master_root_pk")?, "master_root_pk")?;
    let pk_seed = from_hex_exact::<32>(json.field_str("pk_seed")?, "pk_seed")?;
    let batch_size = json.field_u64("batch_size")? as usize;
    let arr = json
        .get("child_pubkeys")
        .and_then(Json::as_array)
        .ok_or_else(|| CliError::input("missing child_pubkeys array in watch file"))?;
    if arr.len() != batch_size {
        return Err(CliError::input(
            "child_pubkeys length does not match batch_size",
        ));
    }
    let mut child_pubkeys = Vec::with_capacity(batch_size);
    for entry in arr {
        let s = entry
            .as_str()
            .ok_or_else(|| CliError::input("child_pubkeys entry must be hex string"))?;
        child_pubkeys.push(from_hex_exact::<32>(s, "child_pubkey")?);
    }
    let table = commit_inventory_public_keys(pk_seed, child_pubkeys, &CpuReferenceBackend::new())
        .map_err(map_hd_err)?;
    if table.master_pk.master_root_pk != expected_root {
        return Err(CliError::verify(
            "recomputed master_root_pk does not match watch-only inventory header",
        ));
    }
    Ok(table)
}

fn keygen(raw: &[String]) -> Result<(), CliError> {
    let args = Args::parse(
        raw,
        &[
            "threshold",
            "parties",
            "count",
            "vault-dir",
            "watch-out",
            "passphrase-env",
            "passphrase-file",
        ],
        &["deterministic", "allow-unencrypted", "json", "help"],
    )?;
    if args.flag("help") {
        println!(
            "qsag hd keygen [--threshold <t>] [--parties <n>] [--count <pow2>] --vault-dir <dir> --watch-out <path> [--passphrase-env <VAR> | --passphrase-file <path>] [--allow-unencrypted] [--deterministic] [--json]"
        );
        return Ok(());
    }
    args.no_positionals()?;
    let threshold = args.get_u64("threshold")?.unwrap_or(2) as usize;
    let parties = args.get_u64("parties")?.unwrap_or(3) as usize;
    let batch_size = args.get_u64("count")?.unwrap_or(16) as usize;
    if !batch_size.is_power_of_two() || !(2..=65_536).contains(&batch_size) {
        return Err(CliError::usage(
            "--count must be a power of two between 2 and 65536",
        ));
    }
    if (batch_size as u64)
        .checked_mul(80)
        .and_then(|n| n.checked_add(4096))
        .is_none_or(|n| n > MAX_SIG_PROOF_BYTES)
    {
        return Err(CliError::usage(
            "inventory exceeds the bounded watch-file size budget",
        ));
    }
    let passphrase = crate::envelope::passphrase(&args)?;
    if passphrase.is_none() && !args.flag("allow-unencrypted") && !args.flag("deterministic") {
        return Err(CliError::usage(
            "HD custody requires --passphrase-env or --passphrase-file (or explicit --allow-unencrypted)",
        ));
    }
    let vault_dir = args.require("vault-dir")?;
    let watch_out = args.require("watch-out")?;
    ensure_absent(&hd_meta_path(vault_dir))?;
    ensure_absent(watch_out)?;
    private_dir(vault_dir, true)?;

    let deterministic = args.flag("deterministic");
    let label = if deterministic {
        cshake256_framed_32(
            b"QSAG.CLI.HD.DET.LABEL.V1",
            &[
                &[threshold as u8, parties as u8],
                &(batch_size as u64).to_le_bytes(),
            ],
        )
    } else {
        os_random_32()?
    };
    let pk_seed = if deterministic {
        cshake256_framed_32(b"QSAG.CLI.HD.DET.PK_SEED.V1", &[&label])
    } else {
        os_random_32()?
    };
    let config = build_committee(threshold, parties, label)?;

    let mut entropies = Vec::with_capacity(parties);
    for idx in 0..parties {
        let seed = if deterministic {
            cshake256_framed_32(
                b"QSAG.CLI.HD.DET.CUSTODIAN.V1",
                &[&label, &(idx as u64).to_le_bytes()],
            )
        } else {
            os_random_32()?
        };
        entropies.push(Secret32(seed));
    }

    let (custodian_seeds, bundles) = run_dealerless_seed_ceremony(&config, &entropies)?;
    drop(entropies);
    let vaults: Vec<InventoryPartyShareVault> = custodian_seeds
        .iter()
        .map(|cs| derive_inventory_vault(cs, pk_seed, batch_size).map_err(map_hd_err))
        .collect::<Result<Vec<_>, _>>()?;
    let vault_refs: Vec<&InventoryPartyShareVault> = vaults.iter().collect();

    let mut child_pubkeys = Vec::with_capacity(batch_size);
    for idx in 0..batch_size as u32 {
        let (_seed, child_pk) =
            enroll_child_signing_seed_quorum(&config, &vault_refs, idx).map_err(map_hd_err)?;
        child_pubkeys.push(child_pk);
    }

    let table =
        commit_inventory_public_keys(pk_seed, child_pubkeys.clone(), &CpuReferenceBackend::new())
            .map_err(map_hd_err)?;

    for (idx, bundle) in bundles.iter().enumerate() {
        let mut doc = Json::object(vec![
            ("format", Json::str(HD_SHARE_FORMAT)),
            ("scheme", Json::str("hd-local-custody")),
            ("party", Json::num(idx)),
            ("config_digest", Json::hex(&config.digest())),
            ("master_root_pk", Json::hex(&table.master_pk.master_root_pk)),
            ("secret_key", Json::hex(bundle)),
        ]);
        if let Some(pass) = &passphrase {
            crate::envelope::seal(&mut doc, pass)?;
        }
        let encoded = ZeroizingBuf(doc.to_pretty().into_bytes());
        write_new(&hd_share_path(vault_dir, idx), &encoded, true)?;
    }

    let meta = Json::object(vec![
        ("format", Json::str(HD_META_FORMAT)),
        ("custody_format", Json::str(HD_SHARE_FORMAT)),
        ("threshold", Json::num(threshold)),
        ("parties", Json::num(parties)),
        ("batch_size", Json::num(batch_size)),
        ("ceremony_label", Json::hex(&label)),
        ("pk_seed", Json::hex(&pk_seed)),
        ("master_root_pk", Json::hex(&table.master_pk.master_root_pk)),
    ]);
    write_new(&hd_meta_path(vault_dir), meta.to_pretty().as_bytes(), true)?;

    let watch_doc = Json::object(vec![
        ("format", Json::str(HD_WATCH_FORMAT)),
        ("scheme", Json::str("pi-hd-commit-inventory-slh-128f")),
        ("threshold", Json::num(threshold)),
        ("parties", Json::num(parties)),
        ("batch_size", Json::num(batch_size)),
        ("master_root_pk", Json::hex(&table.master_pk.master_root_pk)),
        ("pk_seed", Json::hex(&pk_seed)),
        (
            "pk_seed_limbs",
            limbs4_to_json(&table.master_pk.pk_seed_limbs),
        ),
        (
            "poseidon2_root_limbs",
            limbs4_to_json(&table.master_pk.poseidon2_root_limbs),
        ),
        (
            "child_pubkeys",
            Json::Array(child_pubkeys.iter().map(|pk| Json::hex(pk)).collect()),
        ),
    ]);
    write_new(watch_out, watch_doc.to_pretty().as_bytes(), false)?;

    if args.flag("json") {
        let report = Json::object(vec![
            ("operation", Json::str("hd-keygen")),
            ("threshold", Json::num(threshold)),
            ("parties", Json::num(parties)),
            ("batch_size", Json::num(batch_size)),
            ("master_root_pk", Json::hex(&table.master_pk.master_root_pk)),
            ("vault_dir", Json::str(vault_dir)),
            ("watch_file", Json::str(watch_out)),
        ]);
        print!("{}", report.to_pretty());
    } else {
        println!(
            "initialized ({threshold}, {parties}) HD inventory ({batch_size} SLH-DSA-SHAKE-128f children, master root {}) -> {watch_out}",
            to_hex(&table.master_pk.master_root_pk)
        );
    }
    Ok(())
}

fn derive(raw: &[String]) -> Result<(), CliError> {
    let args = Args::parse(raw, &["watch", "index", "hrp", "out"], &["json", "help"])?;
    if args.flag("help") {
        println!(
            "qsag hd derive --watch <path> --index <child_idx> [--hrp <qsp>] --out <path> [--json]"
        );
        return Ok(());
    }
    args.no_positionals()?;
    let watch_path = args.require("watch")?;
    let index = args
        .get_u64("index")?
        .ok_or_else(|| CliError::usage("missing required option --index <n>"))?;
    let child_idx = u32::try_from(index).map_err(|_| CliError::usage("--index must fit in u32"))?;
    let hrp = args.get("hrp").unwrap_or("qsp");
    let out_path = args.require("out")?;
    ensure_absent(out_path)?;

    let table = load_watch_table(watch_path)?;
    let (addr, proof) = table
        .derive_watch_only_child(child_idx, hrp)
        .map_err(map_hd_err)?;
    verify_inventory_child_proof(&table.master_pk, &proof, &addr, &CpuReferenceBackend::new())
        .map_err(map_hd_err)?;
    let encoded_addr = addr
        .encode()
        .map_err(|e| CliError::usage(format!("Bech32m address encoding failed: {e:?}")))?;

    let proof_doc = Json::object(vec![
        ("format", Json::str(HD_PROOF_FORMAT)),
        ("address", Json::str(&encoded_addr)),
        ("child_idx", Json::num(proof.child_idx)),
        ("child_pk", Json::hex(&proof.child_pk)),
        ("master_root_pk", Json::hex(&table.master_pk.master_root_pk)),
        ("batch_size", Json::num(table.master_pk.batch_size)),
        (
            "pk_seed_limbs",
            limbs4_to_json(&table.master_pk.pk_seed_limbs),
        ),
        (
            "poseidon2_root_limbs",
            limbs4_to_json(&table.master_pk.poseidon2_root_limbs),
        ),
        (
            "poseidon2_siblings",
            Json::Array(
                proof
                    .poseidon2_siblings
                    .iter()
                    .map(limbs4_to_json)
                    .collect(),
            ),
        ),
    ]);
    write_new(out_path, proof_doc.to_pretty().as_bytes(), false)?;

    if args.flag("json") {
        print!("{}", proof_doc.to_pretty());
    } else {
        println!(
            "derived watch-only child #{child_idx}: {encoded_addr} ({} Merkle siblings) -> {out_path}",
            proof.poseidon2_siblings.len()
        );
    }
    Ok(())
}

fn verify_child(raw: &[String]) -> Result<(), CliError> {
    let args = Args::parse(raw, &["watch", "proof"], &["json", "help"])?;
    if args.flag("help") {
        println!("qsag hd verify-child --watch <path> --proof <path> [--json]");
        return Ok(());
    }
    args.no_positionals()?;
    let watch_path = args.require("watch")?;
    let proof_path = args.require("proof")?;

    let watch_json = load_json_checked(watch_path, HD_WATCH_FORMAT, MAX_SIG_PROOF_BYTES)?;
    let proof_json = load_json_checked(proof_path, HD_PROOF_FORMAT, MAX_SIG_PROOF_BYTES)?;

    let master_pk = InventoryMasterPublicKey {
        master_root_pk: from_hex_exact::<32>(
            watch_json.field_str("master_root_pk")?,
            "master_root_pk",
        )?,
        batch_size: watch_json.field_u64("batch_size")? as u32,
        pk_seed_limbs: json_to_limbs4(watch_json.field_str("pk_seed_limbs")?, "pk_seed_limbs")?,
        poseidon2_root_limbs: json_to_limbs4(
            watch_json.field_str("poseidon2_root_limbs")?,
            "poseidon2_root_limbs",
        )?,
    };

    let addr_str = proof_json.field_str("address")?;
    let addr = QsagAddress::decode(addr_str)
        .map_err(|e| CliError::verify(format!("invalid Bech32m child address: {e:?}")))?;
    let child_idx = proof_json.field_u64("child_idx")? as u32;
    let child_pk = from_hex_exact::<32>(proof_json.field_str("child_pk")?, "child_pk")?;
    let sib_arr = proof_json
        .get("poseidon2_siblings")
        .and_then(Json::as_array)
        .ok_or_else(|| CliError::input("missing poseidon2_siblings array"))?;
    let mut siblings = Vec::with_capacity(sib_arr.len());
    for entry in sib_arr {
        let s = entry
            .as_str()
            .ok_or_else(|| CliError::input("sibling entry must be hex string"))?;
        siblings.push(json_to_limbs4(s, "poseidon2_sibling")?);
    }
    let proof = InventoryChildProof {
        child_idx,
        child_pk,
        poseidon2_siblings: siblings,
    };

    verify_inventory_child_proof(&master_pk, &proof, &addr, &CpuReferenceBackend::new())
        .map_err(|e| CliError::verify(format!("HD child proof verification failed: {e:?}")))?;

    if args.flag("json") {
        let report = Json::object(vec![
            ("valid", Json::Bool(true)),
            ("address", Json::str(addr_str)),
            ("child_idx", Json::num(child_idx)),
            ("master_root_pk", Json::hex(&master_pk.master_root_pk)),
        ]);
        print!("{}", report.to_pretty());
    } else {
        println!("valid (child #{child_idx} -> {addr_str})");
    }
    Ok(())
}

fn parse_recover_signers(
    spec: Option<&str>,
    parties: usize,
    threshold: usize,
) -> Result<Vec<usize>, CliError> {
    let Some(spec) = spec else {
        return Ok((0..threshold.min(parties)).collect());
    };
    let mut out = Vec::new();
    for item in spec.split(',') {
        let trimmed = item.trim();
        if trimmed.is_empty() {
            continue;
        }
        let idx: usize = trimmed
            .parse()
            .map_err(|_| CliError::usage("--signers must be comma-separated custodian indices"))?;
        if idx >= parties {
            return Err(CliError::usage(format!(
                "--signers index {idx} out of range (parties = {parties})"
            )));
        }
        if out.contains(&idx) {
            return Err(CliError::usage(format!(
                "duplicate custodian index {idx} in --signers"
            )));
        }
        out.push(idx);
    }
    out.sort_unstable();
    Ok(out)
}

fn recover(raw: &[String]) -> Result<(), CliError> {
    let args = Args::parse(
        raw,
        &[
            "vault-dir",
            "signers",
            "index",
            "proof",
            "secret-out",
            "public-out",
            "passphrase-env",
            "passphrase-file",
        ],
        &["json", "help"],
    )?;
    if args.flag("help") {
        println!(
            "qsag hd recover --vault-dir <dir> [--signers <i,j,..>] --index <child_idx> --proof <child.json> --secret-out <path> [--public-out <path>] [--passphrase-env <VAR> | --passphrase-file <path>] [--json]"
        );
        return Ok(());
    }
    args.no_positionals()?;
    let vault_dir = args.require("vault-dir")?;
    let index = args
        .get_u64("index")?
        .ok_or_else(|| CliError::usage("missing required option --index <n>"))?;
    let child_idx = u32::try_from(index).map_err(|_| CliError::usage("--index must fit in u32"))?;
    let proof_path = args.require("proof")?;
    let secret_out = args.require("secret-out")?;
    ensure_absent(secret_out)?;
    if let Some(pub_out) = args.get("public-out") {
        ensure_absent(pub_out)?;
    }
    private_dir(vault_dir, false)?;

    let meta = load_json_checked(&hd_meta_path(vault_dir), HD_META_FORMAT, MAX_KEY_FILE_BYTES)?;
    let proof_json = load_json_checked(proof_path, HD_PROOF_FORMAT, MAX_SIG_PROOF_BYTES)?;

    let threshold = meta.field_u64("threshold")? as usize;
    let parties = meta.field_u64("parties")? as usize;
    let batch_size = meta.field_u64("batch_size")? as usize;
    let label = from_hex_exact::<32>(meta.field_str("ceremony_label")?, "ceremony_label")?;
    let pk_seed = from_hex_exact::<32>(meta.field_str("pk_seed")?, "pk_seed")?;
    let master_root = from_hex_exact::<32>(meta.field_str("master_root_pk")?, "master_root_pk")?;

    let proof_root = from_hex_exact::<32>(
        proof_json.field_str("master_root_pk")?,
        "proof master_root_pk",
    )?;
    if master_root != proof_root {
        return Err(CliError::verify(
            "child proof master_root_pk does not match HD vault",
        ));
    }
    if proof_json.field_u64("child_idx")? as u32 != child_idx {
        return Err(CliError::usage(
            "--index does not match child_idx in --proof file",
        ));
    }
    let expected_child_pk = from_hex_exact::<32>(proof_json.field_str("child_pk")?, "child_pk")?;

    let signers = parse_recover_signers(args.get("signers"), parties, threshold)?;
    let config = build_committee(threshold, parties, label)?;

    if child_idx as usize >= batch_size {
        return Err(CliError::usage("child index out of bounds"));
    }
    let passphrase = crate::envelope::passphrase(&args)?;
    let custodian_seeds = if meta.get("custody_format").is_some() {
        if meta.field_str("custody_format")? != HD_SHARE_FORMAT {
            return Err(CliError::input("unknown HD custody format"));
        }
        let mut selected = Vec::with_capacity(signers.len());
        for &idx in &signers {
            let doc = load_json_checked(
                &hd_share_path(vault_dir, idx),
                HD_SHARE_FORMAT,
                MAX_SIG_PROOF_BYTES,
            )?;
            if doc.field_u64("party")? != idx as u64
                || from_hex_exact::<32>(doc.field_str("config_digest")?, "config_digest")?
                    != config.digest()
                || from_hex_exact::<32>(doc.field_str("master_root_pk")?, "master_root_pk")?
                    != master_root
            {
                return Err(CliError::verify(
                    "HD custody bundle does not match enrollment",
                ));
            }
            let opened = crate::envelope::open(&doc, passphrase.as_deref())?;
            selected.push(restore_custodian(
                &config,
                idx as u16,
                opened.secret_key()?,
            )?);
        }
        selected
    } else {
        // Explicit compatibility for v1 inventories; newly enrolled vaults never persist these seeds.
        let mut entropies = Vec::with_capacity(parties);
        for idx in 0..parties {
            let raw = read_bounded_file(&hd_seed_path(vault_dir, idx), 32)?;
            entropies.push(Secret32(
                raw.0
                    .as_slice()
                    .try_into()
                    .map_err(|_| CliError::input("corrupt HD seed"))?,
            ));
        }
        let (all, _) = run_dealerless_seed_ceremony(&config, &entropies)?;
        all.into_iter()
            .filter(|s| signers.contains(&(s.party_id() as usize)))
            .collect()
    };
    let selected_vaults = custodian_seeds
        .iter()
        .map(|cs| derive_inventory_vault(cs, pk_seed, batch_size).map_err(map_hd_err))
        .collect::<Result<Vec<_>, _>>()?;
    let selected_refs: Vec<_> = selected_vaults.iter().collect();

    let recovered_seed =
        recover_child_signing_seed(&config, &selected_refs, child_idx, Some(&expected_child_pk))
            .map_err(map_hd_err)?;
    let (sk, pk) =
        slh_keygen_from_seed(&Fips205Params::SLH_DSA_SHAKE_128F, recovered_seed.expose()).map_err(
            |_| CliError::verify("SLH-DSA-SHAKE-128f keygen from recovered seed failed"),
        )?;
    let sk_bytes = crate::cli::ZeroizingBuf(sk.to_bytes());
    let sk_hex = to_hex_zeroizing(&sk_bytes.0);
    let sk_hex_str = std::str::from_utf8(&sk_hex.0)
        .map_err(|_| CliError::input("internal hex encoding error"))?;
    let pk_bytes = pk.to_bytes();

    // Emit a vault-enrolled `qsag-secret-key-v1` SLH-DSA-SHAKE-128f key file usable directly by `qsag sign`.
    let mut vault = crate::vault::Vault::acquire(secret_out, true)?;
    // Same enrollment sequence as `qsag keygen`. The vault state MAC covers a fresh 16-byte
    // `enrollment_nonce` (`vault::tag` refuses a secret file without one), so recovering the same
    // child twice yields two enrollments whose lock files are not interchangeable. The nonce is
    // not mixed into the key: an SLH-DSA child is fully determined by the recovered seed.
    let enrollment_entropy = Secret32(os_random_32()?);
    let mut secret_doc = Json::object(vec![
        ("format", Json::str(SECRET_FORMAT)),
        ("scheme", Json::str("slh-dsa-shake-128f")),
        ("enrollment_nonce", Json::hex(&enrollment_entropy[..16])),
        ("uses_completed", Json::num(0)),
        ("child_idx", Json::num(child_idx)),
        ("master_root_pk", Json::hex(&master_root)),
        ("secret_key", Json::str(sk_hex_str)),
        ("public_key", Json::hex(&pk_bytes)),
    ]);
    vault.set_key_material(&crate::envelope::open(&secret_doc, None)?);
    if let Some(pass) = &passphrase {
        crate::envelope::seal(&mut secret_doc, pass)?;
    }
    vault.bind(&mut secret_doc)?;
    vault.prepare(&mut secret_doc)?;
    let encoded_secret = crate::cli::ZeroizingBuf(secret_doc.to_pretty().into_bytes());
    vault.seal(&mut secret_doc)?;
    write_new(secret_out, &encoded_secret.0, true)?;

    if let Some(pub_out) = args.get("public-out") {
        let spki = pk
            .to_spki_der(&Fips205Params::SLH_DSA_SHAKE_128F)
            .map_err(|e| CliError::usage(e.to_string()))?;
        let pub_doc = Json::object(vec![
            ("format", Json::str(crate::keys::PUBLIC_FORMAT)),
            ("scheme", Json::str("slh-dsa-shake-128f")),
            ("spki_der", Json::hex(&spki)),
            ("public_key", Json::hex(&pk_bytes)),
        ]);
        write_new(pub_out, pub_doc.to_pretty().as_bytes(), false)?;
    }

    if args.flag("json") {
        let report = Json::object(vec![
            ("operation", Json::str("hd-recover")),
            ("scheme", Json::str("slh-dsa-shake-128f")),
            ("child_idx", Json::num(child_idx)),
            ("public_key", Json::hex(&pk_bytes)),
            (
                "signers",
                Json::Array(signers.iter().map(|i| Json::num(*i)).collect()),
            ),
            ("secret_file", Json::str(secret_out)),
        ]);
        print!("{}", report.to_pretty());
    } else {
        println!(
            "recovered child #{child_idx} SLH-DSA-SHAKE-128f key from {} custodian(s) -> {secret_out}",
            signers.len()
        );
    }
    Ok(())
}

pub fn run(raw: &[String]) -> Result<(), CliError> {
    let Some((sub, rest)) = raw.split_first() else {
        print!("{HD_HELP}");
        return Err(CliError::usage("hd requires a subcommand (try --help)"));
    };
    match sub.as_str() {
        "--help" | "-h" | "help" => {
            print!("{HD_HELP}");
            Ok(())
        }
        "keygen" => keygen(rest),
        "derive" => derive(rest),
        "verify-child" => verify_child(rest),
        "recover" => recover(rest),
        other => Err(CliError::usage(format!(
            "unknown hd subcommand '{other}' (expected keygen, derive, verify-child, or recover)"
        ))),
    }
}
