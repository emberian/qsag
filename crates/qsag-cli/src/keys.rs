//! `keygen`, `sign`, and `verify`.

use qsag_accel::CpuReferenceBackend;
use qsag_accel::keccak::{cshake256_framed_32, cshake256_framed_xof};
use qsag_addr::{KeyIdentityKind, QsagAddress};
use qsag_core::ceremony_journal::{CeremonyContext, CeremonyReservation, FsCeremonyJournal};
use qsag_core::fips205::{
    Fips205Params, SlhPublicKey, SlhSecretKey, slh_keygen_from_seed, slh_sign, slh_verify,
};
use qsag_core::pcg_dense::{FsSeedBurnTracker, SeedBurnTracker};
use qsag_fts::{
    FrontierDpTable, FrontierFtsError, FrontierFtsProfile, FrontierFtsPublicKey,
    FrontierFtsSignature, FrontierFtsSigningKey, FsWalFtsEpochLatch, ParallelSeededError,
    ParallelSeededMerkleLayers, ParallelSeededPublicKey, ParallelSeededSignature,
    assemble_parallel_seeded_public_key, verify_frontier_fts, verify_parallel_seeded_fts,
};

use crate::cli::{
    Args, CliError, MAX_KEY_FILE_BYTES, MAX_SIG_PROOF_BYTES, Secret32, ZeroizingBuf, os_random_32,
    read_bounded_file, read_input, write_new,
};
use crate::codec::{Json, from_hex_exact};
#[cfg(not(any(test, feature = "test-dealer")))]
use crate::dealerless_ceremony::DealerlessThresholdFtsSetup;
use crate::schemes::{Scheme, THRESHOLD_FTS_PARAMS};

pub const SECRET_FORMAT: &str = "qsag-secret-key-v1";
pub const PUBLIC_FORMAT: &str = "qsag-public-key-v1";
pub const SIGNATURE_FORMAT: &str = "qsag-signature-v1";

/// Domain-separated 32-byte subkey of a key file's master seed.
pub fn derive(seed: &[u8; 32], label: &[u8]) -> [u8; 32] {
    cshake256_framed_32(b"QSAG.CLI.DERIVE.V1", &[seed, label])
}

pub fn derive_secret(seed: &[u8; 32], label: &[u8]) -> Secret32 {
    Secret32::new(derive(seed, label))
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

/// The provisioned committee an `fts-threshold` command signs with: the dealerless ceremony.
#[cfg(not(any(test, feature = "test-dealer")))]
type ThresholdSetup = DealerlessThresholdFtsSetup;

#[cfg(not(any(test, feature = "test-dealer")))]
fn threshold_setup(
    seed: &[u8; 32],
    parties: u64,
    params: qsag_fts::ParallelSeededParams,
    cached_tree: Option<(ParallelSeededPublicKey, ParallelSeededMerkleLayers)>,
) -> Result<ThresholdSetup, CliError> {
    DealerlessThresholdFtsSetup::run_ceremony(
        params,
        usize::try_from(parties).map_err(|_| CliError::usage("party count is not representable on this platform"))?,
        derive(seed, b"threshold dkg ceremony"),
        cached_tree,
    )
    .map_err(|e| {
        CliError::usage(format!(
            "dealerless threshold setup failed ({e:?})"
        ))
    })
}

/// Trusted-dealer provisioning for fast library unit tests and explicit `test-dealer` builds only.
/// Production builds run the shared-operand + stream-folded Keccak-x8 Gilboa dealerless ceremony
/// and persist encrypted per-party `ParallelSeededDkgReservoir` (`QSFTSRS1`) sidecars so `qsag sign`
/// signs directly from the persisted reservoirs without re-running DKG.
#[cfg(any(test, feature = "test-dealer"))]
struct ThresholdSetup(qsag_fts::ParallelSeededThresholdSetup);

#[cfg(any(test, feature = "test-dealer"))]
impl std::ops::Deref for ThresholdSetup {
    type Target = qsag_fts::ParallelSeededThresholdSetup;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[cfg(any(test, feature = "test-dealer"))]
impl ThresholdSetup {
    fn threshold_sign(
        &mut self,
        epoch: u32,
        msg: &[u8],
        session_id: [u8; 32],
        persistence: &mut impl qsag_fts::LeafBurnPersistence,
    ) -> Result<ParallelSeededSignature, ParallelSeededError> {
        self.0
            .threshold_sign(epoch, msg, session_id, persistence, &CpuReferenceBackend)
    }
}

#[cfg(any(test, feature = "test-dealer"))]
fn threshold_setup(
    seed: &[u8; 32],
    parties: u64,
    params: qsag_fts::ParallelSeededParams,
    cached_tree: Option<(ParallelSeededPublicKey, ParallelSeededMerkleLayers)>,
) -> Result<ThresholdSetup, CliError> {
    let failed = |e: ParallelSeededError| {
        CliError::usage(format!("trusted-dealer threshold setup failed ({e:?})"))
    };
    let setup = qsag_fts::ParallelSeededThresholdSetup::trusted_dealer_setup_for_testing(
        params,
        usize::try_from(parties)
            .map_err(|_| CliError::usage("party count is not representable on this platform"))?,
        derive(seed, b"threshold dealer entropy"),
        derive(seed, b"threshold pk_seed"),
        &CpuReferenceBackend,
    )
    .map_err(failed)?;
    // The tree recorded in the key file must be the one this seed provisions.
    if let Some((cached_pk, cached_layers)) = cached_tree
        && (cached_pk != setup.pk || cached_layers != setup.public_tree_layers)
    {
        return Err(failed(ParallelSeededError::InvalidAuthenticationPath));
    }
    Ok(ThresholdSetup(setup))
}

fn encode_merkle_leaf_hex(digest: &[u64; 4]) -> Json {
    let mut out = [0u8; 32];
    for (i, &w) in digest.iter().enumerate() {
        out[i * 8..(i + 1) * 8].copy_from_slice(&w.to_le_bytes());
    }
    Json::hex(&out)
}

fn load_cached_threshold_tree(
    secret: &Json,
    params: qsag_fts::ParallelSeededParams,
) -> Result<Option<(ParallelSeededPublicKey, ParallelSeededMerkleLayers)>, CliError> {
    let Some(leaves_arr) = secret.get("merkle_leaves").and_then(Json::as_array) else {
        return Ok(None);
    };
    let Some(pk_seed_str) = secret.get("pk_seed").and_then(Json::as_str) else {
        return Ok(None);
    };
    let pk_seed_bytes: [u8; 32] = from_hex_exact(pk_seed_str, "pk_seed")?;
    let mut leaves = Vec::with_capacity(leaves_arr.len());
    for item in leaves_arr {
        let s = item
            .as_str()
            .ok_or_else(|| CliError::input("corrupt merkle_leaves entry"))?;
        let raw: [u8; 32] = from_hex_exact(s, "merkle_leaf")?;
        let limbs = core::array::from_fn(|i| {
            let mut b = [0u8; 8];
            b.copy_from_slice(&raw[i * 8..(i + 1) * 8]);
            u64::from_le_bytes(b)
        });
        leaves.push(limbs);
    }
    let (pk, layers) = assemble_parallel_seeded_public_key(params, pk_seed_bytes, &leaves)
        .map_err(|e| CliError::input(format!("invalid cached threshold Merkle leaves: {e:?}")))?;
    Ok(Some((pk, layers)))
}

fn threshold_params(file: &Json) -> Result<qsag_fts::ParallelSeededParams, CliError> {
    let height = file.field_u64("tree_height")?;
    if !(1..=10).contains(&height) {
        return Err(CliError::input("unsupported threshold tree height"));
    }
    Ok(qsag_fts::ParallelSeededParams {
        tree_height: height as usize,
        ..THRESHOLD_FTS_PARAMS
    })
}

#[cfg(not(any(test, feature = "test-dealer")))]
const MAX_RESERVOIR_RECORD_BYTES: usize = 64 * 1024 * 1024;

#[cfg(not(any(test, feature = "test-dealer")))]
fn reservoir_sidecar_path(secret_path: &str, party: usize) -> String {
    format!("{secret_path}.party-{party}.reservoir")
}

#[cfg(not(any(test, feature = "test-dealer")))]
fn write_threshold_reservoirs(
    secret_path: &str,
    seed: &[u8; 32],
    setup: &ThresholdSetup,
    create_new: bool,
) -> Result<(u64, [u8; 32]), CliError> {
    use qsag_asm::durable::LockedRecord;
    let (generation, blobs) = setup
        .serialize_reservoirs()
        .map_err(|e| CliError::state(format!("serializing threshold reservoirs failed: {e:?}")))?;
    let pk_seed = setup.pk.pk_seed_bytes;
    let mut tags_flat = Vec::with_capacity(blobs.len() * 32);
    for (party, plain) in blobs.iter().enumerate() {
        let path = reservoir_sidecar_path(secret_path, party);
        let record = if create_new {
            LockedRecord::create_new(&path)
                .map_err(|e| CliError::io("creating threshold reservoir sidecar", e))?
        } else {
            LockedRecord::open_existing(&path)
                .map_err(|_| CliError::state("CorruptOrRolledBackThresholdReservoir"))?
        };
        let seal = record.lock_identity_seal();
        let rand = os_random_32()?;
        let nonce: [u8; 16] = rand[..16].try_into().unwrap();
        let p_be = (party as u16).to_be_bytes();
        let gen_be = generation.to_be_bytes();
        let mut pad = ZeroizingBuf::new(vec![0u8; plain.len()]);
        cshake256_framed_xof(
            b"QSAG.CLI.FTS.RES.ENC.V1",
            &[seed, &pk_seed, &p_be, &gen_be, &nonce],
            &mut pad.0,
        );
        let mut out = Vec::with_capacity(8 + 8 + 16 + plain.len() + 32);
        out.extend_from_slice(b"QSFTSRC1");
        out.extend_from_slice(&gen_be);
        out.extend_from_slice(&nonce);
        for (&b, &m) in plain.iter().zip(pad.0.iter()) {
            out.push(b ^ m);
        }
        let tag = cshake256_framed_32(
            b"QSAG.CLI.FTS.RES.MAC.V1",
            &[seed, &seal, &pk_seed, &p_be, &out],
        );
        out.extend_from_slice(&tag);
        tags_flat.extend_from_slice(&tag);
        record
            .replace(&out)
            .map_err(|e| CliError::io("persisting threshold reservoir sidecar", e))?;
    }
    let commit = cshake256_framed_32(
        b"QSAG.CLI.FTS.RES.COMMIT.V1",
        &[&pk_seed, &generation.to_be_bytes(), &tags_flat],
    );
    Ok((generation, commit))
}

#[cfg(not(any(test, feature = "test-dealer")))]
fn load_or_setup_threshold(
    secret_path: &str,
    secret_json: &Json,
    seed: &[u8; 32],
    parties: u64,
    params: qsag_fts::ParallelSeededParams,
    cached_pk: ParallelSeededPublicKey,
    cached_layers: ParallelSeededMerkleLayers,
) -> Result<(ThresholdSetup, bool), CliError> {
    use qsag_asm::durable::LockedRecord;
    let Some(gen_val) = secret_json.get("reservoir_generation") else {
        let setup = threshold_setup(seed, parties, params, Some((cached_pk, cached_layers)))?;
        return Ok((setup, false));
    };
    let expected_gen = match gen_val {
        Json::Number(s) => s.parse::<u64>().map_err(|_| crate::vault::corrupt())?,
        _ => return Err(crate::vault::corrupt()),
    };
    let expected_commit: [u8; 32] = from_hex_exact(
        secret_json
            .field_str("reservoir_commit")
            .map_err(|_| crate::vault::corrupt())?,
        "reservoir_commit",
    )
    .map_err(|_| crate::vault::corrupt())?;
    let n = usize::try_from(parties).map_err(|_| CliError::usage("invalid party count"))?;
    let pk_seed = cached_pk.pk_seed_bytes;
    let mut tags_flat = Vec::with_capacity(n * 32);
    let mut decrypted = Vec::with_capacity(n);

    for party in 0..n {
        let path = reservoir_sidecar_path(secret_path, party);
        let record = LockedRecord::open_existing(&path)
            .map_err(|_| CliError::state("CorruptOrRolledBackThresholdReservoir"))?;
        let seal = record.lock_identity_seal();
        let raw = record
            .read_bounded(MAX_RESERVOIR_RECORD_BYTES)
            .map_err(|_| CliError::state("CorruptOrRolledBackThresholdReservoir"))?;
        if raw.len() < 8 + 8 + 16 + 32 || &raw[..8] != b"QSFTSRC1" {
            return Err(CliError::state("CorruptOrRolledBackThresholdReservoir"));
        }
        let body = &raw[..raw.len() - 32];
        let stored_tag = &raw[raw.len() - 32..];
        let p_be = (party as u16).to_be_bytes();
        let expected_tag = cshake256_framed_32(
            b"QSAG.CLI.FTS.RES.MAC.V1",
            &[seed, &seal, &pk_seed, &p_be, body],
        );
        if !qsag_accel::ct::ct_eq_bytes(stored_tag, &expected_tag) {
            return Err(CliError::state("CorruptOrRolledBackThresholdReservoir"));
        }
        let rec_gen = u64::from_be_bytes(body[8..16].try_into().unwrap());
        if rec_gen != expected_gen {
            return Err(CliError::state("CorruptOrRolledBackThresholdReservoir"));
        }
        let nonce = &body[16..32];
        let ct = &body[32..];
        let mut plain = ZeroizingBuf::new(vec![0u8; ct.len()]);
        cshake256_framed_xof(
            b"QSAG.CLI.FTS.RES.ENC.V1",
            &[seed, &pk_seed, &p_be, &expected_gen.to_be_bytes(), nonce],
            &mut plain.0,
        );
        for (slot, &c) in plain.0.iter_mut().zip(ct.iter()) {
            *slot ^= c;
        }
        tags_flat.extend_from_slice(stored_tag);
        decrypted.push(plain);
    }
    let actual_commit = cshake256_framed_32(
        b"QSAG.CLI.FTS.RES.COMMIT.V1",
        &[&pk_seed, &expected_gen.to_be_bytes(), &tags_flat],
    );
    if !qsag_accel::ct::ct_eq_bytes(&actual_commit, &expected_commit) {
        return Err(CliError::state("CorruptOrRolledBackThresholdReservoir"));
    }
    let decrypted_slices: Vec<&[u8]> = decrypted.iter().map(|b| b.0.as_slice()).collect();
    let setup = DealerlessThresholdFtsSetup::from_persisted_reservoirs(
        cached_pk,
        cached_layers,
        expected_gen,
        &decrypted_slices,
    )
    .map_err(|_| CliError::state("CorruptOrRolledBackThresholdReservoir"))?;
    Ok((setup, true))
}

#[cfg(any(test, feature = "test-dealer"))]
fn load_or_setup_threshold(
    _secret_path: &str,
    _secret_json: &Json,
    seed: &[u8; 32],
    parties: u64,
    params: qsag_fts::ParallelSeededParams,
    cached_pk: ParallelSeededPublicKey,
    cached_layers: ParallelSeededMerkleLayers,
) -> Result<(ThresholdSetup, bool), CliError> {
    let setup = threshold_setup(seed, parties, params, Some((cached_pk, cached_layers)))?;
    Ok((setup, false))
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
    anchor_cfg: Option<&crate::anchor::AnchorConfig>,
) -> Result<
    (
        qsag_core::LedgerCheckpoint,
        qsag_core::LedgerCheckpoint,
        Option<[u8; 24]>,
    ),
    CliError,
> {
    let ceremony_mac = derive_secret(seed, b"ceremony journal mac");
    let seedburn_mac = derive_secret(seed, b"seed burn ledger mac");
    let (ceremony_journal, ceremony_seal) = if let Some(cfg) = anchor_cfg {
        let ceremony_anchor_mac = derive_secret(seed, b"external ceremony anchor mac");
        let ceremony_anchor = crate::anchor::FsExternalMountAnchor::provision_fresh(
            cfg,
            &[secret_path],
            &[],
            "ceremony",
            key_id,
            ceremony_anchor_mac.0,
        )?;
        let seal = ceremony_anchor.lock_identity_seal();
        let j = FsCeremonyJournal::create_new_anchored(
            ceremony_journal_path(secret_path),
            key_id,
            ceremony_mac.0,
            Box::new(ceremony_anchor),
        )
        .map_err(|e| CliError::io("creating anchored ceremony reservation journal", e))?;
        (j, Some(seal))
    } else {
        let j = FsCeremonyJournal::create_new(
            ceremony_journal_path(secret_path),
            key_id,
            ceremony_mac.0,
        )
        .map_err(|e| CliError::io("creating ceremony reservation journal", e))?;
        (j, None)
    };
    let seed_burns =
        FsSeedBurnTracker::provision_genesis(seed_burn_ledger_path(secret_path), seedburn_mac.0)
            .map_err(|_| CliError::state("creating seed burn ledger failed"))?;
    let ledger_ckpt = seed_burns.checkpoint();
    Ok((ledger_ckpt, ceremony_journal.checkpoint(), ceremony_seal))
}

/// Outcome of reserving one use or epoch in the seed burn ledger.
enum SeedBurn {
    /// Burned by this call; the caller may sign once the vault retains the checkpoint.
    Fresh,
    /// Burned by an earlier attempt. `secret_json` now carries the ledger's current
    /// checkpoint; nothing may be signed under this identifier.
    AlreadySpent,
}

#[allow(clippy::too_many_arguments)]
fn burn_stateful_ceremony_with_checkpoint(
    secret_path: &str,
    secret_json: &mut Json,
    key_id: [u8; 32],
    seed: &[u8; 32],
    ceremony_id: [u8; 32],
    seed_burn_id: [u8; 32],
    base_context: CeremonyContext,
    anchor_cfg: Option<&crate::anchor::AnchorConfig>,
    observed_uses: u64,
) -> Result<SeedBurn, CliError> {
    let retained_ledger_ckpt = crate::vault::read_ledger_checkpoint(secret_json)?;
    let retained_ceremony_ckpt = crate::vault::read_ceremony_checkpoint(secret_json)?;
    let ceremony_mac = derive_secret(seed, b"ceremony journal mac");
    let seedburn_mac = derive_secret(seed, b"seed burn ledger mac");

    let mut ceremony_journal = if let Some(cfg) = anchor_cfg {
        let ceremony_anchor_mac = derive_secret(seed, b"external ceremony anchor mac");
        let ceremony_anchor = crate::anchor::FsExternalMountAnchor::open_existing(
            cfg,
            &[secret_path],
            &[],
            "ceremony",
            key_id,
            ceremony_anchor_mac.0,
        )?;
        ceremony_anchor.verify_expected_seal(secret_json, "anchor_ceremony_seal")?;
        let j = FsCeremonyJournal::open_existing_anchored(
            ceremony_journal_path(secret_path),
            key_id,
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
            ceremony_journal_path(secret_path),
            key_id,
            ceremony_mac.0,
            retained_ceremony_ckpt,
        )
        .map_err(|_| CliError::state("CorruptOrRolledBackCeremonyJournal"))?
    };

    let mut seed_burns = FsSeedBurnTracker::open_existing(
        seed_burn_ledger_path(secret_path),
        seedburn_mac.0,
        retained_ledger_ckpt,
    )
    .map_err(|_| CliError::state("CorruptOrRolledBackLedgerCheckpoint"))?;
    let min_seed_burn_cursor = ceremony_journal
        .last_committed()
        .map_or(0, |c| c.seed_burn_cursor)
        .max(ceremony_journal.checkpoint().generation.saturating_sub(1));
    if seed_burns.checkpoint().generation < min_seed_burn_cursor {
        return Err(CliError::state("CorruptOrRolledBackLedgerCheckpoint"));
    }

    if seed_burns
        .is_burned(&seed_burn_id)
        .map_err(|_| CliError::state("CorruptOrRolledBackLedgerCheckpoint"))?
    {
        crate::vault::record_ledger_checkpoint(secret_json, seed_burns.checkpoint());
        crate::vault::record_ceremony_checkpoint(secret_json, ceremony_journal.checkpoint());
        return Ok(SeedBurn::AlreadySpent);
    }
    // Burn first: a crash may waste this slot, but must never leave a ceremony
    // cursor ahead of the durable burn ledger and block all subsequent slots.
    seed_burns
        .burn(&seed_burn_id)
        .map_err(|_| CliError::state("CorruptOrRolledBackLedgerCheckpoint"))?;
    let cursor = seed_burns.checkpoint().generation;
    let hedge_gen = cursor.max(observed_uses.saturating_add(1));
    custody_crash_point("after_seed_burn")?;
    let context = CeremonyContext {
        policy_id: base_context.policy_id,
        spend_amount: base_context.spend_amount,
        mpc_nonce_epoch: cursor,
    };
    let permit = ceremony_journal
        .persist_with_context(
            CeremonyReservation {
                ceremony_id,
                key_id,
                epoch_or_codeword: seed_burn_id,
                seed_burn_cursor: cursor,
                hedge_generation: hedge_gen,
            },
            None,
            false,
            context,
        )
        .map_err(|_| CliError::state("CorruptOrRolledBackCeremonyJournal"))?;
    custody_crash_point("after_ceremony")?;
    seed_burns
        .authorize_release(&ceremony_journal, permit)
        .map_err(|_| CliError::state("CorruptOrRolledBackLedgerCheckpoint"))?;
    seed_burns
        .begin_expansion(&ceremony_id, &seed_burn_id)
        .map_err(|_| CliError::state("CorruptOrRolledBackLedgerCheckpoint"))?;
    crate::vault::record_ledger_checkpoint(secret_json, seed_burns.checkpoint());
    crate::vault::record_ceremony_checkpoint(secret_json, ceremony_journal.checkpoint());
    Ok(SeedBurn::Fresh)
}

// Thread-local fault injection cannot affect another test or a production process.
#[cfg(test)]
std::thread_local! {
    static CUSTODY_CRASH: std::cell::Cell<Option<&'static str>> = const { std::cell::Cell::new(None) };
}

fn custody_crash_point(_point: &str) -> Result<(), CliError> {
    #[cfg(test)]
    if CUSTODY_CRASH.with(|hook| hook.get() == Some(_point)) {
        CUSTODY_CRASH.with(|hook| hook.set(None));
        return Err(CliError::state("injected custody crash"));
    }
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
  --tree-height <h>     fts-threshold: Merkle height 1..=10 (default: 10, 1024 epochs)
  --fast-demo           fts-threshold: eight-epoch disposable tree; external anchor optional
  --parties <n>         fts-threshold: number of signing parties, 2..=255 (default: 3)
  --validators <k>      agg-jorts-poseidon2: committee size (default: 8; bounded by public-key file size)
  --wal-dir <dir>       agg-jorts-poseidon2: directory in which each validator's epoch
                        write-ahead log is created (required for that scheme)
  --anchor-dir <dir>    stateful schemes: owner-only 0700 external monotone anchor directory
  --anchor-tpm-nv <base>  a TPM2 NV counter that was never incremented (tpm2_nvdefine <index>
                        -C o -s 8 -a \"authread|authwrite|no_da|nt=counter\"); committees reserve
                        validators+1 of them: validator i=base+i, ceremony=base+validators
  --anchor-vmgenid     optional snapshot/clone guard; requires disjoint --anchor-dir or TPM
  --vault-dir <dir>     explicit local custody directory verified disjoint from --anchor-dir
  --allow-single-disk-anchor  permit --anchor-dir on the same filesystem device (distinct inode);
                        it then stops a restore of the custody directory only: a volume or VM
                        snapshot rewinds the anchor with it
  --policy-ledger-dir <dir>  enroll the key against this custody policy ledger: it will then
                        sign only an intent that ledger releases (not for agg-jorts-poseidon2);
                        with --policy-anchor-dir / --policy-passphrase-* as the ledger requires
  --ephemeral-unanchored  allow disposable stateful keys without rollback protection
  --json                print the public key file contents to standard output as well
";

/// A stateful key is used with an external anchor, or its rollback protection is waived
/// by name. Stateless SLH-DSA keys need neither.
pub(crate) fn require_stateful_anchor(
    scheme: Scheme,
    anchor: Option<&crate::anchor::AnchorConfig>,
    ephemeral_unanchored: bool,
) -> Result<(), CliError> {
    if matches!(scheme, Scheme::Slh(_)) && !(anchor.is_some() && ephemeral_unanchored) {
        return Ok(());
    }
    crate::anchor::require_anchor_or_waiver(anchor.is_some(), ephemeral_unanchored, "anchor-dir")
}

/// `--validators` of a committee key (default 8), bounded by the key file size.
fn committee_validators(args: &Args) -> Result<u32, CliError> {
    let validators = args.get_u64("validators")?.unwrap_or(8);
    // A canonical validator key is 65 bytes, encoded as 130 hex digits.
    // Reserve whitespace and metadata within the reader's own file limit.
    if validators == 0
        || validators > u32::MAX as u64
        || validators
            .checked_mul(140)
            .and_then(|n| n.checked_add(4096))
            .is_none_or(|n| n > MAX_KEY_FILE_BYTES)
    {
        return Err(CliError::usage(
            "validator committee exceeds the bounded public-key file size",
        ));
    }
    Ok(validators as u32)
}

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
            "tree-height",
            "validators",
            "wal-dir",
            "passphrase-env",
            "passphrase-file",
            "anchor-dir",
            "vault-dir",
            "anchor-tpm-nv",
            "anchor-tpm-device",
            "anchor-tpm-auth-env",
            "policy-ledger-dir",
            "policy-anchor-dir",
            "policy-anchor-tpm-nv",
            "policy-anchor-tpm-device",
            "policy-anchor-tpm-auth-env",
            "policy-passphrase-env",
            "policy-passphrase-file",
        ],
        &[
            "json",
            "help",
            "deterministic-test-only",
            "force-overwrite",
            "fast-demo",
            "accept-trusted-dealer-demo",
            "allow-single-disk-anchor",
            "anchor-vmgenid",
            "anchor-vmgenid-strict",
            "ephemeral-unanchored",
            "policy-allow-single-disk-anchor",
            "policy-vmgenid",
            "policy-vmgenid-strict",
        ],
    )?;
    if args.flag("help") {
        print!("{KEYGEN_HELP}");
        return Ok(());
    }
    args.no_positionals()?;
    let scheme = Scheme::by_name(args.require("scheme")?)?;
    require_dealer_acceptance(scheme, &args)?;
    // A committee reserves one counter per validator and one for its ceremony.
    let tpm_slots = match scheme {
        Scheme::AggCommittee => committee_validators(&args)?.saturating_add(1),
        _ => 1,
    };
    crate::anchor::refuse_policy_tpm_overlap(&args, tpm_slots)?;
    let policy_pin = crate::policy_ledger::key_pin_from_args(&args)?;
    if policy_pin.is_some() && matches!(scheme, Scheme::AggCommittee) {
        return Err(CliError::usage(
            "--policy-ledger-dir does not apply to committee keys: `qsag aggregate` has no policy gate",
        ));
    }
    let anchor_cfg = crate::anchor::AnchorConfig::from_args(&args)?;
    if args.flag("fast-demo") && !matches!(scheme, Scheme::ThresholdFts) {
        return Err(CliError::usage("--fast-demo applies only to fts-threshold"));
    }
    require_stateful_anchor(
        scheme,
        anchor_cfg.as_ref(),
        args.flag("ephemeral-unanchored") || (args.flag("fast-demo") && anchor_cfg.is_none()),
    )?;
    if matches!(scheme, Scheme::Slh(_)) && anchor_cfg.is_some() {
        return Err(CliError::usage(
            "--anchor-dir applies only to stateful schemes",
        ));
    }
    crate::anchor::preflight_tpm_enrollment(anchor_cfg.as_ref(), &args, tpm_slots)?;
    let passphrase = crate::envelope::passphrase(&args)?;
    let secret_out = args.require("secret-out")?;
    let public_out = args.require("public-out")?;
    if let Some(cfg) = &anchor_cfg {
        cfg.validate_isolation(&[secret_out], &[], true)?;
    }
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
        let opened = crate::envelope::open(&old, passphrase.as_deref().map(Vec::as_slice))?;
        vault.set_key_material(&opened);
        vault.authenticate(&old)?;
        if !matches!(scheme_of(&old)?, Scheme::Slh(_)) {
            return Err(CliError::state("stateful vault overwrite refused"));
        }
    }
    let hrp = args.get("hrp").unwrap_or("qsp");
    let seed = Secret32::new(match args.get("seed-file") {
        Some(path) => {
            let text = read_bounded_file(path, MAX_KEY_FILE_BYTES)?;
            from_hex_exact(
                std::str::from_utf8(&text.0).map_err(|_| CliError::input("invalid seed text"))?,
                "seed",
            )?
        }
        None => os_random_32()?,
    });
    let entropy = Secret32::new(os_random_32()?);
    let nonce = &entropy[..16];
    let seed = if !matches!(scheme, Scheme::Slh(_)) && !args.flag("deterministic-test-only") {
        Secret32::new(cshake256_framed_32(
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
    if let Some(ledger) = &policy_pin {
        secret.push((crate::policy_ledger::KEY_PIN_FIELD, Json::hex(ledger)));
    }
    let mut public = vec![
        ("format", Json::str(PUBLIC_FORMAT)),
        ("scheme", Json::str(scheme_name)),
    ];

    let public_key: Vec<u8> = match scheme {
        Scheme::Slh(params) => {
            let (sk, pk) = slh_keygen_from_seed(&params, &seed[..])
                .map_err(|e| CliError::usage(e.to_string()))?;
            let raw_key = ZeroizingBuf::new(sk.to_bytes());
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
            let burn_mac = derive_secret(&seed, b"burn journal mac");
            FsWalFtsEpochLatch::create(burn_journal_path(secret_out), key.wal_key(), burn_mac.0)
                .map_err(|e| CliError::io("creating frontier use journal", e))?;
            let (ledger_ckpt, ceremony_ckpt, ceremony_seal) = provision_stateful_seed_burn_ledger(
                secret_out,
                key.wal_key(),
                &seed,
                anchor_cfg.as_ref(),
            )?;
            if let Some(seal) = ceremony_seal {
                secret.push(("anchor_required", Json::Bool(true)));
                secret.push(("anchor_ceremony_seal", Json::hex(&seal)));
            }
            secret.push(("ledger_checkpoint_gen", Json::num(ledger_ckpt.generation)));
            secret.push(("ledger_checkpoint_tag", Json::hex(&ledger_ckpt.tag)));
            secret.push((
                "ceremony_checkpoint_gen",
                Json::num(ceremony_ckpt.generation),
            ));
            secret.push(("ceremony_checkpoint_tag", Json::hex(&ceremony_ckpt.tag)));
            secret.push(("seed", Json::hex(&seed[..])));
            [&key.pk.pk_seed[..], &key.pk.root].concat()
        }
        Scheme::ThresholdFts => {
            secret.push((
                "custody_model",
                Json::str("local-seed-ceremony-demo; single-host shares"),
            ));
            public.push((
                "custody_model",
                Json::str("local-seed-ceremony-demo; single-host shares"),
            ));
            let parties = args.get_u64("parties")?.unwrap_or(3);
            let tree_height = match (args.flag("fast-demo"), args.get_u64("tree-height")?) {
                (true, Some(_)) => {
                    return Err(CliError::usage(
                        "pass either --fast-demo or --tree-height, not both",
                    ));
                }
                (true, None) => 3usize,
                (false, Some(h)) if (1..=10).contains(&h) => h as usize,
                (false, Some(_)) => {
                    return Err(CliError::usage(
                        "--tree-height for fts-threshold must be between 1 and 10",
                    ));
                }
                (false, None) => 10usize,
            };
            let params = qsag_fts::ParallelSeededParams {
                tree_height,
                ..THRESHOLD_FTS_PARAMS
            };
            secret.push(("tree_height", Json::num(params.tree_height)));
            public.push(("tree_height", Json::num(params.tree_height)));
            let setup = threshold_setup(&seed, parties, params, None)?;
            secret.push(("pk_seed", Json::hex(&setup.pk.pk_seed_bytes)));
            let leaves_json: Vec<Json> = setup.public_tree_layers[0]
                .iter()
                .map(encode_merkle_leaf_hex)
                .collect();
            secret.push(("merkle_leaves", Json::Array(leaves_json)));
            #[cfg(not(any(test, feature = "test-dealer")))]
            {
                let (res_gen, res_commit) =
                    write_threshold_reservoirs(secret_out, &seed, &setup, true)?;
                secret.push(("reservoir_generation", Json::num(res_gen)));
                secret.push(("reservoir_commit", Json::hex(&res_commit)));
            }
            let burn_mac = derive_secret(&seed, b"burn journal mac");
            FsWalFtsEpochLatch::create(
                burn_journal_path(secret_out),
                setup.pk.pk_seed_bytes,
                burn_mac.0,
            )
            .map_err(|e| CliError::io("creating the epoch burn journal", e))?;
            let (ledger_ckpt, ceremony_ckpt, ceremony_seal) = provision_stateful_seed_burn_ledger(
                secret_out,
                setup.pk.pk_seed_bytes,
                &seed,
                anchor_cfg.as_ref(),
            )?;
            if let Some(seal) = ceremony_seal {
                secret.push(("anchor_required", Json::Bool(true)));
                secret.push(("anchor_ceremony_seal", Json::hex(&seal)));
            }
            secret.push(("ledger_checkpoint_gen", Json::num(ledger_ckpt.generation)));
            secret.push(("ledger_checkpoint_tag", Json::hex(&ledger_ckpt.tag)));
            secret.push((
                "ceremony_checkpoint_gen",
                Json::num(ceremony_ckpt.generation),
            ));
            secret.push(("ceremony_checkpoint_tag", Json::hex(&ceremony_ckpt.tag)));
            secret.push(("seed", Json::hex(&seed[..])));
            secret.push(("parties", Json::num(parties)));
            public.push(("parties", Json::num(parties)));
            public.push(("epochs", Json::num(1u32 << params.tree_height)));
            threshold_public_bytes(&setup.pk)
        }
        Scheme::AggCommittee => {
            let validators = u64::from(committee_validators(&args)?);
            let wal_dir = args
                .get("wal-dir")
                .ok_or_else(|| CliError::usage("agg-jorts-poseidon2 requires --wal-dir"))?;
            crate::agg::enroll_committee(&seed, validators as u32, wal_dir)?;
            let keys: Vec<Json> = (0..validators as u32)
                .map(|i| Json::hex(&crate::agg::validator(&seed, i).pk.to_bytes()))
                .collect();
            let root = qsag_agg::compute_committee_root(&crate::agg::committee_from_json(&keys)?);
            let (ceremony_ckpt, ceremony_seal) = crate::agg::enroll_committee_ceremony(
                secret_out,
                &seed,
                validators as u32,
                wal_dir,
                root,
                anchor_cfg.as_ref(),
            )?;
            if let Some(seal) = ceremony_seal {
                secret.push(("anchor_required", Json::Bool(true)));
                secret.push(("anchor_ceremony_seal", Json::hex(&seal)));
            }
            secret.push((
                "ceremony_checkpoint_gen",
                Json::num(ceremony_ckpt.generation),
            ));
            secret.push(("ceremony_checkpoint_tag", Json::hex(&ceremony_ckpt.tag)));
            secret.push(("seed", Json::hex(&seed[..])));
            secret.push(("validators", Json::num(validators)));
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
    vault.set_key_material(&crate::envelope::open(&secret, None)?);
    if let Some(pass) = &passphrase {
        crate::envelope::seal(&mut secret, pass)?;
    }
    vault.bind(&mut secret)?;
    vault.prepare(&mut secret)?;
    let encoded = ZeroizingBuf::new(secret.to_pretty().into_bytes());
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
  --anchor-dir <dir>  verify and advance external monotone anchor before releasing signature
                      (stateful schemes require it unless --ephemeral-unanchored is given)
  --ephemeral-unanchored  sign with a disposable stateful key enrolled without an anchor
  --vault-dir <dir>   explicit local custody directory verified disjoint from --anchor-dir
  --allow-single-disk-anchor  permit --anchor-dir on the same filesystem device (distinct inode);
                        it then stops a restore of the custody directory only: a volume or VM
                        snapshot rewinds the anchor with it
  --policy-id-hex <hex>  32-byte policy identifier committed into CeremonyContext
  --spend-amount <n>  spend amount committed into CeremonyContext (default: 0)
  --json              print the signature file contents to standard output as well

Custody policy gate. The message must be the file `qsag policy propose` wrote. An intent
that is unapproved, over a cap, expired, bound to another key or message, or already
released is refused with exit code 3 before any key state moves. A key enrolled with
--policy-ledger-dir signs only this way. With the gate, a stateful ceremony commits the
ledger's policy digest and the intent amount, so --policy-id-hex and --spend-amount are
not accepted.

{GATE}  --policy-retry      sign an already released intent again: same key, same message, no new spend
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
    let parsed =
        ParallelSeededSignature::from_bytes_canonical(&pk.params, bytes).map_err(|_| {
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
        &[
            "secret",
            "in",
            "out",
            "ctx-hex",
            "epoch",
            "passphrase-env",
            "passphrase-file",
            "anchor-dir",
            "vault-dir",
            "anchor-tpm-nv",
            "anchor-tpm-device",
            "anchor-tpm-auth-env",
            "policy-id-hex",
            "spend-amount",
            "policy-ledger-dir",
            "policy-intent",
            "policy-anchor-dir",
            "policy-anchor-tpm-nv",
            "policy-anchor-tpm-device",
            "policy-anchor-tpm-auth-env",
            "policy-passphrase-env",
            "policy-passphrase-file",
        ],
        &[
            "deterministic",
            "json",
            "help",
            "accept-trusted-dealer-demo",
            "allow-single-disk-anchor",
            "anchor-vmgenid",
            "anchor-vmgenid-strict",
            "ephemeral-unanchored",
            "policy-allow-single-disk-anchor",
            "policy-vmgenid",
            "policy-vmgenid-strict",
            "policy-retry",
        ],
    )?;
    if args.flag("help") {
        print!(
            "{}",
            SIGN_HELP.replace("{GATE}", crate::policy_ledger::GATE_HELP)
        );
        return Ok(());
    }
    args.no_positionals()?;
    crate::anchor::refuse_policy_tpm_overlap(&args, 1)?;
    let anchor_cfg = crate::anchor::AnchorConfig::from_args(&args)?;
    let mut base_context = crate::anchor::parse_ceremony_context(&args, 0)?;
    let has_context_flags =
        args.get("policy-id-hex").is_some() || args.get("spend-amount").is_some();
    let secret_path = args.require("secret")?;
    let out_path = args.require("out")?;
    let message = read_input(args.require("in")?)?;
    // The ledger lock is taken before the key's and held until the signature is written.
    let mut gate = crate::policy_ledger::Gate::from_args(&args, true)?;
    let policy_retry = args.flag("policy-retry");
    if gate.is_none() && policy_retry {
        return Err(CliError::usage(
            "--policy-retry requires --policy-ledger-dir",
        ));
    }
    if gate.is_some() && has_context_flags {
        return Err(CliError::usage(
            "--policy-id-hex and --spend-amount are taken from the released intent under --policy-ledger-dir",
        ));
    }
    let mut vault = crate::vault::Vault::acquire(secret_path, false)?;
    let mut secret = load_json(secret_path, SECRET_FORMAT)?;
    let scheme = scheme_of(&secret)?;
    require_stateful_anchor(
        scheme,
        anchor_cfg.as_ref(),
        args.flag("ephemeral-unanchored"),
    )?;
    require_dealer_acceptance(scheme, &args)?;
    if matches!(scheme, Scheme::Slh(_)) && (anchor_cfg.is_some() || has_context_flags) {
        return Err(CliError::usage(
            "stateful ceremony options (--anchor-dir, --policy-id-hex, --spend-amount) apply only to stateful schemes",
        ));
    }
    let passphrase = crate::envelope::passphrase(&args)?;
    let opened = crate::envelope::open(&secret, passphrase.as_deref().map(Vec::as_slice))?;
    vault.set_key_material(&opened);
    vault.authenticate(&secret)?;
    crate::policy_ledger::enforce_key_pin(&secret, gate.as_ref())?;
    if !matches!(scheme, Scheme::Slh(_) | Scheme::AggCommittee) {
        crate::anchor::enforce_anchor_requirement(&secret, anchor_cfg.as_ref())?;
        if let Some(gate) = &gate {
            crate::policy_ledger::ceremony_spend(gate.intent_amount()?)?;
        }
    }
    // Release the intent for exactly this key, message and context. Called by each scheme
    // once the key is known to be able to sign and before any of its durable state moves.
    // A stateful scheme passes its ceremony context, which commits the ledger's policy
    // digest and the full 128-bit intent amount.
    let mut release = |public_key: &[u8],
                       ctx: &[u8],
                       context: Option<&mut CeremonyContext>,
                       extra: &mut Vec<(&'static str, Json)>|
     -> Result<(), CliError> {
        let Some(gate) = gate.as_mut() else {
            return Ok(());
        };
        let suite = scheme
            .suite_tag()
            .ok_or_else(|| CliError::usage("this scheme cannot sign gated policy intents"))?;
        let granted = gate.authorize(
            &crate::policy_ledger::signing_key_id(suite, public_key),
            &message,
            ctx,
            policy_retry,
        )?;
        if let Some(context) = context {
            context.policy_id = granted.policy_digest;
            context.spend_amount = crate::policy_ledger::ceremony_spend(granted.amount_units)?;
        }
        extra.push(("policy_ledger_id", Json::hex(gate.ledger_id())));
        extra.push(("policy_digest", Json::hex(&granted.policy_digest)));
        extra.push(("policy_intent", Json::hex(&granted.intent_id)));
        extra.push(("spend_amount", Json::num(granted.amount_units)));
        Ok(())
    };
    let ctx = crate::codec::from_hex(args.get("ctx-hex").unwrap_or(""))?;
    if !matches!(scheme, Scheme::Slh(_)) && !ctx.is_empty() {
        return Err(CliError::usage("--ctx-hex applies only to SLH-DSA schemes"));
    }
    let fresh = if args.flag("deterministic") {
        None
    } else {
        Some(Secret32::new(os_random_32()?))
    };
    let mut extra: Vec<(&str, Json)> = Vec::new();
    if has_context_flags {
        extra.push(("policy_id", Json::hex(&base_context.policy_id)));
        extra.push(("spend_amount", Json::num(base_context.spend_amount)));
    }

    let signature: ZeroizingBuf = match scheme {
        Scheme::Slh(params) => {
            let sk = SlhSecretKey::from_bytes_for_params(&params, opened.secret_key()?)
                .map_err(|e| CliError::input(format!("secret key: {e}")))?;
            let hedged = fresh.as_ref().map(|entropy| {
                let mut out = Secret32::new([0u8; 32]);
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
            release(&sk.public_key().to_bytes(), &ctx, None, &mut extra)?;
            let mut candidate = ZeroizingBuf::new(
                slh_sign(&params, &message, &ctx, &sk, opt_rand)
                    .map_err(|e| CliError::usage(format!("signing failed: {e}")))?,
            );
            if let Some((idx, mask)) = fault_byte
                && let Some(slot) = candidate.0.get_mut(idx)
            {
                *slot ^= mask;
            }
            let reference = ZeroizingBuf::new(
                slh_sign(&params, &message, &ctx, &sk, opt_rand)
                    .map_err(|e| CliError::usage(format!("signing failed: {e}")))?,
            );
            verify_slh_before_release(&params, &sk, &message, &ctx, &candidate, &reference)?;
            candidate
        }
        Scheme::Frontier(profile) => {
            let seed = opened.seed()?;
            let used_u64 = secret.field_u64("uses_completed")?;
            let used = u8::try_from(used_u64)
                .map_err(|_| CliError::input("uses_completed out of range"))?;
            let exhausted =
                |e: FrontierFtsError| CliError::state(format!("key can not sign again: {e:?}"));
            let mut key = frontier_key(profile, &seed)
                .resume_at(used)
                .map_err(exhausted)?;
            if key.uses_remaining() == 0 {
                return Err(exhausted(FrontierFtsError::UseBudgetExhausted));
            }
            let mut hedged = Secret32::new([0u8; 32]);
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
            // Recover the use journal before any durable state moves: a journal that
            // can not be opened or does not belong to this key must leave the seed
            // burn ledger and the vault counter exactly as they were.
            let burn_mac = derive_secret(&seed, b"burn journal mac");
            let wal = FsWalFtsEpochLatch::open_existing(
                burn_journal_path(secret_path),
                key.wal_key(),
                burn_mac.0,
            )
            .map_err(|e| CliError::io("recovering frontier use journal", e))?;
            let wal_key = key.wal_key();
            key = key.attach_wal(Box::new(wal)).map_err(exhausted)?;
            if key.uses_remaining() == 0 {
                return Err(exhausted(FrontierFtsError::UseBudgetExhausted));
            }
            release(
                &[&key.pk.pk_seed[..], &key.pk.root].concat(),
                &[],
                Some(&mut base_context),
                &mut extra,
            )?;
            // Verify retained LedgerCheckpoint against durable_ledger, burn this use's seed,
            // and seal the new LedgerCheckpoint + advanced counter into the vault BEFORE signing.
            let burn = burn_stateful_ceremony_with_checkpoint(
                secret_path,
                &mut secret,
                wal_key,
                &seed.0,
                ceremony_id,
                use_seed_id,
                base_context,
                anchor_cfg.as_ref(),
                used_u64,
            )?;
            vault.reserve(secret_path, &mut secret)?;
            if matches!(burn, SeedBurn::AlreadySpent) {
                // An earlier attempt burned this use's seed and stopped before the vault
                // counter moved. The use stays spent; the counter has now caught up, so
                // the uses after it are reachable again.
                let budget = profile.params().max_safe_uses;
                let spent = used.saturating_add(1).max(key.uses_completed());
                return Err(CliError::state(format!(
                    "use {used} was spent by an interrupted signing attempt; {} of {budget} uses remain",
                    budget.saturating_sub(spent),
                )));
            }
            let dp = FrontierDpTable::build(profile);
            let sig = key.sign(&dp, &message, &hedged.0).map_err(exhausted)?;
            extra.push(("uses_remaining", Json::num(key.uses_remaining())));
            let mut bytes = ZeroizingBuf::new(sig.to_bytes(profile));
            if let Some((idx, mask)) = fault_byte
                && let Some(slot) = bytes.0.get_mut(idx)
            {
                *slot ^= mask;
            }
            verify_frontier_bytes_before_release(&key.pk, &dp, profile, &message, &bytes)?;
            bytes
        }
        Scheme::ThresholdFts => {
            let seed = opened.seed()?;
            let used_u64 = secret.field_u64("uses_completed")?;
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
            let parties = secret.field_u64("parties")?;
            if !(2..=255).contains(&parties) {
                return Err(CliError::usage(
                    "dealerless threshold setup requires 2 <= parties <= 255",
                ));
            }
            let cached_tree = load_cached_threshold_tree(&secret, params)?;
            let burn_mac = derive_secret(&seed, b"burn journal mac");
            let mut session = Secret32::new([0u8; 32]);
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
            let (mut setup, mut journal, persisted_reservoir) =
                if let Some((cached_pk, cached_layers)) = cached_tree {
                    let pk_seed_bytes = cached_pk.pk_seed_bytes;
                    let journal = FsWalFtsEpochLatch::open_existing(
                        burn_journal_path(secret_path),
                        pk_seed_bytes,
                        burn_mac.0,
                    )
                    .map_err(|e| CliError::state(format!("epoch burn journal unavailable: {e}")))?;
                    let preloaded = if secret.get("reservoir_generation").is_some() {
                        Some(load_or_setup_threshold(
                            secret_path,
                            &secret,
                            &seed,
                            parties,
                            params,
                            cached_pk.clone(),
                            cached_layers.clone(),
                        )?)
                    } else {
                        None
                    };
                    let ceremony_id = cshake256_framed_32(
                        b"QSAG.CLI.THRESHOLD.CEREMONY.V1",
                        &[
                            &seed.0,
                            &pk_seed_bytes,
                            &epoch.to_be_bytes(),
                            &session.0,
                            &message,
                        ],
                    );
                    let epoch_seed_id = cshake256_framed_32(
                        b"QSAG.CLI.THRESHOLD.EPOCH_SEED.V1",
                        &[&seed.0, &pk_seed_bytes, &epoch.to_be_bytes()],
                    );
                    release(
                        &threshold_public_bytes(&cached_pk),
                        &[],
                        Some(&mut base_context),
                        &mut extra,
                    )?;
                    // Verify retained LedgerCheckpoint against durable_ledger, burn the epoch seed,
                    // and seal the ratcheted LedgerCheckpoint into the vault BEFORE signing.
                    let burned = burn_stateful_ceremony_with_checkpoint(
                        secret_path,
                        &mut secret,
                        pk_seed_bytes,
                        &seed.0,
                        ceremony_id,
                        epoch_seed_id,
                        base_context,
                        anchor_cfg.as_ref(),
                        used_u64,
                    )?;
                    // Retain the recovered checkpoint even when this epoch cannot sign.
                    vault.reserve(secret_path, &mut secret)?;
                    if matches!(burned, SeedBurn::AlreadySpent) {
                        return Err(CliError::state(format!("epoch {epoch} was already spent")));
                    }
                    let (setup, is_persisted) = match preloaded {
                        Some(pair) => pair,
                        None => load_or_setup_threshold(
                            secret_path,
                            &secret,
                            &seed,
                            parties,
                            params,
                            cached_pk,
                            cached_layers,
                        )?,
                    };
                    (setup, journal, is_persisted)
                } else {
                    let setup = threshold_setup(&seed, parties, params, None)?;
                    let journal = FsWalFtsEpochLatch::open_existing(
                        burn_journal_path(secret_path),
                        setup.pk.pk_seed_bytes,
                        burn_mac.0,
                    )
                    .map_err(|e| CliError::state(format!("epoch burn journal unavailable: {e}")))?;
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
                    release(
                        &threshold_public_bytes(&setup.pk),
                        &[],
                        Some(&mut base_context),
                        &mut extra,
                    )?;
                    let burned = burn_stateful_ceremony_with_checkpoint(
                        secret_path,
                        &mut secret,
                        setup.pk.pk_seed_bytes,
                        &seed.0,
                        ceremony_id,
                        epoch_seed_id,
                        base_context,
                        anchor_cfg.as_ref(),
                        used_u64,
                    )?;
                    vault.reserve(secret_path, &mut secret)?;
                    if matches!(burned, SeedBurn::AlreadySpent) {
                        return Err(CliError::state(format!("epoch {epoch} was already spent")));
                    }
                    (setup, journal, false)
                };
            let sig = setup
                .threshold_sign(epoch as u32, &message, session.0, &mut journal)
                .map_err(|e| match e {
                    ParallelSeededError::PersistenceFailed
                    | ParallelSeededError::EpochUseBudgetExhausted => {
                        CliError::state(format!("epoch {epoch} was already spent"))
                    }
                    other => CliError::usage(format!("threshold signing failed: {other:?}")),
                })?;
            #[cfg(not(any(test, feature = "test-dealer")))]
            if persisted_reservoir {
                let (next_gen, next_commit) =
                    write_threshold_reservoirs(secret_path, &seed, &setup, false)?;
                crate::vault::set(&mut secret, "reservoir_generation", Json::num(next_gen));
                crate::vault::set(&mut secret, "reservoir_commit", Json::hex(&next_commit));
                vault.commit_state(secret_path, &mut secret)?;
            }
            #[cfg(any(test, feature = "test-dealer"))]
            let _ = persisted_reservoir;
            extra.push(("epoch", Json::num(epoch)));
            let mut bytes = ZeroizingBuf::new(sig.to_bytes());
            if let Some((idx, mask)) = fault_byte
                && let Some(slot) = bytes.0.get_mut(idx)
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
    if !ctx.is_empty() && !matches!(scheme, Scheme::Slh(_)) {
        return Err(CliError::usage("--ctx-hex applies only to SLH-DSA schemes"));
    }
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
    Ok((
        scheme_of(&public)?,
        public.field_hex("public_key")?.to_vec(),
    ))
}

#[cfg(test)]
mod vault_tests {
    use super::*;
    fn ephemeral(raw: &[String]) -> Vec<String> {
        let mut args = raw.to_vec();
        if !args.iter().any(|arg| arg == "--anchor-dir") {
            args.push("--ephemeral-unanchored".into());
        }
        args
    }
    fn keygen(raw: &[String]) -> Result<(), CliError> {
        super::keygen(&ephemeral(raw))
    }
    fn sign(raw: &[String]) -> Result<(), CliError> {
        super::sign(&ephemeral(raw))
    }

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
            "fts-compact-1122".into(),
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

    /// The use journal is recovered before the seed burn ledger and the vault counter
    /// move, so a journal that can not be opened costs nothing: every durable file is
    /// byte-identical afterwards and the key signs once the journal is reachable again.
    #[test]
    fn failed_use_journal_recovery_leaves_frontier_key_usable() {
        let dir = std::env::temp_dir().join(format!(
            "qsag-journal-outage-{}",
            crate::codec::to_hex(&os_random_32().unwrap())
        ));
        std::fs::create_dir(&dir).unwrap();
        let path = |s: &str| dir.join(s).to_str().unwrap().to_owned();
        std::fs::write(path("msg"), b"signed after the outage").unwrap();
        keygen(&[
            "--scheme".into(),
            "fts-compact-1122".into(),
            "--secret-out".into(),
            path("sk"),
            "--public-out".into(),
            path("pk"),
        ])
        .unwrap();
        let command = [
            "--secret".into(),
            path("sk"),
            "--in".into(),
            path("msg"),
            "--out".into(),
            path("sig"),
        ];
        let durable = [
            "sk",
            "sk.vault.lock",
            "sk.seedburn",
            "sk.ceremony",
            "sk.burn.away",
        ];
        let snapshot = || -> Vec<Vec<u8>> {
            durable
                .iter()
                .map(|name| std::fs::read(path(name)).unwrap())
                .collect()
        };
        std::fs::rename(path("sk.burn"), path("sk.burn.away")).unwrap();
        let before = snapshot();
        for _ in 0..3 {
            let error = sign(&command).unwrap_err();
            assert!(
                error.message.contains("recovering frontier use journal"),
                "{error}"
            );
            assert!(!dir.join("sig").exists());
            assert!(!dir.join("sk.burn").exists());
            assert_eq!(snapshot(), before);
        }
        let uses = |name: &str| {
            load_json(&path("sk"), SECRET_FORMAT)
                .unwrap()
                .field_u64(name)
                .unwrap()
        };
        assert_eq!(uses("uses_completed"), 0);
        std::fs::rename(path("sk.burn.away"), path("sk.burn")).unwrap();
        sign(&command).unwrap();
        assert_eq!(uses("uses_completed"), 1);
        verify(&[
            "--public".into(),
            path("pk"),
            "--in".into(),
            path("msg"),
            "--sig".into(),
            path("sig"),
        ])
        .unwrap();
        std::fs::remove_dir_all(dir).unwrap();
    }

    /// A crash after the seed burn and before the vault counter moved leaves the ledger one
    /// use ahead of the vault. Restoring that vault cannot restore signing authority.
    #[test]
    fn interrupted_seed_burn_blocks_reuse_of_the_single_use_key() {
        let dir = std::env::temp_dir().join(format!(
            "qsag-interrupted-burn-{}",
            crate::codec::to_hex(&os_random_32().unwrap())
        ));
        std::fs::create_dir(&dir).unwrap();
        let path = |s: &str| dir.join(s).to_str().unwrap().to_owned();
        std::fs::write(path("msg"), b"second use").unwrap();
        keygen(&[
            "--scheme".into(),
            "fts-frontier-2338".into(),
            "--secret-out".into(),
            path("sk"),
            "--public-out".into(),
            path("pk"),
        ])
        .unwrap();
        let command = |out: &str| -> Vec<String> {
            vec![
                "--secret".into(),
                path("sk"),
                "--in".into(),
                path("msg"),
                "--out".into(),
                path(out),
                "--deterministic".into(),
            ]
        };
        let uses = || {
            load_json(&path("sk"), SECRET_FORMAT)
                .unwrap()
                .field_u64("uses_completed")
                .unwrap()
        };
        // The vault files as they were before the first use's seed burn.
        let vault_before = [
            std::fs::read(path("sk")).unwrap(),
            std::fs::read(path("sk.vault.lock")).unwrap(),
        ];
        sign(&command("sig0")).unwrap();
        assert_eq!(uses(), 1);
        std::fs::write(path("sk"), &vault_before[0]).unwrap();
        std::fs::write(path("sk.vault.lock"), &vault_before[1]).unwrap();
        assert_eq!(uses(), 0);

        // The durable burn remains authoritative for a single-use profile, even
        // though the vault snapshot claims that the key is fresh.
        for output in ["sig0-again", "sig1"] {
            let error = sign(&command(output)).unwrap_err();
            assert!(error.message.contains("UseBudgetExhausted"), "{error}");
            assert!(!dir.join(output).exists());
        }
        verify(&[
            "--public".into(),
            path("pk"),
            "--in".into(),
            path("msg"),
            "--sig".into(),
            path("sig0"),
        ])
        .unwrap();
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
            "fts-compact-1122".into(),
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
        return Err(CliError::usage(
            "fts-threshold requires --accept-trusted-dealer-demo: one local seed holds all shares; this is not distributed DKG custody",
        ));
    }
    Ok(())
}
#[cfg(test)]
mod custody_tests {
    use super::*;
    fn ephemeral_sign_inner(raw: &[String], fault: Option<(usize, u8)>) -> Result<(), CliError> {
        super::sign_inner(&ephemeral(raw), fault)
    }

    fn ephemeral(raw: &[String]) -> Vec<String> {
        let mut args = raw.to_vec();
        if !args.iter().any(|arg| arg == "--anchor-dir") {
            args.push("--ephemeral-unanchored".into());
        }
        args
    }
    fn keygen(raw: &[String]) -> Result<(), CliError> {
        super::keygen(&ephemeral(raw))
    }
    fn sign(raw: &[String]) -> Result<(), CliError> {
        super::sign(&ephemeral(raw))
    }

    #[test]
    fn interrupted_burn_and_ceremony_recover_and_ratchet_threshold_vault() {
        for point in ["after_seed_burn", "after_ceremony"] {
            let dir = std::env::temp_dir().join(format!(
                "qsag-custody-crash-{}",
                crate::codec::to_hex(&os_random_32().unwrap())
            ));
            std::fs::create_dir(&dir).unwrap();
            let path = |name: &str| dir.join(name).to_str().unwrap().to_owned();
            std::fs::write(path("msg"), b"crash recovery").unwrap();
            keygen(&[
                "--scheme".into(),
                "fts-threshold".into(),
                "--accept-trusted-dealer-demo".into(),
                "--fast-demo".into(),
                "--secret-out".into(),
                path("sk"),
                "--public-out".into(),
                path("pk"),
            ])
            .unwrap();
            let mut args = vec![
                "--secret".into(),
                path("sk"),
                "--in".into(),
                path("msg"),
                "--out".into(),
                path("sig"),
                "--epoch".into(),
                "1".into(),
                "--accept-trusted-dealer-demo".into(),
            ];
            CUSTODY_CRASH.with(|hook| hook.set(Some(point)));
            assert!(
                sign(&args)
                    .unwrap_err()
                    .message
                    .contains("injected custody crash")
            );
            assert!(!dir.join("sig").exists());
            assert_eq!(
                load_json(&path("sk"), SECRET_FORMAT)
                    .unwrap()
                    .field_u64("ledger_checkpoint_gen")
                    .unwrap(),
                0
            );
            // All handles from the interrupted call have closed. Reopening the
            // old vault must catch up durably even though this epoch is spent.
            assert!(sign(&args).unwrap_err().message.contains("already spent"));
            let recovered = load_json(&path("sk"), SECRET_FORMAT).unwrap();
            assert_eq!(recovered.field_u64("ledger_checkpoint_gen").unwrap(), 1);
            let mut vault = crate::vault::Vault::acquire(&path("sk"), false).unwrap();
            vault.authenticate(&recovered).unwrap();
            drop(vault);
            assert!(!dir.join("sig").exists());
            args[7] = "2".into();
            sign(&args).unwrap();
            verify(&[
                "--public".into(),
                path("pk"),
                "--in".into(),
                path("msg"),
                "--sig".into(),
                path("sig"),
            ])
            .unwrap();
            assert_eq!(
                load_json(&path("sk"), SECRET_FORMAT)
                    .unwrap()
                    .field_u64("ledger_checkpoint_gen")
                    .unwrap(),
                2
            );
            std::fs::remove_dir_all(dir).unwrap();
        }
    }

    #[test]
    fn sealed_frontier_roundtrip_preserves_ciphertext_on_reservation() {
        let dir = std::env::temp_dir().join(format!(
            "qsag-sealed-{}",
            crate::codec::to_hex(&os_random_32().unwrap())
        ));
        std::fs::create_dir(&dir).unwrap();
        let path = |name: &str| dir.join(name).to_str().unwrap().to_owned();
        std::fs::write(path("pass"), b"a test passphrase").unwrap();
        std::fs::write(path("msg"), b"sealed custody").unwrap();
        keygen(&[
            "--scheme".into(),
            "fts-compact-1122".into(),
            "--secret-out".into(),
            path("sk"),
            "--public-out".into(),
            path("pk"),
            "--passphrase-file".into(),
            path("pass"),
        ])
        .unwrap();
        let before = load_json(&path("sk"), SECRET_FORMAT).unwrap();
        let command = [
            "--secret".into(),
            path("sk"),
            "--in".into(),
            path("msg"),
            "--out".into(),
            path("sig"),
            "--passphrase-file".into(),
            path("pass"),
        ];
        std::fs::write(path("pass"), b"wrong passphrase").unwrap();
        assert!(sign(&command).is_err());
        assert_eq!(
            load_json(&path("sk"), SECRET_FORMAT)
                .unwrap()
                .field_u64("uses_completed")
                .unwrap(),
            0
        );
        std::fs::write(path("pass"), b"a test passphrase").unwrap();
        sign(&command).unwrap();
        let after = load_json(&path("sk"), SECRET_FORMAT).unwrap();
        assert_eq!(
            before.field_str("seed").unwrap(),
            after.field_str("seed").unwrap()
        );
        assert_eq!(after.field_u64("uses_completed").unwrap(), 1);
        verify(&[
            "--public".into(),
            path("pk"),
            "--in".into(),
            path("msg"),
            "--sig".into(),
            path("sig"),
        ])
        .unwrap();
        std::fs::remove_dir_all(dir).unwrap();
    }
    #[test]
    fn public_replace_failure_preserves_old_secret_and_vault() {
        let dir = std::env::temp_dir().join(format!(
            "qsag-overwrite-{}",
            crate::codec::to_hex(&os_random_32().unwrap())
        ));
        std::fs::create_dir(&dir).unwrap();
        let path = |name: &str| dir.join(name).to_str().unwrap().to_owned();
        let mut args = vec![
            "--scheme".into(),
            "slh-dsa-shake-128s".into(),
            "--secret-out".into(),
            path("sk"),
            "--public-out".into(),
            path("pk"),
        ];
        keygen(&args).unwrap();
        let original = std::fs::read(path("sk")).unwrap();
        std::fs::remove_file(path("pk")).unwrap();
        std::fs::create_dir(path("pk")).unwrap();
        args.push("--force-overwrite".into());
        assert!(keygen(&args).is_err());
        assert_eq!(original, std::fs::read(path("sk")).unwrap());
        let mut vault = crate::vault::Vault::acquire(&path("sk"), false).unwrap();
        vault
            .authenticate(&load_json(&path("sk"), SECRET_FORMAT).unwrap())
            .unwrap();
        drop(vault);
        std::fs::remove_dir_all(dir).unwrap();
    }
    #[test]
    fn accepted_threshold_demo_signs_and_rejects_epoch_reuse() {
        let dir = std::env::temp_dir().join(format!(
            "qsag-threshold-demo-{}",
            crate::codec::to_hex(&os_random_32().unwrap())
        ));
        std::fs::create_dir(&dir).unwrap();
        let path = |name: &str| dir.join(name).to_str().unwrap().to_owned();
        std::fs::write(path("msg"), b"explicit demo").unwrap();
        keygen(&[
            "--scheme".into(),
            "fts-threshold".into(),
            "--accept-trusted-dealer-demo".into(),
            "--fast-demo".into(),
            "--secret-out".into(),
            path("sk"),
            "--public-out".into(),
            path("pk"),
        ])
        .unwrap();
        let mut args = vec![
            "--secret".into(),
            path("sk"),
            "--in".into(),
            path("msg"),
            "--out".into(),
            path("sig"),
            "--epoch".into(),
            "5".into(),
        ];
        assert!(sign(&args).is_err());
        args.push("--accept-trusted-dealer-demo".into());
        sign(&args).unwrap();
        verify(&[
            "--public".into(),
            path("pk"),
            "--in".into(),
            path("msg"),
            "--sig".into(),
            path("sig"),
        ])
        .unwrap();
        assert_eq!(sign(&args).unwrap_err().code, 4);
        std::fs::remove_dir_all(dir).unwrap();
    }
    #[test]
    fn threshold_requires_explicit_acceptance() {
        let args = Args::parse(&[], &[], &["accept-trusted-dealer-demo"]).unwrap();
        assert!(require_dealer_acceptance(Scheme::ThresholdFts, &args).is_err());
        let args = Args::parse(
            &["--accept-trusted-dealer-demo".into()],
            &[],
            &["accept-trusted-dealer-demo"],
        )
        .unwrap();
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
        let slh_err = ephemeral_sign_inner(
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
            "fts-compact-1122".into(),
            "--secret-out".into(),
            path("fr.sk"),
            "--public-out".into(),
            path("fr.pk"),
        ])
        .unwrap();
        let fr_err = ephemeral_sign_inner(
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
        let th_err = ephemeral_sign_inner(&th_args, Some((40, 0x80))).unwrap_err();
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
            "1".into(),
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
            "2".into(),
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

    #[test]
    fn cli_retains_ceremony_checkpoint_and_rejects_ceremony_journal_rollback() {
        let dir = std::env::temp_dir().join(format!(
            "qsag-cli-ceremony-rollback-{}",
            crate::codec::to_hex(&os_random_32().unwrap())
        ));
        std::fs::create_dir(&dir).unwrap();
        let path = |name: &str| dir.join(name).to_str().unwrap().to_owned();
        std::fs::write(path("msg"), b"ceremony journal anti-rollback").unwrap();

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

        let genesis_ceremony = std::fs::read(path("th.sk.ceremony")).unwrap();
        sign(&[
            "--secret".into(),
            path("th.sk"),
            "--in".into(),
            path("msg"),
            "--out".into(),
            path("sig1"),
            "--epoch".into(),
            "1".into(),
            "--accept-trusted-dealer-demo".into(),
        ])
        .unwrap();

        // Overwrite `th.sk.ceremony` in-place (preserving inode) with pre-spend genesis bytes.
        std::fs::write(path("th.sk.ceremony"), &genesis_ceremony).unwrap();

        let err = sign(&[
            "--secret".into(),
            path("th.sk"),
            "--in".into(),
            path("msg"),
            "--out".into(),
            path("sig2"),
            "--epoch".into(),
            "2".into(),
            "--accept-trusted-dealer-demo".into(),
        ])
        .unwrap_err();
        assert_eq!(err.code, 4);
        assert!(
            err.message.contains("CorruptOrRolledBackCeremonyJournal"),
            "{err}"
        );
        assert!(!dir.join("sig2").exists());

        std::fs::remove_dir_all(dir).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn anchored_cli_rejects_in_place_full_vault_snapshot_rollback() {
        let dir = std::env::temp_dir().join(format!(
            "qsag-cli-anchored-rollback-{}",
            crate::codec::to_hex(&os_random_32().unwrap())
        ));
        std::fs::create_dir(&dir).unwrap();
        let vault = dir.join("vault");
        let anchor = dir.join("anchor");
        crate::cli::private_dir(vault.to_str().unwrap(), true).unwrap();
        crate::cli::private_dir(anchor.to_str().unwrap(), true).unwrap();
        let msg = dir.join("msg");
        std::fs::write(&msg, b"external anchor snapshot test").unwrap();
        let sk = vault.join("th.sk");
        let pk = dir.join("th.pk");

        keygen(&[
            "--scheme".into(),
            "fts-threshold".into(),
            "--accept-trusted-dealer-demo".into(),
            "--fast-demo".into(),
            "--secret-out".into(),
            sk.to_str().unwrap().into(),
            "--public-out".into(),
            pk.to_str().unwrap().into(),
            "--anchor-dir".into(),
            anchor.to_str().unwrap().into(),
            "--vault-dir".into(),
            vault.to_str().unwrap().into(),
            "--allow-single-disk-anchor".into(),
        ])
        .unwrap();

        // Capture a complete pre-sign snapshot of every file inside `vault` (preserving paths).
        let snapshot: Vec<(std::path::PathBuf, Vec<u8>)> = std::fs::read_dir(&vault)
            .unwrap()
            .map(|e| {
                let p = e.unwrap().path();
                let bytes = std::fs::read(&p).unwrap();
                (p, bytes)
            })
            .collect();

        // Signing without `--anchor-dir` on an enrolled key is refused.
        let missing_anchor = sign(&[
            "--secret".into(),
            sk.to_str().unwrap().into(),
            "--in".into(),
            msg.to_str().unwrap().into(),
            "--out".into(),
            dir.join("unanchored.sig").to_str().unwrap().into(),
            "--epoch".into(),
            "1".into(),
            "--accept-trusted-dealer-demo".into(),
        ])
        .unwrap_err();
        assert_eq!(missing_anchor.code, 4);

        // Legitimate anchored sign with CeremonyContext options succeeds.
        sign(&[
            "--secret".into(),
            sk.to_str().unwrap().into(),
            "--in".into(),
            msg.to_str().unwrap().into(),
            "--out".into(),
            dir.join("sig1").to_str().unwrap().into(),
            "--epoch".into(),
            "1".into(),
            "--accept-trusted-dealer-demo".into(),
            "--anchor-dir".into(),
            anchor.to_str().unwrap().into(),
            "--vault-dir".into(),
            vault.to_str().unwrap().into(),
            "--allow-single-disk-anchor".into(),
            "--policy-id-hex".into(),
            "aa".repeat(32),
            "--spend-amount".into(),
            "9000".into(),
        ])
        .unwrap();

        // Simulate a block-level VM/filesystem snapshot rollback of `vault` in-place (exact same inodes!).
        for (p, bytes) in &snapshot {
            use std::io::Write;
            let mut f = std::fs::OpenOptions::new()
                .write(true)
                .truncate(true)
                .open(p)
                .unwrap();
            f.write_all(bytes).unwrap();
            f.sync_all().unwrap();
        }

        // Re-signing epoch 1 (or even fresh epoch 2) after full vault rollback is refused by `--anchor-dir`!
        for (ep, out_name) in [("1", "replay1.sig"), ("2", "replay2.sig")] {
            let err = sign(&[
                "--secret".into(),
                sk.to_str().unwrap().into(),
                "--in".into(),
                msg.to_str().unwrap().into(),
                "--out".into(),
                dir.join(out_name).to_str().unwrap().into(),
                "--epoch".into(),
                ep.into(),
                "--accept-trusted-dealer-demo".into(),
                "--anchor-dir".into(),
                anchor.to_str().unwrap().into(),
                "--vault-dir".into(),
                vault.to_str().unwrap().into(),
                "--allow-single-disk-anchor".into(),
            ])
            .unwrap_err();
            assert_eq!(err.code, 4, "epoch {ep} must refuse rolled-back vault");
            assert!(!dir.join(out_name).exists());
        }

        std::fs::remove_dir_all(dir).unwrap();
    }
}

#[cfg(test)]
mod anchor_default_tests {
    use super::*;
    #[test]
    fn stateful_keygen_requires_explicit_custody_choice() {
        for name in ["fts-compact-1122", "fts-threshold", "agg-jorts-poseidon2"] {
            assert!(require_stateful_anchor(Scheme::by_name(name).unwrap(), None, false).is_err());
            assert!(require_stateful_anchor(Scheme::by_name(name).unwrap(), None, true).is_ok());
        }
        let error = keygen(&["--scheme".into(), "fts-compact-1122".into()]).unwrap_err();
        assert!(error.message.contains("--ephemeral-unanchored"));
        // Naming an anchor and waiving it at once is refused for every scheme.
        let anchor = crate::anchor::AnchorConfig::dir_only("anchor", None, false);
        for name in ["fts-compact-1122", "slh-dsa-shake-128s"] {
            let scheme = Scheme::by_name(name).unwrap();
            assert!(require_stateful_anchor(scheme, Some(&anchor), true).is_err());
        }
    }
}
