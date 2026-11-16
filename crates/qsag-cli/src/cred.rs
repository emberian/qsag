//! Post-quantum threshold credential & standard-verifier FIPS 204 threshold ML-DSA CLI
//! ceremonies (`qsag cred`), backed by [`qsag_cred::voprf`] and [`qsag_cred::threshold_mldsa`].
//!
//! Subcommands:
//! - `voprf-keygen` — Dealerless Poseidon2 TOPRF setup with encrypted party bundles: the
//!   replicated five-server backend, or the Shamir-SPDZ backend for any `2 <= t <= n <= 64`.
//! - `voprf-eval` — Blinded client query and evaluation with durable monotone counter
//!   reservation: all five servers (replicated), or any `t` persisted shares (Shamir-SPDZ).
//! - `mldsa-keygen` — Dealerless `(t, n)` threshold FIPS 204 ML-DSA (`44`/`65`/`87`) setup:
//!   replicated key shares up to sixteen custodians, Shamir key shares up to sixty-four.
//! - `mldsa-sign` — Sealed-`w1` abort-private `(2t - 1)`-of-`n` threshold FIPS 204 signing
//!   with crash-atomic [`FsNonceBurnStore`] persistence.
//! - `mldsa-verify` — Standard unmodified FIPS 204 `ml_dsa_verify` check.

use std::collections::BTreeMap;
use std::io;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Condvar, Mutex};

use qsag_accel::ct::{ct_eq_bytes, ct_zeroize_bytes};
use qsag_accel::keccak::cshake256_framed_32;
use qsag_asm::durable::LockedRecord;
use qsag_core::wipe::SecretBuffer;
use qsag_core::{ExternalMonotoneAnchor, LedgerCheckpoint};
use qsag_cred::voprf::{self, CounterStore, PublicKey as ToprfPublicKey, SERVERS as TOPRF_SERVERS};
use qsag_cred::voprf_spdz::{
    SpdzConfig, SpdzPublic, SpdzServer, SpdzSession, spdz_blind, spdz_dkg,
};
use qsag_cred::{
    FsNonceBurnStore, MlDsaLevel, MpcTransport, MpcTransportError, NonceBurnPersistence,
    RoundInbox, RoundInfo, RoundKind, ThresholdMlDsaDkgConfig, ThresholdMlDsaError,
    ThresholdMlDsaSignerShare, ThresholdSignSession, ThresholdVerificationPack, ml_dsa_verify,
    threshold_mldsa_dkg_party, threshold_mldsa_shamir_expand_party, threshold_sign_mldsa_party,
};

use crate::anchor::{
    ANCHOR_FLAG_OPTIONS, ANCHOR_NO_VAULT_VALUE_OPTIONS, AnchorConfig, FsExternalMountAnchor,
    enforce_anchor_requirement, require_anchor_or_waiver,
};
use crate::cli::{
    Args, CliError, MAX_KEY_FILE_BYTES, MAX_SIG_PROOF_BYTES, Secret32, ZeroizingBuf, os_random_32,
    private_dir, read_bounded_file, read_input, write_new,
};
use crate::codec::{Json, from_hex, from_hex_exact, to_hex};

const CRED_HELP: &str = "\
qsag cred <subcommand> [options]

Post-quantum threshold credential & standard-verifier FIPS 204 threshold ML-DSA ceremonies:
  voprf-keygen  run dealerless Poseidon2 TOPRF setup: replicated (2, 5), or Shamir-SPDZ (t, n <= 64)
  voprf-eval    evaluate from persisted TOPRF party bundles: all five, or any t (Shamir-SPDZ)
  mldsa-keygen  run dealerless (t, n) threshold FIPS 204 ML-DSA key generation (44 / 65 / 87)
  mldsa-sign    co-sign a message with >= 2t - 1 threshold ML-DSA custodians (sealed-w1 ZK)
  mldsa-verify  verify a standard FIPS 204 ML-DSA signature against the threshold public key
";

const VOPRF_SHARE_FORMAT: &str = "qsag-cred-voprf-share-v1";
const VOPRF_SPDZ_SHARE_FORMAT: &str = "qsag-cred-voprf-spdz-share-v1";
const VOPRF_RSS_SCHEME: &str = "voprf-poseidon2-2of5";
const VOPRF_SPDZ_SCHEME: &str = "voprf-poseidon2-shamir-spdz";
const VOPRF_SPDZ_BACKEND: &str = "shamir-spdz";
const VOPRF_META_FORMAT: &str = "qsag-cred-voprf-meta-v1";
const VOPRF_PUB_FORMAT: &str = "qsag-cred-voprf-public-v1";
const VOPRF_EVAL_FORMAT: &str = "qsag-cred-voprf-eval-v1";
const VOPRF_SHARE_MAGIC: &[u8; 8] = b"QSVPSH02";
const TOPRF_COUNTER_MAGIC: &[u8; 8] = b"QSTOPRF1";
const TOPRF_COUNTER_BODY_LEN: usize = 8 + 32 + 8 + 8 + 1 + 8 + 8 + 8;
const TOPRF_COUNTER_RECORD_LEN: usize = TOPRF_COUNTER_BODY_LEN + 32;
const CRED_PSTATE_MAGIC: &[u8; 8] = b"QSCRPST1";
const CRED_PSTATE_MAX_PARTIES: usize = 256;

const MLDSA_META_FORMAT: &str = "qsag-cred-mldsa-meta-v1";
const MLDSA_PUB_FORMAT: &str = "qsag-cred-mldsa-public-v1";
const MLDSA_SIG_FORMAT: &str = "qsag-cred-mldsa-signature-v1";

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

fn read_input_arg(args: &Args) -> Result<ZeroizingBuf, CliError> {
    match (args.get("in"), args.get("message")) {
        (Some(_), Some(_)) => Err(CliError::usage("pass either --in or --message, not both")),
        (Some(p), None) | (None, Some(p)) => read_input(p),
        (None, None) => Err(CliError::usage(
            "missing required option --in <path|-> (or --message <path|->)",
        )),
    }
}

// ---------------------------------------------------------------------------
// In-process synchronous channels for multi-custodian local vault execution
// ---------------------------------------------------------------------------

#[derive(Default)]
struct ToprfPhaseSlot {
    arrivals: usize,
    private: [Option<[Vec<u8>; TOPRF_SERVERS]>; TOPRF_SERVERS],
    broadcast: [Option<Vec<u8>>; TOPRF_SERVERS],
    aborted: bool,
}

impl Drop for ToprfPhaseSlot {
    fn drop(&mut self) {
        for arr in self.private.iter_mut().flatten() {
            for buf in arr {
                ct_zeroize_bytes(buf);
            }
        }
        for buf in self.broadcast.iter_mut().flatten() {
            ct_zeroize_bytes(buf);
        }
    }
}

struct SharedToprfHub {
    aborted: AtomicBool,
    phases: Mutex<BTreeMap<([u8; 32], bool), ToprfPhaseSlot>>,
    cv: Condvar,
}

impl SharedToprfHub {
    fn new() -> Arc<Self> {
        Arc::new(Self {
            aborted: AtomicBool::new(false),
            phases: Mutex::new(BTreeMap::new()),
            cv: Condvar::new(),
        })
    }

    fn abort_all(&self) {
        self.aborted.store(true, Ordering::Release);
        if let Ok(mut map) = self.phases.lock() {
            for slot in map.values_mut() {
                slot.aborted = true;
            }
            self.cv.notify_all();
        }
    }
}

struct LocalToprfEndpoint {
    party: usize,
    hub: Arc<SharedToprfHub>,
}

impl voprf::Transport for LocalToprfEndpoint {
    fn exchange(
        &mut self,
        phase: [u8; 32],
        outgoing: [Vec<u8>; TOPRF_SERVERS],
    ) -> Result<[Vec<u8>; TOPRF_SERVERS], voprf::Error> {
        let key = (phase, false);
        let mut guard = self
            .hub
            .phases
            .lock()
            .map_err(|_| voprf::Error::Transport)?;
        {
            let slot = guard.entry(key).or_default();
            if self.hub.aborted.load(Ordering::Acquire)
                || slot.aborted
                || slot.private[self.party].is_some()
            {
                return Err(voprf::Error::Transport);
            }
            slot.private[self.party] = Some(outgoing);
            slot.arrivals += 1;
            if slot.arrivals == TOPRF_SERVERS {
                self.hub.cv.notify_all();
            }
        }
        loop {
            let slot = guard.get(&key).ok_or(voprf::Error::Transport)?;
            // A round every server completed is delivered even if a peer has
            // already failed on it and aborted: the abort only stops later rounds.
            if slot.arrivals == TOPRF_SERVERS {
                let inbox = core::array::from_fn(|sender| {
                    slot.private[sender]
                        .as_ref()
                        .map(|msgs| msgs[self.party].clone())
                        .unwrap_or_default()
                });
                return Ok(inbox);
            }
            if self.hub.aborted.load(Ordering::Acquire) || slot.aborted {
                return Err(voprf::Error::Transport);
            }
            guard = self
                .hub
                .cv
                .wait(guard)
                .map_err(|_| voprf::Error::Transport)?;
        }
    }

    fn broadcast(
        &mut self,
        phase: [u8; 32],
        message: Vec<u8>,
    ) -> Result<[Vec<u8>; TOPRF_SERVERS], voprf::Error> {
        let key = (phase, true);
        let mut guard = self
            .hub
            .phases
            .lock()
            .map_err(|_| voprf::Error::Transport)?;
        {
            let slot = guard.entry(key).or_default();
            if self.hub.aborted.load(Ordering::Acquire)
                || slot.aborted
                || slot.broadcast[self.party].is_some()
            {
                return Err(voprf::Error::Transport);
            }
            slot.broadcast[self.party] = Some(message);
            slot.arrivals += 1;
            if slot.arrivals == TOPRF_SERVERS {
                self.hub.cv.notify_all();
            }
        }
        loop {
            let slot = guard.get(&key).ok_or(voprf::Error::Transport)?;
            // A round every server completed is delivered even if a peer has
            // already failed on it and aborted: the abort only stops later rounds.
            if slot.arrivals == TOPRF_SERVERS {
                let inbox = core::array::from_fn(|sender| {
                    slot.broadcast[sender].clone().unwrap_or_default()
                });
                return Ok(inbox);
            }
            if self.hub.aborted.load(Ordering::Acquire) || slot.aborted {
                return Err(voprf::Error::Transport);
            }
            guard = self
                .hub
                .cv
                .wait(guard)
                .map_err(|_| voprf::Error::Transport)?;
        }
    }
}

/// Vault-wide external monotone anchor + MAC-authenticated per-party generation ledger (`QSCRPST1`),
/// binding every custodian's durable burn/counter generation AND the vault-wide high-water
/// counter/epoch into a single [`FsExternalMountAnchor`] (`--anchor-dir`, `--anchor-tpm-nv`,
/// `--anchor-vmgenid`).
struct VaultPartyGenAnchor {
    anchor: FsExternalMountAnchor,
    pstate_record: LockedRecord,
    domain: &'static str,
    domain_hash: [u8; 32],
    key_id: [u8; 32],
    pstate_mac_key: Secret32,
    parties: usize,
    total_steps: u64,
    high_water: Option<u64>,
    party_gens: Vec<u64>,
}

fn cred_anchor_subkeys(
    root_mac: &[u8; 32],
    domain: &str,
    key_id: &[u8; 32],
) -> (Secret32, Secret32) {
    let anchor_mac = Secret32::new(cshake256_framed_32(
        b"QSAG.CLI.CRED.ANCHOR_MAC.V1",
        &[root_mac, domain.as_bytes(), key_id],
    ));
    let pstate_mac = Secret32::new(cshake256_framed_32(
        b"QSAG.CLI.CRED.PSTATE_MAC.V1",
        &[root_mac, domain.as_bytes(), key_id],
    ));
    (anchor_mac, pstate_mac)
}

fn cred_pstate_path(
    anchor_cfg: &AnchorConfig,
    vault_dir: &str,
    domain: &str,
    key_id: &[u8; 32],
) -> PathBuf {
    let digest = cshake256_framed_32(
        b"QSAG.CLI.CRED.PSTATE.SLOT.V1",
        &[domain.as_bytes(), key_id],
    );
    let hex_id = to_hex(&digest);
    match &anchor_cfg.anchor_dir {
        Some(dir) => Path::new(dir).join(format!("{domain}-{hex_id}.pstate")),
        None => Path::new(vault_dir).join(format!(".qsag-{domain}-{hex_id}.pstate")),
    }
}

impl VaultPartyGenAnchor {
    fn encode_pstate(&self) -> Vec<u8> {
        let body_len = 8 + 32 + 32 + 8 + 8 + 1 + 8 + 8 * self.parties;
        let mut buf = Vec::with_capacity(body_len + 32);
        buf.extend_from_slice(CRED_PSTATE_MAGIC);
        buf.extend_from_slice(&self.domain_hash);
        buf.extend_from_slice(&self.key_id);
        buf.extend_from_slice(&(self.parties as u64).to_le_bytes());
        buf.extend_from_slice(&self.total_steps.to_le_bytes());
        match self.high_water {
            Some(hw) => {
                buf.push(1);
                buf.extend_from_slice(&hw.to_le_bytes());
            }
            None => {
                buf.push(0);
                buf.extend_from_slice(&0u64.to_le_bytes());
            }
        }
        for &g in &self.party_gens {
            buf.extend_from_slice(&g.to_le_bytes());
        }
        let seal = self.pstate_record.lock_identity_seal();
        let mac = cshake256_framed_32(
            b"QSAG.CLI.CRED.PSTATE.RECORD.V1",
            &[&self.pstate_mac_key.0, &seal, &buf],
        );
        buf.extend_from_slice(&mac);
        buf
    }

    fn checkpoint_for(&self, encoded_pstate: &[u8]) -> io::Result<LedgerCheckpoint> {
        let generation = self
            .total_steps
            .checked_add(1)
            .ok_or_else(|| io::Error::other("cred anchor generation overflow"))?;
        let tag = cshake256_framed_32(
            b"QSAG.CLI.CRED.ANCHOR.TAG.V1",
            &[
                self.domain.as_bytes(),
                &self.key_id,
                &generation.to_le_bytes(),
                encoded_pstate,
            ],
        );
        Ok(LedgerCheckpoint { generation, tag })
    }

    fn create(
        anchor_cfg: &AnchorConfig,
        vault_dir: &str,
        domain: &'static str,
        key_id: [u8; 32],
        root_mac: &[u8; 32],
        parties: usize,
    ) -> Result<[u8; 24], CliError> {
        if parties == 0 || parties > CRED_PSTATE_MAX_PARTIES {
            return Err(CliError::usage("party count exceeds anchor ledger bound"));
        }
        let (anchor_mac, pstate_mac_key) = cred_anchor_subkeys(root_mac, domain, &key_id);
        let anchor = FsExternalMountAnchor::provision_fresh(
            anchor_cfg,
            &[],
            &[vault_dir],
            domain,
            key_id,
            anchor_mac.0,
        )?;
        let pstate_path = cred_pstate_path(anchor_cfg, vault_dir, domain, &key_id);
        let pstate_record = LockedRecord::create_new(&pstate_path).map_err(|e| {
            CliError::state(format!(
                "enrolling external party-state ledger ({domain}): {e}"
            ))
        })?;
        let domain_hash = cshake256_framed_32(b"QSAG.CLI.CRED.DOMAIN.V1", &[domain.as_bytes()]);
        let this = Self {
            anchor,
            pstate_record,
            domain,
            domain_hash,
            key_id,
            pstate_mac_key,
            parties,
            total_steps: 0,
            high_water: None,
            party_gens: vec![0; parties],
        };
        let encoded = this.encode_pstate();
        this.pstate_record.replace(&encoded).map_err(|e| {
            CliError::state(format!(
                "writing initial external party-state ({domain}): {e}"
            ))
        })?;
        let ckpt = this
            .checkpoint_for(&encoded)
            .map_err(|e| CliError::state(format!("computing initial anchor checkpoint: {e}")))?;
        this.anchor.advance(ckpt).map_err(|e| {
            CliError::state(format!("initializing external anchor ({domain}): {e}"))
        })?;
        Ok(this.anchor.lock_identity_seal())
    }

    fn open(
        anchor_cfg: &AnchorConfig,
        vault_dir: &str,
        meta: &Json,
        domain: &'static str,
        key_id: [u8; 32],
        root_mac: &[u8; 32],
        parties: usize,
    ) -> Result<Arc<Mutex<Self>>, CliError> {
        if parties == 0 || parties > CRED_PSTATE_MAX_PARTIES {
            return Err(CliError::state("invalid party count in anchored vault"));
        }
        let (anchor_mac, pstate_mac_key) = cred_anchor_subkeys(root_mac, domain, &key_id);
        let anchor = FsExternalMountAnchor::open_existing(
            anchor_cfg,
            &[],
            &[vault_dir],
            domain,
            key_id,
            anchor_mac.0,
        )?;
        anchor.verify_expected_seal(meta, "anchor_ceremony_seal")?;
        let ckpt = anchor
            .load()
            .map_err(|e| {
                CliError::state(format!("ExternalAnchorRollbackOrCorrupt ({domain}): {e}"))
            })?
            .ok_or_else(|| CliError::state(format!("ExternalAnchorMissingState ({domain})")))?;

        let pstate_path = cred_pstate_path(anchor_cfg, vault_dir, domain, &key_id);
        let pstate_record = LockedRecord::open_existing(&pstate_path).map_err(|e| {
            CliError::state(format!(
                "ExternalAnchorUnavailableOrCorrupt ({domain} pstate): {e}"
            ))
        })?;
        let expected_len = 8 + 32 + 32 + 8 + 8 + 1 + 8 + 8 * parties + 32;
        let bytes = pstate_record.read_bounded(expected_len).map_err(|e| {
            CliError::state(format!(
                "ExternalAnchorUnavailableOrCorrupt ({domain} pstate): {e}"
            ))
        })?;
        if bytes.len() != expected_len {
            return Err(CliError::state("ExternalAnchorPartyStateLengthMismatch"));
        }
        let (body, stored_mac) = bytes.split_at(expected_len - 32);
        let seal = pstate_record.lock_identity_seal();
        let expected_mac = Secret32::new(cshake256_framed_32(
            b"QSAG.CLI.CRED.PSTATE.RECORD.V1",
            &[&pstate_mac_key.0, &seal, body],
        ));
        if !ct_eq_bytes(stored_mac, &expected_mac.0) {
            return Err(CliError::state("ExternalAnchorPartyStateMacMismatch"));
        }
        let domain_hash = cshake256_framed_32(b"QSAG.CLI.CRED.DOMAIN.V1", &[domain.as_bytes()]);
        if &body[..8] != CRED_PSTATE_MAGIC
            || !ct_eq_bytes(&body[8..40], &domain_hash)
            || !ct_eq_bytes(&body[40..72], &key_id)
        {
            return Err(CliError::state("ExternalAnchorPartyStateHeaderMismatch"));
        }
        let stored_parties = usize::try_from(u64::from_le_bytes(body[72..80].try_into().unwrap()))
            .map_err(|_| CliError::input("party count out of range"))?;
        if stored_parties != parties {
            return Err(CliError::state("ExternalAnchorPartyCountMismatch"));
        }
        let total_steps = u64::from_le_bytes(body[80..88].try_into().unwrap());
        let hw_raw = u64::from_le_bytes(body[89..97].try_into().unwrap());
        let high_water = match body[88] {
            0 => {
                if hw_raw != 0 || total_steps != 0 {
                    return Err(CliError::state("ExternalAnchorPartyStateCorrupt"));
                }
                None
            }
            1 => {
                if total_steps == 0 {
                    return Err(CliError::state("ExternalAnchorPartyStateCorrupt"));
                }
                Some(hw_raw)
            }
            _ => return Err(CliError::state("ExternalAnchorPartyStateCorrupt")),
        };
        let mut party_gens = Vec::with_capacity(parties);
        let mut gen_sum = 0u64;
        for p in 0..parties {
            let off = 97 + p * 8;
            let g = u64::from_le_bytes(body[off..off + 8].try_into().unwrap());
            gen_sum = gen_sum
                .checked_add(g)
                .ok_or_else(|| CliError::state("ExternalAnchorPartyStateOverflow"))?;
            party_gens.push(g);
        }
        if gen_sum != total_steps {
            return Err(CliError::state("ExternalAnchorPartyStateStepSumMismatch"));
        }
        let this = Self {
            anchor,
            pstate_record,
            domain,
            domain_hash,
            key_id,
            pstate_mac_key,
            parties,
            total_steps,
            high_water,
            party_gens,
        };
        let expected_ckpt = this
            .checkpoint_for(&bytes)
            .map_err(|_| CliError::state("ExternalAnchorCheckpointOverflow"))?;
        if ckpt.generation != expected_ckpt.generation
            || !ct_eq_bytes(&ckpt.tag, &expected_ckpt.tag)
        {
            return Err(CliError::state("ExternalAnchorDetectedRollback"));
        }
        Ok(Arc::new(Mutex::new(this)))
    }

    fn party_min_gen(&self, party: usize) -> Result<u64, CliError> {
        self.party_gens
            .get(party)
            .copied()
            .ok_or_else(|| CliError::state("party index out of bounds in anchor state"))
    }

    fn high_water(&self) -> Option<u64> {
        self.high_water
    }

    fn record_step(
        &mut self,
        party: usize,
        next_party_gen: u64,
        counter_or_epoch: u64,
    ) -> io::Result<()> {
        let prev_gen = *self
            .party_gens
            .get(party)
            .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidInput, "party out of bounds"))?;
        if next_party_gen <= prev_gen {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "party generation did not advance monotonically",
            ));
        }
        let delta = next_party_gen - prev_gen;
        let next_steps = self
            .total_steps
            .checked_add(delta)
            .ok_or_else(|| io::Error::other("total_steps overflow"))?;
        self.party_gens[party] = next_party_gen;
        self.total_steps = next_steps;
        self.high_water = Some(
            self.high_water
                .map_or(counter_or_epoch, |hw| hw.max(counter_or_epoch)),
        );
        let encoded = self.encode_pstate();
        self.pstate_record.replace(&encoded)?;
        let ckpt = self.checkpoint_for(&encoded)?;
        self.anchor.advance(ckpt)
    }
}

#[derive(Clone, Copy)]
struct ToprfCounterState {
    generation: u64,
    high_water: Option<u64>,
    used_items: u64,
    quota: u64,
}

/// Exclusive `LockedRecord`-backed, `cSHAKE256`-authenticated TOPRF monotone counter & evaluation
/// quota ledger (`QSTOPRF1`), bound to `(commitment, party, lock_identity_seal)` and optionally
/// ratcheted onto a [`VaultPartyGenAnchor`].
struct FsToprfCounterStore {
    record: LockedRecord,
    expected_key: [u8; 32],
    expected_party: usize,
    mac_key: Secret32,
    vault_anchor: Option<Arc<Mutex<VaultPartyGenAnchor>>>,
}

impl FsToprfCounterStore {
    fn encode_record(
        record: &LockedRecord,
        key: &[u8; 32],
        party: usize,
        mac_key: &Secret32,
        st: ToprfCounterState,
    ) -> [u8; TOPRF_COUNTER_RECORD_LEN] {
        let mut body = [0u8; TOPRF_COUNTER_BODY_LEN];
        body[..8].copy_from_slice(TOPRF_COUNTER_MAGIC);
        body[8..40].copy_from_slice(key);
        body[40..48].copy_from_slice(&(party as u64).to_le_bytes());
        body[48..56].copy_from_slice(&st.generation.to_le_bytes());
        match st.high_water {
            Some(hw) => {
                body[56] = 1;
                body[57..65].copy_from_slice(&hw.to_le_bytes());
            }
            None => {
                body[56] = 0;
            }
        }
        body[65..73].copy_from_slice(&st.used_items.to_le_bytes());
        body[73..81].copy_from_slice(&st.quota.to_le_bytes());
        let seal = record.lock_identity_seal();
        let mac = cshake256_framed_32(
            b"QSAG.CLI.TOPRF.COUNTER.MAC.V1",
            &[&mac_key.0, &seal, &body],
        );
        let mut out = [0u8; TOPRF_COUNTER_RECORD_LEN];
        out[..TOPRF_COUNTER_BODY_LEN].copy_from_slice(&body);
        out[TOPRF_COUNTER_BODY_LEN..].copy_from_slice(&mac);
        out
    }

    fn create(
        path: &str,
        commitment: [u8; 32],
        party: usize,
        mac_key: [u8; 32],
        quota: u64,
    ) -> Result<(), CliError> {
        if quota == 0 || quota > voprf::MAX_EVALUATIONS_PER_KEY {
            return Err(CliError::usage(format!(
                "--max-evaluations must be in 1..={}",
                voprf::MAX_EVALUATIONS_PER_KEY
            )));
        }
        let key_secret = Secret32::new(mac_key);
        let record = LockedRecord::create_new(path)
            .map_err(|e| CliError::io(format_args!("creating TOPRF counter {path}"), e))?;
        let init = ToprfCounterState {
            generation: 0,
            high_water: None,
            used_items: 0,
            quota,
        };
        let encoded = Self::encode_record(&record, &commitment, party, &key_secret, init);
        record
            .replace(&encoded)
            .map_err(|e| CliError::io(format_args!("initializing TOPRF counter {path}"), e))
    }

    fn open_at_least(
        path: &str,
        commitment: [u8; 32],
        party: usize,
        mac_key: [u8; 32],
        min_generation: u64,
        vault_anchor: Option<Arc<Mutex<VaultPartyGenAnchor>>>,
    ) -> Result<Self, CliError> {
        let key_secret = Secret32::new(mac_key);
        let record = LockedRecord::open_existing(path)
            .map_err(|e| CliError::state(format!("opening TOPRF counter ledger {path}: {e}")))?;
        let store = Self {
            record,
            expected_key: commitment,
            expected_party: party,
            mac_key: key_secret,
            vault_anchor,
        };
        let st = store.read_verified_state().map_err(|_| {
            CliError::state("TOPRF counter ledger failed authentication or is corrupt")
        })?;
        if st.generation < min_generation {
            return Err(CliError::state(
                "ExternalAnchorDetectedRollback: TOPRF counter generation behind external anchor",
            ));
        }
        Ok(store)
    }

    fn read_verified_state(&self) -> Result<ToprfCounterState, voprf::Error> {
        let bytes = self
            .record
            .read_bounded(TOPRF_COUNTER_RECORD_LEN)
            .map_err(|_| voprf::Error::Counter)?;
        if bytes.len() != TOPRF_COUNTER_RECORD_LEN {
            return Err(voprf::Error::Counter);
        }
        let body = &bytes[..TOPRF_COUNTER_BODY_LEN];
        let stored_mac = &bytes[TOPRF_COUNTER_BODY_LEN..];
        let seal = self.record.lock_identity_seal();
        let expected_mac = Secret32::new(cshake256_framed_32(
            b"QSAG.CLI.TOPRF.COUNTER.MAC.V1",
            &[&self.mac_key.0, &seal, body],
        ));
        if !ct_eq_bytes(stored_mac, &expected_mac.0)
            || &body[..8] != TOPRF_COUNTER_MAGIC
            || !ct_eq_bytes(&body[8..40], &self.expected_key)
        {
            return Err(voprf::Error::Counter);
        }
        let party = usize::try_from(u64::from_le_bytes(body[40..48].try_into().unwrap()))
            .map_err(|_| voprf::Error::Counter)?;
        if party != self.expected_party {
            return Err(voprf::Error::Counter);
        }
        let generation = u64::from_le_bytes(body[48..56].try_into().unwrap());
        let hw_raw = u64::from_le_bytes(body[57..65].try_into().unwrap());
        let used_items = u64::from_le_bytes(body[65..73].try_into().unwrap());
        let quota = u64::from_le_bytes(body[73..81].try_into().unwrap());
        if quota == 0 || quota > voprf::MAX_EVALUATIONS_PER_KEY || used_items > quota {
            return Err(voprf::Error::Counter);
        }
        let high_water = match body[56] {
            0 => {
                if hw_raw != 0 || generation != 0 || used_items != 0 {
                    return Err(voprf::Error::Counter);
                }
                None
            }
            1 => {
                if hw_raw == u64::MAX || generation == 0 || used_items == 0 {
                    return Err(voprf::Error::Counter);
                }
                Some(hw_raw)
            }
            _ => return Err(voprf::Error::Counter),
        };
        Ok(ToprfCounterState {
            generation,
            high_water,
            used_items,
            quota,
        })
    }
}

impl CounterStore for FsToprfCounterStore {
    fn high_water(&self) -> Result<Option<u64>, voprf::Error> {
        self.read_verified_state().map(|st| st.high_water)
    }

    fn reserve(
        &mut self,
        key: &[u8; 32],
        party: usize,
        counter: u64,
        items: usize,
    ) -> Result<(), voprf::Error> {
        if !ct_eq_bytes(key, &self.expected_key)
            || party != self.expected_party
            || items == 0
            || counter == u64::MAX
        {
            return Err(voprf::Error::Counter);
        }
        let st = self.read_verified_state()?;
        match st.high_water {
            Some(hw) => {
                if counter <= hw || counter > hw.saturating_add(voprf::MAX_COUNTER_WINDOW) {
                    return Err(voprf::Error::Counter);
                }
            }
            None => {
                if counter >= voprf::MAX_COUNTER_WINDOW {
                    return Err(voprf::Error::Counter);
                }
            }
        }
        let next_used = st
            .used_items
            .checked_add(items as u64)
            .ok_or(voprf::Error::Quota)?;
        if next_used > st.quota {
            return Err(voprf::Error::Quota);
        }
        let next_gen = st.generation.checked_add(1).ok_or(voprf::Error::Counter)?;
        let next = ToprfCounterState {
            generation: next_gen,
            high_water: Some(counter),
            used_items: next_used,
            quota: st.quota,
        };
        let encoded = Self::encode_record(
            &self.record,
            &self.expected_key,
            self.expected_party,
            &self.mac_key,
            next,
        );
        self.record
            .replace(&encoded)
            .map_err(|_| voprf::Error::Counter)?;
        if let Some(anchor) = &self.vault_anchor {
            let mut guard = anchor.lock().map_err(|_| voprf::Error::Counter)?;
            guard
                .record_step(self.expected_party, next_gen, counter)
                .map_err(|_| voprf::Error::Counter)?;
        }
        Ok(())
    }
}

fn voprf_meta_path(vault_dir: &str) -> String {
    Path::new(vault_dir)
        .join("voprf-meta.json")
        .to_string_lossy()
        .into_owned()
}

fn voprf_share_path(vault_dir: &str, party: usize) -> String {
    Path::new(vault_dir)
        .join(format!("voprf-party-{party}.share"))
        .to_string_lossy()
        .into_owned()
}

fn voprf_counter_path(vault_dir: &str, party: usize) -> String {
    Path::new(vault_dir)
        .join(format!("voprf-counter-{party}.json"))
        .to_string_lossy()
        .into_owned()
}

/// Seal one party's secret bundle under the passphrase (if any), bind it to its
/// vault lock and write it. Shared by the TOPRF and ML-DSA custody formats.
fn write_party_bundle(
    path: &str,
    mut bundle: Json,
    passphrase: Option<&[u8]>,
    limit: u64,
) -> Result<(), CliError> {
    if let Some(pass) = passphrase {
        crate::envelope::seal(&mut bundle, pass)?;
    }
    let mut lock = crate::vault::Vault::acquire(path, true)?;
    let opened = crate::envelope::open(&bundle, passphrase)?;
    lock.set_key_material(&opened);
    lock.bind(&mut bundle)?;
    lock.seal(&mut bundle)?;
    let encoded = ZeroizingBuf::new(bundle.to_pretty().into_bytes());
    if encoded.len() as u64 > limit {
        return Err(CliError::input("party share bundle exceeds file bound"));
    }
    write_new(path, &encoded, true)
}

/// Open and authenticate one party's secret bundle. The lock is held by the caller
/// for as long as the secret is in use.
fn open_party_bundle(
    path: &str,
    format: &str,
    limit: u64,
    passphrase: Option<&[u8]>,
) -> Result<(crate::vault::Vault, Json, crate::envelope::OpenedSecret), CliError> {
    let mut lock = crate::vault::Vault::acquire(path, false)?;
    let bundle = load_json_checked(path, format, limit)?;
    let opened = crate::envelope::open(&bundle, passphrase)?;
    lock.set_key_material(&opened);
    lock.authenticate(&bundle)?;
    Ok((lock, bundle, opened))
}

/// Enrollment facts every TOPRF party bundle is bound to.
struct VoprfEnrollment<'a> {
    share_format: &'a str,
    scheme: &'a str,
    threshold: usize,
    parties: usize,
    session: [u8; 32],
    commitment: [u8; 32],
    quota: u64,
}

/// Write one party's encrypted, vault-bound share bundle and its authenticated `LockedRecord` counter file.
#[allow(clippy::too_many_arguments)]
fn write_voprf_bundle(
    vault_dir: &str,
    party: usize,
    enrollment: &VoprfEnrollment<'_>,
    counter_mac_key: &Secret32,
    vault_anchor_mac: &Secret32,
    server_secret: &[u8],
    passphrase: Option<&[u8]>,
) -> Result<(), CliError> {
    let mut payload = ZeroizingBuf::new(Vec::with_capacity(8 + 64 + server_secret.len()));
    payload.0.extend_from_slice(VOPRF_SHARE_MAGIC);
    payload.0.extend_from_slice(&counter_mac_key.0);
    payload.0.extend_from_slice(&vault_anchor_mac.0);
    payload.0.extend_from_slice(server_secret);
    let enrollment_nonce = Secret32::new(os_random_32()?);
    let bundle = Json::object(vec![
        ("format", Json::str(enrollment.share_format)),
        ("enrollment_nonce", Json::hex(&enrollment_nonce[..16])),
        ("scheme", Json::str(enrollment.scheme)),
        ("party", Json::num(party)),
        ("threshold", Json::num(enrollment.threshold)),
        ("parties", Json::num(enrollment.parties)),
        ("session_id", Json::hex(&enrollment.session)),
        ("commitment", Json::hex(&enrollment.commitment)),
        ("secret_key", Json::hex(&payload)),
    ]);
    write_party_bundle(
        &voprf_share_path(vault_dir, party),
        bundle,
        passphrase,
        MAX_KEY_FILE_BYTES,
    )?;
    FsToprfCounterStore::create(
        &voprf_counter_path(vault_dir, party),
        enrollment.commitment,
        party,
        counter_mac_key.0,
        enrollment.quota,
    )
}

struct OpenedVoprfShare {
    lock: crate::vault::Vault,
    counter_mac: Secret32,
    vault_anchor_mac: Secret32,
    server_bytes: ZeroizingBuf,
}

/// Open and authenticate one party's share bundle against the enrollment it must belong to.
fn load_voprf_bundle(
    vault_dir: &str,
    party: usize,
    enrollment: &VoprfEnrollment<'_>,
    passphrase: Option<&[u8]>,
) -> Result<OpenedVoprfShare, CliError> {
    let (lock, bundle, opened) = open_party_bundle(
        &voprf_share_path(vault_dir, party),
        enrollment.share_format,
        MAX_KEY_FILE_BYTES,
        passphrase,
    )?;
    if bundle.field_u64("party")? != party as u64
        || bundle.field_u64("threshold")? != enrollment.threshold as u64
        || bundle.field_u64("parties")? != enrollment.parties as u64
        || bundle.field_hex("session_id")?.0.as_slice() != enrollment.session
        || bundle.field_hex("commitment")?.0.as_slice() != enrollment.commitment
    {
        return Err(CliError::state("TOPRF share enrollment mismatch"));
    }
    let raw = opened.secret_key()?;
    if raw.len() < 72 || &raw[..8] != VOPRF_SHARE_MAGIC {
        return Err(CliError::input(
            "corrupt or unsupported TOPRF share payload",
        ));
    }
    let counter_mac = Secret32::new(raw[8..40].try_into().unwrap());
    let vault_anchor_mac = Secret32::new(raw[40..72].try_into().unwrap());
    let server_bytes = ZeroizingBuf::new(raw[72..].to_vec());
    Ok(OpenedVoprfShare {
        lock,
        counter_mac,
        vault_anchor_mac,
        server_bytes,
    })
}

fn toprf_seed(deterministic: bool, domain: &[u8], parts: &[&[u8]]) -> Result<[u8; 32], CliError> {
    if deterministic {
        Ok(cshake256_framed_32(domain, parts))
    } else {
        os_random_32()
    }
}

fn format_voprf_eval_refusal(counter: u64, err: voprf::Error) -> CliError {
    match err {
        voprf::Error::Counter => CliError::state(format!(
            "TOPRF monotone counter {counter} refused (already spent, rolled back, or outside window)"
        )),
        voprf::Error::Quota => CliError::state(format!(
            "TOPRF evaluation quota exhausted at monotone counter {counter}"
        )),
        other => CliError::verify(format!("TOPRF evaluation aborted: {other}")),
    }
}

fn preflight_voprf_party_files(vault_dir: &str, parties: usize) -> Result<(), CliError> {
    for party in 0..parties {
        let share = voprf_share_path(vault_dir, party);
        ensure_absent(&share)?;
        ensure_absent(&format!("{share}.vault.lock"))?;
        let counter = voprf_counter_path(vault_dir, party);
        ensure_absent(&counter)?;
        ensure_absent(&format!("{counter}.lock"))?;
    }
    Ok(())
}

/// Dealerless Shamir-SPDZ enrollment for any `2 <= threshold <= parties <= 64`.
#[allow(clippy::too_many_arguments)]
fn voprf_spdz_keygen(
    args: &Args,
    threshold: u64,
    parties: u64,
    quota: u64,
    anchor_cfg: Option<&AnchorConfig>,
    passphrase: Option<&[u8]>,
    vault_dir: &str,
    public_out: &str,
) -> Result<(), CliError> {
    let config = SpdzConfig::new(
        usize::try_from(threshold).map_err(|_| CliError::usage("threshold out of range"))?,
        usize::try_from(parties).map_err(|_| CliError::usage("parties out of range"))?,
    )
    .map_err(|_| {
        CliError::usage(
            "the Shamir-SPDZ TOPRF backend supports 2 <= --threshold <= --parties <= 64",
        )
    })?;
    private_dir(vault_dir, true)?;
    preflight_voprf_party_files(vault_dir, config.servers())?;
    let deterministic = args.flag("deterministic");
    let session = toprf_seed(
        deterministic,
        b"QSAG.CLI.TOPRF.DET.SESSION.V1",
        &[b"voprf-keygen-shamir-spdz"],
    )?;
    let mut seeds = SecretBuffer(Vec::with_capacity(config.servers()));
    for party in 0..config.servers() {
        seeds.push(toprf_seed(
            deterministic,
            b"QSAG.CLI.TOPRF.DET.SEED.V1",
            &[&(party as u64).to_le_bytes()],
        )?);
    }
    let servers = spdz_dkg(config, session, &seeds).map_err(|e| {
        CliError::verify(format!(
            "dealerless Shamir-SPDZ TOPRF enrollment aborted: {e}"
        ))
    })?;
    let public = servers[0].public().clone();
    let commitment = public.public_key().commitment();
    let vault_anchor_mac = Secret32::new(toprf_seed(
        deterministic,
        b"QSAG.CLI.TOPRF.DET.ANCHOR_MAC.V1",
        &[&commitment, &session],
    )?);
    let anchor_seal = match anchor_cfg {
        Some(cfg) => Some(VaultPartyGenAnchor::create(
            cfg,
            vault_dir,
            "cred_voprf",
            commitment,
            &vault_anchor_mac.0,
            config.servers(),
        )?),
        None => None,
    };
    let enrollment = VoprfEnrollment {
        share_format: VOPRF_SPDZ_SHARE_FORMAT,
        scheme: VOPRF_SPDZ_SCHEME,
        threshold: config.threshold(),
        parties: config.servers(),
        session,
        commitment,
        quota,
    };
    for (party, server) in servers.iter().enumerate() {
        let counter_mac = Secret32::new(toprf_seed(
            deterministic,
            b"QSAG.CLI.TOPRF.DET.COUNTER_MAC.V1",
            &[&commitment, &(party as u64).to_le_bytes()],
        )?);
        let payload = ZeroizingBuf::new(server.to_secret_bytes());
        write_voprf_bundle(
            vault_dir,
            party,
            &enrollment,
            &counter_mac,
            &vault_anchor_mac,
            &payload.0,
            passphrase,
        )?;
    }
    let record = public.to_bytes();
    let mut meta_fields = vec![
        ("format", Json::str(VOPRF_META_FORMAT)),
        ("share_format", Json::str(VOPRF_SPDZ_SHARE_FORMAT)),
        ("backend", Json::str(VOPRF_SPDZ_BACKEND)),
        ("threshold", Json::num(config.threshold())),
        ("parties", Json::num(config.servers())),
        ("max_evaluations", Json::num(quota)),
        ("session_id", Json::hex(&session)),
        ("commitment", Json::hex(&commitment)),
        ("enrollment", Json::hex(&record)),
    ];
    if let Some(seal) = anchor_seal {
        meta_fields.push(("anchor_required", Json::Bool(true)));
        meta_fields.push(("anchor_ceremony_seal", Json::hex(&seal)));
    }
    let meta = Json::object(meta_fields);
    write_new(
        &voprf_meta_path(vault_dir),
        meta.to_pretty().as_bytes(),
        true,
    )?;
    let pub_doc = Json::object(vec![
        ("format", Json::str(VOPRF_PUB_FORMAT)),
        ("scheme", Json::str(VOPRF_SPDZ_SCHEME)),
        ("threshold", Json::num(config.threshold())),
        ("parties", Json::num(config.servers())),
        ("commitment", Json::hex(&commitment)),
        ("enrollment", Json::hex(&record)),
    ]);
    write_new(public_out, pub_doc.to_pretty().as_bytes(), false)?;
    if args.flag("json") {
        let report = Json::object(vec![
            ("operation", Json::str("cred-voprf-keygen")),
            ("backend", Json::str(VOPRF_SPDZ_BACKEND)),
            ("vault_dir", Json::str(vault_dir)),
            ("public_file", Json::str(public_out)),
            ("commitment", Json::hex(&commitment)),
        ]);
        print!("{}", report.to_pretty());
    } else {
        println!(
            "initialized ({}, {}) dealerless Shamir-SPDZ TOPRF vault {vault_dir} (commitment {})",
            config.threshold(),
            config.servers(),
            to_hex(&commitment)
        );
    }
    Ok(())
}

/// Evaluate from any `threshold` persisted Shamir-SPDZ shares. Without `--signers`
/// the first `threshold` share files present in the vault form the quorum.
#[allow(clippy::too_many_arguments)]
fn voprf_spdz_eval(
    args: &Args,
    meta: &Json,
    pub_json: &Json,
    anchor_cfg: Option<&AnchorConfig>,
    vault_dir: &str,
    out_path: &str,
    counter: u64,
    input: &ZeroizingBuf,
    passphrase: Option<&[u8]>,
) -> Result<(), CliError> {
    let record = meta.field_hex("enrollment")?;
    if pub_json.field_hex("enrollment")?.0 != record.0 {
        return Err(CliError::verify(
            "public file enrollment record does not match TOPRF vault",
        ));
    }
    let public = SpdzPublic::from_bytes(&record.0)
        .map_err(|e| CliError::input(format!("invalid TOPRF enrollment record: {e}")))?;
    let session = from_hex_exact::<32>(meta.field_str("session_id")?, "session_id")?;
    let commitment = public.public_key().commitment();
    let (threshold, parties) = (public.config().threshold(), public.config().servers());
    let quota = meta
        .get("max_evaluations")
        .and_then(Json::as_u64)
        .unwrap_or(voprf::MAX_EVALUATIONS_PER_KEY);
    if from_hex_exact::<32>(meta.field_str("commitment")?, "commitment")? != commitment
        || meta.field_u64("threshold")? != threshold as u64
        || meta.field_u64("parties")? != parties as u64
        || meta.field_str("share_format")? != VOPRF_SPDZ_SHARE_FORMAT
    {
        return Err(CliError::state(
            "TOPRF vault metadata does not match its enrollment record",
        ));
    }
    let selected: Vec<usize> = match args.get("signers") {
        Some(spec) => parse_party_indices(Some(spec), parties, parties)?,
        None => (0..parties)
            .filter(|&party| Path::new(&voprf_share_path(vault_dir, party)).exists())
            .take(threshold)
            .collect(),
    };
    if selected.len() < threshold {
        return Err(CliError::state(format!(
            "the ({threshold}, {parties}) Shamir-SPDZ TOPRF needs {threshold} online servers; only {} selected or present",
            selected.len()
        )));
    }
    let enrollment = VoprfEnrollment {
        share_format: VOPRF_SPDZ_SHARE_FORMAT,
        scheme: VOPRF_SPDZ_SCHEME,
        threshold,
        parties,
        session,
        commitment,
        quota,
    };
    let mut locks = Vec::with_capacity(selected.len());
    let mut servers = Vec::with_capacity(selected.len());
    let mut counter_macs = Vec::with_capacity(selected.len());
    let mut agreed_anchor_mac: Option<Secret32> = None;
    for &party in &selected {
        let opened = load_voprf_bundle(vault_dir, party, &enrollment, passphrase)?;
        if let Some(prev) = &agreed_anchor_mac {
            if !ct_eq_bytes(&prev.0, &opened.vault_anchor_mac.0) {
                return Err(CliError::state("TOPRF custodian anchor MAC mismatch"));
            }
        } else {
            agreed_anchor_mac = Some(Secret32::new(opened.vault_anchor_mac.0));
        }
        servers.push(
            SpdzServer::from_secret_bytes(&opened.server_bytes.0, &public, party)
                .map_err(|e| CliError::input(format!("invalid TOPRF share: {e}")))?,
        );
        counter_macs.push(opened.counter_mac);
        locks.push(opened.lock);
    }

    let vault_anchor = match anchor_cfg {
        Some(cfg) => {
            let root_mac = agreed_anchor_mac
                .as_ref()
                .ok_or_else(|| CliError::state("missing TOPRF anchor MAC"))?;
            let va = VaultPartyGenAnchor::open(
                cfg,
                vault_dir,
                meta,
                "cred_voprf",
                commitment,
                &root_mac.0,
                parties,
            )?;
            let hw = va
                .lock()
                .map_err(|_| CliError::state("TOPRF anchor mutex poisoned"))?
                .high_water();
            if hw.is_some_and(|prev| counter <= prev) {
                return Err(CliError::state(format!(
                    "TOPRF monotone counter {counter} refused by external anchor (high-water {:?})",
                    hw
                )));
            }
            Some(va)
        }
        None => None,
    };

    let mut stores = Vec::with_capacity(selected.len());
    for (&party, mac_key) in selected.iter().zip(&counter_macs) {
        let min_gen = match &vault_anchor {
            Some(va) => va
                .lock()
                .map_err(|_| CliError::state("TOPRF anchor mutex poisoned"))?
                .party_min_gen(party)?,
            None => 0,
        };
        stores.push(FsToprfCounterStore::open_at_least(
            &voprf_counter_path(vault_dir, party),
            commitment,
            party,
            mac_key.0,
            min_gen,
            vault_anchor.clone(),
        )?);
    }

    let deterministic = args.flag("deterministic");
    let eval_session = toprf_seed(
        deterministic,
        b"QSAG.CLI.TOPRF.DET.EVAL_SESSION.V1",
        &[&commitment, &counter.to_le_bytes()],
    )?;
    let mut seeds = SecretBuffer(Vec::with_capacity(selected.len()));
    for &party in &selected {
        seeds.push(toprf_seed(
            deterministic,
            b"QSAG.CLI.TOPRF.DET.SERVER.V1",
            &[
                &commitment,
                &counter.to_le_bytes(),
                &(party as u64).to_le_bytes(),
            ],
        )?);
    }
    let refused = |e: voprf::Error| format_voprf_eval_refusal(counter, e);
    let (session_state, grants) = {
        let mut quorum: Vec<&mut SpdzServer> = servers.iter_mut().collect();
        let mut store_refs: Vec<&mut dyn CounterStore> = stores
            .iter_mut()
            .map(|store| store as &mut dyn CounterStore)
            .collect();
        SpdzSession::begin(
            &mut quorum,
            &mut store_refs,
            eval_session,
            counter,
            1,
            &seeds,
        )
        .map_err(refused)?
    };
    let (client, request) = spdz_blind(
        &public,
        &[input.0.as_slice()],
        eval_session,
        counter,
        &grants,
    )
    .map_err(|e| CliError::verify(format!("TOPRF mask grants rejected by the client: {e}")))?;
    let outputs = session_state.evaluate(&request).map_err(refused)?;
    let evaluation = client
        .finalize(&outputs)
        .map_err(|e| CliError::verify(format!("TOPRF client finalize failed: {e}")))?;
    let pk = public.public_key();
    let prf_value = evaluation
        .value_for(&pk, &input.0)
        .ok_or_else(|| CliError::verify("TOPRF evaluation missing bound input output"))?;
    drop(stores);
    drop(locks);

    let eval_doc = Json::object(vec![
        ("format", Json::str(VOPRF_EVAL_FORMAT)),
        ("scheme", Json::str(VOPRF_SPDZ_SCHEME)),
        ("commitment", Json::hex(&commitment)),
        ("counter", Json::num(counter)),
        ("session_id", Json::hex(&eval_session)),
        ("prf_output", Json::hex(&prf_value)),
        (
            "servers",
            Json::Array(selected.iter().map(|party| Json::num(*party)).collect()),
        ),
        ("faulty_servers", Json::Array(Vec::new())),
    ]);
    write_new(out_path, eval_doc.to_pretty().as_bytes(), true)?;
    if args.flag("json") {
        print!("{}", eval_doc.to_pretty());
    } else {
        println!(
            "evaluated ({threshold}, {parties}) Shamir-SPDZ TOPRF at counter {counter} with servers {selected:?} -> {out_path}"
        );
    }
    Ok(())
}

fn run_voprf_dkg_threads(
    session: [u8; 32],
    entropies: &[Secret32; TOPRF_SERVERS],
) -> Result<Vec<voprf::Server>, CliError> {
    let cfg = voprf::Config::new(2, TOPRF_SERVERS)
        .map_err(|e| CliError::usage(format!("TOPRF config failed: {e}")))?;
    let hub = SharedToprfHub::new();
    let results: Vec<Result<voprf::Server, voprf::Error>> = std::thread::scope(|s| {
        let mut handles = Vec::with_capacity(TOPRF_SERVERS);
        for (party, ent) in entropies.iter().enumerate() {
            let hub_ref = Arc::clone(&hub);
            let party_entropy = ent.0;
            handles.push(s.spawn(move || {
                let mut net = LocalToprfEndpoint {
                    party,
                    hub: Arc::clone(&hub_ref),
                };
                let res = voprf::dkg(cfg, party, session, party_entropy, &mut net);
                if res.is_err() {
                    hub_ref.abort_all();
                }
                res
            }));
        }
        handles
            .into_iter()
            .map(|h| h.join().unwrap_or(Err(voprf::Error::Transport)))
            .collect()
    });
    results
        .into_iter()
        .collect::<Result<Vec<_>, _>>()
        .map_err(|e| CliError::verify(format!("dealerless TOPRF DKG aborted: {e}")))
}

fn voprf_keygen(raw: &[String]) -> Result<(), CliError> {
    let mut opts = vec![
        "vault-dir",
        "public-out",
        "threshold",
        "parties",
        "backend",
        "max-evaluations",
        "passphrase-env",
        "passphrase-file",
    ];
    opts.extend_from_slice(ANCHOR_NO_VAULT_VALUE_OPTIONS);
    let mut flags = vec!["deterministic", "allow-unencrypted", "json", "help"];
    flags.extend_from_slice(ANCHOR_FLAG_OPTIONS);
    let args = Args::parse(raw, &opts, &flags)?;
    if args.flag("help") {
        println!(
            "qsag cred voprf-keygen --vault-dir <dir> --public-out <path> [--threshold 2 --parties 5] [--backend rss|shamir-spdz] [--max-evaluations <n>] [--anchor-dir <dir> | --anchor-tpm-nv <idx> | --anchor-vmgenid | --ephemeral-unanchored] [--passphrase-env <name> | --passphrase-file <path> | --allow-unencrypted] [--deterministic] [--json]\n  rss: replicated (2, 5), all five servers evaluate. shamir-spdz: any 2 <= threshold <= parties <= 64, any `threshold` servers evaluate (default when the committee is not (2, 5))."
        );
        return Ok(());
    }
    args.no_positionals()?;
    let vault_dir = args.require("vault-dir")?;
    let public_out = args.require("public-out")?;
    let anchor_cfg = AnchorConfig::from_quorum_args(&args, vault_dir)?;
    require_anchor_or_waiver(
        anchor_cfg.is_some(),
        args.flag("ephemeral-unanchored"),
        "anchor-dir",
    )?;
    let quota = args
        .get_u64("max-evaluations")?
        .unwrap_or(voprf::MAX_EVALUATIONS_PER_KEY);
    if quota == 0 || quota > voprf::MAX_EVALUATIONS_PER_KEY {
        return Err(CliError::usage(format!(
            "--max-evaluations must be in 1..={}",
            voprf::MAX_EVALUATIONS_PER_KEY
        )));
    }
    let threshold = args.get_u64("threshold")?.unwrap_or(2);
    let parties = args.get_u64("parties")?.unwrap_or(TOPRF_SERVERS as u64);
    let replicated_shape = (threshold, parties) == (2, TOPRF_SERVERS as u64);
    let spdz = match args.get("backend") {
        None => !replicated_shape,
        Some("rss") => false,
        Some(VOPRF_SPDZ_BACKEND) => true,
        Some(other) => {
            return Err(CliError::usage(format!(
                "unknown TOPRF --backend '{other}' (expected rss or shamir-spdz)"
            )));
        }
    };
    if !spdz && !replicated_shape {
        return Err(CliError::usage(
            "the replicated TOPRF backend supports only --threshold 2 --parties 5; use --backend shamir-spdz for other committees",
        ));
    }
    let passphrase = crate::envelope::passphrase(&args)?;
    if passphrase.is_none() && !args.flag("allow-unencrypted") && !args.flag("deterministic") {
        return Err(CliError::usage(
            "TOPRF custody requires --passphrase-env or --passphrase-file (or explicit --allow-unencrypted)",
        ));
    }
    ensure_absent(&voprf_meta_path(vault_dir))?;
    ensure_absent(public_out)?;
    if spdz {
        return voprf_spdz_keygen(
            &args,
            threshold,
            parties,
            quota,
            anchor_cfg.as_ref(),
            passphrase.as_deref().map(Vec::as_slice),
            vault_dir,
            public_out,
        );
    }
    private_dir(vault_dir, true)?;
    preflight_voprf_party_files(vault_dir, TOPRF_SERVERS)?;

    let deterministic = args.flag("deterministic");
    let session = toprf_seed(
        deterministic,
        b"QSAG.CLI.TOPRF.DET.SESSION.V1",
        &[b"voprf-keygen"],
    )?;
    let mut entropies: [Secret32; TOPRF_SERVERS] = core::array::from_fn(|_| Secret32::new([0; 32]));
    for (party, entropy) in entropies.iter_mut().enumerate() {
        entropy.0 = toprf_seed(
            deterministic,
            b"QSAG.CLI.TOPRF.DET.SEED.V1",
            &[&(party as u64).to_le_bytes()],
        )?;
    }

    let servers = run_voprf_dkg_threads(session, &entropies)?;
    let commitment = servers[0].public_key().commitment();
    for srv in &servers[1..] {
        if srv.public_key().commitment() != commitment {
            return Err(CliError::verify(
                "TOPRF DKG servers disagreed on public commitment",
            ));
        }
    }

    let vault_anchor_mac = Secret32::new(toprf_seed(
        deterministic,
        b"QSAG.CLI.TOPRF.DET.ANCHOR_MAC.V1",
        &[&commitment, &session],
    )?);
    let anchor_seal = match &anchor_cfg {
        Some(cfg) => Some(VaultPartyGenAnchor::create(
            cfg,
            vault_dir,
            "cred_voprf",
            commitment,
            &vault_anchor_mac.0,
            TOPRF_SERVERS,
        )?),
        None => None,
    };

    let enrollment = VoprfEnrollment {
        share_format: VOPRF_SHARE_FORMAT,
        scheme: VOPRF_RSS_SCHEME,
        threshold: 2,
        parties: TOPRF_SERVERS,
        session,
        commitment,
        quota,
    };
    for (party, server) in servers.iter().enumerate() {
        let counter_mac = Secret32::new(toprf_seed(
            deterministic,
            b"QSAG.CLI.TOPRF.DET.COUNTER_MAC.V1",
            &[&commitment, &(party as u64).to_le_bytes()],
        )?);
        let payload = ZeroizingBuf::new(server.to_secret_bytes());
        write_voprf_bundle(
            vault_dir,
            party,
            &enrollment,
            &counter_mac,
            &vault_anchor_mac,
            &payload.0,
            passphrase.as_deref().map(Vec::as_slice),
        )?;
    }

    let mut meta_fields = vec![
        ("format", Json::str(VOPRF_META_FORMAT)),
        ("share_format", Json::str(VOPRF_SHARE_FORMAT)),
        ("threshold", Json::num(2)),
        ("parties", Json::num(TOPRF_SERVERS)),
        ("max_evaluations", Json::num(quota)),
        ("session_id", Json::hex(&session)),
        ("commitment", Json::hex(&commitment)),
    ];
    if let Some(seal) = anchor_seal {
        meta_fields.push(("anchor_required", Json::Bool(true)));
        meta_fields.push(("anchor_ceremony_seal", Json::hex(&seal)));
    }
    let meta = Json::object(meta_fields);
    write_new(
        &voprf_meta_path(vault_dir),
        meta.to_pretty().as_bytes(),
        true,
    )?;

    let pub_doc = Json::object(vec![
        ("format", Json::str(VOPRF_PUB_FORMAT)),
        ("scheme", Json::str(VOPRF_RSS_SCHEME)),
        ("threshold", Json::num(2)),
        ("parties", Json::num(TOPRF_SERVERS)),
        ("commitment", Json::hex(&commitment)),
    ]);
    write_new(public_out, pub_doc.to_pretty().as_bytes(), false)?;

    if args.flag("json") {
        let report = Json::object(vec![
            ("operation", Json::str("cred-voprf-keygen")),
            ("vault_dir", Json::str(vault_dir)),
            ("public_file", Json::str(public_out)),
            ("commitment", Json::hex(&commitment)),
        ]);
        print!("{}", report.to_pretty());
    } else {
        println!(
            "initialized (2, 5) dealerless TOPRF vault {vault_dir} (commitment {})",
            to_hex(&commitment)
        );
    }
    Ok(())
}

fn voprf_eval(raw: &[String]) -> Result<(), CliError> {
    let mut opts = vec![
        "vault-dir",
        "public",
        "counter",
        "in",
        "message",
        "out",
        "signers",
        "passphrase-env",
        "passphrase-file",
    ];
    opts.extend_from_slice(ANCHOR_NO_VAULT_VALUE_OPTIONS);
    let mut flags = vec!["deterministic", "json", "help"];
    flags.extend_from_slice(ANCHOR_FLAG_OPTIONS);
    let args = Args::parse(raw, &opts, &flags)?;
    if args.flag("help") {
        println!(
            "qsag cred voprf-eval --vault-dir <dir> --public <path> --counter <n> --in <path|-> --out <path> [--signers 0,1,2,3,4] [--anchor-dir <dir> | --anchor-tpm-nv <idx> | --anchor-vmgenid | --ephemeral-unanchored] [--passphrase-env <name> | --passphrase-file <path>] [--deterministic] [--json]\n  Replicated vaults need all five servers. Shamir-SPDZ vaults evaluate with any `threshold` servers: --signers, or by default the first `threshold` share files present."
        );
        return Ok(());
    }
    args.no_positionals()?;
    let vault_dir = args.require("vault-dir")?;
    let anchor_cfg = AnchorConfig::from_quorum_args(&args, vault_dir)?;
    require_anchor_or_waiver(
        anchor_cfg.is_some(),
        args.flag("ephemeral-unanchored"),
        "anchor-dir",
    )?;
    let public_path = args.require("public")?;
    let counter = args
        .get_u64("counter")?
        .ok_or_else(|| CliError::usage("missing required option --counter <n>"))?;
    let out_path = args.require("out")?;
    ensure_absent(out_path)?;
    private_dir(vault_dir, false)?;

    let passphrase = crate::envelope::passphrase(&args)?;
    let input = read_input_arg(&args)?;
    let meta = load_json_checked(
        &voprf_meta_path(vault_dir),
        VOPRF_META_FORMAT,
        MAX_KEY_FILE_BYTES,
    )?;
    enforce_anchor_requirement(&meta, anchor_cfg.as_ref())?;
    let pub_json = load_json_checked(public_path, VOPRF_PUB_FORMAT, MAX_KEY_FILE_BYTES)?;
    if meta.get("backend").and_then(Json::as_str) == Some(VOPRF_SPDZ_BACKEND) {
        return voprf_spdz_eval(
            &args,
            &meta,
            &pub_json,
            anchor_cfg.as_ref(),
            vault_dir,
            out_path,
            counter,
            &input,
            passphrase.as_deref().map(Vec::as_slice),
        );
    }
    let session = from_hex_exact::<32>(meta.field_str("session_id")?, "session_id")?;
    let commitment = from_hex_exact::<32>(meta.field_str("commitment")?, "commitment")?;
    let quota = meta
        .get("max_evaluations")
        .and_then(Json::as_u64)
        .unwrap_or(voprf::MAX_EVALUATIONS_PER_KEY);
    let pub_commitment =
        from_hex_exact::<32>(pub_json.field_str("commitment")?, "public commitment")?;
    if commitment != pub_commitment {
        return Err(CliError::verify(
            "public file commitment does not match TOPRF vault",
        ));
    }
    if meta.field_str("share_format")? != VOPRF_SHARE_FORMAT {
        return Err(CliError::input("unsupported TOPRF share format"));
    }

    let pk = ToprfPublicKey::from_commitment(commitment);
    let selected = parse_party_indices(args.get("signers"), TOPRF_SERVERS, TOPRF_SERVERS)?;
    if selected != (0..TOPRF_SERVERS).collect::<Vec<_>>() {
        return Err(CliError::state(
            "the replicated TOPRF circuit requires all five servers; enroll with --backend shamir-spdz for exact-threshold evaluation",
        ));
    }
    let enrollment = VoprfEnrollment {
        share_format: VOPRF_SHARE_FORMAT,
        scheme: VOPRF_RSS_SCHEME,
        threshold: 2,
        parties: TOPRF_SERVERS,
        session,
        commitment,
        quota,
    };
    let mut locks = Vec::with_capacity(TOPRF_SERVERS);
    let mut servers = Vec::with_capacity(TOPRF_SERVERS);
    let mut counter_macs = Vec::with_capacity(TOPRF_SERVERS);
    let mut agreed_anchor_mac: Option<Secret32> = None;
    for party in selected {
        let opened = load_voprf_bundle(
            vault_dir,
            party,
            &enrollment,
            passphrase.as_deref().map(Vec::as_slice),
        )?;
        if let Some(prev) = &agreed_anchor_mac {
            if !ct_eq_bytes(&prev.0, &opened.vault_anchor_mac.0) {
                return Err(CliError::state("TOPRF custodian anchor MAC mismatch"));
            }
        } else {
            agreed_anchor_mac = Some(Secret32::new(opened.vault_anchor_mac.0));
        }
        servers.push(
            voprf::Server::from_secret_bytes(&opened.server_bytes.0, &pk, party)
                .map_err(|e| CliError::input(format!("invalid TOPRF share: {e}")))?,
        );
        counter_macs.push(opened.counter_mac);
        locks.push(opened.lock);
    }

    let vault_anchor = match &anchor_cfg {
        Some(cfg) => {
            let root_mac = agreed_anchor_mac
                .as_ref()
                .ok_or_else(|| CliError::state("missing TOPRF anchor MAC"))?;
            let va = VaultPartyGenAnchor::open(
                cfg,
                vault_dir,
                &meta,
                "cred_voprf",
                commitment,
                &root_mac.0,
                TOPRF_SERVERS,
            )?;
            let hw = va
                .lock()
                .map_err(|_| CliError::state("TOPRF anchor mutex poisoned"))?
                .high_water();
            if hw.is_some_and(|prev| counter <= prev) {
                return Err(CliError::state(format!(
                    "TOPRF monotone counter {counter} refused by external anchor (high-water {:?})",
                    hw
                )));
            }
            Some(va)
        }
        None => None,
    };

    let mut stores = Vec::with_capacity(TOPRF_SERVERS);
    for (party, mac_key) in counter_macs.iter().enumerate() {
        let min_gen = match &vault_anchor {
            Some(va) => va
                .lock()
                .map_err(|_| CliError::state("TOPRF anchor mutex poisoned"))?
                .party_min_gen(party)?,
            None => 0,
        };
        stores.push(FsToprfCounterStore::open_at_least(
            &voprf_counter_path(vault_dir, party),
            commitment,
            party,
            mac_key.0,
            min_gen,
            vault_anchor.clone(),
        )?);
    }

    let deterministic = args.flag("deterministic");
    let eval_session = if deterministic {
        cshake256_framed_32(
            b"QSAG.CLI.TOPRF.DET.EVAL_SESSION.V1",
            &[&commitment, &counter.to_le_bytes()],
        )
    } else {
        os_random_32()?
    };
    let client_entropy = Secret32::new(if deterministic {
        cshake256_framed_32(
            b"QSAG.CLI.TOPRF.DET.CLIENT.V1",
            &[&commitment, &counter.to_le_bytes(), &input.0],
        )
    } else {
        os_random_32()?
    });

    let (client, requests) = voprf::blind(
        &pk,
        &[input.0.as_slice()],
        eval_session,
        counter,
        client_entropy.0,
    )
    .map_err(|e| match e {
        voprf::Error::Counter | voprf::Error::Quota => format_voprf_eval_refusal(counter, e),
        other => CliError::usage(format!("TOPRF blind failed: {other}")),
    })?;

    let hub = SharedToprfHub::new();
    let eval_results: Vec<Result<voprf::Output, voprf::Error>> = std::thread::scope(|s| {
        let mut handles = Vec::with_capacity(TOPRF_SERVERS);
        for (((party, mut srv), mut store), req) in
            servers.into_iter().enumerate().zip(stores).zip(requests)
        {
            let hub_ref = Arc::clone(&hub);
            handles.push(s.spawn(move || {
                let mut net = LocalToprfEndpoint {
                    party,
                    hub: Arc::clone(&hub_ref),
                };
                let res = srv.evaluate(req, &mut store, &mut net);
                if res.is_err() {
                    hub_ref.abort_all();
                }
                res
            }));
        }
        handles
            .into_iter()
            .map(|h| h.join().unwrap_or(Err(voprf::Error::Transport)))
            .collect()
    });
    drop(locks);

    let mut outputs_vec = Vec::with_capacity(TOPRF_SERVERS);
    for res in eval_results {
        match res {
            Ok(out) => outputs_vec.push(Some(out)),
            Err(e) => return Err(format_voprf_eval_refusal(counter, e)),
        }
    }
    let outputs_arr: [Option<voprf::Output>; TOPRF_SERVERS] = outputs_vec
        .try_into()
        .map_err(|_| CliError::verify("TOPRF output count mismatch"))?;
    let evaluation = client
        .finalize(outputs_arr)
        .map_err(|e| CliError::verify(format!("TOPRF client finalize failed: {e}")))?;
    let prf_value = evaluation
        .value_for(&pk, &input.0)
        .ok_or_else(|| CliError::verify("TOPRF evaluation missing bound input output"))?;

    let eval_doc = Json::object(vec![
        ("format", Json::str(VOPRF_EVAL_FORMAT)),
        ("scheme", Json::str(VOPRF_RSS_SCHEME)),
        ("commitment", Json::hex(&commitment)),
        ("counter", Json::num(counter)),
        ("session_id", Json::hex(&eval_session)),
        ("prf_output", Json::hex(&prf_value)),
        (
            "faulty_servers",
            Json::Array(
                evaluation
                    .faulty_servers
                    .iter()
                    .map(|p| Json::num(*p))
                    .collect(),
            ),
        ),
    ]);
    write_new(out_path, eval_doc.to_pretty().as_bytes(), true)?;

    if args.flag("json") {
        print!("{}", eval_doc.to_pretty());
    } else {
        println!(
            "evaluated (2, 5) TOPRF at counter {counter} -> {}",
            out_path
        );
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Dealerless Threshold FIPS 204 ML-DSA (`44`, `65`, `87`)
// ---------------------------------------------------------------------------

struct MpcRoundSlot {
    arrivals: usize,
    private: Vec<Option<Vec<Vec<u8>>>>,
    broadcast: Vec<Option<Vec<u8>>>,
    aborted: bool,
}

impl MpcRoundSlot {
    fn new(parties: usize) -> Self {
        Self {
            arrivals: 0,
            private: vec![None; parties],
            broadcast: vec![None; parties],
            aborted: false,
        }
    }
}

impl Drop for MpcRoundSlot {
    fn drop(&mut self) {
        for rows in self.private.iter_mut().flatten() {
            for buf in rows {
                ct_zeroize_bytes(buf);
            }
        }
        for buf in self.broadcast.iter_mut().flatten() {
            ct_zeroize_bytes(buf);
        }
    }
}

struct SharedMpcHub {
    parties: usize,
    aborted: AtomicBool,
    rounds: Mutex<BTreeMap<(u64, u8), MpcRoundSlot>>,
    cv: Condvar,
}

impl SharedMpcHub {
    fn new(parties: usize) -> Arc<Self> {
        Arc::new(Self {
            parties,
            aborted: AtomicBool::new(false),
            rounds: Mutex::new(BTreeMap::new()),
            cv: Condvar::new(),
        })
    }

    fn abort_all(&self) {
        self.aborted.store(true, Ordering::SeqCst);
        if let Ok(mut map) = self.rounds.lock() {
            for slot in map.values_mut() {
                slot.aborted = true;
            }
            self.cv.notify_all();
        }
    }
}

struct LocalMpcEndpoint {
    me: usize,
    hub: Arc<SharedMpcHub>,
}

impl MpcTransport for LocalMpcEndpoint {
    fn exchange(
        &mut self,
        info: RoundInfo,
        private: Vec<Vec<u8>>,
        broadcast: Vec<u8>,
    ) -> Result<RoundInbox, MpcTransportError> {
        let n = self.hub.parties;
        if private.len() != n {
            return Err(MpcTransportError);
        }
        let key = (info.index, info.phase);
        let mut guard = self.hub.rounds.lock().map_err(|_| MpcTransportError)?;
        if self.hub.aborted.load(Ordering::SeqCst) {
            return Err(MpcTransportError);
        }
        {
            let slot = guard.entry(key).or_insert_with(|| MpcRoundSlot::new(n));
            if slot.aborted || slot.private[self.me].is_some() {
                return Err(MpcTransportError);
            }
            slot.private[self.me] = Some(private);
            slot.broadcast[self.me] = Some(broadcast);
            slot.arrivals += 1;
            if slot.arrivals == n {
                self.hub.cv.notify_all();
            }
        }
        loop {
            let slot = guard.get(&key).ok_or(MpcTransportError)?;
            // A completed round is delivered even if a peer has already failed on
            // it and aborted, so every custodian reports the protocol's own verdict.
            if slot.arrivals == n {
                let mut recv_priv = Vec::with_capacity(n);
                let mut recv_bcast = Vec::with_capacity(n);
                for sender in 0..n {
                    let p = if sender == self.me {
                        Vec::new()
                    } else {
                        slot.private[sender]
                            .as_ref()
                            .and_then(|rows| rows.get(self.me))
                            .cloned()
                            .unwrap_or_default()
                    };
                    let b = slot.broadcast[sender].clone().unwrap_or_default();
                    recv_priv.push(p);
                    recv_bcast.push(b);
                }
                return Ok(RoundInbox {
                    private: recv_priv,
                    broadcast: recv_bcast,
                });
            }
            if slot.aborted {
                return Err(MpcTransportError);
            }
            guard = self.hub.cv.wait(guard).map_err(|_| MpcTransportError)?;
        }
    }
}

// A local restoration capsule contains only this party's entropy and received
// enrollment messages. It never contains another party's entropy or inbox.
// Until the core exposes a direct share codec, replaying this authenticated local
// transcript rebuilds one share without contacting or reconstructing absent peers.
const MLDSA_SHARE_FORMAT: &str = "qsag-cred-mldsa-local-share-v1";
const MLDSA_SHAMIR_SHARE_FORMAT: &str = "qsag-cred-mldsa-shamir-share-v1";
const MLDSA_RSS_PAYLOAD_MAGIC: &[u8; 8] = b"QSMLRS02";
const MLDSA_SHAMIR_PAYLOAD_MAGIC: &[u8; 8] = b"QSMLSH02";
const MLDSA_BUNDLE_LIMIT: u64 = 256 * 1024 * 1024;

struct AnchoredNonceBurnStore {
    inner: FsNonceBurnStore,
    party_idx: usize,
    user_epoch: u64,
    vault_anchor: Option<Arc<Mutex<VaultPartyGenAnchor>>>,
    poisoned: bool,
}

impl NonceBurnPersistence for AnchoredNonceBurnStore {
    fn reserve(&mut self, party_id: u16, epoch: u64, session_id: &[u8; 32], attempt: u32) -> bool {
        if self.poisoned || !self.inner.reserve(party_id, epoch, session_id, attempt) {
            self.poisoned = true;
            return false;
        }
        if let Some(anchor) = &self.vault_anchor {
            let ok = anchor
                .lock()
                .ok()
                .and_then(|mut guard| {
                    guard
                        .record_step(self.party_idx, self.inner.generation(), self.user_epoch)
                        .ok()
                })
                .is_some();
            if !ok {
                self.poisoned = true;
                return false;
            }
        }
        true
    }

    fn next_epoch(&self, key_id: &[u8; 32], party_id: u16) -> Result<u64, ThresholdMlDsaError> {
        if self.poisoned {
            return Err(ThresholdMlDsaError::NoncePersistenceFailed);
        }
        self.inner.next_epoch(key_id, party_id)
    }
}

fn round_binding(info: RoundInfo, private: &[Vec<u8>], broadcast: &[u8]) -> [u8; 32] {
    let kind = match info.kind {
        RoundKind::KeySetup => 0,
        RoundKind::KeyConfirm => 1,
        RoundKind::Multiply => 2,
        RoundKind::VerifyReshare => 3,
        RoundKind::ViewDigest => 4,
        RoundKind::Open => 5,
        RoundKind::Confirm => 6,
        RoundKind::Input => 7,
    };
    let index = info.index.to_le_bytes();
    let phase_kind = [info.phase, kind];
    let mut frames = vec![index.as_slice(), phase_kind.as_slice(), broadcast];
    frames.extend(private.iter().map(Vec::as_slice));
    cshake256_framed_32(b"QSAG.CLI.TMLDSA.LOCAL_ROUND.V1", &frames)
}

struct RecordingMpc {
    net: LocalMpcEndpoint,
    transcript: ZeroizingBuf,
}

impl MpcTransport for RecordingMpc {
    fn exchange(
        &mut self,
        info: RoundInfo,
        private: Vec<Vec<u8>>,
        broadcast: Vec<u8>,
    ) -> Result<RoundInbox, MpcTransportError> {
        let binding = round_binding(info, &private, &broadcast);
        let inbox = self.net.exchange(info, private, broadcast)?;
        self.transcript.0.extend_from_slice(&binding);
        for row in [&inbox.private, &inbox.broadcast] {
            self.transcript
                .0
                .extend_from_slice(&(row.len() as u64).to_le_bytes());
            for bytes in row {
                self.transcript
                    .0
                    .extend_from_slice(&(bytes.len() as u64).to_le_bytes());
                self.transcript.0.extend_from_slice(bytes);
            }
        }
        if self.transcript.len() as u64 > MLDSA_BUNDLE_LIMIT / 2 - 4096 {
            return Err(MpcTransportError);
        }
        Ok(inbox)
    }
}

struct RestoringMpc<'a> {
    remaining: &'a [u8],
    parties: usize,
}

impl RestoringMpc<'_> {
    fn take(&mut self, len: usize) -> Result<&[u8], MpcTransportError> {
        if len > self.remaining.len() {
            return Err(MpcTransportError);
        }
        let (head, tail) = self.remaining.split_at(len);
        self.remaining = tail;
        Ok(head)
    }
    fn number(&mut self) -> Result<usize, MpcTransportError> {
        let bytes = self.take(8)?;
        usize::try_from(u64::from_le_bytes(
            bytes.try_into().map_err(|_| MpcTransportError)?,
        ))
        .map_err(|_| MpcTransportError)
    }
    fn row(&mut self, out: &mut Vec<Vec<u8>>) -> Result<(), MpcTransportError> {
        if self.number()? != self.parties {
            return Err(MpcTransportError);
        }
        for _ in 0..self.parties {
            let len = self.number()?;
            out.push(self.take(len)?.to_vec());
        }
        Ok(())
    }
}

impl MpcTransport for RestoringMpc<'_> {
    fn exchange(
        &mut self,
        info: RoundInfo,
        mut private: Vec<Vec<u8>>,
        mut broadcast: Vec<u8>,
    ) -> Result<RoundInbox, MpcTransportError> {
        let binding = round_binding(info, &private, &broadcast);
        for bytes in &mut private {
            ct_zeroize_bytes(bytes);
        }
        ct_zeroize_bytes(&mut broadcast);
        if self.take(32)? != binding {
            return Err(MpcTransportError);
        }
        let mut inbox = RoundInbox::default();
        self.row(&mut inbox.private)?;
        self.row(&mut inbox.broadcast)?;
        Ok(inbox)
    }
}

fn mldsa_share_path(vault_dir: &str, party: usize) -> String {
    Path::new(vault_dir)
        .join(format!("mldsa-party-{party}.share"))
        .to_string_lossy()
        .into_owned()
}

fn parse_mldsa_level(spec: Option<&str>) -> Result<(MlDsaLevel, &'static str), CliError> {
    match spec.unwrap_or("44") {
        "44" | "ml-dsa-44" => Ok((MlDsaLevel::MlDsa44, "ml-dsa-44")),
        "65" | "ml-dsa-65" => Ok((MlDsaLevel::MlDsa65, "ml-dsa-65")),
        "87" | "ml-dsa-87" => Ok((MlDsaLevel::MlDsa87, "ml-dsa-87")),
        other => Err(CliError::usage(format!(
            "unsupported --level '{other}' (expected 44, 65, or 87)"
        ))),
    }
}

fn mldsa_meta_path(vault_dir: &str) -> String {
    Path::new(vault_dir)
        .join("mldsa-meta.json")
        .to_string_lossy()
        .into_owned()
}

fn mldsa_burn_path(vault_dir: &str, party: usize) -> PathBuf {
    Path::new(vault_dir).join(format!("mldsa-party-{party}.burn"))
}

fn map_mldsa_err(err: ThresholdMlDsaError) -> CliError {
    match err {
        ThresholdMlDsaError::InvalidThresholdParameters { .. }
        | ThresholdMlDsaError::InsufficientHonestHolderCoverage { .. }
        | ThresholdMlDsaError::DuplicateOrUnknownParty { .. }
        | ThresholdMlDsaError::UnsupportedLevel
        | ThresholdMlDsaError::ContextTooLong => CliError::usage(format!("{err}")),
        ThresholdMlDsaError::QuorumTooSmall { have, need } => CliError::state(format!(
            "signing quorum too small: have {have} custodians, threshold ML-DSA requires >= {need} (2t - 1)"
        )),
        ThresholdMlDsaError::NoncePersistenceFailed
        | ThresholdMlDsaError::RejectionBudgetExhausted { .. } => {
            CliError::state(format!("threshold ML-DSA nonce/epoch burn refused: {err}"))
        }
        other => CliError::verify(format!("threshold ML-DSA ceremony failed: {other}")),
    }
}

fn run_mldsa_dkg_threads(
    config: &ThresholdMlDsaDkgConfig,
    entropies: &[Secret32],
) -> Result<Vec<(ThresholdMlDsaSignerShare, ZeroizingBuf)>, CliError> {
    let n = config.party_ids.len();
    let hub = SharedMpcHub::new(n);
    let outputs: Vec<Result<_, ThresholdMlDsaError>> = std::thread::scope(|s| {
        let mut handles = Vec::with_capacity(n);
        for (pos, (&party_id, ent)) in config.party_ids.iter().zip(entropies).enumerate() {
            let hub_ref = Arc::clone(&hub);
            let cfg_clone = config.clone();
            let seed_bytes = ent.0;
            handles.push(s.spawn(move || {
                let mut net = RecordingMpc {
                    net: LocalMpcEndpoint {
                        me: pos,
                        hub: Arc::clone(&hub_ref),
                    },
                    transcript: ZeroizingBuf::new(Vec::new()),
                };
                let res = threshold_mldsa_dkg_party(&cfg_clone, party_id, &seed_bytes, &mut net);
                if res.is_err() {
                    hub_ref.abort_all();
                }
                res.map(|share| (share, net.transcript))
            }));
        }
        handles
            .into_iter()
            .map(|h| {
                h.join().unwrap_or(Err(ThresholdMlDsaError::Mpc(
                    qsag_cred::MpcError::Transport,
                )))
            })
            .collect()
    });
    outputs
        .into_iter()
        .collect::<Result<Vec<_>, _>>()
        .map_err(map_mldsa_err)
}

/// The Shamir ceremony for committees above sixteen custodians: the first `2t - 1`
/// custodians sample the key with the replicated ceremony, then all `n` expand it
/// into one Shamir share each.
fn run_mldsa_shamir_ceremony(
    config: &ThresholdMlDsaDkgConfig,
    entropies: &[Secret32],
) -> Result<Vec<ThresholdMlDsaSignerShare>, CliError> {
    let committee = config.shamir_committee().map_err(map_mldsa_err)?;
    let sampled = run_mldsa_dkg_threads(&committee, &entropies[..committee.party_ids.len()])?;
    let n = config.party_ids.len();
    let mut states: Vec<Option<ThresholdMlDsaSignerShare>> =
        sampled.into_iter().map(|(share, _)| Some(share)).collect();
    states.resize_with(n, || None);
    let hub = SharedMpcHub::new(n);
    let outputs: Vec<Result<_, ThresholdMlDsaError>> = std::thread::scope(|s| {
        let mut handles = Vec::with_capacity(n);
        for (pos, ((&party_id, ent), share)) in config
            .party_ids
            .iter()
            .zip(entropies)
            .zip(states)
            .enumerate()
        {
            let hub_ref = Arc::clone(&hub);
            let seed = Secret32::new(cshake256_framed_32(
                b"QSAG.CLI.TMLDSA.SHAMIR.EXPAND_SEED.V1",
                &[&ent.0],
            ));
            handles.push(s.spawn(move || {
                let mut net = LocalMpcEndpoint {
                    me: pos,
                    hub: Arc::clone(&hub_ref),
                };
                let res =
                    threshold_mldsa_shamir_expand_party(config, party_id, share, &seed.0, &mut net);
                if res.is_err() {
                    hub_ref.abort_all();
                }
                res
            }));
        }
        handles
            .into_iter()
            .map(|h| {
                h.join().unwrap_or(Err(ThresholdMlDsaError::Mpc(
                    qsag_cred::MpcError::Transport,
                )))
            })
            .collect()
    });
    outputs
        .into_iter()
        .collect::<Result<Vec<_>, _>>()
        .map_err(map_mldsa_err)
}

fn mldsa_keygen(raw: &[String]) -> Result<(), CliError> {
    let mut opts = vec![
        "threshold",
        "parties",
        "level",
        "backend",
        "vault-dir",
        "public-out",
        "passphrase-env",
        "passphrase-file",
    ];
    opts.extend_from_slice(ANCHOR_NO_VAULT_VALUE_OPTIONS);
    let mut flags = vec!["deterministic", "allow-unencrypted", "json", "help"];
    flags.extend_from_slice(ANCHOR_FLAG_OPTIONS);
    let args = Args::parse(raw, &opts, &flags)?;
    if args.flag("help") {
        println!(
            "qsag cred mldsa-keygen [--threshold <t>] [--parties <n>] [--level <44|65|87>] [--backend rss|shamir] --vault-dir <dir> --public-out <path> [--anchor-dir <dir> | --anchor-tpm-nv <idx> | --anchor-vmgenid | --ephemeral-unanchored] [--passphrase-env <VAR> | --passphrase-file <PATH>] [--allow-unencrypted] [--deterministic] [--json]\n  rss: replicated key shares, at most 16 custodians. shamir: one Shamir share per custodian, at most 64 custodians and threshold 8 (default above 16). Both sign with >= 2t - 1 custodians."
        );
        return Ok(());
    }
    args.no_positionals()?;
    let vault_dir = args.require("vault-dir")?;
    let public_out = args.require("public-out")?;
    let anchor_cfg = AnchorConfig::from_quorum_args(&args, vault_dir)?;
    require_anchor_or_waiver(
        anchor_cfg.is_some(),
        args.flag("ephemeral-unanchored"),
        "anchor-dir",
    )?;
    let passphrase = crate::envelope::passphrase(&args)?;
    if passphrase.is_none() && !args.flag("deterministic") && !args.flag("allow-unencrypted") {
        return Err(CliError::usage(
            "custodian enrollment requires --passphrase-env/--passphrase-file (or explicit --allow-unencrypted)",
        ));
    }
    let threshold = usize::try_from(args.get_u64("threshold")?.unwrap_or(2))
        .map_err(|_| CliError::usage("invalid threshold"))?;
    let parties = usize::try_from(args.get_u64("parties")?.unwrap_or(3))
        .map_err(|_| CliError::usage("invalid party count"))?;
    if parties == 0 || parties > usize::from(u16::MAX) {
        return Err(CliError::usage("parties must be in 1..=65535"));
    }
    let (level, level_name) = parse_mldsa_level(args.get("level"))?;
    ensure_absent(&mldsa_meta_path(vault_dir))?;
    ensure_absent(public_out)?;

    let deterministic = args.flag("deterministic");
    let session_id = if deterministic {
        cshake256_framed_32(
            b"QSAG.CLI.TMLDSA.DET.DKG_SESSION.V1",
            &[
                level_name.as_bytes(),
                &(threshold as u64).to_le_bytes(),
                &(parties as u64).to_le_bytes(),
            ],
        )
    } else {
        os_random_32()?
    };
    let party_ids: Vec<u16> = (1..=u16::try_from(parties)
        .map_err(|_| CliError::usage("parties out of range"))?)
        .collect();
    let dkg_cfg = ThresholdMlDsaDkgConfig {
        level,
        threshold,
        party_ids,
        session_id,
    };
    let shamir = match args.get("backend") {
        None => parties > qsag_cred::rss_mpc::MAX_MPC_PARTIES,
        Some("rss") => false,
        Some("shamir") => true,
        Some(other) => {
            return Err(CliError::usage(format!(
                "unknown ML-DSA --backend '{other}' (expected rss or shamir)"
            )));
        }
    };
    if shamir {
        dkg_cfg.validate_shamir().map_err(map_mldsa_err)?;
    } else {
        dkg_cfg.validate().map_err(map_mldsa_err)?;
    }
    let share_format = if shamir {
        MLDSA_SHAMIR_SHARE_FORMAT
    } else {
        MLDSA_SHARE_FORMAT
    };

    private_dir(vault_dir, true)?;
    for idx in 0..parties {
        let path = mldsa_share_path(vault_dir, idx);
        ensure_absent(&path)?;
        ensure_absent(&format!("{path}.vault.lock"))?;
        let burn_path = mldsa_burn_path(vault_dir, idx);
        let burn_str = burn_path
            .to_str()
            .ok_or_else(|| CliError::usage("burn path must be UTF-8"))?;
        ensure_absent(burn_str)?;
        ensure_absent(&format!("{burn_str}.lock"))?;
    }
    let mut entropies = Vec::with_capacity(parties);
    for idx in 0..parties {
        let seed = if deterministic {
            cshake256_framed_32(
                b"QSAG.CLI.TMLDSA.DET.DKG_SEED.V1",
                &[&session_id, &(idx as u64).to_le_bytes()],
            )
        } else {
            os_random_32()?
        };
        entropies.push(Secret32::new(seed));
    }

    // Custody payload after the magic, burn MAC key, and vault anchor MAC key: the recorded
    // ceremony transcript and its entropy (replicated), or the encoded Shamir share.
    let shares: Vec<(ThresholdMlDsaSignerShare, ZeroizingBuf)> = if shamir {
        run_mldsa_shamir_ceremony(&dkg_cfg, &entropies)?
            .into_iter()
            .map(|share| {
                let encoded = share.to_shamir_bytes().ok_or_else(|| {
                    CliError::state("Shamir ceremony returned a replicated share")
                })?;
                Ok((share, ZeroizingBuf::new(encoded)))
            })
            .collect::<Result<_, CliError>>()?
    } else {
        run_mldsa_dkg_threads(&dkg_cfg, &entropies)?
    };
    let pack = shares[0].0.verification_pack();
    let pk_bytes = pack.pk_bytes.clone();
    let key_id = pack.policy_signing_key_id();
    let issuer_digest = pack.issuer_pk_digest();

    let vault_anchor_mac = Secret32::new(if deterministic {
        cshake256_framed_32(
            b"QSAG.CLI.TMLDSA.DET.ANCHOR_MAC.V1",
            &[&key_id, &session_id],
        )
    } else {
        os_random_32()?
    });
    let anchor_seal = match &anchor_cfg {
        Some(cfg) => Some(VaultPartyGenAnchor::create(
            cfg,
            vault_dir,
            "cred_mldsa",
            key_id,
            &vault_anchor_mac.0,
            parties,
        )?),
        None => None,
    };

    for (idx, ((_, transcript), ent)) in shares.iter().zip(&entropies).enumerate() {
        let mac_key = Secret32::new(if deterministic {
            cshake256_framed_32(
                b"QSAG.CLI.TMLDSA.DET.BURN_MAC.V1",
                &[&key_id, &(idx as u64).to_le_bytes()],
            )
        } else {
            os_random_32()?
        });
        let mut payload = ZeroizingBuf::new(Vec::with_capacity(104 + transcript.len()));
        if shamir {
            payload.0.extend_from_slice(MLDSA_SHAMIR_PAYLOAD_MAGIC);
        } else {
            payload.0.extend_from_slice(MLDSA_RSS_PAYLOAD_MAGIC);
            payload.0.extend_from_slice(&ent.0);
        }
        payload.0.extend_from_slice(&mac_key.0);
        payload.0.extend_from_slice(&vault_anchor_mac.0);
        payload.0.extend_from_slice(transcript);
        let enrollment_nonce = Secret32::new(os_random_32()?);
        let bundle = Json::object(vec![
            ("format", Json::str(share_format)),
            ("enrollment_nonce", Json::hex(&enrollment_nonce[..16])),
            ("scheme", Json::str(level_name)),
            ("party", Json::num(idx)),
            ("threshold", Json::num(threshold)),
            ("parties", Json::num(parties)),
            ("session_id", Json::hex(&session_id)),
            ("key_id", Json::hex(&key_id)),
            ("public_key", Json::hex(&pk_bytes)),
            ("secret_key", Json::hex(&payload)),
        ]);
        write_party_bundle(
            &mldsa_share_path(vault_dir, idx),
            bundle,
            passphrase.as_deref().map(Vec::as_slice),
            MLDSA_BUNDLE_LIMIT,
        )?;
        FsNonceBurnStore::create(mldsa_burn_path(vault_dir, idx), key_id, mac_key.0)
            .map_err(|e| CliError::io("creating threshold ML-DSA nonce burn ledger", e))?;
    }

    let mut meta_fields = vec![
        ("format", Json::str(MLDSA_META_FORMAT)),
        ("share_format", Json::str(share_format)),
        ("scheme", Json::str(level_name)),
        ("threshold", Json::num(threshold)),
        ("parties", Json::num(parties)),
        ("session_id", Json::hex(&session_id)),
        ("key_id", Json::hex(&key_id)),
        ("issuer_pk_digest", Json::hex(&issuer_digest)),
        ("public_key", Json::hex(&pk_bytes)),
    ];
    if shamir {
        // Shamir shares are restored against the public key-generation result.
        meta_fields.push(("verification_pack", Json::hex(&pack.to_bytes())));
    }
    if let Some(seal) = anchor_seal {
        meta_fields.push(("anchor_required", Json::Bool(true)));
        meta_fields.push(("anchor_ceremony_seal", Json::hex(&seal)));
    }
    let meta = Json::object(meta_fields);
    write_new(
        &mldsa_meta_path(vault_dir),
        meta.to_pretty().as_bytes(),
        true,
    )?;

    let pub_doc = Json::object(vec![
        ("format", Json::str(MLDSA_PUB_FORMAT)),
        ("scheme", Json::str(level_name)),
        ("threshold", Json::num(threshold)),
        ("parties", Json::num(parties)),
        ("signing_quorum", Json::num(2 * threshold - 1)),
        ("issuer_pk_digest", Json::hex(&issuer_digest)),
        ("public_key", Json::hex(&pk_bytes)),
    ]);
    write_new(public_out, pub_doc.to_pretty().as_bytes(), false)?;

    if args.flag("json") {
        print!("{}", pub_doc.to_pretty());
    } else {
        println!(
            "generated dealerless ({threshold}, {parties}) {level_name} vault in {vault_dir} (issuer digest {})",
            to_hex(&issuer_digest)
        );
    }
    Ok(())
}

fn parse_party_indices(
    spec: Option<&str>,
    parties: usize,
    default_count: usize,
) -> Result<Vec<usize>, CliError> {
    let Some(spec) = spec else {
        return Ok((0..default_count.min(parties)).collect());
    };
    let mut out = Vec::new();
    for item in spec.split(',') {
        let trimmed = item.trim();
        if trimmed.is_empty() {
            continue;
        }
        let idx: usize = trimmed.parse().map_err(|_| {
            CliError::usage("--signers must be comma-separated 0-based custodian indices")
        })?;
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

fn mldsa_sign(raw: &[String]) -> Result<(), CliError> {
    let mut opts = vec![
        "vault-dir",
        "signers",
        "epoch",
        "in",
        "message",
        "context-hex",
        "out",
        "passphrase-env",
        "passphrase-file",
    ];
    opts.extend_from_slice(ANCHOR_NO_VAULT_VALUE_OPTIONS);
    let mut flags = vec!["deterministic", "json", "help"];
    flags.extend_from_slice(ANCHOR_FLAG_OPTIONS);
    let args = Args::parse(raw, &opts, &flags)?;
    if args.flag("help") {
        println!(
            "qsag cred mldsa-sign --vault-dir <dir> [--signers <i,j,..>] --epoch <n> --in <path|-> [--context-hex <hex>] --out <path> [--anchor-dir <dir> | --anchor-tpm-nv <idx> | --anchor-vmgenid | --ephemeral-unanchored] [--passphrase-env <VAR> | --passphrase-file <PATH>] [--deterministic] [--json]"
        );
        return Ok(());
    }
    args.no_positionals()?;
    let vault_dir = args.require("vault-dir")?;
    let anchor_cfg = AnchorConfig::from_quorum_args(&args, vault_dir)?;
    require_anchor_or_waiver(
        anchor_cfg.is_some(),
        args.flag("ephemeral-unanchored"),
        "anchor-dir",
    )?;
    let passphrase = crate::envelope::passphrase(&args)?;
    let user_epoch = args
        .get_u64("epoch")?
        .ok_or_else(|| CliError::usage("missing required option --epoch <n>"))?;
    if user_epoch == u64::MAX {
        return Err(CliError::usage("--epoch u64::MAX is reserved"));
    }
    let out_path = args.require("out")?;
    ensure_absent(out_path)?;
    private_dir(vault_dir, false)?;

    let msg = read_input_arg(&args)?;
    let ctx = match args.get("context-hex") {
        Some(h) => from_hex(h)?,
        None => ZeroizingBuf::new(Vec::new()),
    };
    if ctx.len() > 255 {
        return Err(CliError::usage("--context-hex must be at most 255 bytes"));
    }

    let meta = load_json_checked(
        &mldsa_meta_path(vault_dir),
        MLDSA_META_FORMAT,
        MAX_KEY_FILE_BYTES,
    )?;
    enforce_anchor_requirement(&meta, anchor_cfg.as_ref())?;
    let scheme_str = meta.field_str("scheme")?;
    let (level, level_name) = parse_mldsa_level(Some(scheme_str))?;
    let threshold = usize::try_from(meta.field_u64("threshold")?)
        .map_err(|_| CliError::input("threshold out of range"))?;
    let parties = usize::try_from(meta.field_u64("parties")?)
        .map_err(|_| CliError::input("parties out of range"))?;
    if parties == 0 || parties > usize::from(u16::MAX) || threshold == 0 || threshold > parties {
        return Err(CliError::input("invalid ML-DSA threshold or party count"));
    }
    let dkg_session_id = from_hex_exact::<32>(meta.field_str("session_id")?, "session_id")?;
    let key_id = from_hex_exact::<32>(meta.field_str("key_id")?, "key_id")?;
    let expected_pk = meta.field_hex("public_key")?;

    let min_quorum = threshold
        .checked_mul(2)
        .and_then(|q| q.checked_sub(1))
        .ok_or_else(|| CliError::input("invalid threshold"))?;
    let signer_indices = parse_party_indices(args.get("signers"), parties, min_quorum)?;
    if signer_indices.len() < min_quorum {
        return Err(CliError::state(format!(
            "signing quorum too small: selected {} custodians, need >= {min_quorum} (2t - 1)",
            signer_indices.len()
        )));
    }

    let dkg_cfg = ThresholdMlDsaDkgConfig {
        level,
        threshold,
        party_ids: (1..=u16::try_from(parties)
            .map_err(|_| CliError::input("invalid party count"))?)
            .collect(),
        session_id: dkg_session_id,
    };
    let share_format = meta.field_str("share_format")?;
    // Shamir vaults pin the public key-generation result their shares restore against.
    let shamir_pack = if share_format == MLDSA_SHAMIR_SHARE_FORMAT {
        dkg_cfg.validate_shamir().map_err(map_mldsa_err)?;
        let pack = ThresholdVerificationPack::from_bytes(&meta.field_hex("verification_pack")?.0)
            .map_err(map_mldsa_err)?;
        if pack.level != level
            || pack.threshold != threshold
            || pack.party_ids != dkg_cfg.party_ids
            || pack.pk_bytes != expected_pk.0
            || pack.policy_signing_key_id() != key_id
        {
            return Err(CliError::state(
                "ML-DSA vault metadata does not match its public key",
            ));
        }
        Some(pack)
    } else if share_format == MLDSA_SHARE_FORMAT {
        dkg_cfg.validate().map_err(map_mldsa_err)?;
        None
    } else {
        return Err(CliError::input("unsupported ML-DSA share format"));
    };

    let mut locks = Vec::with_capacity(signer_indices.len());
    let mut loaded = Vec::with_capacity(signer_indices.len());
    let mut agreed_anchor_mac: Option<Secret32> = None;
    for &idx in &signer_indices {
        let (lock, bundle, opened) = open_party_bundle(
            &mldsa_share_path(vault_dir, idx),
            share_format,
            MLDSA_BUNDLE_LIMIT,
            passphrase.as_deref().map(Vec::as_slice),
        )?;
        if bundle.field_u64("party")? != idx as u64
            || bundle.field_u64("threshold")? != threshold as u64
            || bundle.field_u64("parties")? != parties as u64
            || bundle.field_str("scheme")? != level_name
            || bundle.field_hex("session_id")?.0.as_slice() != dkg_session_id
            || bundle.field_hex("key_id")?.0.as_slice() != key_id
            || bundle.field_hex("public_key")?.0.as_slice() != expected_pk.0.as_slice()
        {
            return Err(CliError::state("ML-DSA share enrollment mismatch"));
        }
        let payload = opened.secret_key()?;
        if let Some(pack) = &shamir_pack {
            if payload.len() < 72 || &payload[..8] != MLDSA_SHAMIR_PAYLOAD_MAGIC {
                return Err(CliError::input(
                    "corrupt or unsupported ML-DSA Shamir share",
                ));
            }
            let mac = Secret32::new(payload[8..40].try_into().unwrap());
            let anchor_mac = Secret32::new(payload[40..72].try_into().unwrap());
            if let Some(prev) = &agreed_anchor_mac {
                if !ct_eq_bytes(&prev.0, &anchor_mac.0) {
                    return Err(CliError::state("ML-DSA custodian anchor MAC mismatch"));
                }
            } else {
                agreed_anchor_mac = Some(anchor_mac);
            }
            let share = ThresholdMlDsaSignerShare::from_shamir_bytes(
                &payload[72..],
                pack.clone(),
                u16::try_from(idx + 1).map_err(|_| CliError::input("party ID out of range"))?,
            )
            .map_err(|e| CliError::input(format!("invalid ML-DSA Shamir share: {e}")))?;
            loaded.push((idx, share, mac));
            locks.push(lock);
            continue;
        }
        if payload.len() < 104 || &payload[..8] != MLDSA_RSS_PAYLOAD_MAGIC {
            return Err(CliError::input("corrupt or unsupported ML-DSA share"));
        }
        let entropy = Secret32::new(payload[8..40].try_into().unwrap());
        let mac = Secret32::new(payload[40..72].try_into().unwrap());
        let anchor_mac = Secret32::new(payload[72..104].try_into().unwrap());
        if let Some(prev) = &agreed_anchor_mac {
            if !ct_eq_bytes(&prev.0, &anchor_mac.0) {
                return Err(CliError::state("ML-DSA custodian anchor MAC mismatch"));
            }
        } else {
            agreed_anchor_mac = Some(anchor_mac);
        }
        let mut restore = RestoringMpc {
            remaining: &payload[104..],
            parties,
        };
        let share = threshold_mldsa_dkg_party(
            &dkg_cfg,
            u16::try_from(idx + 1).map_err(|_| CliError::input("party ID out of range"))?,
            &entropy.0,
            &mut restore,
        )
        .map_err(map_mldsa_err)?;
        if !restore.remaining.is_empty()
            || share.verification_pack().pk_bytes != expected_pk.0.as_slice()
            || share.verification_pack().policy_signing_key_id() != key_id
        {
            return Err(CliError::state("ML-DSA local share restoration mismatch"));
        }
        loaded.push((idx, share, mac));
        locks.push(lock);
    }

    let vault_anchor = match &anchor_cfg {
        Some(cfg) => {
            let root_mac = agreed_anchor_mac
                .as_ref()
                .ok_or_else(|| CliError::state("missing ML-DSA anchor MAC"))?;
            let va = VaultPartyGenAnchor::open(
                cfg,
                vault_dir,
                &meta,
                "cred_mldsa",
                key_id,
                &root_mac.0,
                parties,
            )?;
            let hw = va
                .lock()
                .map_err(|_| CliError::state("ML-DSA anchor mutex poisoned"))?
                .high_water();
            if hw.is_some_and(|prev| user_epoch <= prev) {
                return Err(CliError::state(format!(
                    "threshold ML-DSA epoch {user_epoch} refused by external anchor (high-water {:?})",
                    hw
                )));
            }
            Some(va)
        }
        None => None,
    };

    // Filter to selected active signers (sorted ascending by party_id).
    let quorum_ids: Vec<u16> = signer_indices
        .iter()
        .map(|&idx| u16::try_from(idx + 1).map_err(|_| CliError::input("party ID out of range")))
        .collect::<Result<_, _>>()?;
    let sign_session_id = cshake256_framed_32(
        b"QSAG.CLI.TMLDSA.SIGN_SESSION.V1",
        &[&key_id, &user_epoch.to_le_bytes()],
    );
    let sign_session = ThresholdSignSession {
        session_id: sign_session_id,
        quorum: quorum_ids.clone(),
    };

    let deterministic = args.flag("deterministic");
    let mut selected: Vec<(
        usize,
        ThresholdMlDsaSignerShare,
        AnchoredNonceBurnStore,
        Secret32,
    )> = Vec::with_capacity(signer_indices.len());
    for (idx, mut share, mac_key) in loaded {
        let min_gen = match &vault_anchor {
            Some(va) => va
                .lock()
                .map_err(|_| CliError::state("ML-DSA anchor mutex poisoned"))?
                .party_min_gen(idx)?,
            None => 0,
        };
        let burn_store = FsNonceBurnStore::open_at_least(
            mldsa_burn_path(vault_dir, idx),
            key_id,
            mac_key.0,
            min_gen,
        )
        .map_err(|e| {
            CliError::state(format!(
                "threshold ML-DSA nonce burn ledger rejected (rollback or corruption): {e}"
            ))
        })?;
        let anchored_store = AnchoredNonceBurnStore {
            inner: burn_store,
            party_idx: idx,
            user_epoch,
            vault_anchor: vault_anchor.clone(),
            poisoned: false,
        };
        share
            .recover_epoch_from_store(&anchored_store)
            .map_err(map_mldsa_err)?;
        let sign_ent = if deterministic {
            cshake256_framed_32(
                b"QSAG.CLI.TMLDSA.DET.SIGN_ENT.V1",
                &[&sign_session_id, &(idx as u64).to_le_bytes(), &mac_key.0],
            )
        } else {
            os_random_32()?
        };
        selected.push((idx, share, anchored_store, Secret32::new(sign_ent)));
    }

    let hub = SharedMpcHub::new(selected.len());
    let sign_results: Vec<Result<qsag_cred::ThresholdSignOutput, ThresholdMlDsaError>> =
        std::thread::scope(|s| {
            let mut handles = Vec::with_capacity(selected.len());
            let msg_ref = msg.0.as_slice();
            let ctx_ref = ctx.0.as_slice();
            let sess_ref = &sign_session;
            for (pos, (_idx, mut share, mut store, sign_ent)) in selected.into_iter().enumerate() {
                let hub_ref = Arc::clone(&hub);
                handles.push(s.spawn(move || {
                    let mut net = LocalMpcEndpoint {
                        me: pos,
                        hub: Arc::clone(&hub_ref),
                    };
                    let res = threshold_sign_mldsa_party(
                        &mut share,
                        sess_ref,
                        msg_ref,
                        ctx_ref,
                        &sign_ent.0,
                        &mut store,
                        &mut net,
                    );
                    if res.is_err() {
                        hub_ref.abort_all();
                    }
                    res
                }));
            }
            handles
                .into_iter()
                .map(|h| {
                    h.join().unwrap_or(Err(ThresholdMlDsaError::Mpc(
                        qsag_cred::MpcError::Transport,
                    )))
                })
                .collect()
        });
    drop(locks);

    let mut outputs = Vec::with_capacity(sign_results.len());
    for res in sign_results {
        outputs.push(res.map_err(map_mldsa_err)?);
    }
    let sig_bytes = outputs[0].signature.clone();
    let attempts = outputs[0].attempts;
    for out in &outputs[1..] {
        if out.signature != sig_bytes {
            return Err(CliError::verify(
                "custodians disagreed on assembled FIPS 204 signature",
            ));
        }
    }
    if !ml_dsa_verify(level, &expected_pk, &msg.0, &ctx, &sig_bytes) {
        return Err(CliError::verify(
            "assembled threshold ML-DSA signature failed FIPS 204 self-verification",
        ));
    }

    let sig_doc = Json::object(vec![
        ("format", Json::str(MLDSA_SIG_FORMAT)),
        ("scheme", Json::str(level_name)),
        ("epoch", Json::num(user_epoch)),
        ("attempts", Json::num(attempts)),
        (
            "signers",
            Json::Array(signer_indices.iter().map(|i| Json::num(*i)).collect()),
        ),
        ("context", Json::hex(&ctx)),
        ("signature", Json::hex(&sig_bytes)),
    ]);
    write_new(out_path, sig_doc.to_pretty().as_bytes(), false)?;

    if args.flag("json") {
        let report = Json::object(vec![
            ("operation", Json::str("cred-mldsa-sign")),
            ("scheme", Json::str(level_name)),
            ("epoch", Json::num(user_epoch)),
            ("attempts", Json::num(attempts)),
            ("signature_bytes", Json::num(sig_bytes.len())),
            ("signature_file", Json::str(out_path)),
        ]);
        print!("{}", report.to_pretty());
    } else {
        println!(
            "signed {level_name} message at epoch {user_epoch} in {attempts} attempt(s) ({} B) -> {out_path}",
            sig_bytes.len()
        );
    }
    Ok(())
}

fn mldsa_verify(raw: &[String]) -> Result<(), CliError> {
    let args = Args::parse(
        raw,
        &["public", "in", "message", "context-hex", "sig"],
        &["json", "help"],
    )?;
    if args.flag("help") {
        println!(
            "qsag cred mldsa-verify --public <path> --in <path|-> [--context-hex <hex>] --sig <path> [--json]\n  --context-hex defaults to empty; a signature cannot select its own verification context."
        );
        return Ok(());
    }
    args.no_positionals()?;
    let pub_path = args.require("public")?;
    let sig_path = args.require("sig")?;
    let msg = read_input_arg(&args)?;

    let pub_json = load_json_checked(pub_path, MLDSA_PUB_FORMAT, MAX_KEY_FILE_BYTES)?;
    let sig_json = load_json_checked(sig_path, MLDSA_SIG_FORMAT, MAX_SIG_PROOF_BYTES)?;
    let scheme_name = pub_json.field_str("scheme")?;
    if sig_json.field_str("scheme")? != scheme_name {
        return Err(CliError::verify(
            "signature scheme does not match threshold ML-DSA public key",
        ));
    }
    let (level, _) = parse_mldsa_level(Some(scheme_name))?;
    let pk_bytes = pub_json.field_hex("public_key")?;
    let sig_bytes = sig_json.field_hex("signature")?;
    let ctx = match args.get("context-hex") {
        Some(h) => from_hex(h)?,
        None => ZeroizingBuf::new(Vec::new()),
    };

    if sig_json.get("context").is_some() && sig_json.field_hex("context")?.0 != ctx.0 {
        return Err(CliError::verify(
            "signature context does not match --context-hex (default: empty)",
        ));
    }
    if !ml_dsa_verify(level, &pk_bytes, &msg.0, &ctx, &sig_bytes) {
        return Err(CliError::verify(
            "FIPS 204 ML-DSA signature verification failed",
        ));
    }

    if args.flag("json") {
        let report = Json::object(vec![
            ("valid", Json::Bool(true)),
            ("scheme", Json::str(scheme_name)),
            ("signature_bytes", Json::num(sig_bytes.len())),
        ]);
        print!("{}", report.to_pretty());
    } else {
        println!("valid ({scheme_name})");
    }
    Ok(())
}

pub fn run(raw: &[String]) -> Result<(), CliError> {
    let Some((sub, rest)) = raw.split_first() else {
        print!("{CRED_HELP}");
        return Err(CliError::usage("cred requires a subcommand (try --help)"));
    };
    match sub.as_str() {
        "--help" | "-h" | "help" => {
            print!("{CRED_HELP}");
            Ok(())
        }
        "voprf-keygen" => voprf_keygen(rest),
        "voprf-eval" => voprf_eval(rest),
        "mldsa-keygen" => mldsa_keygen(rest),
        "mldsa-sign" => mldsa_sign(rest),
        "mldsa-verify" => mldsa_verify(rest),
        other => Err(CliError::usage(format!(
            "unknown cred subcommand '{other}' (expected voprf-keygen, voprf-eval, mldsa-keygen, mldsa-sign, or mldsa-verify)"
        ))),
    }
}

#[cfg(test)]
mod local_share_tests {
    use super::*;

    #[test]
    fn toprf_abort_refuses_future_phases() {
        let hub = SharedToprfHub::new();
        hub.abort_all();
        let mut endpoint = LocalToprfEndpoint { party: 0, hub };
        assert!(
            voprf::Transport::exchange(
                &mut endpoint,
                [0; 32],
                core::array::from_fn(|_| Vec::new())
            )
            .is_err()
        );
        assert!(voprf::Transport::broadcast(&mut endpoint, [1; 32], Vec::new()).is_err());
    }

    #[test]
    fn enrollment_abort_also_refuses_rounds_not_yet_created() {
        let hub = SharedMpcHub::new(2);
        hub.abort_all();
        let mut endpoint = LocalMpcEndpoint { me: 0, hub };
        assert!(
            endpoint
                .exchange(
                    RoundInfo {
                        index: 0,
                        phase: 0,
                        kind: RoundKind::KeySetup
                    },
                    vec![Vec::new(); 2],
                    Vec::new(),
                )
                .is_err()
        );
    }

    #[test]
    fn local_restoration_rejects_wrong_round_and_hostile_lengths() {
        let info = RoundInfo {
            index: 7,
            phase: 2,
            kind: RoundKind::Confirm,
        };
        let private = vec![Vec::new(), vec![3]];
        let broadcast = vec![4];
        let binding = round_binding(info, &private, &broadcast);
        let mut encoded = binding.to_vec();
        for row in [vec![vec![], vec![5]], vec![vec![6], vec![7]]] {
            encoded.extend_from_slice(&2u64.to_le_bytes());
            for bytes in row {
                encoded.extend_from_slice(&(bytes.len() as u64).to_le_bytes());
                encoded.extend_from_slice(&bytes);
            }
        }
        let mut net = RestoringMpc {
            remaining: &encoded,
            parties: 2,
        };
        let inbox = net
            .exchange(info, private.clone(), broadcast.clone())
            .unwrap();
        assert_eq!(inbox.private[1], [5]);
        assert_eq!(inbox.broadcast, [vec![6], vec![7]]);
        assert!(net.remaining.is_empty());
        let mut net = RestoringMpc {
            remaining: &encoded,
            parties: 2,
        };
        assert!(
            net.exchange(
                RoundInfo { index: 8, ..info },
                private.clone(),
                broadcast.clone()
            )
            .is_err()
        );
        for len in 0..encoded.len() {
            let mut net = RestoringMpc {
                remaining: &encoded[..len],
                parties: 2,
            };
            assert!(
                net.exchange(info, private.clone(), broadcast.clone())
                    .is_err()
            );
        }
        encoded[40..48].copy_from_slice(&u64::MAX.to_le_bytes());
        let mut net = RestoringMpc {
            remaining: &encoded,
            parties: 2,
        };
        assert!(net.exchange(info, private, broadcast).is_err());
    }
}
