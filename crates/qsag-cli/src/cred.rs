//! Post-quantum threshold credential & standard-verifier FIPS 204 threshold ML-DSA CLI
//! ceremonies (`qsag cred`), backed by [`qsag_cred::voprf`] and [`qsag_cred::threshold_mldsa`].
//!
//! Subcommands:
//! - `voprf-keygen` — 5-party `(2, 5)` dealerless verifiable lattice OPRF setup (`PiVoprf`).
//! - `voprf-eval`   — Blinded client query + 5-server replicated evaluation with durable
//!                    monotone counter reservation.
//! - `mldsa-keygen` — Dealerless `(t, n)` threshold FIPS 204 ML-DSA (`44`/`65`/`87`) setup.
//! - `mldsa-sign`   — Sealed-`w1` abort-private `(2t - 1)`-of-`n` threshold FIPS 204 signing
//!                    with crash-atomic [`FsNonceBurnStore`] persistence.
//! - `mldsa-verify` — Standard unmodified FIPS 204 `ml_dsa_verify` check.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Condvar, Mutex};

use qsag_accel::ct::ct_zeroize_bytes;
use qsag_accel::keccak::cshake256_framed_32;
use qsag_cred::voprf::{self, CounterStore, PublicKey as ToprfPublicKey, SERVERS as TOPRF_SERVERS};
use qsag_cred::{
    FsNonceBurnStore, MlDsaLevel, MpcTransport, MpcTransportError, RoundInbox, RoundInfo,
    ThresholdMlDsaDkgConfig, ThresholdMlDsaError, ThresholdMlDsaSignerShare, ThresholdSignSession,
    ml_dsa_verify, threshold_mldsa_dkg_party, threshold_sign_mldsa_party,
};

use crate::cli::{
    Args, CliError, MAX_KEY_FILE_BYTES, MAX_SIG_PROOF_BYTES, Secret32, ZeroizingBuf, os_random_32,
    private_dir, read_bounded_file, read_input, replace_secret, write_new,
};
use crate::codec::{Json, from_hex, from_hex_exact, to_hex};

const CRED_HELP: &str = "\
qsag cred <subcommand> [options]

Post-quantum threshold credential & standard-verifier FIPS 204 threshold ML-DSA ceremonies:
  voprf-keygen  run dealerless (2, 5) lattice TOPRF setup into a private custodian vault
  voprf-eval    evaluate a blinded input across the (2, 5) TOPRF committee (monotone counter)
  mldsa-keygen  run dealerless (t, n) threshold FIPS 204 ML-DSA key generation (44 / 65 / 87)
  mldsa-sign    co-sign a message with >= 2t - 1 threshold ML-DSA custodians (sealed-w1 ZK)
  mldsa-verify  verify a standard FIPS 204 ML-DSA signature against the threshold public key
";

const VOPRF_META_FORMAT: &str = "qsag-cred-voprf-meta-v1";
const VOPRF_PUB_FORMAT: &str = "qsag-cred-voprf-public-v1";
const VOPRF_EVAL_FORMAT: &str = "qsag-cred-voprf-eval-v1";
const VOPRF_COUNTER_FORMAT: &str = "qsag-cred-voprf-counter-v1";

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
    let text =
        std::str::from_utf8(&bytes.0).map_err(|_| CliError::input(format!("{path} is not UTF-8")))?;
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
        for slot in &mut self.private {
            if let Some(arr) = slot {
                for buf in arr {
                    ct_zeroize_bytes(buf);
                }
            }
        }
        for slot in &mut self.broadcast {
            if let Some(buf) = slot {
                ct_zeroize_bytes(buf);
            }
        }
    }
}

struct SharedToprfHub {
    phases: Mutex<BTreeMap<([u8; 32], bool), ToprfPhaseSlot>>,
    cv: Condvar,
}

impl SharedToprfHub {
    fn new() -> Arc<Self> {
        Arc::new(Self {
            phases: Mutex::new(BTreeMap::new()),
            cv: Condvar::new(),
        })
    }

    fn abort_all(&self) {
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
        let mut guard = self.hub.phases.lock().map_err(|_| voprf::Error::Transport)?;
        {
            let slot = guard.entry(key).or_default();
            if slot.aborted || slot.private[self.party].is_some() {
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
            if slot.aborted {
                return Err(voprf::Error::Transport);
            }
            if slot.arrivals == TOPRF_SERVERS {
                let inbox = core::array::from_fn(|sender| {
                    slot.private[sender]
                        .as_ref()
                        .map(|msgs| msgs[self.party].clone())
                        .unwrap_or_default()
                });
                return Ok(inbox);
            }
            guard = self.hub.cv.wait(guard).map_err(|_| voprf::Error::Transport)?;
        }
    }

    fn broadcast(
        &mut self,
        phase: [u8; 32],
        message: Vec<u8>,
    ) -> Result<[Vec<u8>; TOPRF_SERVERS], voprf::Error> {
        let key = (phase, true);
        let mut guard = self.hub.phases.lock().map_err(|_| voprf::Error::Transport)?;
        {
            let slot = guard.entry(key).or_default();
            if slot.aborted || slot.broadcast[self.party].is_some() {
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
            if slot.aborted {
                return Err(voprf::Error::Transport);
            }
            if slot.arrivals == TOPRF_SERVERS {
                let inbox = core::array::from_fn(|sender| {
                    slot.broadcast[sender].clone().unwrap_or_default()
                });
                return Ok(inbox);
            }
            guard = self.hub.cv.wait(guard).map_err(|_| voprf::Error::Transport)?;
        }
    }
}

struct FsToprfCounterStore {
    path: String,
    expected_key: [u8; 32],
    expected_party: usize,
}

impl CounterStore for FsToprfCounterStore {
    fn high_water(&self) -> Result<Option<u64>, voprf::Error> {
        let json = load_json_checked(&self.path, VOPRF_COUNTER_FORMAT, MAX_KEY_FILE_BYTES)
            .map_err(|_| voprf::Error::Counter)?;
        let key = from_hex_exact::<32>(
            json.field_str("key").map_err(|_| voprf::Error::Counter)?,
            "counter key",
        )
        .map_err(|_| voprf::Error::Counter)?;
        let party = json
            .field_u64("party")
            .map_err(|_| voprf::Error::Counter)? as usize;
        if key != self.expected_key || party != self.expected_party {
            return Err(voprf::Error::Counter);
        }
        match json.get("high_water") {
            Some(Json::Null) => Ok(None),
            Some(v) => v.as_u64().map(Some).ok_or(voprf::Error::Counter),
            None => Err(voprf::Error::Counter),
        }
    }

    fn reserve(
        &mut self,
        key: &[u8; 32],
        party: usize,
        counter: u64,
        items: usize,
    ) -> Result<(), voprf::Error> {
        if key != &self.expected_key || party != self.expected_party || items == 0 {
            return Err(voprf::Error::Counter);
        }
        let prev = self.high_water()?;
        if prev.is_some_and(|hw| counter <= hw) || counter == u64::MAX {
            return Err(voprf::Error::Counter);
        }
        let doc = Json::object(vec![
            ("format", Json::str(VOPRF_COUNTER_FORMAT)),
            ("party", Json::num(party)),
            ("key", Json::hex(key)),
            ("high_water", Json::num(counter)),
        ]);
        replace_secret(&self.path, doc.to_pretty().as_bytes()).map_err(|_| voprf::Error::Counter)
    }
}

fn voprf_meta_path(vault_dir: &str) -> String {
    Path::new(vault_dir)
        .join("voprf-meta.json")
        .to_string_lossy()
        .into_owned()
}

fn voprf_seed_path(vault_dir: &str, party: usize) -> String {
    Path::new(vault_dir)
        .join(format!("voprf-party-{party}.seed"))
        .to_string_lossy()
        .into_owned()
}

fn voprf_counter_path(vault_dir: &str, party: usize) -> String {
    Path::new(vault_dir)
        .join(format!("voprf-counter-{party}.json"))
        .to_string_lossy()
        .into_owned()
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
    let args = Args::parse(
        raw,
        &["vault-dir", "public-out"],
        &["deterministic", "json", "help"],
    )?;
    if args.flag("help") {
        println!(
            "qsag cred voprf-keygen --vault-dir <dir> --public-out <path> [--deterministic] [--json]"
        );
        return Ok(());
    }
    args.no_positionals()?;
    let vault_dir = args.require("vault-dir")?;
    let public_out = args.require("public-out")?;
    ensure_absent(&voprf_meta_path(vault_dir))?;
    ensure_absent(public_out)?;
    private_dir(vault_dir, true)?;

    let deterministic = args.flag("deterministic");
    let session = if deterministic {
        cshake256_framed_32(b"QSAG.CLI.TOPRF.DET.SESSION.V1", &[b"voprf-keygen"])
    } else {
        os_random_32()?
    };
    let entropies: [Secret32; TOPRF_SERVERS] = core::array::from_fn(|party| {
        let bytes = if deterministic {
            cshake256_framed_32(
                b"QSAG.CLI.TOPRF.DET.SEED.V1",
                &[&(party as u64).to_le_bytes()],
            )
        } else {
            os_random_32().unwrap_or([0u8; 32])
        };
        Secret32(bytes)
    });
    if !deterministic && entropies.iter().any(|s| s.0 == [0u8; 32]) {
        return Err(CliError::new(
            crate::cli::exit::IO,
            "OS CSPRNG returned all-zero entropy",
        ));
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

    for (party, ent) in entropies.iter().enumerate() {
        write_new(&voprf_seed_path(vault_dir, party), &ent.0, true)?;
        let counter_doc = Json::object(vec![
            ("format", Json::str(VOPRF_COUNTER_FORMAT)),
            ("party", Json::num(party)),
            ("key", Json::hex(&commitment)),
            ("high_water", Json::Null),
        ]);
        write_new(
            &voprf_counter_path(vault_dir, party),
            counter_doc.to_pretty().as_bytes(),
            true,
        )?;
    }

    let meta = Json::object(vec![
        ("format", Json::str(VOPRF_META_FORMAT)),
        ("threshold", Json::num(2)),
        ("parties", Json::num(TOPRF_SERVERS)),
        ("session_id", Json::hex(&session)),
        ("commitment", Json::hex(&commitment)),
    ]);
    write_new(&voprf_meta_path(vault_dir), meta.to_pretty().as_bytes(), true)?;

    let pub_doc = Json::object(vec![
        ("format", Json::str(VOPRF_PUB_FORMAT)),
        ("scheme", Json::str("voprf-poseidon2-2of5")),
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
    let args = Args::parse(
        raw,
        &["vault-dir", "public", "counter", "in", "message", "out"],
        &["deterministic", "json", "help"],
    )?;
    if args.flag("help") {
        println!(
            "qsag cred voprf-eval --vault-dir <dir> --public <path> --counter <n> --in <path|-> --out <path> [--deterministic] [--json]"
        );
        return Ok(());
    }
    args.no_positionals()?;
    let vault_dir = args.require("vault-dir")?;
    let public_path = args.require("public")?;
    let counter = args
        .get_u64("counter")?
        .ok_or_else(|| CliError::usage("missing required option --counter <n>"))?;
    let out_path = args.require("out")?;
    ensure_absent(out_path)?;
    private_dir(vault_dir, false)?;

    let input = read_input_arg(&args)?;
    let meta = load_json_checked(&voprf_meta_path(vault_dir), VOPRF_META_FORMAT, MAX_KEY_FILE_BYTES)?;
    let pub_json = load_json_checked(public_path, VOPRF_PUB_FORMAT, MAX_KEY_FILE_BYTES)?;
    let session = from_hex_exact::<32>(meta.field_str("session_id")?, "session_id")?;
    let commitment = from_hex_exact::<32>(meta.field_str("commitment")?, "commitment")?;
    let pub_commitment = from_hex_exact::<32>(pub_json.field_str("commitment")?, "public commitment")?;
    if commitment != pub_commitment {
        return Err(CliError::verify(
            "public file commitment does not match TOPRF vault",
        ));
    }

    let mut entropies = [
        Secret32([0; 32]),
        Secret32([0; 32]),
        Secret32([0; 32]),
        Secret32([0; 32]),
        Secret32([0; 32]),
    ];
    for (party, slot) in entropies.iter_mut().enumerate() {
        let raw_seed = read_bounded_file(&voprf_seed_path(vault_dir, party), 64)?;
        if raw_seed.0.len() != 32 {
            return Err(CliError::input("corrupt TOPRF party seed length"));
        }
        slot.0.copy_from_slice(&raw_seed.0);
    }

    let servers = run_voprf_dkg_threads(session, &entropies)?;
    let pk = ToprfPublicKey::from_commitment(commitment);

    let deterministic = args.flag("deterministic");
    let eval_session = if deterministic {
        cshake256_framed_32(
            b"QSAG.CLI.TOPRF.DET.EVAL_SESSION.V1",
            &[&commitment, &counter.to_le_bytes()],
        )
    } else {
        os_random_32()?
    };
    let client_entropy = Secret32(if deterministic {
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
        voprf::Error::Counter | voprf::Error::Quota => {
            CliError::state(format!("TOPRF request rejected: {e}"))
        }
        other => CliError::usage(format!("TOPRF blind failed: {other}")),
    })?;

    let hub = SharedToprfHub::new();
    let eval_results: Vec<Result<voprf::Output, voprf::Error>> = std::thread::scope(|s| {
        let mut handles = Vec::with_capacity(TOPRF_SERVERS);
        for ((party, mut srv), req) in servers.into_iter().enumerate().zip(requests) {
            let hub_ref = Arc::clone(&hub);
            let counter_file = voprf_counter_path(vault_dir, party);
            handles.push(s.spawn(move || {
                let mut store = FsToprfCounterStore {
                    path: counter_file,
                    expected_key: commitment,
                    expected_party: party,
                };
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

    let mut outputs_vec = Vec::with_capacity(TOPRF_SERVERS);
    for res in eval_results {
        match res {
            Ok(out) => outputs_vec.push(Some(out)),
            Err(voprf::Error::Counter | voprf::Error::Quota) => {
                return Err(CliError::state(format!(
                    "TOPRF monotone counter {counter} refused (already spent or outside window)"
                )));
            }
            Err(other) => {
                return Err(CliError::verify(format!(
                    "TOPRF evaluation aborted: {other}"
                )));
            }
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
        ("scheme", Json::str("voprf-poseidon2-2of5")),
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
