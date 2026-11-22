//! One CNF custodian per process. Transport readers drain one bounded packet ahead
//! so simultaneous large MPC sends cannot deadlock on full duplex socket buffers.

use std::io::{self, Read, Write};
use std::net::{Shutdown, SocketAddr, TcpListener, TcpStream};
use std::sync::mpsc::{Receiver, sync_channel};
use std::time::{Duration, Instant};

use crate::anchor::{AnchorConfig, FsExternalMountAnchor};
use crate::cli::{
    Args, CliError, MAX_KEY_FILE_BYTES, Secret32, os_random_32, private_dir, read_bounded_file,
    read_input, write_new,
};
use crate::codec::from_hex_exact;
use qsag_core::cnf_rss::{CnfRssConfig, CnfRssKeyShare256};
use qsag_core::fips205::{Fips205Params, SlhPublicKey, slh_verify};
use qsag_fts::{FrontierFtsProfile, FrontierFtsPublicKey, FsWalFtsEpochLatch};
use qsag_quorum::hash::{SeedRng, h32, mac32, mac32_verify};
use qsag_quorum::party_node::PoisonJournal;
use qsag_quorum::poison_journal::{FsDurablePoisonAndSessionJournal, JournalOpenMode};
use qsag_quorum::wire_channel::{MAX_FRAME_PAYLOAD, TransportError, WireTransport};
use qsag_quorum::{IsolatedCnfParty, run_isolated_cnf_dkg};

const HELP: &str = "\
qsag quorum wire <dkg|init|public|sign> --vault-dir DIR --anchor-dir DIR
    --deployment-id HEX32 --profile SLH-DSA-SHAKE-128F [options]

To generate shares, provision vault-dir/links with one 32-byte pairwise secret per
roster member in order (zero for self). Run dkg at each endpoint with --party INDEX
--threshold T --peers ADDRESSES --session HEX32. This writes only its local share.
Alternatively import this party's QSCNFK01 file as vault-dir/share. Run init once per
custodian. The profile and deployment are fixed at init. Use a separate anchor per
party. Frontier profiles Compact1122 and Full256Bit use a 32-byte CNF share and
a separate one-use burn anchor. TPM enrollment needs two consecutive counters for
Frontier and one for SLH-DSA. Wire DKG uses the next NV index after those. --anchor-tpm-nv INDEX may replace --anchor-dir.
Directory anchors normally
require a different device (--allow-single-disk-anchor waives device isolation).

Run public, then sign, on every roster member with matching --peers ADDR,ADDR,...
(in zero-based party order) and a fresh common --session HEX32 for each ceremony.
public writes the raw public key (seed followed by root) to --out PATH and authenticates a copy
in the vault. sign reads --in FILE and writes the raw signature to --out PATH.
";

const DEADLINE: Duration = Duration::from_secs(120);

struct Peer {
    tx: TcpStream,
    rx: Receiver<io::Result<Vec<u8>>>,
}
impl Drop for Peer {
    fn drop(&mut self) {
        let _ = self.tx.shutdown(Shutdown::Both);
    }
}
struct Mesh {
    me: usize,
    peers: Vec<Option<Peer>>,
}

fn packet(rx: &mut TcpStream) -> io::Result<Vec<u8>> {
    let mut len = [0; 4];
    rx.read_exact(&mut len)?;
    let len = u32::from_be_bytes(len) as usize;
    if !(qsag_quorum::wire_channel::SEALED_FRAME_OVERHEAD..=MAX_FRAME_PAYLOAD).contains(&len) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "invalid sealed frame length",
        ));
    }
    let mut bytes = vec![0; len];
    rx.read_exact(&mut bytes)?;
    Ok(bytes)
}

fn peer(stream: TcpStream) -> io::Result<Peer> {
    stream.set_nodelay(true)?;
    stream.set_write_timeout(Some(DEADLINE))?;
    stream.set_read_timeout(Some(DEADLINE))?;
    let mut reader = stream.try_clone()?;
    let (tx, rx) = sync_channel(1);
    std::thread::Builder::new().spawn(move || {
        loop {
            let p = packet(&mut reader);
            let failed = p.is_err();
            if tx.send(p).is_err() || failed {
                break;
            }
        }
    })?;
    Ok(Peer { tx: stream, rx })
}

impl Mesh {
    fn connect(me: usize, addrs: &[SocketAddr]) -> io::Result<Self> {
        let listener = TcpListener::bind(addrs[me])?;
        listener.set_nonblocking(true)?;
        let until = Instant::now() + DEADLINE;
        let mut peers: Vec<Option<Peer>> = (0..addrs.len()).map(|_| None).collect();
        for (idx, addr) in addrs[..me].iter().enumerate() {
            let mut stream = loop {
                match TcpStream::connect_timeout(addr, Duration::from_millis(500)) {
                    Ok(stream) => break stream,
                    Err(e)
                        if matches!(
                            e.kind(),
                            io::ErrorKind::ConnectionRefused | io::ErrorKind::TimedOut
                        ) && Instant::now() < until =>
                    {
                        std::thread::sleep(Duration::from_millis(40))
                    }
                    Err(e) => return Err(e),
                }
            };
            stream.set_write_timeout(Some(DEADLINE))?;
            stream.write_all(&[me as u8])?;
            peers[idx] = Some(peer(stream)?);
        }
        for _ in me + 1..addrs.len() {
            let mut stream = loop {
                match listener.accept() {
                    Ok((stream, _)) => break stream,
                    Err(e) if e.kind() == io::ErrorKind::WouldBlock && Instant::now() < until => {
                        std::thread::sleep(Duration::from_millis(20))
                    }
                    Err(e) => return Err(e),
                }
            };
            let mut id = [0];
            stream.set_read_timeout(Some(DEADLINE))?;
            stream.read_exact(&mut id)?;
            let idx = usize::from(id[0]);
            // The id routes the socket. Only the peer-specific EtM key authenticates it.
            if idx <= me || idx >= peers.len() || peers[idx].is_some() {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "invalid peer route",
                ));
            }
            peers[idx] = Some(peer(stream)?);
        }
        Ok(Self { me, peers })
    }
}

impl WireTransport for Mesh {
    fn party(&self) -> usize {
        self.me
    }
    fn parties(&self) -> usize {
        self.peers.len()
    }
    fn send_frame(&mut self, to: usize, _round: u32, payload: &[u8]) -> Result<(), TransportError> {
        let p = self
            .peers
            .get_mut(to)
            .and_then(Option::as_mut)
            .ok_or(TransportError::UnknownPeer { peer: to })?;
        if payload.len() > MAX_FRAME_PAYLOAD {
            return Err(TransportError::PayloadTooLarge);
        }
        p.tx.write_all(&(payload.len() as u32).to_be_bytes())
            .and_then(|()| p.tx.write_all(payload))
            .map_err(|_| TransportError::Closed { peer: to })
    }
    fn recv_frame(&mut self, _from: usize, _round: u32) -> Result<Vec<u8>, TransportError> {
        Err(TransportError::AuthenticationFailed)
    }
    fn recv_authenticated_envelope(
        &mut self,
        from: usize,
        _round: u32,
    ) -> Result<Vec<u8>, TransportError> {
        self.peers
            .get(from)
            .and_then(Option::as_ref)
            .ok_or(TransportError::UnknownPeer { peer: from })?
            .rx
            .recv_timeout(DEADLINE)
            .map_err(|_| TransportError::Closed { peer: from })?
            .map_err(|_| TransportError::Closed { peer: from })
    }
}

#[derive(Clone, Copy)]
enum Profile {
    Slh(Fips205Params),
    Frontier(FrontierFtsProfile),
}

impl Profile {
    fn parse(s: &str) -> Result<Self, CliError> {
        match s.to_ascii_lowercase().as_str() {
            "compact1122" | "fts-compact-1122" => {
                Ok(Self::Frontier(FrontierFtsProfile::Compact1122))
            }
            "full256bit" | "fts-frontier-2338" => {
                Ok(Self::Frontier(FrontierFtsProfile::Full256Bit))
            }
            _ => Fips205Params::ALL_OFFICIAL
                .into_iter()
                .find(|p| p.name.eq_ignore_ascii_case(s))
                .map(Self::Slh)
                .ok_or_else(|| CliError::usage("unknown wire custody profile")),
        }
    }
    fn name(self) -> &'static str {
        match self {
            Self::Slh(p) => p.name,
            Self::Frontier(FrontierFtsProfile::Compact1122) => "Compact1122",
            Self::Frontier(_) => "Full256Bit",
        }
    }
    fn width(self) -> usize {
        match self {
            Self::Slh(p) => p.n,
            Self::Frontier(_) => 32,
        }
    }
}

fn addresses(args: &Args) -> Result<Vec<SocketAddr>, CliError> {
    let addrs = args
        .require("peers")?
        .split(',')
        .map(str::parse::<SocketAddr>)
        .collect::<Result<Vec<_>, _>>()
        .map_err(|_| CliError::usage("peers must be comma-separated numeric socket addresses"))?;
    if addrs
        .iter()
        .collect::<std::collections::BTreeSet<_>>()
        .len()
        != addrs.len()
    {
        return Err(CliError::usage(
            "one distinct address per enrolled party is required",
        ));
    }
    Ok(addrs)
}

fn dkg(
    args: &Args,
    vault: &str,
    config: &AnchorConfig,
    deployment: [u8; 32],
    profile: Profile,
) -> Result<(), CliError> {
    let addrs = addresses(args)?;
    let me = args
        .get_u64("party")?
        .and_then(|n| usize::try_from(n).ok())
        .filter(|i| *i < addrs.len())
        .ok_or_else(|| CliError::usage("--party must be a zero-based index in --peers"))?;
    let t = args
        .get_u64("threshold")?
        .and_then(|n| usize::try_from(n).ok())
        .ok_or_else(|| CliError::usage("--threshold is required"))?;
    let cfg =
        CnfRssConfig::new(t, addrs.len()).map_err(|_| CliError::usage("invalid CNF roster"))?;
    if !cfg.supports_pure_hash_multiplication() {
        return Err(CliError::usage(
            "threshold requires an honest-majority CNF roster",
        ));
    }
    let links_path = format!("{vault}/links");
    let share_path = format!("{vault}/share");
    match std::fs::symlink_metadata(&share_path) {
        Ok(_) => return Err(CliError::state("this vault already contains a share")),
        Err(e) if e.kind() == io::ErrorKind::NotFound => (),
        Err(e) => return Err(CliError::io("checking share destination", e)),
    }
    let extra = if matches!(profile, Profile::Frontier(_)) {
        2
    } else {
        1
    };
    let config = config.tpm_slot(extra, extra + 1)?;
    config.validate_isolation(&[&links_path], &[vault], true)?;
    let bytes = read_bounded_file(&links_path, (32 * addrs.len()) as u64)?;
    if bytes.len() != 32 * addrs.len() {
        return Err(CliError::input(
            "link key file must hold one 32-byte entry per party",
        ));
    }
    let links = bytes.as_chunks::<32>().0;
    if links[me] != [0; 32]
        || links
            .iter()
            .enumerate()
            .any(|(i, k)| i != me && (*k == [0; 32] || links[..i].contains(k)))
    {
        return Err(CliError::input(
            "each peer requires a distinct nonzero pairwise key; self entry must be zero",
        ));
    }
    let nonce = from_hex_exact::<32>(args.require("session")?, "session")?;
    let id = h32(
        b"QSAG.CNF.DKG.ANCHOR-ID/v1",
        &[
            &deployment,
            &[me as u8, t as u8, addrs.len() as u8],
            profile.name().as_bytes(),
        ],
    );
    let key = Secret32::new(h32(b"QSAG.CNF.DKG.JOURNAL/v1", &[&id, &bytes]));
    let akey = mac32(&key, b"QSAG.CNF.ANCHOR/v1", &[&id]);
    let sid = h32(
        b"QSAG.CNF.DKG.SESSION/v1",
        &[
            &deployment,
            &nonce,
            &[t as u8, addrs.len() as u8],
            profile.name().as_bytes(),
        ],
    );
    let log = format!("{vault}/dkg-journal");
    let j = match std::fs::symlink_metadata(&log) {
        Ok(_) => {
            let a = FsExternalMountAnchor::open_existing(
                &config,
                &[&links_path],
                &[vault],
                "cnf-dkg",
                id,
                akey,
            )?;
            FsDurablePoisonAndSessionJournal::start_next_anchored(&log, *key, sid, Box::new(a))
        }
        Err(e) if e.kind() == io::ErrorKind::NotFound => {
            crate::anchor::preflight_tpm_enrollment(Some(&config), args, 1)?;
            let a = FsExternalMountAnchor::provision_fresh(
                &config,
                &[&links_path],
                &[vault],
                "cnf-dkg",
                id,
                akey,
            )?;
            FsDurablePoisonAndSessionJournal::open_anchored(
                &log,
                *key,
                sid,
                JournalOpenMode::CreateNew,
                Box::new(a),
            )
        }
        Err(e) => return Err(CliError::io("checking DKG journal", e)),
    };
    let mut journal = j.map_err(|e| CliError::state(e.to_string()))?;
    journal
        .reserve_session(&sid)
        .map_err(|e| CliError::state(e.to_string()))?;
    let mesh = Mesh::connect(me, &addrs).map_err(|e| CliError::io("connecting DKG peers", e))?;
    let mut rng = SeedRng::new(&Secret32::new(os_random_32()?), &sid);
    let keys = run_isolated_cnf_dkg(
        &cfg,
        profile.width(),
        deployment,
        mesh,
        sid,
        links.to_vec(),
        &mut rng,
    )
    .map_err(|e| CliError::state(format!("CNF DKG: {e}")))?;
    let share = keys
        .finish_enrollment()
        .map_err(|e| CliError::state(e.to_string()))?;
    write_new(&share_path, &share.to_secret_bytes(), true)
}

pub fn run(raw: &[String]) -> Result<(), CliError> {
    if raw.is_empty() || raw.iter().any(|a| a == "--help") {
        print!("{HELP}");
        return Ok(());
    }
    let op = raw[0].as_str();
    if !matches!(op, "dkg" | "init" | "public" | "sign") {
        return Err(CliError::usage(HELP));
    }
    let mut options = vec![
        "vault-dir",
        "anchor-dir",
        "anchor-tpm-nv",
        "anchor-tpm-device",
        "anchor-tpm-auth-env",
        "deployment-id",
        "profile",
    ];
    if op != "init" {
        options.extend(["session", "peers"]);
    }
    if op == "dkg" {
        options.extend(["threshold", "party"]);
    }
    if matches!(op, "public" | "sign") {
        options.push("out");
    }
    if op == "sign" {
        options.push("in");
    }
    let args = Args::parse(&raw[1..], &options, &["allow-single-disk-anchor"])?;
    args.no_positionals()?;
    let vault = args.require("vault-dir")?;
    let config = AnchorConfig::from_quorum_args(&args, vault)?
        .ok_or_else(|| CliError::usage("wire custody requires --anchor-dir or --anchor-tpm-nv"))?;
    private_dir(vault, false)?;
    let deploy = from_hex_exact::<32>(args.require("deployment-id")?, "deployment id")?;
    let profile = Profile::parse(args.require("profile")?)?;
    if op == "dkg" {
        return dkg(&args, vault, &config, deploy, profile);
    }
    let anchor_slots = if matches!(profile, Profile::Frontier(_)) {
        2
    } else {
        1
    };
    crate::anchor::preflight_tpm_enrollment(
        (op == "init").then_some(&config),
        &args,
        anchor_slots,
    )?;
    let session_cfg = config.tpm_slot(0, anchor_slots)?;
    let path = format!("{vault}/share");
    config.validate_isolation(&[&path], &[vault], op == "init")?;
    let raw_share = read_bounded_file(&path, MAX_KEY_FILE_BYTES)?;
    let share = CnfRssKeyShare256::from_secret_bytes(&raw_share)
        .map_err(|e| CliError::input(format!("invalid local CNF share: {e:?}")))?;
    if profile.width() != share.key_len || !share.config().supports_pure_hash_multiplication() {
        return Err(CliError::input(
            "CNF share does not match profile or honest-majority roster",
        ));
    }
    let id = h32(
        b"QSAG.CNF.VAULT/v1",
        &[
            &deploy,
            &share.pk_seed,
            &[share.party_id as u8],
            profile.name().as_bytes(),
        ],
    );
    let key = Secret32::new(h32(b"QSAG.CNF.JOURNAL/v1", &[&id, &raw_share]));
    drop(raw_share);
    let anchor_key = mac32(&key, b"QSAG.CNF.ANCHOR/v1", &[&id]);
    let journal_path = format!("{vault}/sessions");
    let public_path = format!("{vault}/public-key");
    if op == "init" {
        let anchor = FsExternalMountAnchor::provision_fresh(
            &session_cfg,
            &[&path],
            &[vault],
            "cnf-wire",
            id,
            anchor_key,
        )?;
        FsDurablePoisonAndSessionJournal::open_anchored(
            journal_path,
            *key,
            id,
            JournalOpenMode::CreateNew,
            Box::new(anchor),
        )
        .map_err(|e| CliError::state(format!("enrolling CNF journal: {e}")))?;
        return Ok(());
    }
    let nonce = from_hex_exact::<32>(args.require("session")?, "session")?;
    let out = args.require("out")?;
    let addrs = addresses(&args)?;
    if addrs.len() != share.config().parties() {
        return Err(CliError::usage(
            "one distinct address per enrolled party is required",
        ));
    }
    let mut message = Vec::new();
    let mut public = Vec::new();
    if op == "sign" {
        message = read_input(args.require("in")?)?.0.to_vec();
        let record = read_bounded_file(&public_path, 96)?;
        if record.len() != 2 * profile.width() + 32 {
            return Err(CliError::state("invalid enrolled public key"));
        }
        let (pk, tag) = record.split_at(2 * profile.width());
        if !mac32_verify(&key, b"QSAG.CNF.PUBLIC/v1", &[pk], tag.try_into().unwrap()) {
            return Err(CliError::state("public key authentication failed"));
        }
        public.extend_from_slice(pk);
    }
    let sid = h32(
        b"QSAG.CNF.CEREMONY/v2",
        &[
            &deploy,
            &nonce,
            op.as_bytes(),
            profile.name().as_bytes(),
            &share.pk_seed,
            &public,
            &message,
        ],
    );
    let anchor = FsExternalMountAnchor::open_existing(
        &session_cfg,
        &[&path],
        &[vault],
        "cnf-wire",
        id,
        anchor_key,
    )?;
    let journal = FsDurablePoisonAndSessionJournal::start_next_anchored(
        journal_path,
        *key,
        sid,
        Box::new(anchor),
    )
    .map_err(|e| CliError::state(format!("allocating CNF session: {e}")))?;
    let mesh = Mesh::connect(share.party_id, &addrs)
        .map_err(|e| CliError::io("connecting CNF peers", e))?;
    let entropy = Secret32::new(os_random_32()?);
    let mut party = IsolatedCnfParty::from_custody(deploy, &share, mesh, sid, &entropy, journal)
        .map_err(|e| CliError::state(format!("starting CNF party: {e}")))?;
    if op == "public" {
        let pk = match profile {
            Profile::Slh(params) => party
                .slh_keygen(&params)
                .map_err(|e| CliError::state(e.to_string()))?
                .to_bytes(),
            Profile::Frontier(profile) => {
                let pk = party
                    .frontier_public_key(profile)
                    .map_err(|e| CliError::state(e.to_string()))?;
                let burn_key = pk.wal_key();
                let burn_cfg = config.tpm_slot(1, 2)?;
                let burn_id = h32(
                    b"QSAG.CNF.FRONTIER.USE-ID/v1",
                    &[&burn_key, &[share.party_id as u8]],
                );
                let burn_path = format!("{vault}/frontier-use");
                let fresh = match std::fs::symlink_metadata(&burn_path) {
                    Ok(_) => false,
                    Err(e) if e.kind() == io::ErrorKind::NotFound => true,
                    Err(e) => return Err(CliError::io("checking frontier burn journal", e)),
                };
                let wal_mac = mac32(&key, b"QSAG.CNF.FTS.WAL/v1", &[&burn_key]);
                let anchor_key = mac32(&key, b"QSAG.CNF.FTS.ANCHOR/v1", &[&burn_key]);
                if fresh {
                    let a = FsExternalMountAnchor::provision_fresh(
                        &burn_cfg,
                        &[&path],
                        &[vault],
                        "cnf-frontier-use",
                        burn_id,
                        anchor_key,
                    )?;
                    FsWalFtsEpochLatch::create_anchored(burn_path, burn_key, wal_mac, Box::new(a))
                } else {
                    let a = FsExternalMountAnchor::open_existing(
                        &burn_cfg,
                        &[&path],
                        &[vault],
                        "cnf-frontier-use",
                        burn_id,
                        anchor_key,
                    )?;
                    FsWalFtsEpochLatch::open_anchored(burn_path, burn_key, wal_mac, Box::new(a))
                }
                .map_err(|e| CliError::io("enrolling one-use Frontier journal", e))?;
                [&pk.pk_seed[..], &pk.root].concat()
            }
        };
        let mut record = pk.clone();
        record.extend_from_slice(&mac32(&key, b"QSAG.CNF.PUBLIC/v1", &[&pk]));
        match std::fs::symlink_metadata(&public_path) {
            // The record ends in a tag under the vault's journal key.
            Ok(_)
                if qsag_core::wipe::ct_eq_bytes(
                    &read_bounded_file(&public_path, 96)?,
                    &record,
                ) => {}
            Ok(_) => return Err(CliError::state("enrolled public key differs")),
            Err(e) if e.kind() == io::ErrorKind::NotFound => {
                write_new(&public_path, &record, true)?
            }
            Err(e) => return Err(CliError::io("checking enrolled public key", e)),
        }
        write_new(out, &pk, false)
    } else {
        let sig = match profile {
            Profile::Slh(params) => {
                let pk = SlhPublicKey::from_bytes_for_params(&params, &public)
                    .map_err(|e| CliError::state(e.to_string()))?;
                let sig = party
                    .slh_sign(&params, &message, &[], &pk, None)
                    .map_err(|e| CliError::state(e.to_string()))?;
                if !slh_verify(&params, &message, &sig, &[], &pk) {
                    return Err(CliError::verify("CNF signature verification failed"));
                }
                sig
            }
            Profile::Frontier(profile) => {
                let pk = FrontierFtsPublicKey {
                    profile,
                    pk_seed: public[..32]
                        .try_into()
                        .map_err(|_| CliError::input("invalid public seed"))?,
                    root: public[32..].to_vec(),
                };
                let burn_key = pk.wal_key();
                let burn_cfg = config.tpm_slot(1, 2)?;
                let burn_id = h32(
                    b"QSAG.CNF.FRONTIER.USE-ID/v1",
                    &[&burn_key, &[share.party_id as u8]],
                );
                let a = FsExternalMountAnchor::open_existing(
                    &burn_cfg,
                    &[&path],
                    &[vault],
                    "cnf-frontier-use",
                    burn_id,
                    mac32(&key, b"QSAG.CNF.FTS.ANCHOR/v1", &[&burn_key]),
                )?;
                let mut wal = FsWalFtsEpochLatch::open_anchored(
                    format!("{vault}/frontier-use"),
                    burn_key,
                    mac32(&key, b"QSAG.CNF.FTS.WAL/v1", &[&burn_key]),
                    Box::new(a),
                )
                .map_err(|e| CliError::io("opening one-use Frontier journal", e))?;
                party
                    .frontier_sign(&pk, &message, &nonce, &mut wal)
                    .map_err(|e| CliError::state(e.to_string()))?
                    .to_bytes(profile)
            }
        };
        write_new(out, &sig, false)
    }
}
