#![forbid(unsafe_code)]
//! One CNF custodian per process. Transport readers drain one bounded packet ahead
//! so simultaneous large MPC sends cannot deadlock on full duplex socket buffers.

use std::io::{self, Read, Write};
use std::net::{Shutdown, SocketAddr, TcpListener, TcpStream};
use std::sync::mpsc::{Receiver, sync_channel};
use std::time::{Duration, Instant};

use crate::anchor::{AnchorConfig, FsExternalMountAnchor};
use crate::cli::{
    Args, CliError, MAX_KEY_FILE_BYTES, MAX_MSG_BYTES, Secret32, ZeroizingBuf, os_random_32,
    private_dir, read_bounded_file, read_input, replace_secret, write_new,
};
use crate::codec::from_hex_exact;
use qsag_core::belt_latch::{BeltLatch, FsBeltWal};
use qsag_core::cnf_rss::{CnfRssConfig, CnfRssKeyShare256};
use qsag_core::fips205::{Fips205Params, SlhPublicKey, slh_verify};
use qsag_core::wipe::{SecretBuffer, ct_eq_bytes};
use qsag_fts::{FrontierFtsProfile, FrontierFtsPublicKey, FsWalFtsEpochLatch};
use qsag_quorum::hash::{SeedRng, h32, mac32, mac32_verify};
use qsag_quorum::party_node::PoisonJournal;
use qsag_quorum::poison_journal::{FsDurablePoisonAndSessionJournal, JournalOpenMode};
use qsag_quorum::wire_channel::{
    ConfidentialWireChannel, MAX_FRAME_PAYLOAD, TransportError, WireTransport,
};
use qsag_quorum::{IsolatedCnfParty, run_isolated_cnf_dkg};

const HELP: &str = "\
qsag quorum wire <dkg|init|public|sign|refresh|daemon> --vault-dir DIR --anchor-dir DIR
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

qsag quorum daemon --vault-dir DIR --anchor-dir DIR --deployment-id HEX32 --profile PROFILE
    --party INDEX --peers ADDRESSES --control-listen ADDR [--session-timeout-ms MS]
    [--max-ceremonies N] [--operator-key-file FILE] [--allow-single-disk-anchor]
The deadline covers the full MPC computation and defaults to 30000 ms. Size it for
the profile and roster. The limit counts successful ceremonies.
qsag quorum wire <public|sign|refresh> --control-peers ADDRESSES --deployment-id HEX32
    --profile PROFILE --session HEX32 --out PATH [--in FILE] [--slot N]
    (--operator-key-file FILE | --vault-dir DIR) [--session-timeout-ms MS]
Use the same raw 32-byte operator key at every daemon and the coordinator, or
authorize a roster member via its vault and pairwise links. A vault/operator-key
file selects operator authentication. Each request needs a fresh nonce. A slot
on sign burns every skipped consensus index. Frontier keys retain their one-use limit.
TPM-backed consensus slots require a fourth counter at base + 3.
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
    until: Option<Instant>,
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

fn peer(stream: TcpStream, deadline: Option<Instant>) -> io::Result<Peer> {
    let timeout = deadline.map(remaining).transpose()?.unwrap_or(DEADLINE);
    stream.set_nodelay(true)?;
    stream.set_write_timeout(Some(timeout))?;
    stream.set_read_timeout(Some(timeout))?;
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
    fn connect(me: usize, addrs: &[SocketAddr], deadline: Option<Instant>) -> io::Result<Self> {
        if addrs.len() > 255 || me >= addrs.len() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "invalid roster or party index",
            ));
        }
        let listener = TcpListener::bind(addrs[me])?;
        listener.set_nonblocking(true)?;
        let until = deadline.unwrap_or_else(|| Instant::now() + DEADLINE);
        let mut peers: Vec<Option<Peer>> = (0..addrs.len()).map(|_| None).collect();
        for (idx, addr) in addrs[..me].iter().enumerate() {
            let mut stream = loop {
                match TcpStream::connect_timeout(
                    addr,
                    remaining(until)?.min(Duration::from_millis(500)),
                ) {
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
            stream.set_write_timeout(Some(remaining(until)?))?;
            stream.write_all(&[me as u8])?;
            peers[idx] = Some(peer(stream, deadline)?);
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
            // BSD inherits O_NONBLOCK from the listening socket. Packet readers
            // use blocking reads with a deadline, including the routing byte.
            stream.set_nonblocking(false)?;
            let mut id = [0];
            stream.set_read_timeout(Some(remaining(until)?))?;
            stream.read_exact(&mut id)?;
            let idx = usize::from(id[0]);
            // The id routes the socket. Only the peer-specific EtM key authenticates it.
            if idx <= me || idx >= peers.len() || peers[idx].is_some() {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "invalid peer route",
                ));
            }
            peers[idx] = Some(peer(stream, deadline)?);
        }
        Ok(Self {
            me,
            peers,
            until: deadline,
        })
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
        if let Some(until) = self.until {
            send_until(&mut p.tx, &(payload.len() as u32).to_be_bytes(), until)
                .and_then(|()| send_until(&mut p.tx, payload, until))
                .map_err(|_| TransportError::Closed { peer: to })?;
            return Ok(());
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
            .recv_timeout(
                self.until
                    .map_or(DEADLINE, |d| d.saturating_duration_since(Instant::now())),
            )
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

fn addresses(raw: &str) -> Result<Vec<SocketAddr>, CliError> {
    let addrs = raw
        .split(',')
        .take(256)
        .map(str::parse::<SocketAddr>)
        .collect::<Result<Vec<_>, _>>()
        .map_err(|_| CliError::usage("peers must be comma-separated numeric socket addresses"))?;
    if addrs.len() > 255 {
        return Err(CliError::usage("a roster supports at most 255 parties"));
    }
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

fn read_links(
    path: &str,
    me: usize,
    n: usize,
) -> Result<qsag_core::wipe::SecretVec<[u8; 32]>, CliError> {
    let bytes = read_bounded_file(path, (32 * n) as u64)?;
    if bytes.len() != 32 * n {
        return Err(CliError::input(
            "link key file must hold one 32-byte entry per party",
        ));
    }
    let links = bytes.as_chunks::<32>().0;
    let mut valid = ct_eq_bytes(&links[me], &[0; 32]);
    for (i, key) in links.iter().enumerate().filter(|(i, _)| *i != me) {
        valid &= !ct_eq_bytes(key, &[0; 32]);
        for previous in &links[..i] {
            valid &= !ct_eq_bytes(previous, key);
        }
    }
    if !valid {
        return Err(CliError::input(
            "each peer requires a distinct nonzero pairwise key; self entry must be zero",
        ));
    }
    Ok(SecretBuffer(links.to_vec()))
}

fn dkg(
    args: &Args,
    vault: &str,
    config: &AnchorConfig,
    deployment: [u8; 32],
    profile: Profile,
) -> Result<(), CliError> {
    let addrs = addresses(args.require("peers")?)?;
    if addrs.len() > 255 {
        return Err(CliError::usage("a roster supports at most 255 parties"));
    }
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
    let links = read_links(&links_path, me, addrs.len())?;
    let nonce = from_hex_exact::<32>(args.require("session")?, "session")?;
    let id = h32(
        b"QSAG.CNF.DKG.ANCHOR-ID/v1",
        &[
            &deployment,
            &[me as u8, t as u8, addrs.len() as u8],
            profile.name().as_bytes(),
        ],
    );
    let key = Secret32::new(h32(
        b"QSAG.CNF.DKG.JOURNAL/v1",
        &[&id, links.as_flattened()],
    ));
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
    let mesh =
        Mesh::connect(me, &addrs, None).map_err(|e| CliError::io("connecting DKG peers", e))?;
    let mut rng = SeedRng::new(&Secret32::new(os_random_32()?), &sid);
    let keys = run_isolated_cnf_dkg(
        &cfg,
        profile.width(),
        deployment,
        mesh,
        sid,
        links.into_inner(),
        &mut rng,
    )
    .map_err(|e| CliError::state(format!("CNF DKG: {e}")))?;
    let share = keys
        .finish_enrollment()
        .map_err(|e| CliError::state(e.to_string()))?;
    write_new(&share_path, &share.to_secret_bytes(), true)
}

struct Vault<'a> {
    vault: &'a str,
    config: AnchorConfig,
    deploy: [u8; 32],
    profile: Profile,
    id: [u8; 32],
    key: Secret32,
    me: usize,
    n: usize,
    pk_seed: [u8; 32],
}

fn state(e: impl std::fmt::Display) -> CliError {
    CliError::state(e.to_string())
}

fn read_share(path: &str) -> Result<(CnfRssKeyShare256, ZeroizingBuf), CliError> {
    let raw = read_bounded_file(path, MAX_KEY_FILE_BYTES)?;
    let share = CnfRssKeyShare256::from_secret_bytes(&raw)
        .map_err(|e| CliError::input(format!("invalid local CNF share: {e:?}")))?;
    Ok((share, raw))
}

fn optional(path: &str, max: u64) -> Result<Option<ZeroizingBuf>, CliError> {
    match std::fs::symlink_metadata(path) {
        Ok(_) => read_bounded_file(path, max).map(Some),
        Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(None),
        Err(e) => Err(CliError::io("checking custody file", e)),
    }
}

impl<'a> Vault<'a> {
    fn open(
        vault: &'a str,
        config: AnchorConfig,
        deploy: [u8; 32],
        profile: Profile,
        init: bool,
    ) -> Result<Self, CliError> {
        let path = format!("{vault}/share");
        config.validate_isolation(&[&path], &[vault], init)?;
        let (share, raw) = read_share(&path)?;
        if profile.width() != share.key_len || !share.config().supports_pure_hash_multiplication() {
            return Err(CliError::input(
                "CNF share does not match profile or honest-majority roster",
            ));
        }
        let me = share.party_id;
        let n = share.config().parties();
        let id = h32(
            b"QSAG.CNF.VAULT/v1",
            &[
                &deploy,
                &share.pk_seed,
                &[me as u8],
                profile.name().as_bytes(),
            ],
        );
        let key = match optional(&format!("{vault}/journal-key"), 32)? {
            Some(bytes) => SecretBuffer(
                bytes[..]
                    .try_into()
                    .map_err(|_| CliError::state("invalid journal key"))?,
            ),
            None => SecretBuffer(h32(b"QSAG.CNF.JOURNAL/v1", &[&id, &raw])),
        };
        Ok(Self {
            vault,
            config,
            deploy,
            profile,
            id,
            key,
            pk_seed: share.pk_seed,
            me,
            n,
        })
    }

    fn anchor(&self, create: bool) -> Result<FsExternalMountAnchor, CliError> {
        let key = mac32(&self.key, b"QSAG.CNF.ANCHOR/v1", &[&self.id]);
        let open = if create {
            FsExternalMountAnchor::provision_fresh
        } else {
            FsExternalMountAnchor::open_existing
        };
        open(
            &self.config,
            &[&format!("{}/share", self.vault)],
            &[self.vault],
            "cnf-wire",
            self.id,
            key,
        )
    }
    fn init(&self) -> Result<(), CliError> {
        FsDurablePoisonAndSessionJournal::open_anchored(
            format!("{}/sessions", self.vault),
            *self.key,
            self.id,
            JournalOpenMode::CreateNew,
            Box::new(self.anchor(true)?),
        )
        .map_err(state)?;
        Ok(())
    }

    fn slot(&self, slot: u64, message: &[u8], sid: &[u8; 32]) -> Result<(), CliError> {
        let path = format!("{}/consensus-slots", self.vault);
        let fresh = match std::fs::symlink_metadata(&path) {
            Ok(_) => false,
            Err(e) if e.kind() == io::ErrorKind::NotFound => true,
            Err(e) => return Err(state(e)),
        };
        let vault = self.vault;
        let open = if fresh {
            FsExternalMountAnchor::provision_fresh
        } else {
            FsExternalMountAnchor::open_existing
        };
        // Offsets zero through two are reserved for sessions, Frontier and DKG.
        let config = self.config.tpm_slot(3, 4)?;
        let a = open(
            &config,
            &[&format!("{vault}/share")],
            &[vault],
            "cnf-slot",
            self.id,
            mac32(&self.key, b"QSAG.CNF.SLOT.ANCHOR/v1", &[&self.id]),
        )?;
        let key = mac32(&self.key, b"QSAG.CNF.SLOT.WAL/v1", &[&self.id]);
        let wal = if fresh {
            FsBeltWal::provision_genesis_anchored(path, key, Box::new(a))
        } else {
            FsBeltWal::open_existing_anchored(path, key, Box::new(a))
        }
        .map_err(state)?;
        let capacity = match self.profile {
            Profile::Slh(p) => p.h.min(62),
            Profile::Frontier(_) => 62,
        };
        BeltLatch::recover_slot_indexed(wal, capacity)
            .map_err(state)?
            .bind_consensus_slot(
                slot,
                &h32(b"QSAG.CNF.SLOT.MESSAGE/v1", &[message]),
                sid,
                &[],
            )
            .map_err(state)?;
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Operation {
    Public = 1,
    Sign = 2,
    Refresh = 3,
}
impl Operation {
    fn parse(op: &str) -> Result<Self, CliError> {
        match op {
            "sign" => Ok(Self::Sign),
            "public" => Ok(Self::Public),
            "refresh" => Ok(Self::Refresh),
            _ => Err(CliError::usage(HELP)),
        }
    }
}
struct Request {
    op: Operation,
    nonce: [u8; 32],
    slot: Option<u64>,
    message: Vec<u8>,
}
impl Request {
    fn context(&self, deploy: &[u8; 32], profile: Profile) -> [u8; 32] {
        h32(
            b"QSAG.CNF.CONTROL.CONTEXT/v1",
            &[
                deploy,
                profile.name().as_bytes(),
                &[self.op as u8],
                &self.nonce,
                &[u8::from(self.slot.is_some())],
                &self.slot.unwrap_or_default().to_be_bytes(),
                &self.message,
            ],
        )
    }
}
fn execute(
    v: &Vault<'_>,
    request: &Request,
    addrs: &[SocketAddr],
    until: Option<Instant>,
) -> Result<Vec<u8>, CliError> {
    let (vault, config, profile, deploy, key) = (v.vault, &v.config, v.profile, v.deploy, &v.key);
    let op = request.op;
    let nonce = request.nonce;
    let message = &request.message;
    let path = format!("{vault}/share");
    let public_path = format!("{vault}/public-key");
    if addrs.len() != v.n {
        return Err(CliError::usage(
            "one mesh address per custodian is required",
        ));
    }
    let links = read_links(&format!("{vault}/links"), v.me, v.n)?;
    let nonce_id = h32(b"QSAG.CNF.CONTROL.NONCE/v1", &[&deploy, &nonce]);
    let mut journal = FsDurablePoisonAndSessionJournal::start_next_anchored(
        format!("{vault}/sessions"),
        **key,
        nonce_id,
        Box::new(v.anchor(false)?),
    )
    .map_err(|e| CliError::state(format!("allocating CNF session: {e}")))?;
    let mut public = Vec::new();
    if op == Operation::Sign {
        let record = read_bounded_file(&public_path, 96)?;
        if record.len() != 2 * profile.width() + 32 {
            return Err(CliError::state("invalid enrolled public key"));
        }
        let (pk, tag) = record.split_at(2 * profile.width());
        if !ct_eq_bytes(&mac32(key, b"QSAG.CNF.PUBLIC/v1", &[pk]), tag) {
            return Err(CliError::state("public key authentication failed"));
        }
        public.extend_from_slice(pk);
    }
    // Keep previously reserved standalone public/sign IDs burned after an upgrade.
    let sid = if request.slot.is_none() && op != Operation::Refresh {
        let name: &[u8] = if op == Operation::Public {
            b"public"
        } else {
            b"sign"
        };
        h32(
            b"QSAG.CNF.CEREMONY/v2",
            &[
                &deploy,
                &nonce,
                name,
                profile.name().as_bytes(),
                &v.pk_seed,
                &public,
                message,
            ],
        )
    } else {
        h32(
            b"QSAG.CNF.CEREMONY/v3",
            &[&request.context(&deploy, profile), &v.pk_seed, &public],
        )
    };
    journal.advance_session(sid).map_err(state)?;
    let mut rotation = Rotation::load(v, &journal)?;
    if let Some(slot) = request.slot {
        v.slot(slot, message, &sid)?;
    }
    let mesh =
        Mesh::connect(v.me, addrs, until).map_err(|e| CliError::io("connecting CNF peers", e))?;
    let mut channel = ConfidentialWireChannel::establish_pq_hybrid(
        mesh,
        deploy,
        sid,
        links.into_inner(),
        os_random_32()?,
    )
    .map_err(state)?;
    rotation.reconcile(v, &mut journal, &mut channel)?;
    let (share, _) = read_share(&path)?;
    let entropy = Secret32::new(os_random_32()?);
    let mut party = IsolatedCnfParty::from_custody_with_channel(
        deploy,
        &share,
        channel,
        sid,
        &entropy,
        &mut journal,
    )
    .map_err(state)?;
    if op == Operation::Refresh {
        let fresh = party.refresh_share(&share).map_err(state)?;
        let mut next = Rotation::prepare(v, rotation.current, sid, &fresh)?;
        party.confirm_refresh_prepared().map_err(state)?;
        drop(party);
        next.install(v, &mut journal)?;
        return Ok(request.context(&deploy, profile).to_vec());
    }
    if op == Operation::Public {
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
                let wal_mac = mac32(key, b"QSAG.CNF.FTS.WAL/v1", &[&burn_key]);
                let anchor_key = mac32(key, b"QSAG.CNF.FTS.ANCHOR/v1", &[&burn_key]);
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
        record.extend_from_slice(&mac32(key, b"QSAG.CNF.PUBLIC/v1", &[&pk]));
        match std::fs::symlink_metadata(&public_path) {
            // The record ends in a tag under the vault's journal key.
            Ok(_)
                if qsag_core::wipe::ct_eq_bytes(&read_bounded_file(&public_path, 96)?, &record) => {
            }
            Ok(_) => return Err(CliError::state("enrolled public key differs")),
            Err(e) if e.kind() == io::ErrorKind::NotFound => {
                write_new(&public_path, &record, true)?
            }
            Err(e) => return Err(CliError::io("checking enrolled public key", e)),
        }
        Ok(pk)
    } else {
        let sig = match profile {
            Profile::Slh(params) => {
                let pk = SlhPublicKey::from_bytes_for_params(&params, &public)
                    .map_err(|e| CliError::state(e.to_string()))?;
                let sig = party
                    .slh_sign(&params, message, &[], &pk, None)
                    .map_err(|e| CliError::state(e.to_string()))?;
                if !slh_verify(&params, message, &sig, &[], &pk) {
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
                    mac32(key, b"QSAG.CNF.FTS.ANCHOR/v1", &[&burn_key]),
                )?;
                let mut wal = FsWalFtsEpochLatch::open_anchored(
                    format!("{vault}/frontier-use"),
                    burn_key,
                    mac32(key, b"QSAG.CNF.FTS.WAL/v1", &[&burn_key]),
                    Box::new(a),
                )
                .map_err(|e| CliError::io("opening one-use Frontier journal", e))?;
                party
                    .frontier_sign(&pk, message, &nonce, &mut wal)
                    .map_err(|e| CliError::state(e.to_string()))?
                    .to_bytes(profile)
            }
        };
        public.extend_from_slice(&sig);
        Ok(public)
    }
}

/// The authenticated proposal survives a disconnect between preparation and installation.
/// The session journal commits the digest before the canonical share file is replaced.
struct Rotation {
    current: [u8; 32],
    candidate: Option<([u8; 32], ZeroizingBuf)>,
}
impl Rotation {
    fn commitment(id: &[u8; 32], raw: &[u8]) -> [u8; 32] {
        h32(b"QSAG.CNF.REFRESH.SHARE/v1", &[id, raw])
    }

    fn load(v: &Vault<'_>, journal: &FsDurablePoisonAndSessionJournal) -> Result<Self, CliError> {
        let share_path = format!("{}/share", v.vault);
        let raw = read_bounded_file(&share_path, MAX_KEY_FILE_BYTES)?;
        let manifest = optional(
            &format!("{}/refresh-record", v.vault),
            MAX_KEY_FILE_BYTES + 96,
        )?;
        let mut current = [0; 32];
        let mut candidate = None;
        if let Some(bytes) = manifest {
            if bytes.len() <= 96 {
                return Err(CliError::state("truncated refresh record"));
            }
            let (data, tag) = bytes.split_at(bytes.len() - 32);
            if !ct_eq_bytes(
                tag,
                &mac32(&v.key, b"QSAG.CNF.REFRESH.RECORD/v1", &[&v.id, data]),
            ) {
                return Err(CliError::state("invalid refresh record"));
            }
            current.copy_from_slice(&data[..32]);
            let proposal: [u8; 32] = data[32..64].try_into().map_err(state)?;
            let next = &data[64..];
            if journal.share_checkpoint() == Some(Self::commitment(&proposal, next)) {
                if !ct_eq_bytes(&raw, next) {
                    replace_secret(&share_path, next)?;
                }
                return Ok(Self {
                    current: proposal,
                    candidate: None,
                });
            }
            candidate = Some((proposal, SecretBuffer(next.to_vec())));
        }
        let valid = match journal.share_checkpoint() {
            None => {
                current == [0; 32]
                    && ct_eq_bytes(&h32(b"QSAG.CNF.JOURNAL/v1", &[&v.id, &raw]), &v.key[..])
            }
            Some(tag) => ct_eq_bytes(&Self::commitment(&current, &raw), &tag),
        };
        if !valid {
            return Err(CliError::state(
                "share differs from the anchored custody generation",
            ));
        }
        Ok(Self { current, candidate })
    }

    fn prepare(
        v: &Vault<'_>,
        current: [u8; 32],
        id: [u8; 32],
        share: &CnfRssKeyShare256,
    ) -> Result<Self, CliError> {
        let path = format!("{}/journal-key", v.vault);
        if optional(&path, 32)?.is_none() {
            write_new(&path, &v.key[..], true)?;
        }
        let raw = share.to_secret_bytes();
        let mut record = SecretBuffer(Vec::with_capacity(96 + raw.len()));
        record.extend_from_slice(&current);
        record.extend_from_slice(&id);
        record.extend_from_slice(&raw);
        let tag = mac32(&v.key, b"QSAG.CNF.REFRESH.RECORD/v1", &[&v.id, &record]);
        record.extend_from_slice(&tag);
        let path = format!("{}/refresh-record", v.vault);
        replace_secret(&path, &record)?;
        Ok(Self {
            current,
            candidate: Some((id, raw)),
        })
    }

    fn install(
        &mut self,
        v: &Vault<'_>,
        journal: &mut FsDurablePoisonAndSessionJournal,
    ) -> Result<(), CliError> {
        let (id, raw) = self
            .candidate
            .take()
            .ok_or_else(|| CliError::state("missing prepared share"))?;
        journal
            .commit_share(Self::commitment(&id, &raw))
            .map_err(state)?;
        replace_secret(&format!("{}/share", v.vault), &raw)?;
        self.current = id;
        Ok(())
    }

    fn reconcile<T: WireTransport>(
        &mut self,
        v: &Vault<'_>,
        journal: &mut FsDurablePoisonAndSessionJournal,
        channel: &mut ConfidentialWireChannel<T>,
    ) -> Result<(), CliError> {
        const OFFER: u32 = 0x0416_0000;
        const ACCEPT: u32 = 0x0417_0000;
        let next = self.candidate.as_ref().map_or(self.current, |(id, _)| *id);
        let mut choices = vec![next, self.current];
        let peers = || (0..v.n).filter(|&i| i != v.me);
        for p in peers() {
            channel
                .send_frame(p, OFFER, &[self.current, next].concat())
                .map_err(state)?;
        }
        for p in peers() {
            let raw = channel.recv_frame(p, OFFER).map_err(state)?;
            if raw.len() != 64 {
                return Err(CliError::state("invalid share generation offer"));
            }
            choices.retain(|c| raw[..32] == c[..] || raw[32..] == c[..]);
        }
        let choice = choices
            .first()
            .ok_or_else(|| CliError::state("custodians have incompatible share generations"))?;
        for p in peers() {
            channel.send_frame(p, ACCEPT, choice).map_err(state)?;
        }
        for p in peers() {
            if channel.recv_frame(p, ACCEPT).map_err(state)?[..] != choice[..] {
                return Err(CliError::state("custodians disagree on share generation"));
            }
        }
        if *choice != self.current {
            self.install(v, journal)?;
        }
        Ok(())
    }
}

fn remaining(until: Instant) -> io::Result<Duration> {
    until
        .checked_duration_since(Instant::now())
        .filter(|d| !d.is_zero())
        .ok_or_else(|| io::Error::new(io::ErrorKind::TimedOut, "ceremony deadline expired"))
}
fn send_until(stream: &mut TcpStream, mut data: &[u8], until: Instant) -> io::Result<()> {
    while !data.is_empty() {
        stream.set_write_timeout(Some(remaining(until)?))?;
        match stream.write(data)? {
            0 => return Err(io::ErrorKind::WriteZero.into()),
            n => data = &data[n..],
        }
    }
    Ok(())
}
fn read_until(stream: &mut TcpStream, mut data: &mut [u8], until: Instant) -> io::Result<()> {
    while !data.is_empty() {
        stream.set_read_timeout(Some(remaining(until)?))?;
        match stream.read(data)? {
            0 => return Err(io::ErrorKind::UnexpectedEof.into()),
            n => data = &mut data[n..],
        }
    }
    Ok(())
}

const OPERATOR: u8 = 255;
const CONTROL_MAGIC: &[u8; 8] = b"QSCNFR01";
const CONTROL_REQUEST: &[u8] = b"QSAG.CNF.CONTROL.REQUEST/v1";
const CONTROL_REPLY: &[u8] = b"QSAG.CNF.CONTROL.REPLY/v1";

enum Authority {
    Operator(Secret32),
    Member {
        me: usize,
        links: qsag_core::wipe::SecretVec<[u8; 32]>,
    },
}
impl Authority {
    fn operator(raw: &[u8]) -> Result<Self, CliError> {
        let key: [u8; 32] = raw
            .try_into()
            .map_err(|_| CliError::input("operator key must contain 32 raw bytes"))?;
        if ct_eq_bytes(&key, &[0; 32]) {
            return Err(CliError::input("zero operator key"));
        }
        Ok(Self::Operator(SecretBuffer(key)))
    }
    fn load(args: &Args, roster: Option<(&str, usize, usize)>) -> Result<Self, CliError> {
        if let Some(path) = args.get("operator-key-file") {
            return Self::operator(&read_bounded_file(path, 32)?);
        }
        let (vault, me, n) =
            roster.ok_or_else(|| CliError::usage("provide --operator-key-file or --vault-dir"))?;
        if let Some(key) = optional(&format!("{vault}/operator-key"), 32)? {
            return Self::operator(&key);
        }
        Ok(Self::Member {
            me,
            links: read_links(&format!("{vault}/links"), me, n)?,
        })
    }
    fn sender(&self) -> u8 {
        match self {
            Self::Operator(_) => OPERATOR,
            Self::Member { me, .. } => *me as u8,
        }
    }
    fn key(&self, sender: u8, target: usize, deploy: &[u8; 32]) -> Result<Secret32, CliError> {
        let inputs = [sender, target as u8];
        let k = match self {
            Self::Operator(k) if sender == OPERATOR => {
                mac32(k, b"QSAG.CNF.OPERATOR/v1", &[deploy, &inputs])
            }
            Self::Member { me, links }
                if usize::from(sender) < links.len()
                    && target < links.len()
                    && (*me == target || *me == usize::from(sender)) =>
            {
                let peer = if *me == target {
                    usize::from(sender)
                } else {
                    target
                };
                let key = if peer == *me {
                    SecretBuffer(h32(b"QSAG.CNF.CONTROL.LOCAL/v1", &[links.as_flattened()]))
                } else {
                    SecretBuffer(links[peer])
                };
                mac32(&key, b"QSAG.CNF.MEMBER/v1", &[deploy, &inputs])
            }
            _ => return Err(CliError::state("control authentication failed")),
        };
        Ok(SecretBuffer(k))
    }
}

fn header(req: &Request, ctx: &[u8; 32], sender: u8, target: usize) -> [u8; 88] {
    let mut out = [0; 88];
    out[..8].copy_from_slice(CONTROL_MAGIC);
    out[8..12].copy_from_slice(&[
        sender,
        target as u8,
        req.op as u8,
        u8::from(req.slot.is_some()),
    ]);
    out[12..20].copy_from_slice(&req.slot.unwrap_or_default().to_be_bytes());
    out[20..52].copy_from_slice(&req.nonce);
    out[52..56].copy_from_slice(&(req.message.len() as u32).to_be_bytes());
    out[56..].copy_from_slice(ctx);
    out
}

fn handle(
    mut stream: TcpStream,
    v: &Vault<'_>,
    mesh: &[SocketAddr],
    auth: &Authority,
    until: Instant,
) -> Result<bool, CliError> {
    let mut head = [0; 88];
    let mut tag = [0; 32];
    read_until(&mut stream, &mut head, until).map_err(state)?;
    read_until(&mut stream, &mut tag, until).map_err(state)?;
    let key = auth.key(head[8], v.me, &v.deploy)?;
    if &head[..8] != CONTROL_MAGIC
        || head[9] as usize != v.me
        || !mac32_verify(&key, CONTROL_REQUEST, &[&head], &tag)
    {
        return Err(CliError::state("control authentication failed"));
    }
    let op = match head[10] {
        1 => Operation::Public,
        2 => Operation::Sign,
        3 => Operation::Refresh,
        _ => return Err(CliError::input("invalid operation")),
    };
    let slot = u64::from_be_bytes(head[12..20].try_into().map_err(state)?);
    let slot = match head[11] {
        0 if slot == 0 => None,
        1 if op == Operation::Sign => Some(slot),
        _ => return Err(CliError::input("invalid slot")),
    };
    let len = u32::from_be_bytes(head[52..56].try_into().map_err(state)?) as usize;
    if len as u64 > MAX_MSG_BYTES || (op != Operation::Sign && len != 0) {
        return Err(CliError::input("invalid ceremony input length"));
    }
    let mut req = Request {
        op,
        slot,
        nonce: head[20..52].try_into().map_err(state)?,
        message: vec![0; len],
    };
    read_until(&mut stream, &mut req.message, until).map_err(state)?;
    let ctx = req.context(&v.deploy, v.profile);
    if !ct_eq_bytes(&ctx, &head[56..]) {
        return Err(CliError::state("control context mismatch"));
    }
    let (status, data) = match execute(v, &req, mesh, Some(until)) {
        Ok(data) => (0u8, data),
        Err(e) => {
            eprintln!("custodian {} rejected {:?}: {e}", v.me, req.op);
            (1, e.to_string().into_bytes())
        }
    };
    let size = (data.len() as u32).to_be_bytes();
    let tag = mac32(&key, CONTROL_REPLY, &[&head, &[status], &size, &data]);
    for part in [&[status][..], &size, &tag, &data] {
        if let Err(e) = send_until(&mut stream, part, until) {
            eprintln!("custodian {} could not deliver ceremony result: {e}", v.me);
            break;
        }
    }
    Ok(status == 0)
}

fn serve(
    v: &Vault<'_>,
    mesh: &[SocketAddr],
    auth: &Authority,
    listener: TcpListener,
    timeout: Duration,
    max: Option<u64>,
) -> Result<(), CliError> {
    if mesh.len() != v.n {
        return Err(CliError::usage("mesh roster differs from enrolled share"));
    }
    let path = format!("{}/sessions", v.vault);
    drop(read_links(&format!("{}/links", v.vault), v.me, v.n)?);
    let journal = FsDurablePoisonAndSessionJournal::recover_head_anchored(
        path,
        *v.key,
        Box::new(v.anchor(false)?),
    )
    .map_err(state)?;
    Rotation::load(v, &journal)?;
    drop(journal);
    eprintln!(
        "custodian {} listening on {}",
        v.me,
        listener.local_addr().map_err(state)?
    );
    let mut count = 0;
    while max != Some(count) {
        let (stream, _) = listener.accept().map_err(state)?;
        match handle(stream, v, mesh, auth, deadline(timeout)?) {
            Ok(true) => count += 1,
            Ok(false) => (),
            Err(e) => eprintln!("custodian {} closed control connection: {e}", v.me),
        }
    }
    Ok(())
}

fn deadline(timeout: Duration) -> Result<Instant, CliError> {
    Instant::now()
        .checked_add(timeout)
        .ok_or_else(|| CliError::usage("session timeout exceeds clock range"))
}

fn contact(
    addr: SocketAddr,
    req: &Request,
    head: [u8; 88],
    key: Secret32,
    until: Instant,
) -> Result<Vec<u8>, CliError> {
    let mut stream =
        TcpStream::connect_timeout(&addr, remaining(until).map_err(state)?).map_err(state)?;
    let tag = mac32(&key, CONTROL_REQUEST, &[&head]);
    for part in [&head[..], &tag, &req.message] {
        send_until(&mut stream, part, until).map_err(state)?;
    }
    let mut reply = [0; 37];
    read_until(&mut stream, &mut reply, until).map_err(state)?;
    let size = u32::from_be_bytes(reply[1..5].try_into().map_err(state)?) as usize;
    if size > 1024 * 1024 {
        return Err(CliError::input("oversized control reply"));
    }
    let mut data = vec![0; size];
    read_until(&mut stream, &mut data, until).map_err(state)?;
    if !ct_eq_bytes(
        &reply[5..],
        &mac32(
            &key,
            CONTROL_REPLY,
            &[&head, &reply[..1], &reply[1..5], &data],
        ),
    ) {
        return Err(CliError::verify("invalid response MAC"));
    }
    if reply[0] != 0 {
        return Err(CliError::state(format!(
            "custodian at {addr}: {}",
            String::from_utf8_lossy(&data)
        )));
    }
    Ok(data)
}

fn verify_output<'a>(
    req: &Request,
    profile: Profile,
    ctx: &[u8; 32],
    data: &'a [u8],
) -> Result<&'a [u8], CliError> {
    let pk_len = 2 * profile.width();
    match req.op {
        Operation::Public if data.len() == pk_len => Ok(data),
        Operation::Refresh if ct_eq_bytes(ctx, data) => Ok(data),
        Operation::Sign if data.len() > pk_len => {
            let (pk, sig) = data.split_at(pk_len);
            match profile {
                Profile::Slh(p) => {
                    let pk = SlhPublicKey::from_bytes_for_params(&p, pk).map_err(state)?;
                    if !slh_verify(&p, &req.message, sig, &[], &pk) {
                        return Err(CliError::verify("invalid SLH signature"));
                    }
                }
                Profile::Frontier(p) => {
                    let pk = FrontierFtsPublicKey {
                        profile: p,
                        pk_seed: pk[..32].try_into().map_err(state)?,
                        root: pk[32..].to_vec(),
                    };
                    let sig = qsag_fts::FrontierFtsSignature::from_bytes(p, sig).map_err(state)?;
                    qsag_fts::verify_frontier_fts(
                        &pk,
                        &qsag_fts::FrontierDpTable::build(p),
                        &req.message,
                        &sig,
                    )
                    .map_err(state)?;
                }
            }
            Ok(sig)
        }
        _ => Err(CliError::verify("invalid ceremony result")),
    }
}

fn coordinate(
    req: &Request,
    deploy: &[u8; 32],
    profile: Profile,
    peers: &[SocketAddr],
    auth: &Authority,
    timeout: Duration,
) -> Result<Vec<u8>, CliError> {
    if !(3..=qsag_core::cnf_rss::MAX_CNF_RSS_PARTIES).contains(&peers.len()) {
        return Err(CliError::usage("invalid control roster size"));
    }
    let ctx = req.context(deploy, profile);
    let until = deadline(timeout)?;
    let data = std::thread::scope(|s| {
        let mut tasks = Vec::new();
        for (p, &addr) in peers.iter().enumerate() {
            let head = header(req, &ctx, auth.sender(), p);
            let key = auth.key(auth.sender(), p, deploy)?;
            tasks.push(s.spawn(move || contact(addr, req, head, key, until)));
        }
        let mut first = None;
        for task in tasks {
            let data = task
                .join()
                .map_err(|_| CliError::state("control worker terminated"))??;
            match &first {
                None => first = Some(data),
                Some(a) if a == &data => (),
                Some(_) => return Err(CliError::verify("custodians returned different results")),
            }
        }
        first.ok_or_else(|| CliError::state("empty control roster"))
    })?;
    Ok(verify_output(req, profile, &ctx, &data)?.to_vec())
}

pub fn run(raw: &[String]) -> Result<(), CliError> {
    if raw.is_empty() || raw.iter().any(|s| s == "--help") {
        print!("{HELP}");
        return Ok(());
    }
    let op = raw[0].as_str();
    let mut options = vec![
        "vault-dir",
        "anchor-dir",
        "anchor-tpm-nv",
        "anchor-tpm-device",
        "anchor-tpm-auth-env",
        "deployment-id",
        "profile",
    ];
    match op {
        "dkg" => options.extend(["session", "peers", "threshold", "party"]),
        "init" => (),
        "daemon" => options.extend([
            "party",
            "peers",
            "control-listen",
            "operator-key-file",
            "session-timeout-ms",
            "max-ceremonies",
        ]),
        "public" | "sign" | "refresh" => {
            options.extend([
                "session",
                "peers",
                "out",
                "control-peers",
                "daemon-peers",
                "operator-key-file",
                "session-timeout-ms",
            ]);
            if op == "sign" {
                options.extend(["in", "slot"]);
            }
        }
        _ => return Err(CliError::usage(HELP)),
    }
    let args = Args::parse(&raw[1..], &options, &["allow-single-disk-anchor"])?;
    args.no_positionals()?;
    let control = args
        .get("control-peers")
        .or_else(|| args.get("daemon-peers"));
    if control.is_some()
        && (args.get("peers").is_some()
            || (args.get("control-peers").is_some() && args.get("daemon-peers").is_some()))
    {
        return Err(CliError::usage("select exactly one mesh or control roster"));
    }
    let config = if control.is_none() {
        let vault = args.require("vault-dir")?;
        let config = AnchorConfig::from_quorum_args(&args, vault)?.ok_or_else(|| {
            CliError::usage("wire custody requires --anchor-dir or --anchor-tpm-nv")
        })?;
        private_dir(vault, false)?;
        Some(config)
    } else {
        None
    };
    let deploy = from_hex_exact::<32>(args.require("deployment-id")?, "deployment id")?;
    let profile = Profile::parse(args.require("profile")?)?;
    let timeout = Duration::from_millis(args.get_u64("session-timeout-ms")?.unwrap_or(30000));
    if timeout.is_zero() {
        return Err(CliError::usage("session timeout must be positive"));
    }
    deadline(timeout)?;
    let req = |op| -> Result<Request, CliError> {
        Ok(Request {
            op,
            nonce: from_hex_exact(args.require("session")?, "session")?,
            slot: args.get_u64("slot")?,
            message: if op == Operation::Sign {
                read_input(args.require("in")?)?.into_inner()
            } else {
                vec![]
            },
        })
    };
    if let Some(peers) = control {
        let peers = addresses(peers)?;
        let roster = if let Some(vault) = args.get("vault-dir") {
            let (s, _) = read_share(&format!("{vault}/share"))?;
            if s.config().parties() != peers.len() {
                return Err(CliError::usage("control roster differs from vault"));
            }
            Some((vault, s.party_id, peers.len()))
        } else {
            None
        };
        let out = crate::cli::reserve_output(args.require("out")?, false)?;
        let auth = Authority::load(&args, roster)?;
        return crate::cli::finish_output(
            out,
            &coordinate(
                &req(Operation::parse(op)?)?,
                &deploy,
                profile,
                &peers,
                &auth,
                timeout,
            )?,
        );
    }
    let vault = args.require("vault-dir")?;
    let config = config.ok_or_else(|| CliError::usage("missing anchor"))?;
    if op == "dkg" {
        return dkg(&args, vault, &config, deploy, profile);
    }
    if op == "init" {
        crate::anchor::preflight_tpm_enrollment(
            Some(&config),
            &args,
            if matches!(profile, Profile::Frontier(_)) {
                2
            } else {
                1
            },
        )?;
    }
    let v = Vault::open(vault, config, deploy, profile, op == "init")?;
    if op == "init" {
        return v.init();
    }
    let mesh = addresses(args.require("peers")?)?;
    if op == "daemon" {
        if args.get_u64("party")? != Some(v.me as u64) {
            return Err(CliError::usage("--party must match enrolled share"));
        }
        let auth = Authority::load(&args, Some((vault, v.me, v.n)))?;
        let listen = args
            .require("control-listen")?
            .parse::<SocketAddr>()
            .map_err(state)?;
        let listener = TcpListener::bind(listen).map_err(state)?;
        return serve(
            &v,
            &mesh,
            &auth,
            listener,
            timeout,
            args.get_u64("max-ceremonies")?,
        );
    }
    let req = req(Operation::parse(op)?)?;
    let out = crate::cli::reserve_output(args.require("out")?, false)?;
    let until = args
        .get("session-timeout-ms")
        .map(|_| deadline(timeout))
        .transpose()?;
    let result = execute(&v, &req, &mesh, until)?;
    crate::cli::finish_output(
        out,
        verify_output(&req, profile, &req.context(&deploy, profile), &result)?,
    )
}

/// Independent per-link keys for authenticated local TCP participants in one ceremony.
pub(crate) fn ceremony_channels(
    count: usize,
    session: [u8; 32],
) -> Result<Vec<ConfidentialWireChannel<qsag_quorum::wire_channel::TcpEndpoint>>, CliError> {
    qsag_quorum::wire_channel::confidential_loopback(count, session)
        .map_err(|e| CliError::io("connecting local ceremony", e))
}

#[cfg(test)]
mod tests {
    use super::*;
    use qsag_core::{cnf_rss::run_dealerless_cnf_rss_dkg, preprocessing::PartyPrivateRng};
    use std::path::PathBuf;

    // A real SLH hypertree with 256 leaves and shorter FORS parameters bounds this
    // TCP test's work. Production CLI parsing accepts only the registered profiles.
    const PARAMS: Fips205Params = Fips205Params {
        name: "test-SLH",
        n: 16,
        h: 8,
        d: 4,
        hp: 2,
        a: 1,
        k: 1,
        lg_w: 4,
        m: 3,
    };
    struct Fixture {
        root: PathBuf,
        mesh: Vec<SocketAddr>,
        expected: Vec<u8>,
        params: Fips205Params,
    }
    #[test]
    fn oversize_rosters_are_refused_before_connecting() {
        let addr: SocketAddr = "127.0.0.1:1".parse().unwrap();
        assert!(
            Mesh::connect(0, &[addr; 256], None)
                .is_err_and(|e| e.kind() == io::ErrorKind::InvalidInput)
        );
        let peers = (0..256)
            .map(|n| format!("127.0.0.1:{n}"))
            .collect::<Vec<_>>()
            .join(",");
        assert!(addresses(&peers).is_err());
    }

    fn listener() -> TcpListener {
        TcpListener::bind("127.0.0.1:0").unwrap()
    }
    impl Fixture {
        fn new(params: Fips205Params) -> Self {
            let root = std::env::temp_dir().join(crate::codec::to_hex(&os_random_32().unwrap()));
            std::fs::create_dir(&root).unwrap();
            let cfg = CnfRssConfig::new(2, 3).unwrap();
            let mut rngs: Vec<_> = (0..3)
                .map(|p| PartyPrivateRng::from_seed([p; 32], b"daemon test"))
                .collect();
            let (shares, pk_seed) =
                run_dealerless_cnf_rss_dkg([41; 32], &cfg, 16, &mut rngs).unwrap();
            let (mut sk, mut prf) = ([0; 16], [0; 16]);
            for i in 0..cfg.total_slots() {
                let (a, b, _) = shares.iter().find_map(|s| s.held_slot(i)).unwrap();
                for j in 0..16 {
                    sk[j] ^= a[j];
                    prf[j] ^= b[j];
                }
            }
            let pk = qsag_core::fips205::slh_keygen_internal(&params, &sk, &prf, &pk_seed[..16])
                .unwrap()
                .1
                .to_bytes();
            let sockets: Vec<_> = (0..3).map(|_| listener()).collect();
            let mesh = sockets.iter().map(|s| s.local_addr().unwrap()).collect();
            let f = Self {
                root,
                mesh,
                expected: pk,
                params,
            };
            for (i, s) in shares.iter().enumerate() {
                let (path, config) = f.paths(i);
                private_dir(&path, true).unwrap();
                write_new(&format!("{path}/share"), &s.to_secret_bytes(), true).unwrap();
                let keys: Vec<_> = (0..3)
                    .map(|j| {
                        if j == i {
                            [0; 32]
                        } else {
                            [(3 * i.min(j) + j.max(i) + 1) as u8; 32]
                        }
                    })
                    .collect();
                write_new(&format!("{path}/links"), keys.as_flattened(), true).unwrap();
                let v = Vault::open(&path, config, [7; 32], Profile::Slh(params), true).unwrap();
                v.init().unwrap();
            }
            f
        }
        fn paths(&self, i: usize) -> (String, AnchorConfig) {
            let path = self.root.join(format!("member-{i}")).display().to_string();
            let config = AnchorConfig::dir_only(
                self.root.join(format!("anchor-{i}")).display().to_string(),
                Some(path.clone()),
                true,
            );
            (path, config)
        }
        fn shares(&self) -> Vec<Vec<u8>> {
            (0..3)
                .map(|i| std::fs::read(format!("{}/share", self.paths(i).0)).unwrap())
                .collect()
        }
        fn start(
            &self,
            max: u64,
            timeout: Duration,
        ) -> (Vec<SocketAddr>, Vec<std::thread::JoinHandle<()>>) {
            let mut peers = vec![];
            let mut threads = vec![];
            for i in 0..3 {
                let (path, config) = self.paths(i);
                let mesh = self.mesh.clone();
                let sock = listener();
                peers.push(sock.local_addr().unwrap());
                let params = self.params;
                threads.push(std::thread::spawn(move || {
                    let v =
                        Vault::open(&path, config, [7; 32], Profile::Slh(params), false).unwrap();
                    serve(
                        &v,
                        &mesh,
                        &Authority::operator(&[12; 32]).unwrap(),
                        sock,
                        timeout,
                        Some(max),
                    )
                    .unwrap()
                }));
            }
            (peers, threads)
        }
    }
    impl Drop for Fixture {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.root);
        }
    }
    fn call(
        params: Fips205Params,
        peers: &[SocketAddr],
        op: Operation,
        nonce: u8,
        slot: Option<u64>,
    ) -> Result<Vec<u8>, CliError> {
        let req = Request {
            op,
            nonce: [nonce; 32],
            slot,
            message: if op == Operation::Sign {
                slot.unwrap_or_default().to_be_bytes().to_vec()
            } else {
                vec![]
            },
        };
        coordinate(
            &req,
            &[7; 32],
            Profile::Slh(params),
            peers,
            &Authority::operator(&[12; 32])?,
            Duration::from_secs(7200),
        )
    }

    #[test]
    fn tooth_daemon_signs_across_refresh_and_rejects_replays() {
        signing_ceremonies(PARAMS, Duration::from_secs(1200))
    }

    #[test]
    #[ignore = "full FIPS 205 SHAKE-128f signing twice over TCP"]
    fn daemon_full_slh_signs_across_refresh() {
        signing_ceremonies(Fips205Params::SLH_DSA_SHAKE_128F, Duration::from_secs(7200))
    }

    fn signing_ceremonies(params: Fips205Params, timeout: Duration) {
        let f = Fixture::new(params);
        let (peers, threads) = f.start(5, timeout);
        assert_eq!(
            call(params, &peers, Operation::Public, 1, None).unwrap(),
            f.expected
        );
        let pk = SlhPublicKey::from_bytes_for_params(&params, &f.expected).unwrap();
        let sig = call(params, &peers, Operation::Sign, 2, Some(10)).unwrap();
        assert!(slh_verify(&params, &10u64.to_be_bytes(), &sig, &[], &pk));
        let before = f.shares();
        call(params, &peers, Operation::Refresh, 3, None).unwrap();
        let installed = f.shares();
        for (a, b) in before.iter().zip(&installed) {
            assert_ne!(a, b);
        }
        // Recreate a crash after the anchor committed but before the share rename.
        replace_secret(&format!("{}/share", f.paths(1).0), &before[1]).unwrap();
        let sig = call(params, &peers, Operation::Sign, 4, Some(250)).unwrap();
        assert!(slh_verify(&params, &250u64.to_be_bytes(), &sig, &[], &pk));
        assert_eq!(f.shares(), installed);
        assert!(
            call(params, &peers, Operation::Refresh, 2, None)
                .unwrap_err()
                .message
                .contains("session")
        );
        for (nonce, slot) in [(5, 250), (6, 100)] {
            assert!(
                call(params, &peers, Operation::Sign, nonce, Some(slot))
                    .unwrap_err()
                    .message
                    .contains("consumed")
            );
        }
        call(params, &peers, Operation::Refresh, 7, None).unwrap();
        for t in threads {
            t.join().unwrap();
        }
    }

    #[test]
    fn daemon_cli_refresh_from_roster_vault() {
        let profile = Profile::Slh(Fips205Params::SLH_DSA_SHAKE_128F);
        let f = Fixture::new(Fips205Params::SLH_DSA_SHAKE_128F);
        let sockets: Vec<_> = (0..3).map(|_| listener()).collect();
        let peers: Vec<_> = sockets.iter().map(|s| s.local_addr().unwrap()).collect();
        let csv = |addrs: &[SocketAddr]| {
            addrs
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(",")
        };
        let mesh = csv(&f.mesh);
        let mut threads = vec![];
        for (p, socket) in sockets.into_iter().enumerate() {
            let (path, cfg) = f.paths(p);
            let args = [
                "--vault-dir",
                &path,
                "--anchor-dir",
                cfg.anchor_dir.as_deref().unwrap(),
                "--deployment-id",
                &"07".repeat(32),
                "--profile",
                profile.name(),
                "--party",
                &p.to_string(),
                "--peers",
                &mesh,
                "--control-listen",
                &peers[p].to_string(),
                "--max-ceremonies",
                "1",
                "--allow-single-disk-anchor",
            ]
            .map(str::to_owned);
            threads.push(std::thread::spawn(move || {
                drop(socket);
                let mut cmd = if p == 0 {
                    vec!["daemon".to_owned()]
                } else {
                    vec!["wire".to_owned(), "daemon".to_owned()]
                };
                cmd.extend(args);
                crate::quorum::run(&cmd).unwrap();
            }));
        }
        for peer in &peers {
            let limit = Instant::now() + Duration::from_secs(10);
            while TcpStream::connect_timeout(peer, Duration::from_millis(100)).is_err() {
                assert!(Instant::now() < limit, "daemon failed to listen");
                std::thread::sleep(Duration::from_millis(20));
            }
        }
        let out = f.root.join("receipt");
        let cmd = [
            "wire",
            "refresh",
            "--control-peers",
            &csv(&peers),
            "--vault-dir",
            &f.paths(0).0,
            "--deployment-id",
            &"07".repeat(32),
            "--profile",
            profile.name(),
            "--session",
            &"11".repeat(32),
            "--out",
            out.to_str().unwrap(),
        ]
        .map(str::to_owned);
        crate::quorum::run(&cmd).unwrap();
        let expected = Request {
            op: Operation::Refresh,
            nonce: [17; 32],
            slot: None,
            message: vec![],
        }
        .context(&[7; 32], profile);
        assert_eq!(std::fs::read(out).unwrap(), expected);
        for t in threads {
            t.join().unwrap();
        }
        // Reopen every vault from the rotated share and the original journal.
        let installed = f.shares();
        let (peers, restarted) = f.start(1, Duration::from_secs(30));
        assert!(
            call(f.params, &peers, Operation::Refresh, 17, None)
                .unwrap_err()
                .message
                .contains("session")
        );
        call(f.params, &peers, Operation::Refresh, 18, None).unwrap();
        for (previous, current) in installed.iter().zip(f.shares()) {
            assert_ne!(*previous, current);
        }
        for t in restarted {
            t.join().unwrap();
        }
    }

    #[test]
    fn tooth_daemon_serves_after_stalled_and_unauthenticated_clients() {
        let f = Fixture::new(PARAMS);
        let timeout = Duration::from_secs(2);
        let (peers, threads) = f.start(1, timeout);
        let mut stalled = TcpStream::connect(peers[0]).unwrap();
        stalled
            .set_read_timeout(Some(timeout + Duration::from_secs(2)))
            .unwrap();
        stalled.write_all(b"Q").unwrap();
        let mut byte = [0];
        assert_eq!(stalled.read(&mut byte).unwrap(), 0);
        let req = Request {
            op: Operation::Refresh,
            nonce: [7; 32],
            slot: None,
            message: vec![],
        };
        assert!(
            coordinate(
                &req,
                &[7; 32],
                Profile::Slh(PARAMS),
                &peers,
                &Authority::operator(&[88; 32]).unwrap(),
                timeout
            )
            .is_err()
        );
        call(PARAMS, &peers, Operation::Refresh, 7, None).unwrap();
        for t in threads {
            t.join().unwrap();
        }
    }
}
