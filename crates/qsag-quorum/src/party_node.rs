#![forbid(unsafe_code)]
//! Single-party protocol nodes: each value of these types is one party, holds only that
//! party's secrets, and talks to its peers through a [`WireTransport`].
//!
//! * [`IsolatedJortsParty`] — one custodian of Mode QS-A
//!   ([`crate::quorum_jorts::CommitteeCustodian`]): bind, exchange MAC-authenticated latch
//!   echoes with the committee, open the additive share, combine and self-verify.
//! * [`IsolatedQuorumParty`] — one custodian of Mode QS-B
//!   ([`crate::quorum_jorts::ShamirCustodian`]): acknowledge, assemble the latch
//!   certificate, open the Shamir share, reconstruct with attribution.
//! * [`IsolatedRss256Party`] — one party of a three-party replicated Boolean engine that
//!   evaluates `Keccak-f[1600]` on shared states. Party `i` holds its share pair
//!   `(s_i, s_{i+1})` of every state, the two pad keys `(k_i, k_{i+1})`, its two pairwise MAC
//!   keys, its private coins, its poison flag and its journal.
//!
//! ### The replicated engine
//! A wave is one permutation of every loaded state. In each of the 24 rounds a party applies
//! the linear layer to both of its shares locally and sends one masked product share per chi
//! AND gate to its predecessor (200 bytes per state and round). Nothing is opened until a
//! barrier ([`IsolatedRss256Party::check`]) has accepted every gate since the last one:
//!
//! 1. every party commits to two coin shares (commit round), then opens the first together
//!    with a MAC-authenticated digest of the commitments it received, so that two parties
//!    shown different commitments notice before the coin is used;
//! 2. the first coin fixes the gate weights and every party, as prover, sends one verifier
//!    its share of the proof polynomial ([`crate::dzk`]);
//! 3. the second coin is opened and fixes two evaluation points; the two verifiers of each
//!    prover exchange their evaluations and check the node sum and both points;
//! 4. the parties exchange MAC-authenticated verdicts.
//!
//! Any failure, including a transport failure inside a wave or a barrier, sets the party's
//! poison flag, records it in the journal and sends an abort frame to both peers. A poisoned
//! party refuses every later wave, barrier and opening for that session, also after a restart
//! with the same journal.
//!
//! ### Limits
//! * Share pairs, pad keys and MAC keys come from a dealer in the tests and the benchmark
//!   (`deal_rss256_keys`, `deal_keccak_shares`, compiled only for tests and with the
//!   `testing-ephemeral` feature). Production callers can import enrolled custody
//!   using the key-share codec; this module does not establish the enrollment or
//!   authenticated key agreement itself.
//! * The engine evaluates plain `Keccak-f[1600]` states one 64-bit word per lane. It is not
//!   bitsliced across signatures and is not a replacement for the 256-lane engine of
//!   `qsag_core::rss256`; it exists to run the protocol with separated parties.
//! * Security is with abort: a corrupted party can stop a session and can learn an opened
//!   output while an honest party aborts.

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;
use qsag_verified::VerifiedRssPoisonLatch;

use qsag_asm::{KECCAK_ROTATION_OFFSETS, KECCAK_ROUND_CONSTANTS};
use qsag_core::belt_latch::DurableWal;
use qsag_core::keccak_mpc::RssKeyShare256;
use qsag_core::rss256::Shake256Prg256;
use qsag_core::wipe::{SecretBuffer, SecretVec, ct_eq_bytes, ct_eq_bytes32};

use crate::dzk::{
    DzkShape, Gf128, NodeBasis, challenge_points, data_node_sum, decode_elements, derive_weights,
    dot, encode_elements, expand_elements, prove, row_product_sum, weighted_sum, x_evals, y_evals,
};
use crate::hash::{SeedRng, h32, mac32, mac32_verify};
use crate::quorum_jorts::{
    CommitteeCustodian, LatchAck, LatchCertificate, LatchEcho, Node, QuorumError, QuorumJortsSig,
    SHARE_OPENING_WIRE_BYTES, ShamirCustodian, ShareOpening, WOTS_CHAINS, combine_additive,
    combine_shamir_robust, quorum_jorts_verify,
};
use crate::wire_channel::{MacSealedWireChannel, TransportError, WireTransport};

/// Round tags. The low byte of a gate round is the Keccak round index.
pub const ROUND_GATE: u32 = 0x0100_0000;
pub const ROUND_COIN_COMMIT: u32 = 0x0200_0000;
pub const ROUND_COIN_REVEAL_A: u32 = 0x0201_0000;
pub const ROUND_PROOF_SHARE: u32 = 0x0202_0000;
pub const ROUND_COIN_REVEAL_B: u32 = 0x0203_0000;
pub const ROUND_VERIFIER: u32 = 0x0204_0000;
pub const ROUND_VERDICT: u32 = 0x0205_0000;
pub const ROUND_OPEN: u32 = 0x0300_0000;
pub const ROUND_ECHO: u32 = 0x1000_0000;
pub const ROUND_SHARE: u32 = 0x1001_0000;
pub const ROUND_ACK: u32 = 0x2000_0000;
pub const ROUND_SHAMIR_SHARE: u32 = 0x2001_0000;
/// Sent to peers by a party that gives up; never a valid protocol round.
pub const ROUND_ABORT: u32 = 0x0F00_0000;

const TAG_COIN_COMMIT: &[u8] = b"QSAG.QUORUM.RSS.COIN.COMMIT/v1";
const TAG_COIN_ECHO: &[u8] = b"QSAG.QUORUM.RSS.COIN.ECHO/v1";
const TAG_COIN_ECHO_MAC: &[u8] = b"QSAG.QUORUM.RSS.COIN.ECHO.MAC/v1";
const TAG_SEED_A: &[u8] = b"QSAG.QUORUM.RSS.SEED.A/v1";
const TAG_SEED_B: &[u8] = b"QSAG.QUORUM.RSS.SEED.B/v1";
const TAG_VERDICT: &[u8] = b"QSAG.QUORUM.RSS.VERDICT/v1";
const TAG_DZK_PRG: &[u8] = b"QSAG.QUORUM.RSS.DZK.PRG/v1";
#[cfg(any(test, feature = "testing-ephemeral"))]
const TAG_RSS_KEY: &[u8] = b"QSAG.QUORUM.RSS.DEAL/v1";

const PURPOSE_CHI_PAD: u64 = 1;
const PRG_MASK_F: u8 = 1;
const PRG_MASK_G: u8 = 2;
const PRG_H_SHARE: u8 = 3;
const MAX_WAVE: u64 = (1 << 56) - 1;

/// Which check of a barrier rejected a prover's gates.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DzkStage {
    /// The node sum of the proof polynomial does not match the weighted gate claim.
    SumCheck,
    /// The proof polynomial is not the product polynomial at an evaluation point.
    PointCheck,
}

/// Errors of the isolated party nodes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NodeError {
    Transport(TransportError),
    Quorum(QuorumError),
    InvalidParameters,
    /// The party's poison flag is set for this session.
    Poisoned,
    /// An opening or a share load was requested while unverified gates exist.
    OpenBeforeCheck,
    /// A peer's message has the wrong length or encoding for its round.
    MalformedMessage {
        from: usize,
        round: u32,
    },
    /// A peer sent an abort frame.
    PeerAborted {
        party: usize,
    },
    /// A coin opening does not match its commitment.
    CoinOpeningRejected {
        party: usize,
    },
    /// The commitments `party` reports differ from the ones this party received.
    CoinEchoMismatch {
        party: usize,
    },
    /// A MAC under the pairwise key with `party` does not verify.
    MacInvalid {
        party: usize,
    },
    /// The proof for the gate messages of `prover` was rejected. This is not attribution:
    /// the other verifier of that proof may be the party that deviated.
    MultiplicationCheckFailed {
        prover: usize,
        stage: DzkStage,
    },
    /// The joint coin gave unusable evaluation points (negligible probability).
    BadChallenge,
    /// The two holders of an opened share sent different values.
    OpenShareMismatch,
    /// The poison journal could not be written.
    Journal,
    /// The wave counter left its domain.
    WaveCounterOverflow,
}

impl From<TransportError> for NodeError {
    fn from(e: TransportError) -> Self {
        Self::Transport(e)
    }
}

impl From<QuorumError> for NodeError {
    fn from(e: QuorumError) -> Self {
        Self::Quorum(e)
    }
}

impl fmt::Display for NodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Transport(e) => write!(f, "transport: {e}"),
            Self::Quorum(e) => write!(f, "quorum: {e}"),
            Self::InvalidParameters => f.write_str("invalid node parameters"),
            Self::Poisoned => f.write_str("session is poisoned"),
            Self::OpenBeforeCheck => f.write_str("opening requested before the barrier"),
            Self::MalformedMessage { from, round } => {
                write!(f, "malformed message from party {from} in round {round:#x}")
            }
            Self::PeerAborted { party } => write!(f, "party {party} aborted"),
            Self::CoinOpeningRejected { party } => {
                write!(f, "coin opening of party {party} rejected")
            }
            Self::CoinEchoMismatch { party } => {
                write!(f, "party {party} saw different coin commitments")
            }
            Self::MacInvalid { party } => write!(f, "MAC of party {party} invalid"),
            Self::MultiplicationCheckFailed { prover, stage } => {
                write!(f, "gates of party {prover} rejected ({stage:?})")
            }
            Self::BadChallenge => f.write_str("unusable evaluation points"),
            Self::OpenShareMismatch => f.write_str("opened share copies differ"),
            Self::Journal => f.write_str("poison journal write failed"),
            Self::WaveCounterOverflow => f.write_str("wave counter overflow"),
        }
    }
}

impl core::error::Error for NodeError {}

fn recv_from<T: WireTransport>(
    transport: &mut T,
    from: usize,
    round: u32,
) -> Result<SecretVec<u8>, NodeError> {
    match transport.recv_frame(from, round) {
        Ok(payload) => Ok(SecretBuffer(payload)),
        Err(TransportError::RoundTagMismatch {
            got: ROUND_ABORT, ..
        }) => Err(NodeError::PeerAborted { party: from }),
        Err(e) => Err(NodeError::Transport(e)),
    }
}

fn send_abort<T: WireTransport>(transport: &mut T, peers: &[usize]) {
    for &peer in peers {
        // Best effort: the peer may already be gone.
        let _ = transport.send_frame(peer, ROUND_ABORT, &[]);
    }
}

// ---------------------------------------------------------------------------------------------
// Mode QS-A over the wire
// ---------------------------------------------------------------------------------------------

/// Bytes of a latch echo on the wire.
pub const ECHO_WIRE_BYTES: usize = 4 + 8 + 32 + 32;

fn encode_echo(echo: &LatchEcho) -> Vec<u8> {
    let mut out = Vec::with_capacity(ECHO_WIRE_BYTES);
    out.extend_from_slice(&(echo.committee as u32).to_be_bytes());
    out.extend_from_slice(&echo.epoch.to_be_bytes());
    out.extend_from_slice(&echo.binding);
    out.extend_from_slice(&echo.mac);
    out
}

fn decode_echo(from: usize, raw: &[u8]) -> Option<LatchEcho> {
    if raw.len() != ECHO_WIRE_BYTES {
        return None;
    }
    Some(LatchEcho {
        from,
        committee: u32::from_be_bytes(raw[..4].try_into().ok()?) as usize,
        epoch: u64::from_be_bytes(raw[4..12].try_into().ok()?),
        binding: raw[12..44].try_into().ok()?,
        mac: raw[44..].try_into().ok()?,
    })
}

fn encode_opening(opening: &ShareOpening) -> SecretVec<u8> {
    let mut out = SecretVec::with_capacity(SHARE_OPENING_WIRE_BYTES);
    out.extend_wiping(&opening.leaf.to_be_bytes());
    out.extend_wiping(opening.shares.as_flattened());
    out
}

fn decode_opening(from: usize, raw: &[u8]) -> Option<ShareOpening> {
    if raw.len() != SHARE_OPENING_WIRE_BYTES {
        return None;
    }
    let shares: Vec<Node> = raw[8..].as_chunks::<32>().0.to_vec();
    debug_assert_eq!(shares.len(), WOTS_CHAINS);
    Some(ShareOpening {
        party: from,
        leaf: u64::from_be_bytes(raw[..8].try_into().ok()?),
        shares,
    })
}

/// One custodian of Mode QS-A with its transport.
pub struct IsolatedJortsParty<T: WireTransport, W: DurableWal> {
    custodian: CommitteeCustodian<W>,
    transport: T,
}

impl<T: WireTransport, W: DurableWal> IsolatedJortsParty<MacSealedWireChannel<T>, W> {
    /// Attach this custodian to a fresh, encrypted session in its enrolled deployment.
    pub fn new_deployed(
        deployment: Node,
        session: Node,
        mut custodian: CommitteeCustodian<W>,
        transport: T,
    ) -> Result<Self, NodeError> {
        let keys = custodian.deployed_wire_keys(deployment)?;
        let channel = MacSealedWireChannel::new_encrypted(transport, deployment, session, keys)?;
        Self::from_transport(custodian, channel)
    }
}

impl<T: WireTransport, W: DurableWal> IsolatedJortsParty<T, W> {
    #[cfg(any(test, feature = "testing-ephemeral"))]
    pub fn new(custodian: CommitteeCustodian<W>, transport: T) -> Result<Self, NodeError> {
        Self::from_transport(custodian, transport)
    }

    fn from_transport(custodian: CommitteeCustodian<W>, transport: T) -> Result<Self, NodeError> {
        if transport.party() != custodian.party() || transport.parties() != custodian.layout().n {
            return Err(NodeError::InvalidParameters);
        }
        Ok(Self {
            custodian,
            transport,
        })
    }

    pub fn custodian(&self) -> &CommitteeCustodian<W> {
        &self.custodian
    }

    /// Take the node apart (to move the custodian to another session's transport).
    pub fn into_parts(self) -> (CommitteeCustodian<W>, T) {
        (self.custodian, self.transport)
    }

    /// Sign `msg` at `epoch` of `committee` together with the other members, each running
    /// this same call. No share leaves this party unless every other member echoed, under a
    /// valid MAC, the binding this party persisted. On failure the peers get an abort frame.
    pub fn sign(
        &mut self,
        committee: usize,
        epoch: u64,
        msg: &[u8],
    ) -> Result<QuorumJortsSig, NodeError> {
        let members = self
            .custodian
            .layout()
            .committees()
            .get(committee)
            .ok_or(NodeError::Quorum(QuorumError::UnknownCommittee))?
            .clone();
        let me = self.custodian.party();
        let peers: Vec<usize> = members.iter().copied().filter(|&p| p != me).collect();
        let result = self.sign_inner(committee, epoch, msg, &members, &peers);
        if result.is_err() {
            send_abort(&mut self.transport, &peers);
        }
        result
    }

    fn sign_inner(
        &mut self,
        committee: usize,
        epoch: u64,
        msg: &[u8],
        members: &[usize],
        peers: &[usize],
    ) -> Result<QuorumJortsSig, NodeError> {
        let record = self.custodian.bind(committee, epoch, msg)?;
        for &peer in peers {
            let echo = self.custodian.echo_for(committee, peer)?;
            self.transport
                .send_frame(peer, ROUND_ECHO, &encode_echo(&echo))?;
        }
        let mut echoes = Vec::with_capacity(peers.len());
        for &peer in peers {
            let raw = recv_from(&mut self.transport, peer, ROUND_ECHO)?;
            echoes.push(decode_echo(peer, &raw).ok_or(NodeError::MalformedMessage {
                from: peer,
                round: ROUND_ECHO,
            })?);
        }
        let permit = self.custodian.verify_echoes(committee, &echoes)?;
        let own = self.custodian.open(&permit)?;
        let wire = encode_opening(&own);
        for &peer in peers {
            self.transport.send_frame(peer, ROUND_SHARE, &wire)?;
        }
        let mut openings = vec![own];
        for &peer in peers {
            let raw = recv_from(&mut self.transport, peer, ROUND_SHARE)?;
            openings.push(
                decode_opening(peer, &raw).ok_or(NodeError::MalformedMessage {
                    from: peer,
                    round: ROUND_SHARE,
                })?,
            );
        }
        let sig = combine_additive(self.custodian.tree(), &record, members, &openings)?;
        if !quorum_jorts_verify(self.custodian.tree().public_key(), msg, &sig) {
            return Err(NodeError::Quorum(QuorumError::SignatureVerifyFailed));
        }
        Ok(sig)
    }
}

// ---------------------------------------------------------------------------------------------
// Mode QS-B over the wire
// ---------------------------------------------------------------------------------------------

fn encode_ack(ack: &LatchAck) -> Vec<u8> {
    let mut out = Vec::with_capacity(8 + 32 + 32 * ack.macs.len());
    out.extend_from_slice(&ack.leaf.to_be_bytes());
    out.extend_from_slice(&ack.binding);
    out.extend_from_slice(ack.macs.as_flattened());
    out
}

fn decode_ack(from: usize, parties: usize, raw: &[u8]) -> Option<LatchAck> {
    if raw.len() != 8 + 32 + 32 * parties {
        return None;
    }
    Some(LatchAck {
        from,
        leaf: u64::from_be_bytes(raw[..8].try_into().ok()?),
        binding: raw[8..40].try_into().ok()?,
        macs: raw[40..].as_chunks::<32>().0.to_vec(),
    })
}

/// What a QS-B signing session returns at one custodian.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QuorumSignOutcome {
    pub signature: QuorumJortsSig,
    /// Acknowledgements this custodian verified in the certificate.
    pub certified_by: usize,
    /// Custodians whose openings contradicted the verified reconstruction.
    pub blamed: Vec<usize>,
}

/// One custodian of Mode QS-B with its transport.
pub struct IsolatedQuorumParty<T: WireTransport, W: DurableWal> {
    custodian: ShamirCustodian<W>,
    transport: T,
}

impl<T: WireTransport, W: DurableWal> IsolatedQuorumParty<MacSealedWireChannel<T>, W> {
    /// Attach this custodian to a fresh, encrypted session in its enrolled deployment.
    pub fn new_deployed(
        deployment: Node,
        session: Node,
        mut custodian: ShamirCustodian<W>,
        transport: T,
    ) -> Result<Self, NodeError> {
        let keys = custodian.deployed_wire_keys(deployment)?;
        let channel = MacSealedWireChannel::new_encrypted(transport, deployment, session, keys)?;
        Self::from_transport(custodian, channel)
    }
}

impl<T: WireTransport, W: DurableWal> IsolatedQuorumParty<T, W> {
    #[cfg(any(test, feature = "testing-ephemeral"))]
    pub fn new(custodian: ShamirCustodian<W>, transport: T) -> Result<Self, NodeError> {
        Self::from_transport(custodian, transport)
    }

    fn from_transport(custodian: ShamirCustodian<W>, transport: T) -> Result<Self, NodeError> {
        if transport.party() != custodian.party()
            || transport.parties() != custodian.config().parties()
        {
            return Err(NodeError::InvalidParameters);
        }
        Ok(Self {
            custodian,
            transport,
        })
    }

    pub fn custodian(&self) -> &ShamirCustodian<W> {
        &self.custodian
    }

    /// Take the node apart (to move the custodian to another session's transport).
    pub fn into_parts(self) -> (ShamirCustodian<W>, T) {
        (self.custodian, self.transport)
    }

    /// Sign `msg` at `leaf` with the custodians in `online`, each running this same call;
    /// those in `openers` open their shares. An acknowledgement or opening that does not
    /// arrive or does not decode is skipped: the session succeeds if this custodian still
    /// verifies a quorum of acknowledgements and `t` consistent openings. No share leaves
    /// this party without a certificate it verified itself.
    pub fn sign(
        &mut self,
        online: &[usize],
        openers: &[usize],
        leaf: u64,
        msg: &[u8],
    ) -> Result<QuorumSignOutcome, NodeError> {
        let me = self.custodian.party();
        let parties = self.custodian.config().parties();
        if !online.contains(&me) || online.iter().any(|&p| p >= parties) {
            return Err(NodeError::InvalidParameters);
        }
        let peers: Vec<usize> = online.iter().copied().filter(|&p| p != me).collect();
        let result = self.sign_inner(&peers, openers, leaf, msg);
        if result.is_err() {
            send_abort(&mut self.transport, &peers);
        }
        result
    }

    fn sign_inner(
        &mut self,
        peers: &[usize],
        openers: &[usize],
        leaf: u64,
        msg: &[u8],
    ) -> Result<QuorumSignOutcome, NodeError> {
        let me = self.custodian.party();
        let parties = self.custodian.config().parties();
        let (record, ack) = self.custodian.ack(leaf, msg)?;
        let wire = encode_ack(&ack);
        for &peer in peers {
            self.transport.send_frame(peer, ROUND_ACK, &wire)?;
        }
        let mut acks = vec![ack];
        for &peer in peers {
            if let Ok(raw) = recv_from(&mut self.transport, peer, ROUND_ACK)
                && let Some(ack) = decode_ack(peer, parties, &raw)
            {
                acks.push(ack);
            }
        }
        let cert = LatchCertificate::assemble(&record, acks);
        let certified_by = self.custodian.verify_certificate(&cert)?;
        let mut openings = Vec::new();
        if openers.contains(&me) {
            let own = self.custodian.open(leaf, msg, &cert)?;
            let wire = encode_opening(&own);
            for &peer in peers {
                self.transport.send_frame(peer, ROUND_SHAMIR_SHARE, &wire)?;
            }
            openings.push(own);
        }
        for &peer in peers.iter().filter(|p| openers.contains(p)) {
            if let Ok(raw) = recv_from(&mut self.transport, peer, ROUND_SHAMIR_SHARE)
                && let Some(opening) = decode_opening(peer, &raw)
            {
                openings.push(opening);
            }
        }
        let (signature, blamed) = combine_shamir_robust(
            self.custodian.config(),
            self.custodian.tree(),
            &record,
            &openings,
        )?;
        if !quorum_jorts_verify(self.custodian.tree().public_key(), msg, &signature) {
            return Err(NodeError::Quorum(QuorumError::SignatureVerifyFailed));
        }
        Ok(QuorumSignOutcome {
            signature,
            certified_by,
            blamed,
        })
    }
}

// ---------------------------------------------------------------------------------------------
// Three-party replicated Keccak engine, one party per value
// ---------------------------------------------------------------------------------------------

/// Durable record of reserved and poisoned sessions.
pub trait PoisonJournal {
    /// Atomically and durably reserve `session_id` before any protocol masks, coins,
    /// or transport frames are derived. Reusing a previously reserved or poisoned
    /// `session_id` must fail closed so crash recovery never repeats pads or coins.
    fn reserve_session(&mut self, session_id: &[u8; 32]) -> Result<(), NodeError>;

    /// Record that `session_id` is poisoned; return only once it would survive a restart.
    fn mark_poisoned(&mut self, session_id: &[u8; 32]) -> Result<(), NodeError>;

    fn is_poisoned(&self, session_id: &[u8; 32]) -> bool;
}

impl<J: PoisonJournal> PoisonJournal for &mut J {
    fn reserve_session(&mut self, id: &[u8; 32]) -> Result<(), NodeError> {
        (**self).reserve_session(id)
    }
    fn mark_poisoned(&mut self, id: &[u8; 32]) -> Result<(), NodeError> {
        (**self).mark_poisoned(id)
    }
    fn is_poisoned(&self, id: &[u8; 32]) -> bool {
        (**self).is_poisoned(id)
    }
}

/// Volatile [`PoisonJournal`], restricted to tests and `testing-ephemeral`. It forgets
/// every reservation at process exit, so a restarted party would reuse its session masks;
/// production nodes take `poison_journal::FsDurablePoisonAndSessionJournal`.
#[cfg(any(test, feature = "testing-ephemeral"))]
#[derive(Clone, Debug, Default)]
pub struct MemoryPoisonJournal {
    reserved_sessions: Vec<[u8; 32]>,
    sessions: Vec<[u8; 32]>,
    fail_next: bool,
}

#[cfg(any(test, feature = "testing-ephemeral"))]
impl MemoryPoisonJournal {
    pub fn new() -> Self {
        Self::default()
    }

    /// Make the next poison write fail.
    pub fn fail_next_write(&mut self) {
        self.fail_next = true;
    }
}

#[cfg(any(test, feature = "testing-ephemeral"))]
impl PoisonJournal for MemoryPoisonJournal {
    fn reserve_session(&mut self, session_id: &[u8; 32]) -> Result<(), NodeError> {
        if self.sessions.contains(session_id) || self.reserved_sessions.contains(session_id) {
            return Err(NodeError::Journal);
        }
        self.reserved_sessions.push(*session_id);
        Ok(())
    }

    fn mark_poisoned(&mut self, session_id: &[u8; 32]) -> Result<(), NodeError> {
        if self.fail_next {
            self.fail_next = false;
            return Err(NodeError::Journal);
        }
        if !self.is_poisoned(session_id) {
            self.sessions.push(*session_id);
        }
        Ok(())
    }

    fn is_poisoned(&self, session_id: &[u8; 32]) -> bool {
        self.sessions.contains(session_id)
    }
}

const TAG_OPEN_BINDING: &[u8] = b"QSAG.RSS.OPEN.BINDING/v1";
const TAG_OPEN_COPY: &[u8] = b"QSAG.RSS.OPEN.COPY/v1";

/// The only place opened lanes are reconstructed from the three share slots. It consumes
/// the release permit of the opening round, which only an accepting
/// `qsag_verified::ConsumingOpeningGuard2Lane` can produce.
fn reconstruct_opened(
    _release: qsag_verified::OpeningReleasePermit,
    states: usize,
    words: usize,
    mine: &[u64],
    next: &[u64],
    third: &[u64],
) -> Vec<Vec<u64>> {
    (0..states)
        .map(|s| {
            (0..words)
                .map(|w| mine[s * words + w] ^ next[s * words + w] ^ third[s * words + w])
                .collect()
        })
        .collect()
}

mod share_pair {
    /// One party's replicated share of a `Keccak-f[1600]` state: share slot `party` and share
    /// slot `party + 1`. The state is the xor of the three slots.
    ///
    /// Strictly move-only (`!Clone` in all profiles) and opaque outside `party_node` in production
    /// builds (`R-Ex-10` / `R12`): production callers enroll states exclusively via WAL/session-
    /// mediated [`super::IsolatedRss256Party::enroll_rss_key_block`], while test/`testing-ephemeral`
    /// harnesses consume party- and session-bound tickets once via
    /// [`super::IsolatedRss256Party::load_shares`].
    pub struct SharePair {
        pub(super) party: usize,
        pub(super) session_id: Option<[u8; 32]>,
        pub(super) mine: [u64; 25],
        pub(super) next: [u64; 25],
    }

    impl SharePair {
        /// Custodian party index (`0..3`) bound to this state share pair.
        #[inline]
        pub const fn party(&self) -> usize {
            self.party
        }

        /// Optional session identifier bound to this state share pair.
        #[inline]
        pub const fn session_id(&self) -> Option<&[u8; 32]> {
            self.session_id.as_ref()
        }
    }
}

#[cfg(any(test, feature = "testing-ephemeral"))]
pub use share_pair::SharePair;
#[cfg(not(any(test, feature = "testing-ephemeral")))]
pub(crate) use share_pair::SharePair;

/// The secrets of one party of the replicated engine.
#[derive(Clone)]
pub struct Rss256PartyKeys {
    pub party: usize,
    /// Pad keys of share slots `party` and `party + 1`.
    pub slot_keys: [[u8; 32]; 2],
    /// MAC keys shared with parties `party + 1` and `party + 2`.
    pub mac_keys: [[u8; 32]; 2],
    /// Seed of the party's private coins.
    pub rng_seed: [u8; 32],
}

/// Dealer for the three parties' keys (tests and measurements; stands in for pairwise key
/// agreement).
/// TRUSTED DEALER TEST/MEASUREMENT HELPER: not dealerless provisioning.
#[cfg(any(test, feature = "testing-ephemeral"))]
pub fn deal_rss256_keys(seed: &[u8; 32]) -> [Rss256PartyKeys; 3] {
    let slot = |j: usize| h32(TAG_RSS_KEY, &[seed, b"slot", &[(j % 3) as u8]]);
    let pair = |a: usize, b: usize| {
        let (lo, hi) = ((a % 3).min(b % 3), (a % 3).max(b % 3));
        h32(TAG_RSS_KEY, &[seed, b"pair", &[lo as u8, hi as u8]])
    };
    core::array::from_fn(|p| Rss256PartyKeys {
        party: p,
        slot_keys: [slot(p), slot(p + 1)],
        mac_keys: [pair(p, p + 1), pair(p, p + 2)],
        rng_seed: h32(TAG_RSS_KEY, &[seed, b"rng", &[p as u8]]),
    })
}

/// Dealer for one shared state: three move-only party-bound slots that xor to `secret`.
/// TRUSTED DEALER TEST/MEASUREMENT HELPER: not dealerless provisioning.
#[cfg(any(test, feature = "testing-ephemeral"))]
pub fn deal_keccak_shares(secret: &[u64; 25], rng: &mut SeedRng) -> [SharePair; 3] {
    deal_keccak_shares_inner(None, secret, rng)
}

/// Session-bound variant of [`deal_keccak_shares`] rejecting cross-session enrollment.
/// TRUSTED DEALER TEST/MEASUREMENT HELPER: not dealerless provisioning.
#[cfg(any(test, feature = "testing-ephemeral"))]
pub fn deal_keccak_shares_for_session(
    session_id: [u8; 32],
    secret: &[u64; 25],
    rng: &mut SeedRng,
) -> [SharePair; 3] {
    deal_keccak_shares_inner(Some(session_id), secret, rng)
}

#[cfg(any(test, feature = "testing-ephemeral"))]
fn deal_keccak_shares_inner(
    session_id: Option<[u8; 32]>,
    secret: &[u64; 25],
    rng: &mut SeedRng,
) -> [SharePair; 3] {
    let mut slots = SecretBuffer([[0u64; 25]; 3]);
    for slot in &mut slots[..2] {
        for word in slot.iter_mut() {
            let mut raw = [0u8; 8];
            rng.fill(&mut raw);
            *word = u64::from_le_bytes(raw);
        }
    }
    for (i, word) in secret.iter().enumerate() {
        slots[2][i] = word ^ slots[0][i] ^ slots[1][i];
    }
    core::array::from_fn(|p| SharePair {
        party: p,
        session_id,
        mine: slots[p],
        next: slots[(p + 1) % 3],
    })
}

/// Theta, rho and pi of `Keccak-f[1600]` (the linear part of a round).
fn keccak_linear(a: &[u64; 25]) -> [u64; 25] {
    let mut c = [0u64; 5];
    for (x, parity) in c.iter_mut().enumerate() {
        *parity = a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20];
    }
    let mut out = [0u64; 25];
    for x in 0..5 {
        let d = c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
        for y in 0..5 {
            let source = x + 5 * y;
            let target = y + 5 * ((2 * x + 3 * y) % 5);
            out[target] = (a[source] ^ d).rotate_left(KECCAK_ROTATION_OFFSETS[source]);
        }
    }
    out
}

/// Lanes of the two chi operands of `lane`: `out = b0 ^ b2 ^ (b1 & b2)`.
#[inline]
const fn chi_operands(lane: usize) -> (usize, usize) {
    let row = 5 * (lane / 5);
    (row + (lane + 1) % 5, row + (lane + 2) % 5)
}

fn words_to_bytes(words: &[u64]) -> SecretVec<u8> {
    let mut out = SecretVec::with_capacity(8 * words.len());
    for word in words {
        out.extend_wiping(&word.to_le_bytes());
    }
    out
}

fn bytes_to_words(raw: &[u8], count: usize) -> Option<Vec<u64>> {
    (raw.len() == 8 * count).then(|| {
        raw.as_chunks::<8>()
            .0
            .iter()
            .map(|c| u64::from_le_bytes(*c))
            .collect()
    })
}

/// Commitment to coin share `value` of `party` (`which` is 0 for the weights coin, 1 for the
/// points coin).
pub(crate) fn coin_commitment(
    session_id: &[u8; 32],
    barrier: u64,
    party: usize,
    which: u8,
    value: &[u8; 32],
) -> [u8; 32] {
    h32(
        TAG_COIN_COMMIT,
        &[
            session_id,
            &barrier.to_be_bytes(),
            &[party as u8, which],
            value,
        ],
    )
}

/// Per-gate values a party keeps until the next barrier. One 64-bit word holds 64 gates.
#[derive(Default)]
struct GateRecord {
    a_mine: Vec<u64>,
    b_mine: Vec<u64>,
    a_next: Vec<u64>,
    b_next: Vec<u64>,
    pad_mine: Vec<u64>,
    pad_next: Vec<u64>,
    /// Product shares received from the successor (its own gate messages).
    received: Vec<u64>,
}

impl GateRecord {
    // Retain previous gates until their barrier, wiping the old allocation on growth.
    fn reserve(&mut self, additional: usize) -> Result<(), NodeError> {
        for words in [
            &mut self.a_mine,
            &mut self.b_mine,
            &mut self.a_next,
            &mut self.b_next,
            &mut self.pad_mine,
            &mut self.pad_next,
            &mut self.received,
        ] {
            let needed = words
                .len()
                .checked_add(additional)
                .ok_or(NodeError::Poisoned)?;
            if needed > words.capacity() {
                let mut next = Vec::new();
                next.try_reserve_exact(needed)
                    .map_err(|_| NodeError::Poisoned)?;
                next.extend_from_slice(words);
                qsag_asm::volatile_fill(words, 0);
                *words = next;
            }
        }
        Ok(())
    }
    fn wipe(&mut self) {
        for v in [
            &mut self.a_mine,
            &mut self.b_mine,
            &mut self.a_next,
            &mut self.b_next,
            &mut self.pad_mine,
            &mut self.pad_next,
            &mut self.received,
        ] {
            qsag_asm::volatile_fill(&mut v[..], 0);

            v.clear();
        }
    }
}

/// Deviations a test can ask a party to make (the party is then the corrupted one).
#[cfg(test)]
#[derive(Clone, Copy, Debug)]
pub(crate) enum Cheat {
    /// Use a product share of state 0 with one bit flipped. With `patch_proof`, also move
    /// the resulting difference into the proof polynomial so that the node sum still
    /// matches.
    FlipGate {
        round: usize,
        lane: usize,
        bit: u32,
        patch_proof: bool,
    },
}

/// One party of the replicated engine (see the module documentation).
pub struct IsolatedRss256Party<T: WireTransport, J: PoisonJournal> {
    party: usize,
    session_id: [u8; 32],
    slot_keys: [[u8; 32]; 2],
    mac_keys: [[u8; 32]; 2],
    rng: SeedRng,
    transport: T,
    journal: J,
    states: Vec<SharePair>,
    wave: u64,
    barrier: u64,
    /// Opening rounds started in this session; each gets its own release guard.
    open_round: u64,
    record: GateRecord,
    verified_latch: Option<VerifiedRssPoisonLatch>,
    unverified: bool,
    poisoned: bool,
    journal_failed: bool,
    #[cfg(test)]
    cheat: Option<Cheat>,
}

impl<T: WireTransport, J: PoisonJournal> Drop for IsolatedRss256Party<T, J> {
    fn drop(&mut self) {
        self.record.wipe();
        for state in &mut self.states {
            qsag_asm::volatile_fill(&mut state.mine[..], 0);
            qsag_asm::volatile_fill(&mut state.next[..], 0);
        }
        for key in self.slot_keys.iter_mut().chain(&mut self.mac_keys) {
            qsag_asm::volatile_fill(&mut key[..], 0);
        }
    }
}

impl<T: WireTransport, J: PoisonJournal> IsolatedRss256Party<MacSealedWireChannel<T>, J> {
    pub fn new_deployed(
        deployment: Node,
        session: Node,
        mut keys: Rss256PartyKeys,
        transport: T,
        journal: J,
    ) -> Result<Self, NodeError> {
        if keys.party >= 3 {
            return Err(NodeError::InvalidParameters);
        }
        let mut links = vec![[0; 32]; 3];
        for i in 0..2 {
            links[(keys.party + 1 + i) % 3] =
                mac32(&keys.mac_keys[i], b"QSAG.RSS.WIRE/v2", &[&deployment]);
            keys.mac_keys[i] = mac32(&keys.mac_keys[i], b"QSAG.RSS.PERMIT/v2", &[&deployment]);
            keys.slot_keys[i] = mac32(&keys.slot_keys[i], b"QSAG.RSS.SLOT/v2", &[&deployment]);
        }
        keys.rng_seed = mac32(&keys.rng_seed, b"QSAG.RSS.COINS/v2", &[&deployment]);
        let channel = MacSealedWireChannel::new_encrypted(transport, deployment, session, links)?;
        Self::from_transport(session, keys, channel, journal)
    }
}

impl<T: WireTransport, J: PoisonJournal> IsolatedRss256Party<T, J> {
    /// A party of session `session_id`. If the journal already lists the session as
    /// poisoned, the party starts poisoned; otherwise construction atomically and durably
    /// reserves `session_id` before any protocol mask or coin can be derived.
    #[cfg(any(test, feature = "testing-ephemeral"))]
    pub fn new(
        session_id: Node,
        keys: Rss256PartyKeys,
        transport: T,
        journal: J,
    ) -> Result<Self, NodeError> {
        Self::from_transport(session_id, keys, transport, journal)
    }

    fn from_transport(
        session_id: [u8; 32],
        keys: Rss256PartyKeys,
        transport: T,
        mut journal: J,
    ) -> Result<Self, NodeError> {
        if keys.party >= 3 || transport.party() != keys.party || transport.parties() != 3 {
            return Err(NodeError::InvalidParameters);
        }
        #[cfg(feature = "std")]
        let rng = {
            let mut fresh = qsag_core::wipe::SecretBuffer([0; 32]);
            qsag_asm::fill_os_random(&mut fresh[..])
                .map_err(|_| NodeError::Transport(TransportError::AuthenticationFailed))?;
            let seed = qsag_core::wipe::SecretBuffer(h32(
                b"QSAG.RSS.PRIVATE.COINS/v1",
                &[&keys.rng_seed, &fresh[..]],
            ));
            SeedRng::new(&seed, &session_id)
        };
        #[cfg(not(feature = "std"))]
        let rng = SeedRng::new(&keys.rng_seed, &session_id);
        let poisoned = journal.is_poisoned(&session_id);
        if !poisoned {
            journal.reserve_session(&session_id)?;
        }
        let verified_latch = if poisoned {
            VerifiedRssPoisonLatch::new_clean()
                .record_check_result(false)
                .0
        } else {
            VerifiedRssPoisonLatch::new_clean()
        };
        Ok(Self {
            party: keys.party,
            session_id,
            slot_keys: keys.slot_keys,
            // Provisioning may span sessions; derive traffic keys after reservation.
            mac_keys: keys
                .mac_keys
                .map(|key| h32(b"QSAG.RSS.SESSION.MAC/v1", &[&key, &session_id])),
            rng,
            transport,
            journal,
            states: Vec::new(),
            wave: 0,
            barrier: 0,
            open_round: 0,
            record: GateRecord::default(),
            verified_latch: Some(verified_latch),
            unverified: false,
            poisoned,
            journal_failed: false,
            #[cfg(test)]
            cheat: None,
        })
    }

    pub fn party(&self) -> usize {
        self.party
    }

    pub fn is_poisoned(&self) -> bool {
        self.poisoned
            || self
                .verified_latch
                .as_ref()
                .is_none_or(VerifiedRssPoisonLatch::is_poisoned)
    }

    /// True while gates exist that no barrier has accepted.
    pub fn has_unverified_gates(&self) -> bool {
        self.unverified
            || self
                .verified_latch
                .as_ref()
                .is_none_or(|latch| latch.is_unverified() || latch.pending_relations() != 0)
    }

    pub fn state_count(&self) -> usize {
        self.states.len()
    }

    /// Barriers passed so far.
    pub fn barriers(&self) -> u64 {
        self.barrier
    }

    /// Production WAL/session-mediated state enrollment directly from a scheme-bound
    /// [`RssKeyShare256`] and a public 200-byte (`[u64; 25]`) framing template (`R-Ex-10`),
    /// without constructing or exposing any external `SharePair`.
    pub fn enroll_rss_key_block(
        &mut self,
        key_share: &RssKeyShare256,
        expected_scheme_identity: &[u8; 32],
        use_prf: bool,
        public_template: &[u64; 25],
        secret_byte_offset: usize,
    ) -> Result<usize, NodeError> {
        self.guarded(|party| {
            if party.has_unverified_gates() {
                return Err(NodeError::OpenBeforeCheck);
            }
            if key_share.party_id != party.party {
                return Err(NodeError::InvalidParameters);
            }
            let shares = key_share
                .replicated_keccak_state_shares(
                    expected_scheme_identity,
                    use_prf,
                    public_template,
                    secret_byte_offset,
                )
                .map_err(|_| NodeError::InvalidParameters)?;
            party.states.push(SharePair {
                party: party.party,
                session_id: Some(party.session_id),
                mine: shares.0.0,
                next: shares.0.1,
            });
            Ok(party.states.len() - 1)
        })
    }

    /// Add this party's move-only share pair of a state; returns the index the state takes. All
    /// three parties must load their pairs of the same states in the same order.
    ///
    /// The state set changes only under the session guard: the journal must be healthy,
    /// the session unpoisoned, `pair.party == self.party`, `pair.session_id` (if bound) must
    /// match `self.session_id`, and every gate so far must be accepted by a barrier.
    #[cfg(any(test, feature = "testing-ephemeral"))]
    pub fn load_shares(&mut self, pair: SharePair) -> Result<usize, NodeError> {
        self.guarded(|party| {
            if party.has_unverified_gates() {
                return Err(NodeError::OpenBeforeCheck);
            }
            if pair.party != party.party {
                return Err(NodeError::InvalidParameters);
            }
            if let Some(bound_sid) = &pair.session_id
                && !ct_eq_bytes32(bound_sid, &party.session_id)
            {
                return Err(NodeError::InvalidParameters);
            }
            party.states.push(pair);
            Ok(party.states.len() - 1)
        })
    }

    #[cfg(test)]
    pub(crate) fn set_cheat(&mut self, cheat: Cheat) {
        self.cheat = Some(cheat);
    }

    const fn succ(&self) -> usize {
        (self.party + 1) % 3
    }

    const fn pred(&self) -> usize {
        (self.party + 2) % 3
    }

    /// MAC key shared with `peer`.
    fn pair_key(&self, peer: usize) -> &[u8; 32] {
        if peer == self.succ() {
            &self.mac_keys[0]
        } else {
            &self.mac_keys[1]
        }
    }

    fn poison(&mut self) -> Result<(), NodeError> {
        self.poisoned = true;
        if let Some(latch) = self.verified_latch.take() {
            self.verified_latch = Some(
                latch
                    .step(qsag_verified::RssLatchStepInput::RecordCheckResult { check_ok: false })
                    .0,
            );
        }
        let persisted = self.journal.mark_poisoned(&self.session_id);
        self.journal_failed |= persisted.is_err();
        let peers = [self.succ(), self.pred()];
        send_abort(&mut self.transport, &peers);
        persisted
    }

    fn guarded<R>(
        &mut self,
        body: impl FnOnce(&mut Self) -> Result<R, NodeError>,
    ) -> Result<R, NodeError> {
        if self.journal_failed {
            return Err(NodeError::Journal);
        }
        if self.is_poisoned() || self.journal.is_poisoned(&self.session_id) {
            self.poisoned = true;
            return Err(NodeError::Poisoned);
        }
        let result = body(self);
        if result.is_err() {
            self.poison()?;
        }
        result
    }

    /// One wave: `Keccak-f[1600]` on every loaded state. The gates stay unverified until
    /// [`Self::check`].
    pub fn permute(&mut self) -> Result<(), NodeError> {
        self.guarded(Self::permute_inner)
    }

    fn permute_inner(&mut self) -> Result<(), NodeError> {
        if self.wave > MAX_WAVE {
            return Err(NodeError::WaveCounterOverflow);
        }
        let n = self.states.len();
        let latch = self.verified_latch.take().ok_or(NodeError::Poisoned)?;
        let (next_latch, stage_res) = latch.stage_relations((24 * 25 * n.max(1)) as u64);
        self.verified_latch = Some(next_latch);
        if let Err(err) = stage_res {
            return Err(match err {
                qsag_verified::PantsGuardError::RelationCounterOverflow => {
                    NodeError::WaveCounterOverflow
                }
                _ => NodeError::Poisoned,
            });
        }
        let domain = (PURPOSE_CHI_PAD << 56) | self.wave;
        self.wave += 1;
        let mut pad_mine = Shake256Prg256::new(&self.slot_keys[0], &self.session_id, domain);
        let mut pad_next = Shake256Prg256::new(&self.slot_keys[1], &self.session_id, domain);
        let (succ, pred) = (self.succ(), self.pred());
        for state in &self.states {
            if state.party() != self.party
                || state
                    .session_id()
                    .is_some_and(|sid| !ct_eq_bytes32(sid, &self.session_id))
            {
                return Err(NodeError::InvalidParameters);
            }
        }
        self.unverified = true;
        self.record
            .reserve(n.checked_mul(25 * 24).ok_or(NodeError::Poisoned)?)?;
        let mut lin_mine: SecretVec<[u64; 25]> = SecretBuffer(vec![[0u64; 25]; n]);
        let mut lin_next: SecretVec<[u64; 25]> = SecretBuffer(vec![[0u64; 25]; n]);
        let mut pads_mine: SecretVec<u64> = SecretBuffer(vec![0u64; 25 * n]);
        let mut pads_next: SecretVec<u64> = SecretBuffer(vec![0u64; 25 * n]);
        let mut message: SecretVec<u64> = SecretBuffer(vec![0u64; 25 * n]);
        for (round, &rc) in KECCAK_ROUND_CONSTANTS.iter().enumerate() {
            pad_mine.fill_words(&mut pads_mine.0);
            pad_next.fill_words(&mut pads_next.0);
            for (s, state) in self.states.iter().enumerate() {
                lin_mine.0[s] = keccak_linear(&state.mine);
                lin_next.0[s] = keccak_linear(&state.next);
                for lane in 0..25 {
                    let (l1, l2) = chi_operands(lane);
                    let (am, an) = (lin_mine.0[s][l1], lin_next.0[s][l1]);
                    let (bm, bn) = (lin_mine.0[s][l2], lin_next.0[s][l2]);
                    let (pm, pn) = (pads_mine.0[25 * s + lane], pads_next.0[25 * s + lane]);
                    message.0[25 * s + lane] = (am & (bm ^ bn)) ^ (an & bm) ^ pm ^ pn;
                    self.record.a_mine.push(am);
                    self.record.b_mine.push(bm);
                    self.record.a_next.push(an);
                    self.record.b_next.push(bn);
                    self.record.pad_mine.push(pm);
                    self.record.pad_next.push(pn);
                }
            }
            #[cfg(test)]
            if let Some(Cheat::FlipGate {
                round: r,
                lane,
                bit,
                ..
            }) = self.cheat
                && r == round
            {
                // The cheater keeps the wrong product share itself, so the sharing stays
                // consistent and exactly this one gate is wrong.
                message.0[lane] ^= 1 << bit;
            }
            let wire_bytes = words_to_bytes(&message.0);
            self.transport
                .send_frame(pred, ROUND_GATE | round as u32, &wire_bytes)?;
            drop(wire_bytes);
            let raw = recv_from(&mut self.transport, succ, ROUND_GATE | round as u32)?;
            let received: SecretVec<u64> = SecretBuffer(bytes_to_words(&raw, 25 * n).ok_or(
                NodeError::MalformedMessage {
                    from: succ,
                    round: ROUND_GATE | round as u32,
                },
            )?);
            drop(raw);
            for (s, state) in self.states.iter_mut().enumerate() {
                for lane in 0..25 {
                    let (_, l2) = chi_operands(lane);
                    state.mine[lane] =
                        lin_mine.0[s][lane] ^ lin_mine.0[s][l2] ^ message.0[25 * s + lane];
                    state.next[lane] =
                        lin_next.0[s][lane] ^ lin_next.0[s][l2] ^ received.0[25 * s + lane];
                }
                // Iota is a public constant: it goes into share slot 0 only.
                match self.party {
                    0 => state.mine[0] ^= rc,
                    2 => state.next[0] ^= rc,
                    _ => {}
                }
            }
            self.record.received.extend_from_slice(&received.0);
        }
        Ok(())
    }

    fn prg_elements(&self, key: &[u8; 32], purpose: u8, prover: usize, count: usize) -> Vec<Gf128> {
        expand_elements(
            TAG_DZK_PRG,
            &[
                key,
                &self.session_id,
                &[purpose, prover as u8],
                &self.barrier.to_be_bytes(),
            ],
            count,
        )
    }

    /// The verification barrier (see the module documentation). On any error the party is
    /// poisoned for the rest of the session.
    pub fn check(&mut self) -> Result<(), NodeError> {
        self.guarded(Self::check_inner)
    }

    fn check_inner(&mut self) -> Result<(), NodeError> {
        if !self.unverified {
            return Ok(());
        }
        let me = self.party;
        let (succ, pred) = (self.succ(), self.pred());
        let peers = [succ, pred];
        let barrier = self.barrier;
        let sid = self.session_id;
        let shape = DzkShape::for_gates(64 * self.record.a_mine.len());
        let m = shape.m;

        // Round 1: commitments to both coin shares.
        let coins = [self.rng.bytes32(), self.rng.bytes32()];
        let mut commits = [[[0u8; 32]; 2]; 3];
        commits[me] = [
            coin_commitment(&sid, barrier, me, 0, &coins[0]),
            coin_commitment(&sid, barrier, me, 1, &coins[1]),
        ];
        let wire = commits[me].concat();
        for peer in peers {
            self.transport.send_frame(peer, ROUND_COIN_COMMIT, &wire)?;
        }
        for peer in peers {
            let raw = recv_from(&mut self.transport, peer, ROUND_COIN_COMMIT)?;
            if raw.len() != 64 {
                return Err(NodeError::MalformedMessage {
                    from: peer,
                    round: ROUND_COIN_COMMIT,
                });
            }
            commits[peer][0].copy_from_slice(&raw[..32]);
            commits[peer][1].copy_from_slice(&raw[32..]);
        }

        // Round 2: open the weights coin and echo the commitments seen.
        let echo = h32(
            TAG_COIN_ECHO,
            &[
                &sid,
                &barrier.to_be_bytes(),
                commits.as_flattened().as_flattened(),
            ],
        );
        for peer in peers {
            let mac = mac32(
                self.pair_key(peer),
                TAG_COIN_ECHO_MAC,
                &[&sid, &barrier.to_be_bytes(), &[me as u8, peer as u8], &echo],
            );
            let wire = [coins[0], echo, mac].concat();
            self.transport
                .send_frame(peer, ROUND_COIN_REVEAL_A, &wire)?;
        }
        let mut coin_a = [[0u8; 32]; 3];
        coin_a[me] = coins[0];
        for peer in peers {
            let raw = recv_from(&mut self.transport, peer, ROUND_COIN_REVEAL_A)?;
            if raw.len() != 96 {
                return Err(NodeError::MalformedMessage {
                    from: peer,
                    round: ROUND_COIN_REVEAL_A,
                });
            }
            coin_a[peer].copy_from_slice(&raw[..32]);
            if coin_commitment(&sid, barrier, peer, 0, &coin_a[peer]) != commits[peer][0] {
                return Err(NodeError::CoinOpeningRejected { party: peer });
            }
            let mac: [u8; 32] = core::array::from_fn(|i| raw[64 + i]);
            if !mac32_verify(
                self.pair_key(peer),
                TAG_COIN_ECHO_MAC,
                &[
                    &sid,
                    &barrier.to_be_bytes(),
                    &[peer as u8, me as u8],
                    &raw[32..64],
                ],
                &mac,
            ) {
                return Err(NodeError::MacInvalid { party: peer });
            }
            if raw[32..64] != echo {
                return Err(NodeError::CoinEchoMismatch { party: peer });
            }
        }
        let seed_a = h32(
            TAG_SEED_A,
            &[&sid, &barrier.to_be_bytes(), coin_a.as_flattened()],
        );

        // Round 3: as prover, send the successor its share of the proof polynomial.
        let row_basis = NodeBasis::new(shape.row_nodes());
        let h_basis = NodeBasis::new(shape.h_nodes());
        let my_weights = derive_weights(&seed_a, me, &shape);
        let masks_f = self.prg_elements(&self.slot_keys[0], PRG_MASK_F, me, 2 * m);
        let masks_g = self.prg_elements(&self.slot_keys[1], PRG_MASK_G, me, 2 * m);
        #[allow(unused_mut)]
        let mut h = prove(
            &shape,
            &my_weights,
            &row_basis,
            &self.record.a_mine,
            &self.record.b_mine,
            &self.record.b_next,
            &self.record.a_next,
            &masks_f,
            &masks_g,
        );
        #[cfg(test)]
        if let Some(Cheat::FlipGate {
            round,
            lane,
            bit,
            patch_proof: true,
        }) = self.cheat
        {
            let gate = 64 * (25 * self.states.len() * round + lane) + bit as usize;
            let beta =
                my_weights.gamma[gate / shape.half()].mul(my_weights.delta[gate % shape.half()]);
            h[1] = h[1].add(beta);
        }
        let h_pad = self.prg_elements(&self.slot_keys[0], PRG_H_SHARE, me, shape.h_nodes());
        let h_out: Vec<Gf128> = h.iter().zip(&h_pad).map(|(a, b)| a.add(*b)).collect();
        self.transport
            .send_frame(succ, ROUND_PROOF_SHARE, &encode_elements(&h_out))?;
        let raw = recv_from(&mut self.transport, pred, ROUND_PROOF_SHARE)?;
        let h_in = decode_elements(&raw, shape.h_nodes()).ok_or(NodeError::MalformedMessage {
            from: pred,
            round: ROUND_PROOF_SHARE,
        })?;

        // Round 4: open the points coin. Both proof shares this party verifies with are
        // fixed by now: one arrived above, the other is derived from a pad key.
        for peer in peers {
            self.transport
                .send_frame(peer, ROUND_COIN_REVEAL_B, &coins[1])?;
        }
        let mut coin_b = [[0u8; 32]; 3];
        coin_b[me] = coins[1];
        for peer in peers {
            let raw = recv_from(&mut self.transport, peer, ROUND_COIN_REVEAL_B)?;
            if raw.len() != 32 {
                return Err(NodeError::MalformedMessage {
                    from: peer,
                    round: ROUND_COIN_REVEAL_B,
                });
            }
            coin_b[peer].copy_from_slice(&raw);
            if coin_commitment(&sid, barrier, peer, 1, &coin_b[peer]) != commits[peer][1] {
                return Err(NodeError::CoinOpeningRejected { party: peer });
            }
        }
        let seed_b = h32(
            TAG_SEED_B,
            &[&sid, &barrier.to_be_bytes(), &seed_a, coin_b.as_flattened()],
        );

        // Round 5a: verifier of the successor's gates on the x side. This party's `next`
        // share slot is the successor's `mine` slot, and it received the gate messages.
        let w_succ = derive_weights(&seed_a, succ, &shape);
        let pts_succ = challenge_points(&seed_b, succ, &shape).ok_or(NodeError::BadChallenge)?;
        let claim_words: Vec<u64> = (0..self.record.received.len())
            .map(|i| {
                self.record.received[i]
                    ^ (self.record.a_next[i] & self.record.b_next[i])
                    ^ self.record.pad_next[i]
            })
            .collect();
        let masks_f_succ = self.prg_elements(&self.slot_keys[1], PRG_MASK_F, succ, 2 * m);
        let h_x = self.prg_elements(&self.slot_keys[1], PRG_H_SHARE, succ, shape.h_nodes());
        let sigma_x = data_node_sum(&shape, &h_x).add(weighted_sum(&shape, &w_succ, &claim_words));
        let mut out_x = vec![sigma_x];
        let mut f_at = Vec::with_capacity(2);
        let mut h_x_at = Vec::with_capacity(2);
        for r in pts_succ {
            h_x_at.push(dot(&h_basis.coeffs_at(r), &h_x));
            f_at.push(x_evals(
                &shape,
                &w_succ,
                &self.record.a_next,
                &self.record.b_next,
                &masks_f_succ,
                &row_basis.coeffs_at(r),
            ));
        }
        out_x.extend_from_slice(&h_x_at);
        out_x.extend(f_at.iter().flatten());

        // Round 5b: verifier of the predecessor's gates on the y side. This party's `mine`
        // share slot is the predecessor's `next` slot.
        let w_pred = derive_weights(&seed_a, pred, &shape);
        let pts_pred = challenge_points(&seed_b, pred, &shape).ok_or(NodeError::BadChallenge)?;
        let masks_g_pred = self.prg_elements(&self.slot_keys[0], PRG_MASK_G, pred, 2 * m);
        let sigma_y =
            data_node_sum(&shape, &h_in).add(weighted_sum(&shape, &w_pred, &self.record.pad_mine));
        let mut out_y = vec![sigma_y];
        let mut g_at = Vec::with_capacity(2);
        let mut h_y_at = Vec::with_capacity(2);
        for r in pts_pred {
            h_y_at.push(dot(&h_basis.coeffs_at(r), &h_in));
            g_at.push(y_evals(
                &shape,
                &self.record.b_mine,
                &self.record.a_mine,
                &masks_g_pred,
                &row_basis.coeffs_at(r),
            ));
        }
        out_y.extend_from_slice(&h_y_at);
        out_y.extend(g_at.iter().flatten());

        // The other verifier of the successor's gates is the predecessor, and vice versa.
        self.transport
            .send_frame(pred, ROUND_VERIFIER, &encode_elements(&out_x))?;
        self.transport
            .send_frame(succ, ROUND_VERIFIER, &encode_elements(&out_y))?;
        let width = 3 + 2 * m;
        let raw = recv_from(&mut self.transport, pred, ROUND_VERIFIER)?;
        let in_y = decode_elements(&raw, width).ok_or(NodeError::MalformedMessage {
            from: pred,
            round: ROUND_VERIFIER,
        })?;
        let raw = recv_from(&mut self.transport, succ, ROUND_VERIFIER)?;
        let in_x = decode_elements(&raw, width).ok_or(NodeError::MalformedMessage {
            from: succ,
            round: ROUND_VERIFIER,
        })?;

        // Successor's proof: own x side, predecessor's y side.
        if sigma_x.add(in_y[0]) != Gf128::ZERO {
            return Err(NodeError::MultiplicationCheckFailed {
                prover: succ,
                stage: DzkStage::SumCheck,
            });
        }
        for k in 0..2 {
            let g = &in_y[3 + k * m..3 + (k + 1) * m];
            if row_product_sum(&w_succ, &f_at[k], g) != h_x_at[k].add(in_y[1 + k]) {
                return Err(NodeError::MultiplicationCheckFailed {
                    prover: succ,
                    stage: DzkStage::PointCheck,
                });
            }
        }
        // Predecessor's proof: successor's x side, own y side.
        if sigma_y.add(in_x[0]) != Gf128::ZERO {
            return Err(NodeError::MultiplicationCheckFailed {
                prover: pred,
                stage: DzkStage::SumCheck,
            });
        }
        for k in 0..2 {
            let f = &in_x[3 + k * m..3 + (k + 1) * m];
            if row_product_sum(&w_pred, f, &g_at[k]) != h_y_at[k].add(in_x[1 + k]) {
                return Err(NodeError::MultiplicationCheckFailed {
                    prover: pred,
                    stage: DzkStage::PointCheck,
                });
            }
        }

        // Round 6: verdicts.
        for peer in peers {
            let verdict = mac32(
                self.pair_key(peer),
                TAG_VERDICT,
                &[
                    &sid,
                    &barrier.to_be_bytes(),
                    &seed_a,
                    &seed_b,
                    &[me as u8, peer as u8],
                ],
            );
            self.transport.send_frame(peer, ROUND_VERDICT, &verdict)?;
        }
        for peer in peers {
            let raw = recv_from(&mut self.transport, peer, ROUND_VERDICT)?;
            let tag: [u8; 32] =
                raw.as_slice()
                    .try_into()
                    .map_err(|_| NodeError::MalformedMessage {
                        from: peer,
                        round: ROUND_VERDICT,
                    })?;
            if !mac32_verify(
                self.pair_key(peer),
                TAG_VERDICT,
                &[
                    &sid,
                    &barrier.to_be_bytes(),
                    &seed_a,
                    &seed_b,
                    &[peer as u8, me as u8],
                ],
                &tag,
            ) {
                return Err(NodeError::MacInvalid { party: peer });
            }
        }

        self.record.wipe();
        self.barrier += 1;
        self.unverified = false;
        let latch = self.verified_latch.take().ok_or(NodeError::Poisoned)?;
        let (next_latch, check_res) = latch.record_check_result(true);
        self.verified_latch = Some(next_latch);
        check_res.map_err(|_| NodeError::Poisoned)?;
        Ok(())
    }

    /// Open the first `words` lanes of every state (4 lanes are a 32-byte digest). Refused
    /// while the party is poisoned or unverified gates exist. The missing share slot
    /// arrives from both of its holders and the two copies must agree.
    pub fn open_prefix(&mut self, words: usize) -> Result<Vec<Vec<u64>>, NodeError> {
        if self.journal_failed {
            return Err(NodeError::Journal);
        }
        if self.is_poisoned() {
            return Err(NodeError::Poisoned);
        }
        let latch = self.verified_latch.take().ok_or(NodeError::Poisoned)?;
        let (next_latch, permit_res) = latch.authorize_open();
        self.verified_latch = Some(next_latch);
        let permit = match permit_res {
            Ok(p) => p,
            Err(qsag_verified::PantsGuardError::RssOpenBeforeCheck) => {
                return Err(NodeError::OpenBeforeCheck);
            }
            Err(_) => return Err(NodeError::Poisoned),
        };
        if self.unverified {
            return Err(NodeError::OpenBeforeCheck);
        }
        if words == 0 || words > 25 {
            return Err(NodeError::InvalidParameters);
        }
        self.guarded(|party| party.open_inner(words, permit))
    }

    fn open_inner(
        &mut self,
        words: usize,
        _permit: qsag_verified::RssOpenPermit,
    ) -> Result<Vec<Vec<u64>>, NodeError> {
        let (succ, pred) = (self.succ(), self.pred());
        let mine: Vec<u64> = self
            .states
            .iter()
            .flat_map(|s| s.mine[..words].to_vec())
            .collect();
        let next: Vec<u64> = self
            .states
            .iter()
            .flat_map(|s| s.next[..words].to_vec())
            .collect();
        // The successor lacks this party's `mine` slot; the predecessor lacks its `next`.
        self.transport
            .send_frame(succ, ROUND_OPEN, &words_to_bytes(&mine))?;
        self.transport
            .send_frame(pred, ROUND_OPEN, &words_to_bytes(&next))?;
        let count = words * self.states.len();
        let from_pred = recv_from(&mut self.transport, pred, ROUND_OPEN)?;
        let from_succ = recv_from(&mut self.transport, succ, ROUND_OPEN)?;
        let third = bytes_to_words(&from_pred, count).ok_or(NodeError::MalformedMessage {
            from: pred,
            round: ROUND_OPEN,
        })?;
        if !ct_eq_bytes(&from_pred, &from_succ) {
            return Err(NodeError::OpenShareMismatch);
        }
        // The release decision is the extracted guard's: one decision per opening round,
        // bound to this session, round and opened shape, accepting only if both holders of
        // the missing slot committed to the same words.
        let round = self.open_round;
        self.open_round = round.checked_add(1).ok_or(NodeError::InvalidParameters)?;
        let binding = h32(
            TAG_OPEN_BINDING,
            &[
                &self.session_id,
                &round.to_be_bytes(),
                &self.barrier.to_be_bytes(),
                &(words as u64).to_be_bytes(),
                &(self.states.len() as u64).to_be_bytes(),
            ],
        );
        let copy_pred = h32(TAG_OPEN_COPY, &[&binding, &from_pred]);
        let copy_succ = h32(TAG_OPEN_COPY, &[&binding, &from_succ]);
        let (_spent, release) =
            qsag_verified::ConsumingOpeningGuard2Lane::new(self.session_id, round, binding, 1)
                .absorb_opening(&copy_pred, &copy_succ, [0, 0])
                .verify_once(&self.session_id, round, &binding);
        let release = release.ok_or(NodeError::OpenShareMismatch)?;
        Ok(reconstruct_opened(
            release,
            self.states.len(),
            words,
            &mine,
            &next,
            &third,
        ))
    }
}

impl Drop for GateRecord {
    fn drop(&mut self) {
        self.wipe();
    }
}
impl core::fmt::Debug for SharePair {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("SharePair([REDACTED])")
    }
}
impl Drop for SharePair {
    fn drop(&mut self) {
        qsag_asm::volatile_fill(&mut self.mine[..], 0);
        qsag_asm::volatile_fill(&mut self.next[..], 0);
        if let Some(ref mut sid) = self.session_id {
            qsag_asm::volatile_fill(&mut sid[..], 0);
        }
    }
}
impl core::fmt::Debug for Rss256PartyKeys {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("Rss256PartyKeys([REDACTED])")
    }
}
impl Drop for Rss256PartyKeys {
    fn drop(&mut self) {
        for key in self
            .slot_keys
            .iter_mut()
            .chain(&mut self.mac_keys)
            .chain(core::iter::once(&mut self.rng_seed))
        {
            qsag_asm::volatile_fill(&mut key[..], 0);
        }
    }
}

#[cfg(feature = "std")]
pub use crate::poison_journal::{FsDurablePoisonAndSessionJournal, JournalOpenMode};

#[cfg(test)]
mod tests {
    use super::*;
    use crate::quorum_jorts::{
        BftShamirJorts, QuorumConfig, StagedShamirKeys, quorum_jorts_verify, stage_bft_shamir,
        stage_committee_partitioned,
    };
    use crate::wire_channel::{FRAME_HEADER_BYTES, InMemoryEndpoint, InMemoryWireMesh, MeshStats};
    use qsag_core::belt_latch::{BeltLatchError, MemoryWal};
    use std::sync::Arc;

    const SEED: [u8; 32] = [0x21; 32];
    const SESSION: [u8; 32] = [0x99; 32];

    /// What a party thread hands back to be dropped only after every thread has been
    /// joined: its node or endpoint. A thread that returned early would otherwise close its
    /// links, and a peer's next send to it would fail before that peer reaches the check
    /// under test.
    type Keep<'a> = Box<dyn Send + 'a>;
    type PartyFn<'a, R> = Box<dyn FnOnce() -> (R, Keep<'a>) + Send + 'a>;

    /// Run one closure per party on its own OS thread and collect the results in order.
    fn run_parties<'a, R: Send>(parties: Vec<PartyFn<'a, R>>) -> Vec<R> {
        let finished: Vec<(R, Keep<'a>)> = std::thread::scope(|scope| {
            let handles: Vec<_> = parties.into_iter().map(|f| scope.spawn(f)).collect();
            handles
                .into_iter()
                .map(|h| h.join().expect("party thread"))
                .collect()
        });
        finished.into_iter().map(|(result, _keep)| result).collect()
    }

    type Tamper = Box<dyn FnMut(usize, u32, &mut Vec<u8>) + Send>;

    /// A transport whose owner rewrites its own outgoing payloads: the wire as a corrupted
    /// party controls it.
    struct TamperTransport {
        inner: InMemoryEndpoint,
        tamper: Tamper,
    }

    impl WireTransport for TamperTransport {
        fn party(&self) -> usize {
            self.inner.party()
        }

        fn parties(&self) -> usize {
            self.inner.parties()
        }

        fn send_frame(
            &mut self,
            to: usize,
            tag: u32,
            payload: &[u8],
        ) -> Result<(), TransportError> {
            let mut payload = payload.to_vec();
            (self.tamper)(to, tag, &mut payload);
            self.inner.send_frame(to, tag, &payload)
        }

        fn recv_frame(&mut self, from: usize, tag: u32) -> Result<Vec<u8>, TransportError> {
            self.inner.recv_frame(from, tag)
        }

        fn recv_authenticated_envelope(
            &mut self,
            from: usize,
            tag: u32,
        ) -> Result<Vec<u8>, TransportError> {
            self.inner.recv_authenticated_envelope(from, tag)
        }
    }

    fn honest(endpoint: InMemoryEndpoint) -> TamperTransport {
        TamperTransport {
            inner: endpoint,
            tamper: Box::new(|_, _, _| {}),
        }
    }

    fn reference_permutation(state: &[u64; 25]) -> [u64; 25] {
        let mut batch = [*state];
        qsag_asm::keccak_f1600_batch(&mut batch);
        batch[0]
    }

    #[test]
    fn linear_layer_and_chi_compose_to_keccak_f1600() {
        let mut state: [u64; 25] =
            core::array::from_fn(|i| 0x0123_4567_89AB_CDEF ^ ((i as u64) << 7));
        let want = reference_permutation(&state);
        for rc in KECCAK_ROUND_CONSTANTS {
            let b = keccak_linear(&state);
            for lane in 0..25 {
                let (l1, l2) = chi_operands(lane);
                state[lane] = b[lane] ^ b[l2] ^ (b[l1] & b[l2]);
            }
            state[0] ^= rc;
        }
        assert_eq!(state, want);
    }

    #[test]
    fn dealt_material_is_split_as_documented() {
        let keys = deal_rss256_keys(&SEED);
        for p in 0..3 {
            let q = (p + 1) % 3;
            // Slot key p + 1 is held by parties p and p + 1, and by nobody else.
            assert_eq!(keys[p].slot_keys[1], keys[q].slot_keys[0]);
            assert_ne!(keys[p].slot_keys[0], keys[q].slot_keys[1]);
            // The MAC key of the pair {p, p + 1}.
            assert_eq!(keys[p].mac_keys[0], keys[q].mac_keys[1]);
            assert_ne!(keys[p].rng_seed, keys[q].rng_seed);
        }
        let secret: [u64; 25] = core::array::from_fn(|i| i as u64 * 0x9E37_79B9_7F4A_7C15);
        let mut rng = SeedRng::new(&SEED, b"deal");
        let shares = deal_keccak_shares(&secret, &mut rng);
        for p in 0..3 {
            assert_eq!(shares[p].next, shares[(p + 1) % 3].mine);
            // Two parties' pairs cover all three slots; one pair does not determine the state.
            let rebuilt: [u64; 25] = core::array::from_fn(|i| {
                shares[p].mine[i] ^ shares[p].next[i] ^ shares[(p + 2) % 3].mine[i]
            });
            assert_eq!(rebuilt, secret);
            assert_ne!(
                core::array::from_fn::<u64, 25, _>(|i| shares[p].mine[i] ^ shares[p].next[i]),
                secret
            );
        }
    }

    #[test]
    fn session_mac_keys_agree_and_reject_cross_session_replay() {
        let provisioned = deal_rss256_keys(&SEED);
        let make = |sid| {
            let (endpoints, _) = InMemoryWireMesh::connect(3, sid);
            endpoints
                .into_iter()
                .zip(provisioned.clone())
                .map(|(endpoint, keys)| {
                    IsolatedRss256Party::new(
                        sid,
                        keys,
                        honest(endpoint),
                        MemoryPoisonJournal::new(),
                    )
                    .unwrap()
                })
                .collect::<Vec<_>>()
        };
        let first = make(SESSION);
        let second = make([0xFA; 32]);
        for p in 0..3 {
            let peer = (p + 1) % 3;
            assert_eq!(first[p].pair_key(peer), first[peer].pair_key(p));
            assert_ne!(first[p].pair_key(peer), second[p].pair_key(peer));
            let payload = b"round-two-echo";
            let tag = mac32(first[p].pair_key(peer), TAG_COIN_ECHO_MAC, &[payload]);
            assert!(mac32_verify(
                first[peer].pair_key(p),
                TAG_COIN_ECHO_MAC,
                &[payload],
                &tag
            ));
            assert!(!mac32_verify(
                second[peer].pair_key(p),
                TAG_COIN_ECHO_MAC,
                &[payload],
                &tag
            ));
        }
    }

    type RssParty = IsolatedRss256Party<TamperTransport, MemoryPoisonJournal>;
    /// Opened lanes of every state.
    type Opened = Vec<Vec<u64>>;

    /// Three parties of one session, each with its own keys, shares of `secrets`, journal
    /// and endpoint. `tamper` wraps the endpoint of party 2.
    fn rss_parties(secrets: &[[u64; 25]], tamper: Tamper) -> (Vec<RssParty>, Arc<MeshStats>) {
        let (endpoints, stats) = InMemoryWireMesh::connect(3, SESSION);
        let keys = deal_rss256_keys(&SEED);
        let mut rng = SeedRng::new(&SEED, b"shares");
        let mut per_party_shares: [Vec<SharePair>; 3] = [
            Vec::with_capacity(secrets.len()),
            Vec::with_capacity(secrets.len()),
            Vec::with_capacity(secrets.len()),
        ];
        for s in secrets {
            let [s0, s1, s2] = deal_keccak_shares_for_session(SESSION, s, &mut rng);
            per_party_shares[0].push(s0);
            per_party_shares[1].push(s1);
            per_party_shares[2].push(s2);
        }
        let mut tamper = Some(tamper);
        let parties = endpoints
            .into_iter()
            .zip(keys)
            .zip(per_party_shares)
            .map(|((endpoint, keys), party_shares)| {
                let p = keys.party;
                let transport = if p == 2 {
                    TamperTransport {
                        inner: endpoint,
                        tamper: tamper.take().expect("one tamper"),
                    }
                } else {
                    honest(endpoint)
                };
                let mut party =
                    IsolatedRss256Party::new(SESSION, keys, transport, MemoryPoisonJournal::new())
                        .unwrap();
                for share in party_shares {
                    party.load_shares(share).unwrap();
                }
                party
            })
            .collect();
        (parties, stats)
    }

    fn secrets(n: usize) -> Vec<[u64; 25]> {
        (0..n)
            .map(|s| core::array::from_fn(|i| ((s as u64 + 1) << 40) ^ (i as u64 * 0x1F3D_5B79)))
            .collect()
    }

    /// What one party thread reports after a run.
    struct RssOutcome {
        permute: Result<(), NodeError>,
        check: Result<(), NodeError>,
        recheck: Result<(), NodeError>,
        open: Result<Vec<Vec<u64>>, NodeError>,
        poisoned: bool,
    }

    /// The standard party program: one wave, the barrier, a second call of the barrier, and
    /// an opening of the whole state.
    fn rss_program(party: &mut RssParty) -> RssOutcome {
        let permute = party.permute();
        let check = party.check();
        let recheck = party.check();
        let open = party.open_prefix(25);
        RssOutcome {
            permute,
            check,
            recheck,
            open,
            poisoned: party.is_poisoned(),
        }
    }

    fn run_rss(parties: Vec<RssParty>) -> Vec<RssOutcome> {
        run_parties(
            parties
                .into_iter()
                .map(|mut party| {
                    Box::new(move || {
                        let outcome = rss_program(&mut party);
                        (outcome, Box::new(party) as Keep)
                    }) as PartyFn<RssOutcome>
                })
                .collect(),
        )
    }

    #[test]
    fn three_threads_evaluate_keccak_and_open_the_reference_output() {
        let secrets = secrets(2);
        let (parties, stats) = rss_parties(&secrets, Box::new(|_, _, _| {}));
        let outcomes: Vec<(Opened, Opened)> = run_parties(
            parties
                .into_iter()
                .map(|mut party| {
                    Box::new(move || {
                        party.permute().unwrap();
                        assert!(party.has_unverified_gates());
                        // Not poisoned, but nothing opens before the barrier.
                        assert_eq!(party.open_prefix(4), Err(NodeError::OpenBeforeCheck));
                        assert!(!party.is_poisoned());
                        party.check().unwrap();
                        assert_eq!(party.barriers(), 1);
                        let first = party.open_prefix(25).unwrap();
                        // A second wave on the same states and a second barrier.
                        party.permute().unwrap();
                        party.check().unwrap();
                        assert_eq!(party.barriers(), 2);
                        let second = party.open_prefix(4).unwrap();
                        // Each opening round took its own release decision.
                        assert_eq!(party.open_round, 2);
                        ((first, second), Box::new(party) as Keep)
                    }) as PartyFn<(Opened, Opened)>
                })
                .collect(),
        );
        let once: Vec<[u64; 25]> = secrets.iter().map(reference_permutation).collect();
        let twice: Vec<[u64; 25]> = once.iter().map(reference_permutation).collect();
        for (first, second) in &outcomes {
            let want_first: Vec<Vec<u64>> = once.iter().map(|s| s.to_vec()).collect();
            let want_second: Vec<Vec<u64>> = twice.iter().map(|s| s[..4].to_vec()).collect();
            assert_eq!(first, &want_first);
            assert_eq!(second, &want_second);
        }
        // Gate traffic: 24 rounds, 200 bytes per state, per party and wave.
        let gate_frames = stats.frames_sent_by(0, |tag| tag & 0xFF00_0000 == ROUND_GATE);
        assert_eq!(gate_frames, 48);
        let gate_bytes: usize = stats
            .frames()
            .iter()
            .filter(|f| f.from == 0 && f.round_tag & 0xFF00_0000 == ROUND_GATE)
            .map(|f| f.wire_bytes - FRAME_HEADER_BYTES)
            .sum();
        assert_eq!(gate_bytes, 2 * 24 * 2 * 200);
    }

    /// Thread 2 flips one byte of a gate message on the wire. Both honest threads reject
    /// its gates at the barrier, stay poisoned, and refuse to open, also after calling the
    /// barrier again.
    #[test]
    fn corrupted_gate_byte_poisons_both_honest_threads() {
        let secrets = secrets(1);
        let tamper: Tamper = Box::new(|_, tag, payload| {
            if tag == ROUND_GATE | 11 {
                payload[77] ^= 0x04;
            }
        });
        let (parties, stats) = rss_parties(&secrets, tamper);
        let outcomes = run_rss(parties);
        // Thread 1 received the flipped byte and is a verifier of thread 2's gates.
        assert_eq!(
            outcomes[1].check,
            Err(NodeError::MultiplicationCheckFailed {
                prover: 2,
                stage: DzkStage::SumCheck
            })
        );
        // Thread 0 checks thread 1's proof first. Thread 1 is honest and its node sum
        // matches, but the other verifier of that proof is thread 2, whose copy of the
        // share diverged from thread 1's at the flipped byte: the evaluations disagree.
        // The rejection names the proof that failed, not the party that deviated.
        assert_eq!(
            outcomes[0].check,
            Err(NodeError::MultiplicationCheckFailed {
                prover: 1,
                stage: DzkStage::PointCheck
            })
        );
        for (p, outcome) in outcomes.iter().enumerate().take(2) {
            assert_eq!(outcome.permute, Ok(()), "party {p}");
            assert!(outcome.poisoned);
            assert_eq!(outcome.recheck, Err(NodeError::Poisoned));
            assert_eq!(outcome.open, Err(NodeError::Poisoned));
            assert_eq!(stats.frames_sent_by(p, |tag| tag == ROUND_OPEN), 0);
        }
        // The corrupted thread learns nothing either: nobody opened to it.
        assert!(outcomes[2].open.is_err());
    }

    /// Thread 2 flips a gate bit and, once the weights are public, patches its proof so
    /// that the node sum matches. The evaluation points catch it.
    #[test]
    fn patched_proof_is_caught_at_the_evaluation_points() {
        let secrets = secrets(1);
        let (mut parties, stats) = rss_parties(&secrets, Box::new(|_, _, _| {}));
        parties[2].set_cheat(Cheat::FlipGate {
            round: 3,
            lane: 13,
            bit: 41,
            patch_proof: true,
        });
        let outcomes = run_rss(parties);
        for (p, outcome) in outcomes.iter().enumerate().take(2) {
            assert_eq!(
                outcome.check,
                Err(NodeError::MultiplicationCheckFailed {
                    prover: 2,
                    stage: DzkStage::PointCheck
                }),
                "party {p}"
            );
            assert!(outcome.poisoned);
            assert_eq!(outcome.recheck, Err(NodeError::Poisoned));
            assert_eq!(outcome.open, Err(NodeError::Poisoned));
            assert_eq!(stats.frames_sent_by(p, |tag| tag == ROUND_OPEN), 0);
        }
    }

    /// The same flipped bit without the patch fails the node sum (control for the test
    /// above: the patch is what moved the failure to the points).
    #[test]
    fn unpatched_gate_flip_fails_the_node_sum() {
        let secrets = secrets(1);
        let (mut parties, _) = rss_parties(&secrets, Box::new(|_, _, _| {}));
        parties[2].set_cheat(Cheat::FlipGate {
            round: 3,
            lane: 13,
            bit: 41,
            patch_proof: false,
        });
        let outcomes = run_rss(parties);
        for outcome in &outcomes[..2] {
            assert_eq!(
                outcome.check,
                Err(NodeError::MultiplicationCheckFailed {
                    prover: 2,
                    stage: DzkStage::SumCheck
                })
            );
        }
    }

    /// Thread 2 opens a coin share that is not the one it committed to.
    #[test]
    fn bad_coin_reveal_poisons_before_any_opening() {
        for round in [ROUND_COIN_REVEAL_A, ROUND_COIN_REVEAL_B] {
            let secrets = secrets(1);
            let tamper: Tamper = Box::new(move |_, tag, payload| {
                if tag == round {
                    payload[0] ^= 1;
                }
            });
            let (parties, stats) = rss_parties(&secrets, tamper);
            let outcomes = run_rss(parties);
            for (p, outcome) in outcomes.iter().enumerate().take(2) {
                assert_eq!(
                    outcome.check,
                    Err(NodeError::CoinOpeningRejected { party: 2 }),
                    "party {p}, round {round:#x}"
                );
                assert!(outcome.poisoned);
                assert_eq!(outcome.recheck, Err(NodeError::Poisoned));
                assert_eq!(outcome.open, Err(NodeError::Poisoned));
                assert_eq!(stats.frames_sent_by(p, |tag| tag == ROUND_OPEN), 0);
            }
        }
    }

    /// Thread 2 equivocates on the coin: it commits to one share towards thread 0 and to
    /// another towards thread 1, and opens each consistently. Every opening matches its
    /// commitment; the echo of the commitments is what differs between the honest threads.
    #[test]
    fn coin_equivocation_is_caught_by_the_commitment_echo() {
        let secrets = secrets(1);
        let other_coin = [0xC0u8; 32];
        let tamper: Tamper = Box::new(move |to, tag, payload| {
            if to != 0 {
                return;
            }
            if tag == ROUND_COIN_COMMIT {
                let forged = coin_commitment(&SESSION, 0, 2, 0, &other_coin);
                payload[..32].copy_from_slice(&forged);
            } else if tag == ROUND_COIN_REVEAL_A {
                payload[..32].copy_from_slice(&other_coin);
            }
        });
        let (parties, stats) = rss_parties(&secrets, tamper);
        let outcomes = run_rss(parties);
        assert_eq!(
            outcomes[0].check,
            Err(NodeError::CoinEchoMismatch { party: 1 })
        );
        assert_eq!(
            outcomes[1].check,
            Err(NodeError::CoinEchoMismatch { party: 0 })
        );
        for (p, outcome) in outcomes.iter().enumerate().take(2) {
            assert!(outcome.poisoned);
            assert_eq!(outcome.open, Err(NodeError::Poisoned));
            assert_eq!(stats.frames_sent_by(p, |tag| tag == ROUND_OPEN), 0);
            // Neither honest thread got as far as sending its proof share.
            assert_eq!(stats.frames_sent_by(p, |tag| tag == ROUND_PROOF_SHARE), 0);
        }
    }

    /// Thread 2 passes the barrier honestly and then sends thread 0 a wrong copy of the
    /// share slot it opens. Thread 0 compares it with thread 1's copy and refuses.
    #[test]
    fn mismatching_opened_share_is_refused() {
        let secrets = secrets(1);
        let tamper: Tamper = Box::new(|to, tag, payload| {
            if tag == ROUND_OPEN && to == 0 {
                payload[3] ^= 0x80;
            }
        });
        let (parties, _) = rss_parties(&secrets, tamper);
        let outcomes = run_rss(parties);
        assert_eq!(outcomes[0].check, Ok(()));
        assert_eq!(outcomes[0].open, Err(NodeError::OpenShareMismatch));
        assert!(outcomes[0].poisoned);
        // Thread 1 received honest copies and opens the right value.
        let want = reference_permutation(&secrets[0]);
        assert_eq!(outcomes[1].open, Ok(vec![want.to_vec()]));
    }

    #[test]
    fn failed_poison_write_is_sticky_and_reported() {
        let (mut endpoints, _) = InMemoryWireMesh::connect(3, SESSION);
        let mut journal = MemoryPoisonJournal::new();
        journal.fail_next_write();
        let mut party = IsolatedRss256Party::new(
            SESSION,
            deal_rss256_keys(&SEED)[0].clone(),
            endpoints.remove(0),
            journal,
        )
        .unwrap();
        let result: Result<(), NodeError> = party.guarded(|_| Err(NodeError::BadChallenge));
        assert_eq!(result, Err(NodeError::Journal));
        assert!(party.is_poisoned());
        assert_eq!(party.check(), Err(NodeError::Journal));
        assert_eq!(party.open_prefix(4), Err(NodeError::Journal));
    }

    #[test]
    fn shares_load_only_under_the_session_guard() {
        let pair = || SharePair {
            party: 0,
            session_id: Some(SESSION),
            mine: [7; 25],
            next: [9; 25],
        };
        let keys = deal_rss256_keys(&SEED);

        // A session the journal lists as poisoned takes no state.
        let (mut endpoints, _) = InMemoryWireMesh::connect(3, SESSION);
        let mut journal = MemoryPoisonJournal::new();
        journal.mark_poisoned(&SESSION).unwrap();
        let mut party =
            IsolatedRss256Party::new(SESSION, keys[0].clone(), endpoints.remove(0), journal)
                .unwrap();
        assert_eq!(party.load_shares(pair()), Err(NodeError::Poisoned));
        assert_eq!(party.state_count(), 0);

        // A clean session takes states in order, until a wave leaves gates unverified:
        // the next load is refused and poisons the session durably.
        let (mut endpoints, _) = InMemoryWireMesh::connect(3, SESSION);
        let mut party = IsolatedRss256Party::new(
            SESSION,
            keys[0].clone(),
            endpoints.remove(0),
            MemoryPoisonJournal::new(),
        )
        .unwrap();
        assert_eq!(party.load_shares(pair()), Ok(0));
        assert_eq!(party.load_shares(pair()), Ok(1));
        assert_eq!(party.state_count(), 2);
        assert!(!party.is_poisoned());
        party.unverified = true;
        assert_eq!(party.load_shares(pair()), Err(NodeError::OpenBeforeCheck));
        assert_eq!(party.state_count(), 2);
        assert!(party.is_poisoned());
        assert!(party.journal.is_poisoned(&SESSION));
        assert_eq!(party.permute(), Err(NodeError::Poisoned));

        // A journal that could not record the poison refuses loads as well.
        let (mut endpoints, _) = InMemoryWireMesh::connect(3, SESSION);
        let mut journal = MemoryPoisonJournal::new();
        journal.fail_next_write();
        let mut party =
            IsolatedRss256Party::new(SESSION, keys[0].clone(), endpoints.remove(0), journal)
                .unwrap();
        assert_eq!(
            party.guarded(|_| Err::<(), _>(NodeError::BadChallenge)),
            Err(NodeError::Journal)
        );
        assert_eq!(party.load_shares(pair()), Err(NodeError::Journal));
        assert_eq!(party.state_count(), 0);
    }

    #[test]
    fn share_debug_and_gate_wipe() {
        let share = SharePair {
            party: 0,
            session_id: Some(SESSION),
            mine: [123; 25],
            next: [456; 25],
        };
        assert_eq!(std::format!("{share:?}"), "SharePair([REDACTED])");
        let mut record = GateRecord::default();
        record.a_mine.resize(4, u64::MAX);
        record.wipe();
        assert!(record.a_mine.is_empty());
    }

    #[test]
    fn enroll_rss_key_block_and_share_pair_sealing() {
        let keys = deal_rss256_keys(&SEED);
        // Party mismatch or session mismatch on `load_shares` rejects and poisons.
        let (mut endpoints, _) = InMemoryWireMesh::connect(3, SESSION);
        let mut p0 = IsolatedRss256Party::new(
            SESSION,
            keys[0].clone(),
            endpoints.remove(0),
            MemoryPoisonJournal::new(),
        )
        .unwrap();
        let mut rng = SeedRng::new(&SEED, b"seal");
        let [_s0, s1, _s2] = deal_keccak_shares_for_session(SESSION, &[1u64; 25], &mut rng);
        assert_eq!(p0.load_shares(s1), Err(NodeError::InvalidParameters));
        assert!(p0.is_poisoned());

        let (mut endpoints2, _) = InMemoryWireMesh::connect(3, SESSION);
        let mut p0_sid = IsolatedRss256Party::new(
            SESSION,
            keys[0].clone(),
            endpoints2.remove(0),
            MemoryPoisonJournal::new(),
        )
        .unwrap();
        let [wrong_sid_s0, _, _] =
            deal_keccak_shares_for_session([0xEE; 32], &[1u64; 25], &mut rng);
        assert_eq!(
            p0_sid.load_shares(wrong_sid_s0),
            Err(NodeError::InvalidParameters)
        );
        assert!(p0_sid.is_poisoned());

        // Production `enroll_rss_key_block` enrolls scheme-bound `RssKeyShare256` states
        // without touching `SharePair` or `load_shares`, runs `permute` + `check` + `open_prefix`,
        // and matches single-prover `Keccak-f[1600]` bit-for-bit.
        let scheme_id = [0x42; 32];
        let sk_slots = [[0x11u8; 32], [0x22u8; 32], [0x33u8; 32]];
        let prf_slots = [[0x44u8; 32], [0x55u8; 32], [0x66u8; 32]];
        let prg_slots = [[0x77u8; 32], [0x88u8; 32], [0x99u8; 32]];
        let mut sk_clear = [0u8; 32];
        for i in 0..32 {
            sk_clear[i] = sk_slots[0][i] ^ sk_slots[1][i] ^ sk_slots[2][i];
        }
        let template: [u64; 25] = core::array::from_fn(|i| (i as u64 + 1) * 0x0102_0304_0506_0708);
        let mut expected_state = template;
        for w in 0..4 {
            let mut b8 = [0u8; 8];
            b8.copy_from_slice(&sk_clear[8 * w..8 * w + 8]);
            expected_state[2 + w] ^= u64::from_le_bytes(b8);
        }
        qsag_asm::keccak_f1600_batch(core::slice::from_mut(&mut expected_state));

        let (endpoints3, _) = InMemoryWireMesh::connect(3, SESSION);
        let nodes: Vec<_> = endpoints3
            .into_iter()
            .zip(keys)
            .map(|(ep, k)| {
                let p = k.party;
                let mut rss_share = RssKeyShare256::from_replicated_shares(
                    p,
                    32,
                    [0xAB; 32],
                    (sk_slots[p], sk_slots[(p + 1) % 3]),
                    (prf_slots[p], prf_slots[(p + 1) % 3]),
                    (prg_slots[p], prg_slots[(p + 1) % 3]),
                )
                .unwrap();
                rss_share.bind_scheme_identity(&scheme_id).unwrap();
                let mut node =
                    IsolatedRss256Party::new(SESSION, k, honest(ep), MemoryPoisonJournal::new())
                        .unwrap();
                assert_eq!(
                    node.enroll_rss_key_block(&rss_share, &scheme_id, false, &template, 16),
                    Ok(0)
                );
                node
            })
            .collect();

        std::thread::scope(|scope| {
            let handles: Vec<_> = nodes
                .into_iter()
                .map(|mut node| {
                    scope.spawn(move || {
                        node.permute().unwrap();
                        node.check().unwrap();
                        node.open_prefix(4).unwrap()
                    })
                })
                .collect();
            for h in handles {
                let opened = h.join().unwrap();
                assert_eq!(opened[0][..], expected_state[..4]);
            }
        });
    }

    #[test]
    fn poison_survives_a_restart_with_the_same_journal() {
        let (mut endpoints, _) = InMemoryWireMesh::connect(3, SESSION);
        let keys = deal_rss256_keys(&SEED);
        let mut journal = MemoryPoisonJournal::new();
        journal.mark_poisoned(&SESSION).unwrap();
        let mut party =
            IsolatedRss256Party::new(SESSION, keys[0].clone(), endpoints.remove(0), journal)
                .unwrap();
        assert!(party.is_poisoned());
        assert_eq!(party.permute(), Err(NodeError::Poisoned));
        assert_eq!(party.check(), Err(NodeError::Poisoned));
        assert_eq!(party.open_prefix(4), Err(NodeError::Poisoned));
        // Another session with the same journal is clean; wrong wiring is refused.
        let (mut endpoints, _) = InMemoryWireMesh::connect(3, [1; 32]);
        let mut journal = MemoryPoisonJournal::new();
        journal.mark_poisoned(&SESSION).unwrap();
        let party =
            IsolatedRss256Party::new([1; 32], keys[1].clone(), endpoints.remove(1), journal)
                .unwrap();
        assert!(!party.is_poisoned());
        assert!(
            IsolatedRss256Party::new(
                [1; 32],
                keys[2].clone(),
                endpoints.remove(0),
                MemoryPoisonJournal::new()
            )
            .is_err()
        );
    }

    // ---- Mode QS-A over threads ------------------------------------------------------------

    type JortsNode = IsolatedJortsParty<InMemoryEndpoint, MemoryWal>;

    /// Nodes for the members of committee `members` of a staged `(3, 5)` key, on a
    /// five-party mesh.
    fn jorts_nodes(members: &[usize]) -> (Vec<JortsNode>, usize, Arc<MeshStats>) {
        let staged = stage_committee_partitioned(3, 5, 6, &SEED).unwrap();
        let committee = staged.layout.committee_index(members).unwrap();
        let (endpoints, stats) = InMemoryWireMesh::connect(5, SESSION);
        let mut nodes = Vec::new();
        for (endpoint, material) in endpoints.into_iter().zip(staged.parties) {
            if !members.contains(&material.party) {
                continue;
            }
            let wals = vec![MemoryWal::new(); material.stores.len()];
            let custodian =
                CommitteeCustodian::new(staged.layout.clone(), staged.tree.clone(), material, wals)
                    .unwrap();
            nodes.push(IsolatedJortsParty::new(custodian, endpoint).unwrap());
        }
        (nodes, committee, stats)
    }

    #[test]
    fn three_threads_sign_as_a_committee() {
        let members = [0usize, 2, 4];
        let (nodes, committee, stats) = jorts_nodes(&members);
        let pk = *nodes[0].custodian().tree().public_key();
        let results = run_parties(
            nodes
                .into_iter()
                .map(|mut node| {
                    Box::new(move || {
                        let result = node.sign(committee, 0, b"threaded");
                        (result, Box::new(node) as Keep)
                    }) as PartyFn<Result<QuorumJortsSig, NodeError>>
                })
                .collect(),
        );
        let sig = results[0].clone().unwrap();
        assert!(quorum_jorts_verify(&pk, b"threaded", &sig));
        assert!(results.iter().all(|r| r.as_ref() == Ok(&sig)));
        // One echo and one opening per ordered pair of members.
        assert_eq!(stats.total_frames(), 12);
        assert_eq!(
            stats.total_bytes() as usize,
            6 * (FRAME_HEADER_BYTES + ECHO_WIRE_BYTES)
                + 6 * (FRAME_HEADER_BYTES + SHARE_OPENING_WIRE_BYTES)
        );
    }

    #[test]
    fn committee_signing_composes_with_encrypted_tcp() {
        use crate::wire_channel::{ConfidentialWireChannel, TcpWireMesh};
        let staged = stage_committee_partitioned(2, 2, 2, &SEED).unwrap();
        let pk = *staged.tree.public_key();
        let (endpoints, _) = TcpWireMesh::loopback(2, SESSION).unwrap();
        let nodes: Vec<_> = endpoints
            .into_iter()
            .zip(staged.parties)
            .map(|(endpoint, material)| {
                let wals = vec![MemoryWal::new(); material.stores.len()];
                let custodian = CommitteeCustodian::new(
                    staged.layout.clone(),
                    staged.tree.clone(),
                    material,
                    wals,
                )
                .unwrap();
                let wire = ConfidentialWireChannel::new(
                    endpoint,
                    [0xDA; 32],
                    SESSION,
                    vec![[0xA7; 32]; 2],
                )
                .unwrap();
                IsolatedJortsParty::new(custodian, wire).unwrap()
            })
            .collect();
        let signatures = std::thread::scope(|scope| {
            let handles: Vec<_> = nodes
                .into_iter()
                .map(|mut node| scope.spawn(move || node.sign(0, 0, b"encrypted custody")))
                .collect();
            handles
                .into_iter()
                .map(|h| h.join().unwrap().unwrap())
                .collect::<Vec<_>>()
        });
        assert_eq!(signatures[0], signatures[1]);
        assert!(quorum_jorts_verify(
            &pk,
            b"encrypted custody",
            &signatures[0]
        ));
    }

    /// Custodians enrolled in one deployment sign over the links `new_deployed` derives.
    /// A custodian enrolled elsewhere shares no wire key with its peer, a bound custodian
    /// refuses a second deployment, and re-deriving for the same one changes nothing.
    #[test]
    fn deployed_committee_signing_is_bound_to_the_enrolled_deployment() {
        use crate::wire_channel::TcpWireMesh;
        use core::time::Duration;
        let custodians = || {
            let staged = stage_committee_partitioned(2, 2, 2, &SEED).unwrap();
            let pk = *staged.tree.public_key();
            let custodians: Vec<_> = staged
                .parties
                .into_iter()
                .map(|material| {
                    let wals = vec![MemoryWal::new(); material.stores.len()];
                    CommitteeCustodian::new(
                        staged.layout.clone(),
                        staged.tree.clone(),
                        material,
                        wals,
                    )
                    .unwrap()
                })
                .collect();
            (pk, custodians)
        };
        let sign = |deployments: [Node; 2]| {
            let (pk, custodians) = custodians();
            let (endpoints, _) = TcpWireMesh::with_timeout(Duration::from_secs(5))
                .loopback(2, SESSION)
                .unwrap();
            let nodes: Vec<_> = endpoints
                .into_iter()
                .zip(custodians)
                .zip(deployments)
                .map(|((endpoint, custodian), deployment)| {
                    IsolatedJortsParty::new_deployed(deployment, SESSION, custodian, endpoint)
                        .unwrap()
                })
                .collect();
            let results = std::thread::scope(|scope| {
                let handles: Vec<_> = nodes
                    .into_iter()
                    .map(|mut node| scope.spawn(move || node.sign(0, 0, b"deployed custody")))
                    .collect();
                handles
                    .into_iter()
                    .map(|h| h.join().unwrap())
                    .collect::<Vec<_>>()
            });
            (pk, results)
        };

        let (pk, same) = sign([[0xDA; 32]; 2]);
        let signature = same[0].clone().unwrap();
        assert_eq!(same[1].as_ref(), Ok(&signature));
        assert!(quorum_jorts_verify(&pk, b"deployed custody", &signature));

        let (_, split) = sign([[0xDA; 32], [0xDB; 32]]);
        assert!(split.iter().all(Result::is_err), "{split:?}");

        let (_, mut custodians) = custodians();
        let custodian = &mut custodians[0];
        let bound = custodian.deployed_wire_keys([0xDA; 32]).unwrap();
        assert_eq!(custodian.deployed_wire_keys([0xDA; 32]).unwrap(), bound);
        assert!(custodian.deployed_wire_keys([0xDB; 32]).is_err());
        assert_eq!(custodian.deployed_wire_keys([0xDA; 32]).unwrap(), bound);
    }

    /// Split view: corrupted thread 2 has thread 0 sign `M1` and thread 1 sign `M2` at the
    /// same epoch, and sends each of them a correctly authenticated echo of what that
    /// thread expects. The honest threads compare echoes with each other and stop before
    /// any share is sent.
    #[test]
    fn split_view_echoes_are_caught_before_any_share_leaves() {
        let members = [0usize, 1, 2];
        let (mut nodes, committee, stats) = jorts_nodes(&members);
        let corrupt = nodes.pop().unwrap();
        let (_, mut wire) = corrupt.into_parts();
        // The corrupted custodian's material, twice: nothing stops it from binding both.
        let rogue = |msg: &[u8]| {
            let mut staged = stage_committee_partitioned(3, 5, 6, &SEED).unwrap();
            let material = staged.parties.remove(2);
            let wals = vec![MemoryWal::new(); material.stores.len()];
            let mut custodian =
                CommitteeCustodian::new(staged.layout.clone(), staged.tree.clone(), material, wals)
                    .unwrap();
            custodian.bind(committee, 0, msg).unwrap();
            custodian
        };
        let (rogue1, rogue2) = (rogue(b"M1"), rogue(b"M2"));
        let mut node1 = nodes.pop().unwrap();
        let mut node0 = nodes.pop().unwrap();
        let results = run_parties(vec![
            Box::new(move || {
                let result = node0.sign(committee, 0, b"M1").map(|_| Vec::new());
                (result, Box::new(node0) as Keep)
            }) as PartyFn<Result<Vec<u8>, NodeError>>,
            Box::new(move || {
                let result = node1.sign(committee, 0, b"M2").map(|_| Vec::new());
                (result, Box::new(node1) as Keep)
            }),
            Box::new(move || {
                let echo0 = rogue1.echo_for(committee, 0).unwrap();
                let echo1 = rogue2.echo_for(committee, 1).unwrap();
                wire.send_frame(0, ROUND_ECHO, &encode_echo(&echo0))
                    .unwrap();
                wire.send_frame(1, ROUND_ECHO, &encode_echo(&echo1))
                    .unwrap();
                // Collect whatever the honest threads send after their echoes.
                let mut harvested = Vec::new();
                for peer in [0usize, 1] {
                    wire.recv_frame(peer, ROUND_ECHO).unwrap();
                    if let Ok(share) = wire.recv_frame(peer, ROUND_SHARE) {
                        harvested.extend(share);
                    }
                }
                (Ok(harvested), Box::new(wire) as Keep)
            }),
        ]);
        assert_eq!(
            results[0],
            Err(NodeError::Quorum(QuorumError::SplitView { party: 1 }))
        );
        assert_eq!(
            results[1],
            Err(NodeError::Quorum(QuorumError::SplitView { party: 0 }))
        );
        assert_eq!(results[2], Ok(Vec::new()), "no share reached thread 2");
        for p in [0usize, 1] {
            assert_eq!(stats.frames_sent_by(p, |tag| tag == ROUND_SHARE), 0);
            assert_eq!(stats.frames_sent_by(p, |tag| tag == ROUND_ECHO), 2);
        }
    }

    /// A spoofed echo: thread 2 tells thread 0 that it bound thread 0's record, without a
    /// valid MAC (it replays the tag it made for thread 1).
    #[test]
    fn echo_with_a_wrong_mac_is_rejected_before_any_share_leaves() {
        let members = [0usize, 1, 2];
        let (mut nodes, committee, stats) = jorts_nodes(&members);
        let (mut rogue, mut wire) = nodes.pop().unwrap().into_parts();
        rogue.bind(committee, 0, b"M").unwrap();
        let mut node1 = nodes.pop().unwrap();
        let mut node0 = nodes.pop().unwrap();
        let results = run_parties(vec![
            Box::new(move || {
                let result = node0.sign(committee, 0, b"M").map(|_| ());
                (result, Box::new(node0) as Keep)
            }) as PartyFn<Result<(), NodeError>>,
            Box::new(move || {
                let result = node1.sign(committee, 0, b"M").map(|_| ());
                (result, Box::new(node1) as Keep)
            }),
            Box::new(move || {
                let for_1 = rogue.echo_for(committee, 1).unwrap();
                wire.send_frame(0, ROUND_ECHO, &encode_echo(&for_1))
                    .unwrap();
                wire.send_frame(1, ROUND_ECHO, &encode_echo(&for_1))
                    .unwrap();
                (Ok(()), Box::new(wire) as Keep)
            }),
        ]);
        assert_eq!(
            results[0],
            Err(NodeError::Quorum(QuorumError::EchoMacInvalid { party: 2 }))
        );
        assert_eq!(stats.frames_sent_by(0, |tag| tag == ROUND_SHARE), 0);
        // Thread 1 got a valid echo from everyone and opened its share; thread 0's abort
        // then stops it. One additive share of three reveals nothing.
        assert_eq!(results[1], Err(NodeError::PeerAborted { party: 0 }));
        assert_eq!(stats.frames_sent_by(1, |tag| tag == ROUND_SHARE), 2);
    }

    // ---- Mode QS-B over threads ------------------------------------------------------------

    type QuorumNode = IsolatedQuorumParty<TamperTransport, MemoryWal>;

    fn staged_3_of_7() -> StagedShamirKeys {
        stage_bft_shamir(QuorumConfig::new(3, 7, 2).unwrap(), 3, &SEED).unwrap()
    }

    /// Nodes for `online` custodians of a `(3, 7, f = 2)` key on a fresh seven-party mesh.
    /// `custodians` supplies the custodian of each party (so latch state can carry over);
    /// `tamper_of` may wrap a party's endpoint.
    fn quorum_nodes(
        session: [u8; 32],
        custodians: Vec<ShamirCustodian<MemoryWal>>,
        mut tamper_of: impl FnMut(usize) -> Option<Tamper>,
    ) -> (Vec<QuorumNode>, Arc<MeshStats>) {
        let (endpoints, stats) = InMemoryWireMesh::connect(7, session);
        let mut endpoints: Vec<Option<InMemoryEndpoint>> =
            endpoints.into_iter().map(Some).collect();
        let nodes = custodians
            .into_iter()
            .map(|custodian| {
                let p = custodian.party();
                let inner = endpoints[p].take().expect("one custodian per party");
                let transport = match tamper_of(p) {
                    Some(tamper) => TamperTransport { inner, tamper },
                    None => honest(inner),
                };
                IsolatedQuorumParty::new(custodian, transport).unwrap()
            })
            .collect();
        (nodes, stats)
    }

    fn custodians_of(
        staged: &StagedShamirKeys,
        parties: &[usize],
    ) -> Vec<ShamirCustodian<MemoryWal>> {
        parties
            .iter()
            .map(|&p| {
                ShamirCustodian::new(
                    staged.cfg,
                    staged.tree.clone(),
                    staged.parties[p].duplicate_for_test(),
                    MemoryWal::new(),
                )
                .unwrap()
            })
            .collect()
    }

    fn run_quorum(
        nodes: Vec<QuorumNode>,
        online: &[usize],
        openers: &[usize],
        leaf: u64,
        msg: &[u8],
    ) -> Vec<(
        Result<QuorumSignOutcome, NodeError>,
        ShamirCustodian<MemoryWal>,
    )> {
        run_parties(
            nodes
                .into_iter()
                .map(|mut node| {
                    Box::new(move || {
                        let result = node.sign(online, openers, leaf, msg);
                        let (custodian, transport) = node.into_parts();
                        ((result, custodian), Box::new(transport) as Keep)
                    }) as PartyFn<(Result<QuorumSignOutcome, NodeError>, _)>
                })
                .collect(),
        )
    }

    #[test]
    fn five_threads_certify_and_three_open() {
        let staged = staged_3_of_7();
        let pk = *staged.tree.public_key();
        let online = [0usize, 1, 3, 4, 6];
        let (nodes, stats) = quorum_nodes(SESSION, custodians_of(&staged, &online), |_| None);
        let results = run_quorum(nodes, &online, &[1, 4, 6], 0, b"five threads");
        for (result, _) in &results {
            let outcome = result.as_ref().unwrap();
            assert!(quorum_jorts_verify(
                &pk,
                b"five threads",
                &outcome.signature
            ));
            assert_eq!(outcome.certified_by, 5);
            assert!(outcome.blamed.is_empty());
        }
        // 5 * 4 acknowledgements (8 + 32 + 7 * 32 bytes) and 3 * 4 openings.
        assert_eq!(stats.total_frames(), 32);
        assert_eq!(
            stats.total_bytes() as usize,
            20 * (FRAME_HEADER_BYTES + 264) + 12 * (FRAME_HEADER_BYTES + SHARE_OPENING_WIRE_BYTES)
        );
    }

    /// Thread 4 flips bytes of its Shamir opening on the wire. With three openers the
    /// chain check fails at every honest thread; with a fourth opener the honest threads
    /// still sign and name thread 4.
    #[test]
    fn flipped_shamir_share_on_the_wire_is_caught_and_attributed() {
        let staged = staged_3_of_7();
        let pk = *staged.tree.public_key();
        let online = [0usize, 1, 2, 3, 4];
        let flip = |p: usize| -> Option<Tamper> {
            (p == 4).then(|| {
                Box::new(|_: usize, tag: u32, payload: &mut Vec<u8>| {
                    if tag == ROUND_SHAMIR_SHARE {
                        for byte in &mut payload[8..] {
                            *byte ^= 0x5A;
                        }
                    }
                }) as Tamper
            })
        };
        let (nodes, _) = quorum_nodes(SESSION, custodians_of(&staged, &online), flip);
        let results = run_quorum(nodes, &online, &[1, 2, 4], 0, b"msg");
        for (result, custodian) in &results {
            if custodian.party() == 4 {
                continue;
            }
            assert!(
                matches!(
                    result,
                    Err(NodeError::Quorum(QuorumError::ChainVerifyFailed { .. }))
                ),
                "party {}: {result:?}",
                custodian.party()
            );
        }
        // Retry of the same record with one more opener: the latches replay.
        let custodians: Vec<_> = results.into_iter().map(|(_, c)| c).collect();
        let (nodes, _) = quorum_nodes([0x9A; 32], custodians, flip);
        let results = run_quorum(nodes, &online, &[1, 2, 3, 4], 0, b"msg");
        for (result, custodian) in &results {
            if custodian.party() == 4 {
                continue;
            }
            let outcome = result.as_ref().unwrap();
            assert!(quorum_jorts_verify(&pk, b"msg", &outcome.signature));
            assert_eq!(outcome.blamed, vec![4]);
        }
    }

    /// Quorum switching over the wire, `(3, 7, f = 2)`: custodians 5 and 6 are corrupted.
    /// After `M1` is signed at leaf 0 with {0, 1, 2, 5, 6}, they run a second session for
    /// `M2` at leaf 0 with the custodians that were not asked, {3, 4}, using fresh state of
    /// their own. Four acknowledgements arrive; the honest threads do not open.
    #[test]
    fn quorum_switch_over_the_wire_yields_no_second_signature() {
        let staged = staged_3_of_7();
        let pk = *staged.tree.public_key();
        let first = [0usize, 1, 2, 5, 6];
        let (nodes, _) = quorum_nodes(SESSION, custodians_of(&staged, &first), |_| None);
        let results = run_quorum(nodes, &first, &[0, 1, 2], 0, b"M1");
        let sig1 = results[0].0.as_ref().unwrap().signature.clone();
        assert!(quorum_jorts_verify(&pk, b"M1", &sig1));

        // Session two. Custodians 5 and 6 come back with empty logs.
        let second = [3usize, 4, 5, 6];
        let (nodes, stats) = quorum_nodes([0x9B; 32], custodians_of(&staged, &second), |_| None);
        let results = run_quorum(nodes, &second, &[3, 5, 6], 0, b"M2");
        for (result, custodian) in &results {
            assert_eq!(
                result.as_ref().unwrap_err(),
                &NodeError::Quorum(QuorumError::CertificateTooSmall {
                    valid: 4,
                    required: 5
                }),
                "party {}",
                custodian.party()
            );
        }
        for p in [3usize, 4] {
            assert_eq!(stats.frames_sent_by(p, |tag| tag == ROUND_SHAMIR_SHARE), 0);
        }
        // The custodians of the first session refuse to join the second one.
        let mut reference = BftShamirJorts::stage(staged.cfg, 3, &SEED).unwrap();
        reference.sign_at(&first, &[0, 1, 2], 0, b"M1").unwrap();
        assert_eq!(
            reference.custodians[0].ack(0, b"M2").unwrap_err(),
            QuorumError::Latch(BeltLatchError::EpochAlreadyBound)
        );
    }
}

/// One party's single-use MSP input at a certified Cut-the-Hash boundary.
/// Rows stay secret and wipe on every success/error path. The caller must enroll
/// this matrix and bind the active committee into the ceremony's message record.
/// This adapter changes only the input sharing, never any MPC gate or MAC check.
pub struct PersonalMspInput {
    party: u16,
    program: crate::access::MonotoneSpanProgram,
    rows: SecretBuffer<Vec<[qsag_core::field::goldilocks::Goldilocks; 4]>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PersonalMspInputError {
    Policy(crate::access::QuorumPolicyError),
    Access(crate::access::AccessError),
}
impl PersonalMspInput {
    pub fn new(
        party: u16,
        program: crate::access::MonotoneSpanProgram,
        rows: SecretBuffer<Vec<[qsag_core::field::goldilocks::Goldilocks; 4]>>,
    ) -> Result<Self, PersonalMspInputError> {
        if rows.len() != program.row_owners().iter().filter(|&&p| p == party).count() {
            return Err(PersonalMspInputError::Access(
                crate::access::AccessError::InvalidShares,
            ));
        }
        Ok(Self {
            party,
            program,
            rows,
        })
    }

    pub fn party(&self) -> u16 {
        self.party
    }

    pub fn program(&self) -> &crate::access::MonotoneSpanProgram {
        &self.program
    }

    /// Collapse under an already issued permit for this party. The weights are those of
    /// the permit's signer set, so every releasing party must hold a permit for the SAME
    /// set: lanes collapsed for different sets do not sum to the secret.
    pub fn release_with_permit(
        self,
        permit: &crate::access::PersonalReleasePermit,
    ) -> Result<SecretBuffer<[qsag_core::field::goldilocks::Goldilocks; 4]>, PersonalMspInputError>
    {
        if permit.party() != self.party || !permit.signers().contains(&self.party) {
            return Err(PersonalMspInputError::Access(
                crate::access::AccessError::Unauthorized,
            ));
        }
        let weights = self
            .program
            .solve_reconstruction_weights(permit.signers())
            .ok_or(PersonalMspInputError::Access(
                crate::access::AccessError::Unauthorized,
            ))?;
        self.program
            .collapse_to_additive_share(self.party, &weights, &self.rows)
            .map_err(PersonalMspInputError::Access)
    }

    /// [`Self::release`] for a ceremony whose signer set was fixed in advance. The
    /// certificate must be signed by exactly `expected_signers`; a certificate that is
    /// valid for the policy but names any other set is refused before anything is
    /// collapsed, because its weights would belong to a different reconstruction.
    pub fn release_for_signers<W: DurableWal>(
        self,
        latch: &mut crate::access::PersonalBeltLatch<W>,
        record: &qsag_core::belt_latch::BeltLatchRecord,
        certificate: &crate::access::PersonalLatchCertificate,
        expected_signers: &crate::access::PartySet,
    ) -> Result<SecretBuffer<[qsag_core::field::goldilocks::Goldilocks; 4]>, PersonalMspInputError>
    {
        let permit = latch
            .authorize(record, certificate)
            .map_err(PersonalMspInputError::Policy)?;
        if permit.signers() != expected_signers {
            return Err(PersonalMspInputError::Access(
                crate::access::AccessError::Unauthorized,
            ));
        }
        self.release_with_permit(&permit)
    }

    /// Consume one input only after the personal BeltLatch authorizes the exact
    /// record. The returned four additive field lanes feed Cut-the-Hash inputs.
    ///
    /// The collapse uses the signer set of THIS party's certificate. Certificates are
    /// receiver-specific, so two parties can hold valid certificates for different
    /// sets; their lanes then do not sum to the secret. Use
    /// [`Self::release_for_signers`] whenever more than one party releases.
    pub fn release<W: DurableWal>(
        self,
        latch: &mut crate::access::PersonalBeltLatch<W>,
        record: &qsag_core::belt_latch::BeltLatchRecord,
        certificate: &crate::access::PersonalLatchCertificate,
    ) -> Result<SecretBuffer<[qsag_core::field::goldilocks::Goldilocks; 4]>, PersonalMspInputError>
    {
        let permit = latch
            .authorize(record, certificate)
            .map_err(PersonalMspInputError::Policy)?;
        self.release_with_permit(&permit)
    }
}
