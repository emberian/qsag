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
//!   ([`deal_rss256_keys`], [`deal_keccak_shares`]); this module has no key agreement.
//! * The engine evaluates plain `Keccak-f[1600]` states one 64-bit word per lane. It is not
//!   bitsliced across signatures and is not a replacement for the 256-lane engine of
//!   `qsag_core::rss256`; it exists to run the protocol with separated parties.
//! * Security is with abort: a corrupted party can stop a session and can learn an opened
//!   output while an honest party aborts.

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use qsag_asm::{KECCAK_ROTATION_OFFSETS, KECCAK_ROUND_CONSTANTS};
use qsag_core::belt_latch::DurableWal;
use qsag_core::rss256::Shake256Prg256;

use crate::dzk::{
    DzkShape, Gf128, NodeBasis, challenge_points, data_node_sum, decode_elements, derive_weights,
    dot, encode_elements, expand_elements, prove, row_product_sum, weighted_sum, x_evals, y_evals,
};
use crate::hash::{SeedRng, h32, mac32, mac32_verify};
use crate::quorum_jorts::{
    CommitteeCustodian, LatchAck, LatchCertificate, LatchEcho, Node, QuorumError, QuorumJortsSig,
    SHARE_OPENING_WIRE_BYTES, ShamirCustodian, ShareOpening, WOTS_CHAINS, combine_additive,
    combine_shamir_robust,
};
use crate::wire_channel::{TransportError, WireTransport};

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
    /// An opening was requested while unverified gates exist.
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

#[derive(PartialEq, Eq)]
struct SecretBytes(Vec<u8>);
impl SecretBytes { fn as_slice(&self) -> &[u8] { &self.0 } }
impl core::ops::Deref for SecretBytes {
    type Target = [u8];
    fn deref(&self) -> &[u8] { &self.0 }
}
impl Drop for SecretBytes {
    fn drop(&mut self) { qsag_asm::volatile_fill(&mut self.0, 0); }
}

fn recv_from<T: WireTransport>(
    transport: &mut T,
    from: usize,
    round: u32,
) -> Result<SecretBytes, NodeError> {
    match transport.recv_frame(from, round) {
        Ok(payload) => Ok(SecretBytes(payload)),
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

fn encode_opening(opening: &ShareOpening) -> SecretBytes {
    let mut out = Vec::with_capacity(SHARE_OPENING_WIRE_BYTES);
    out.extend_from_slice(&opening.leaf.to_be_bytes());
    out.extend_from_slice(opening.shares.as_flattened());
    SecretBytes(out)
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

impl<T: WireTransport, W: DurableWal> IsolatedJortsParty<T, W> {
    pub fn new(custodian: CommitteeCustodian<W>, transport: T) -> Result<Self, NodeError> {
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
        Ok(combine_additive(
            self.custodian.tree(),
            &record,
            members,
            &openings,
        )?)
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

impl<T: WireTransport, W: DurableWal> IsolatedQuorumParty<T, W> {
    pub fn new(custodian: ShamirCustodian<W>, transport: T) -> Result<Self, NodeError> {
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

/// Durable record of poisoned sessions.
pub trait PoisonJournal {
    /// Record that `session_id` is poisoned; return only once it would survive a restart.
    fn mark_poisoned(&mut self, session_id: &[u8; 32]) -> Result<(), NodeError>;

    fn is_poisoned(&self, session_id: &[u8; 32]) -> bool;
}

/// Volatile [`PoisonJournal`] for tests and for hosts that persist one level up.
#[derive(Clone, Debug, Default)]
pub struct MemoryPoisonJournal {
    sessions: Vec<[u8; 32]>,
    fail_next: bool,
}

impl MemoryPoisonJournal {
    pub fn new() -> Self {
        Self::default()
    }

    /// Make the next write fail.
    pub fn fail_next_write(&mut self) {
        self.fail_next = true;
    }
}

impl PoisonJournal for MemoryPoisonJournal {
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

/// One party's replicated share of a `Keccak-f[1600]` state: share slot `party` and share
/// slot `party + 1`. The state is the xor of the three slots.
#[derive(Clone, PartialEq, Eq)]
pub struct SharePair {
    pub mine: [u64; 25],
    pub next: [u64; 25],
}

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

/// Dealer for one shared state: three random slots that xor to `secret`.
/// TRUSTED DEALER TEST/MEASUREMENT HELPER: not dealerless provisioning.
pub fn deal_keccak_shares(secret: &[u64; 25], rng: &mut SeedRng) -> [SharePair; 3] {
    let mut slots = [[0u64; 25]; 3];
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

fn words_to_bytes(words: &[u64]) -> SecretBytes {
    SecretBytes(words.iter().flat_map(|w| w.to_le_bytes()).collect())
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
            v.fill(0);
            core::hint::black_box(v.as_mut_slice());
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
