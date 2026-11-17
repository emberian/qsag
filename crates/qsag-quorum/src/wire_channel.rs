//! Framed point-to-point transport between isolated parties.
//!
//! Every protocol message travels in one frame:
//!
//! ```text
//! magic[4] || session_id[32] || from_be[2] || to_be[2] || round_tag_be[4] || seq_be[8]
//!          || payload_len_be[4] || payload
//! ```
//!
//! The receiver accepts a frame only if every header field is the one it expects: its own
//! session, the peer it is reading from, itself as destination, the round it is in and the
//! next sequence number of that directed link. A frame from another session, a replayed or
//! reordered frame and a frame for another round are all refused, and decoding is strict
//! (no trailing bytes, declared length equal to actual length).
//!
//! Bare frames are not encrypted or authenticated. Use [`MacSealedWireChannel`]
//! with independently provisioned pairwise keys to authenticate socket traffic. The transport assumes authenticated
//! point-to-point links (a thread channel is one; a socket needs a secure channel beneath
//! it), and the protocols put their own MACs on what must convince a third custodian.
//!
//! [`WireTransport`] and the frame codec are `no_std`. The channel mesh and the loopback
//! socket mesh need `std` and are compiled with the `std` feature (and in tests).

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

/// First bytes of every frame.
pub const FRAME_MAGIC: [u8; 4] = *b"QSWF";
/// Bytes before the payload.
pub const FRAME_HEADER_BYTES: usize = 4 + 32 + 2 + 2 + 4 + 8 + 4;
/// Largest payload a frame may carry.
pub const MAX_FRAME_PAYLOAD: usize = 1 << 22;
/// Maximum complete wire frame, including its fixed header.
pub const MAX_WIRE_FRAME_BYTES: usize = FRAME_HEADER_BYTES + MAX_FRAME_PAYLOAD;

/// Transport and framing failures.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TransportError {
    /// The peer index is not a party of the mesh, or is the local party.
    UnknownPeer {
        peer: usize,
    },
    PayloadTooLarge,
    /// The link to `peer` is closed: the peer is gone.
    Closed {
        peer: usize,
    },
    /// Nothing arrived from `peer` in time.
    Timeout {
        peer: usize,
    },
    /// Not a frame: bad magic, truncated header, or length field unequal to the payload.
    Malformed,
    SessionMismatch,
    AuthenticationFailed,
    SequenceExhausted,
    /// The frame names another sender or destination than the link it arrived on.
    RouteMismatch,
    RoundTagMismatch {
        expected: u32,
        got: u32,
    },
    SequenceMismatch {
        expected: u64,
        got: u64,
    },
}

impl fmt::Display for TransportError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnknownPeer { peer } => write!(f, "unknown peer {peer}"),
            Self::PayloadTooLarge => f.write_str("payload too large for one frame"),
            Self::Closed { peer } => write!(f, "link to party {peer} is closed"),
            Self::Timeout { peer } => write!(f, "timed out waiting for party {peer}"),
            Self::Malformed => f.write_str("malformed frame"),
            Self::AuthenticationFailed => f.write_str("wire authentication failed"),
            Self::SequenceExhausted => f.write_str("wire sequence exhausted"),
            Self::SessionMismatch => f.write_str("frame belongs to another session"),
            Self::RouteMismatch => f.write_str("frame arrived on the wrong link"),
            Self::RoundTagMismatch { expected, got } => {
                write!(f, "frame for round {got:#x}, expected round {expected:#x}")
            }
            Self::SequenceMismatch { expected, got } => {
                write!(f, "frame sequence {got}, expected {expected}")
            }
        }
    }
}

impl TransportError {
    /// Returns `true` only when the directed link or sequence space is permanently unusable
    /// (`Closed` or `SequenceExhausted`). Transient timeouts and unauthenticated/malformed/out-of-round
    /// frames must not permanently brick the link (`CRITICAL-11`).
    #[inline]
    pub const fn is_fatal_link_error(&self) -> bool {
        matches!(self, Self::Closed { .. } | Self::SequenceExhausted)
    }
}

impl core::error::Error for TransportError {}

/// Header of one frame.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FrameHeader {
    pub session_id: [u8; 32],
    pub from: u16,
    pub to: u16,
    pub round_tag: u32,
    pub seq: u64,
}

/// Canonical encoding of one frame.
pub fn encode_frame(header: &FrameHeader, payload: &[u8]) -> Result<Vec<u8>, TransportError> {
    if payload.len() > MAX_FRAME_PAYLOAD {
        return Err(TransportError::PayloadTooLarge);
    }
    let mut out = Vec::with_capacity(FRAME_HEADER_BYTES + payload.len());
    out.extend_from_slice(&FRAME_MAGIC);
    out.extend_from_slice(&header.session_id);
    out.extend_from_slice(&header.from.to_be_bytes());
    out.extend_from_slice(&header.to.to_be_bytes());
    out.extend_from_slice(&header.round_tag.to_be_bytes());
    out.extend_from_slice(&header.seq.to_be_bytes());
    out.extend_from_slice(&(payload.len() as u32).to_be_bytes());
    out.extend_from_slice(payload);
    Ok(out)
}

/// Parse a frame header and return it with the payload length it declares.
pub fn decode_header(raw: &[u8]) -> Result<(FrameHeader, usize), TransportError> {
    if raw.len() < FRAME_HEADER_BYTES || raw[..4] != FRAME_MAGIC {
        return Err(TransportError::Malformed);
    }
    let field = |at: usize, len: usize| &raw[at..at + len];
    let mut session_id = [0u8; 32];
    session_id.copy_from_slice(field(4, 32));
    let be16 = |at: usize| u16::from_be_bytes([raw[at], raw[at + 1]]);
    let mut tag = [0u8; 4];
    tag.copy_from_slice(field(40, 4));
    let mut seq = [0u8; 8];
    seq.copy_from_slice(field(44, 8));
    let mut len = [0u8; 4];
    len.copy_from_slice(field(52, 4));
    let payload_len = u32::from_be_bytes(len) as usize;
    if payload_len > MAX_FRAME_PAYLOAD {
        return Err(TransportError::Malformed);
    }
    Ok((
        FrameHeader {
            session_id,
            from: be16(36),
            to: be16(38),
            round_tag: u32::from_be_bytes(tag),
            seq: u64::from_be_bytes(seq),
        },
        payload_len,
    ))
}

/// Strict decoder of one whole frame.
pub fn decode_frame(raw: &[u8]) -> Result<(FrameHeader, &[u8]), TransportError> {
    let (header, payload_len) = decode_header(raw)?;
    if raw.len() != FRAME_HEADER_BYTES + payload_len {
        return Err(TransportError::Malformed);
    }
    Ok((header, &raw[FRAME_HEADER_BYTES..]))
}

/// One party's end of a mesh: frames to and from each peer, in rounds.
pub trait WireTransport {
    /// Index of the local party.
    fn party(&self) -> usize;

    /// Number of parties in the mesh.
    fn parties(&self) -> usize;

    /// Send `payload` to `to_party` as the next frame of round `round_tag`.
    fn send_frame(
        &mut self,
        to_party: usize,
        round_tag: u32,
        payload: &[u8],
    ) -> Result<(), TransportError>;

    /// Receive the next frame from `from_party`. It must belong to this session, to this
    /// link, to round `expected_round_tag` and carry the next sequence number; otherwise
    /// the frame is consumed and an error returned.
    fn recv_frame(
        &mut self,
        from_party: usize,
        expected_round_tag: u32,
    ) -> Result<Vec<u8>, TransportError>;

    /// Receive a transport envelope whose payload has its own authenticated routing,
    /// round and sequence header. Unauthenticated outer sequence counters must not
    /// advance before that payload is authenticated. Built-in meshes bypass their
    /// outer sequencer here; transports with already-authenticated sequencing may
    /// delegate to `recv_frame`. This is not a replacement for `recv_frame` on plain links.
    fn recv_authenticated_envelope(
        &mut self,
        from_party: usize,
        expected_round_tag: u32,
    ) -> Result<Vec<u8>, TransportError>;
}

/// Per-link sequence state of one party. Turns payloads into frames and checks received
/// frames; a transport owns one and moves the bytes.
#[derive(Clone, Debug)]
pub struct FrameSequencer {
    session_id: [u8; 32],
    party: usize,
    send_seq: Vec<u64>,
    recv_seq: Vec<u64>,
}

impl FrameSequencer {
    pub fn new(session_id: [u8; 32], party: usize, parties: usize) -> Self {
        Self {
            session_id,
            party,
            send_seq: vec![0; parties],
            recv_seq: vec![0; parties],
        }
    }

    pub fn party(&self) -> usize {
        self.party
    }

    pub fn parties(&self) -> usize {
        self.send_seq.len()
    }

    pub fn session_id(&self) -> &[u8; 32] {
        &self.session_id
    }

    fn check_peer(&self, peer: usize) -> Result<(), TransportError> {
        if peer == self.party || peer >= self.send_seq.len() || peer > usize::from(u16::MAX) {
            return Err(TransportError::UnknownPeer { peer });
        }
        Ok(())
    }

    /// Frame `payload` for `to` and advance the send sequence of that link.
    pub fn seal(
        &mut self,
        to: usize,
        round_tag: u32,
        payload: &[u8],
    ) -> Result<Vec<u8>, TransportError> {
        self.check_peer(to)?;
        let next = self.send_seq[to]
            .checked_add(1)
            .ok_or(TransportError::SequenceExhausted)?;
        let frame = encode_frame(
            &FrameHeader {
                session_id: self.session_id,
                from: self.party as u16,
                to: to as u16,
                round_tag,
                seq: self.send_seq[to],
            },
            payload,
        )?;
        self.send_seq[to] = next;
        Ok(frame)
    }

    // The inner MAC layer owns replay/round protection. Validating an unauthenticated
    // outer sequence here would let one injected packet desynchronize that layer.
    #[cfg(any(test, feature = "std"))]
    fn open_authenticated_envelope(
        &self,
        from: usize,
        raw: &[u8],
    ) -> Result<Vec<u8>, TransportError> {
        self.check_peer(from)?;
        let (header, payload) = decode_frame(raw)?;
        if header.session_id != self.session_id {
            return Err(TransportError::SessionMismatch);
        }
        if usize::from(header.from) != from || usize::from(header.to) != self.party {
            return Err(TransportError::RouteMismatch);
        }
        Ok(payload.to_vec())
    }

    /// Check a frame that arrived on the link from `from` and return its payload. The
    /// receive sequence advances for every well-formed frame of this session and link, so
    /// one frame of the wrong round does not desynchronise the link.
    pub fn open(
        &mut self,
        from: usize,
        expected_round_tag: u32,
        raw: &[u8],
    ) -> Result<Vec<u8>, TransportError> {
        self.check_peer(from)?;
        let (header, payload) = decode_frame(raw)?;
        if header.session_id != self.session_id {
            return Err(TransportError::SessionMismatch);
        }
        if usize::from(header.from) != from || usize::from(header.to) != self.party {
            return Err(TransportError::RouteMismatch);
        }
        if header.seq != self.recv_seq[from] {
            return Err(TransportError::SequenceMismatch {
                expected: self.recv_seq[from],
                got: header.seq,
            });
        }
        self.recv_seq[from] = self.recv_seq[from]
            .checked_add(1)
            .ok_or(TransportError::SequenceExhausted)?;
        if header.round_tag != expected_round_tag {
            return Err(TransportError::RoundTagMismatch {
                expected: expected_round_tag,
                got: header.round_tag,
            });
        }
        Ok(payload.to_vec())
    }
}

fn derive_enc_subkey(chain_key: &[u8; 32]) -> [u8; 32] {
    let mut xof = qsag_core::sponge::keccak::Cshake256Xof::new(b"QSAG.QUORUM.WIRE_ENC_KEY/v1");
    xof.absorb(chain_key);
    let mut subkey = [0; 32];
    xof.squeeze(&mut subkey);
    subkey
}

fn derive_mac_subkey(chain_key: &[u8; 32]) -> [u8; 32] {
    let mut xof = qsag_core::sponge::keccak::Cshake256Xof::new(b"QSAG.QUORUM.WIRE_MAC_KEY/v1");
    xof.absorb(chain_key);
    let mut subkey = [0; 32];
    xof.squeeze(&mut subkey);
    subkey
}

fn derive_directional_key(
    pairwise_key: &[u8; 32],
    session_id: &[u8; 32],
    from: usize,
    to: usize,
) -> [u8; 32] {
    let mut xof = qsag_core::sponge::keccak::Cshake256Xof::new(b"QSAG.QUORUM.WIRE_DIRECTION/v1");
    xof.absorb(pairwise_key);
    xof.absorb(session_id);
    xof.absorb(&(from as u16).to_be_bytes());
    xof.absorb(&(to as u16).to_be_bytes());
    let mut key = [0; 32];
    xof.squeeze(&mut key);
    key
}

fn wire_mac(mac_key: &[u8; 32], frame: &[u8]) -> [u8; 32] {
    let mut xof = qsag_core::sponge::keccak::Cshake256Xof::new(b"QSAG.QUORUM.WIRE_MAC/v1");
    xof.absorb(mac_key);
    xof.absorb(frame);
    let mut tag = [0; 32];
    xof.squeeze(&mut tag);
    tag
}

fn wire_crypt(enc_key: &[u8; 32], header: &[u8], payload: &mut [u8]) {
    let mut xof = qsag_core::sponge::keccak::Cshake256Xof::new(b"QSAG.QUORUM.WIRE_STREAM/v1");
    xof.absorb(enc_key);
    xof.absorb(header);
    let mut block = [0; 136];
    for chunk in payload.chunks_mut(block.len()) {
        xof.squeeze(&mut block[..chunk.len()]);
        for (byte, pad) in chunk.iter_mut().zip(&block) {
            *byte ^= pad;
        }
    }
    qsag_core::wipe::wipe_bytes(&mut block);
}

fn ratchet_wire_key(key: &mut [u8; 32], tag: &[u8; 32]) {
    let mut xof = qsag_core::sponge::keccak::Cshake256Xof::new(b"QSAG.QUORUM.WIRE_RATCHET/v1");
    xof.absorb(key);
    xof.absorb(tag);
    qsag_core::wipe::wipe_bytes(key);
    xof.squeeze(key);
}

/// Authenticated framing over any mesh endpoint, including `TcpEndpoint`.
///
/// Provision the same independent 32-byte secret at both ends of each pair.
/// Both modes derive independent directional keys `(party -> peer)` vs `(peer -> party)`
/// and separate encryption and MAC subkeys. Encrypted links erase each chain key after
/// advancing it with the authenticated ciphertext tag. Authentication failures do
/// not advance receive state. Receive timeouts and rejected packets leave the link usable;
/// send failures and terminal receive errors require a new session.
/// A session ID must be fresh whenever endpoints are recreated: counters cannot
/// be reset under the same key/session pair. Headers, lengths, rounds, direction,
/// sequence numbers and payloads are MAC-bound. Use [`ConfidentialWireChannel`] or
/// `new_encrypted` for secret shares; `new` authenticates while leaving payloads visible.
pub struct MacSealedWireChannel<T: WireTransport> {
    transport: T,
    sequencer: FrameSequencer,
    keys: Vec<[u8; 32]>,
    recv_keys: Vec<[u8; 32]>,
    failed_links: Vec<bool>,
    encrypted: bool,
}

impl<T: WireTransport> MacSealedWireChannel<T> {
    /// `keys[peer]` is the provisioned pairwise link key; the local entry is wiped and unused.
    pub fn new(
        transport: T,
        session_id: [u8; 32],
        mut keys: Vec<[u8; 32]>,
    ) -> Result<Self, TransportError> {
        if keys.len() != transport.parties()
            || transport.party() >= keys.len()
            || keys.len() > usize::from(u16::MAX) + 1
        {
            for key in &mut keys {
                qsag_asm::volatile_fill(key, 0);
            }
            return Err(TransportError::Malformed);
        }
        let me = transport.party();
        let parties = keys.len();
        let mut send_keys = vec![[0u8; 32]; parties];
        let mut recv_keys = vec![[0u8; 32]; parties];
        for (peer, raw_key) in keys.iter_mut().enumerate() {
            if peer != me {
                send_keys[peer] = derive_directional_key(raw_key, &session_id, me, peer);
                recv_keys[peer] = derive_directional_key(raw_key, &session_id, peer, me);
            }
            qsag_asm::volatile_fill(raw_key, 0);
        }
        let sequencer = FrameSequencer::new(session_id, me, parties);
        Ok(Self {
            transport,
            sequencer,
            keys: send_keys,
            recv_keys,
            failed_links: vec![false; parties],
            encrypted: false,
        })
    }

    /// Authenticate and encrypt payloads using domain-separated encryption and MAC subkeys.
    /// Both peers must select the same mode.
    pub fn new_encrypted(
        transport: T,
        session_id: [u8; 32],
        keys: Vec<[u8; 32]>,
    ) -> Result<Self, TransportError> {
        let mut channel = Self::new(transport, session_id, keys)?;
        channel.encrypted = true;
        Ok(channel)
    }

    fn seal(&mut self, peer: usize, round: u32, payload: &[u8]) -> Result<Vec<u8>, TransportError> {
        self.sequencer.check_peer(peer)?;
        // The outer transport must fit both our authenticated header, mode byte, and tag.
        if payload.len() > MAX_FRAME_PAYLOAD - FRAME_HEADER_BYTES - 33 {
            return Err(TransportError::PayloadTooLarge);
        }
        let mut body = Vec::with_capacity(payload.len() + 1);
        body.push(u8::from(self.encrypted));
        body.extend_from_slice(payload);
        let framed = self.sequencer.seal(peer, round, &body);
        qsag_core::wipe::wipe_bytes(&mut body);
        let mut raw = framed?;
        if self.encrypted {
            let mut enc_key = derive_enc_subkey(&self.keys[peer]);
            let (header, body) = raw.split_at_mut(FRAME_HEADER_BYTES);
            wire_crypt(&enc_key, header, &mut body[1..]);
            qsag_core::wipe::wipe_bytes32(&mut enc_key);
        }
        let mut mac_key = derive_mac_subkey(&self.keys[peer]);
        let tag = wire_mac(&mac_key, &raw);
        qsag_core::wipe::wipe_bytes32(&mut mac_key);
        if self.encrypted {
            ratchet_wire_key(&mut self.keys[peer], &tag);
        }
        raw.extend_from_slice(&tag);
        Ok(raw)
    }

    fn open(&mut self, peer: usize, round: u32, raw: &[u8]) -> Result<Vec<u8>, TransportError> {
        self.sequencer.check_peer(peer)?;
        if raw.len() < FRAME_HEADER_BYTES + 33 || raw.len() > MAX_FRAME_PAYLOAD {
            return Err(TransportError::Malformed);
        }
        let (frame, tag) = raw.split_at(raw.len() - 32);
        let mut mac_key = derive_mac_subkey(&self.recv_keys[peer]);
        let expected = wire_mac(&mac_key, frame);
        qsag_core::wipe::wipe_bytes32(&mut mac_key);
        let mut received = [0; 32];
        received.copy_from_slice(tag);
        if !qsag_core::wipe::ct_eq_bytes32(&expected, &received) {
            return Err(TransportError::AuthenticationFailed);
        }
        let (header, body) = decode_frame(frame)?;
        if body.first() != Some(&u8::from(self.encrypted)) {
            return Err(TransportError::AuthenticationFailed);
        }
        if header.session_id != *self.sequencer.session_id() {
            return Err(TransportError::SessionMismatch);
        }
        if usize::from(header.from) != peer || usize::from(header.to) != self.sequencer.party() {
            return Err(TransportError::RouteMismatch);
        }
        let expected_seq = self.sequencer.recv_seq[peer];
        if header.seq != expected_seq {
            return Err(TransportError::SequenceMismatch {
                expected: expected_seq,
                got: header.seq,
            });
        }
        let next_seq = expected_seq
            .checked_add(1)
            .ok_or(TransportError::SequenceExhausted)?;
        // Refuse a wrong round before advancing either the sequence or key.
        if header.round_tag != round {
            return Err(TransportError::RoundTagMismatch {
                expected: round,
                got: header.round_tag,
            });
        }
        self.sequencer.recv_seq[peer] = next_seq;
        let mut payload = body[1..].to_vec();
        if self.encrypted {
            let mut enc_key = derive_enc_subkey(&self.recv_keys[peer]);
            wire_crypt(&enc_key, &frame[..FRAME_HEADER_BYTES], &mut payload);
            qsag_core::wipe::wipe_bytes32(&mut enc_key);
            ratchet_wire_key(&mut self.recv_keys[peer], &received);
        }
        Ok(payload)
    }

    /// Irreversibly abort this channel and read one authenticated frame as failure evidence.
    ///
    /// A failed send must not suppress an already queued inbound commitment opening: send
    /// and receive keys/sequences are independent. Ordinary I/O remains closed on every
    /// link after this call, even when evidence is received successfully. Only an aborting
    /// protocol may use the payload, to diagnose its failure rather than resume execution.
    /// Authentication, routing, round, replay checks and receive-key erasure still apply;
    /// neither a disconnect nor an unauthenticated accusation is evidence against a peer.
    pub(crate) fn recv_frame_for_abort(
        &mut self,
        peer: usize,
        round: u32,
    ) -> Result<Vec<u8>, TransportError> {
        self.failed_links.fill(true);
        let raw = self.transport.recv_authenticated_envelope(peer, round)?;
        self.open(peer, round, &raw)
    }
}

impl<T: WireTransport> WireTransport for MacSealedWireChannel<T> {
    fn recv_authenticated_envelope(
        &mut self,
        peer: usize,
        round: u32,
    ) -> Result<Vec<u8>, TransportError> {
        self.recv_frame(peer, round)
    }

    fn party(&self) -> usize {
        self.sequencer.party()
    }
    fn parties(&self) -> usize {
        self.sequencer.parties()
    }
    fn send_frame(
        &mut self,
        peer: usize,
        round: u32,
        payload: &[u8],
    ) -> Result<(), TransportError> {
        if self.failed_links.get(peer) == Some(&true) {
            return Err(TransportError::Closed { peer });
        }
        let raw = self.seal(peer, round, payload)?;
        if let Err(err) = self.transport.send_frame(peer, round, &raw) {
            if let Some(failed) = self.failed_links.get_mut(peer) {
                *failed = true;
            }
            return Err(err);
        }
        Ok(())
    }
    fn recv_frame(&mut self, peer: usize, round: u32) -> Result<Vec<u8>, TransportError> {
        if self.failed_links.get(peer) == Some(&true) {
            return Err(TransportError::Closed { peer });
        }
        let raw = match self.transport.recv_authenticated_envelope(peer, round) {
            Ok(raw) => raw,
            Err(err) => {
                if err.is_fatal_link_error()
                    && let Some(failed) = self.failed_links.get_mut(peer)
                {
                    *failed = true;
                }
                return Err(err);
            }
        };
        match self.open(peer, round, &raw) {
            Ok(payload) => Ok(payload),
            Err(err) => {
                if err.is_fatal_link_error()
                    && let Some(failed) = self.failed_links.get_mut(peer)
                {
                    *failed = true;
                }
                Err(err)
            }
        }
    }
}

impl<T: WireTransport> Drop for MacSealedWireChannel<T> {
    fn drop(&mut self) {
        for key in self.keys.iter_mut().chain(&mut self.recv_keys) {
            qsag_asm::volatile_fill(key, 0);
        }
    }
}

/// Encrypted-only wire channel with directional key separation, separate stream and MAC
/// subkeys, strict Encrypt-then-MAC authentication, fail-closed `u64::MAX` sequence bounds,
/// and fail-closed link latching on underlying transport send errors.
pub struct ConfidentialWireChannel<T: WireTransport> {
    inner: MacSealedWireChannel<T>,
    failed_links: Vec<bool>,
}

impl<T: WireTransport> ConfidentialWireChannel<T> {
    /// Provision an encrypted, direction-bound channel from per-peer 32-byte secrets.
    pub fn new(
        transport: T,
        session_id: [u8; 32],
        keys: Vec<[u8; 32]>,
    ) -> Result<Self, TransportError> {
        let inner = MacSealedWireChannel::new_encrypted(transport, session_id, keys)?;
        let parties = inner.parties();
        Ok(Self {
            inner,
            failed_links: vec![false; parties],
        })
    }

    pub fn seal(
        &mut self,
        peer: usize,
        round: u32,
        payload: &[u8],
    ) -> Result<Vec<u8>, TransportError> {
        if self.failed_links.get(peer) == Some(&true) {
            return Err(TransportError::Closed { peer });
        }
        self.inner.seal(peer, round, payload)
    }

    pub fn open(&mut self, peer: usize, round: u32, raw: &[u8]) -> Result<Vec<u8>, TransportError> {
        if self.failed_links.get(peer) == Some(&true) {
            return Err(TransportError::Closed { peer });
        }
        self.inner.open(peer, round, raw)
    }
}

impl<T: WireTransport> WireTransport for ConfidentialWireChannel<T> {
    fn recv_authenticated_envelope(
        &mut self,
        peer: usize,
        round: u32,
    ) -> Result<Vec<u8>, TransportError> {
        self.recv_frame(peer, round)
    }

    fn party(&self) -> usize {
        self.inner.party()
    }

    fn parties(&self) -> usize {
        self.inner.parties()
    }

    fn send_frame(
        &mut self,
        peer: usize,
        round: u32,
        payload: &[u8],
    ) -> Result<(), TransportError> {
        let raw = self.seal(peer, round, payload)?;
        if let Err(err) = self.inner.transport.send_frame(peer, round, &raw) {
            if let Some(failed) = self.failed_links.get_mut(peer) {
                *failed = true;
            }
            return Err(err);
        }
        Ok(())
    }

    fn recv_frame(&mut self, peer: usize, round: u32) -> Result<Vec<u8>, TransportError> {
        if self.failed_links.get(peer) == Some(&true) {
            return Err(TransportError::Closed { peer });
        }
        match self.inner.recv_frame(peer, round) {
            Ok(payload) => Ok(payload),
            Err(err) => {
                if err.is_fatal_link_error()
                    && let Some(failed) = self.failed_links.get_mut(peer)
                {
                    *failed = true;
                }
                Err(err)
            }
        }
    }
}

#[cfg(any(test, feature = "std"))]
pub use mesh::{
    InMemoryEndpoint, InMemoryWireMesh, MeshStats, SentFrame, TcpEndpoint, TcpWireMesh,
    TcpWireMeshBuilder,
};

#[cfg(any(test, feature = "std"))]
mod mesh {
    use super::{FRAME_HEADER_BYTES, FrameSequencer, TransportError, WireTransport, decode_header};
    use std::io::{Read, Write};
    use std::net::{Ipv4Addr, TcpListener, TcpStream};
    use std::sync::mpsc::{Receiver, RecvTimeoutError, Sender, channel};
    use std::sync::{Arc, Mutex};
    use std::time::Duration;
    use std::vec::Vec;

    type Tx = Option<Sender<Vec<u8>>>;
    type Rx = Option<Receiver<Vec<u8>>>;

    /// One frame as it left a party.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct SentFrame {
        pub from: usize,
        pub to: usize,
        pub round_tag: u32,
        /// Bytes on the wire, header included.
        pub wire_bytes: usize,
    }

    /// Log of every frame sent through a mesh, shared by its endpoints.
    #[derive(Debug, Default)]
    pub struct MeshStats {
        frames: Mutex<Vec<SentFrame>>,
    }

    impl MeshStats {
        fn record(&self, frame: SentFrame) {
            self.frames
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner())
                .push(frame);
        }

        /// Every frame sent so far, in the order the sends were logged.
        pub fn frames(&self) -> Vec<SentFrame> {
            self.frames
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner())
                .clone()
        }

        /// Bytes sent by all parties, headers included.
        pub fn total_bytes(&self) -> u64 {
            self.frames().iter().map(|f| f.wire_bytes as u64).sum()
        }

        pub fn total_frames(&self) -> usize {
            self.frames
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner())
                .len()
        }

        /// Bytes sent by `party`, headers included.
        pub fn bytes_sent_by(&self, party: usize) -> u64 {
            self.frames()
                .iter()
                .filter(|f| f.from == party)
                .map(|f| f.wire_bytes as u64)
                .sum()
        }

        /// Frames `party` sent with a round tag accepted by `tag`.
        pub fn frames_sent_by(&self, party: usize, tag: impl Fn(u32) -> bool) -> usize {
            self.frames()
                .iter()
                .filter(|f| f.from == party && tag(f.round_tag))
                .count()
        }

        /// Forget everything logged so far.
        pub fn reset(&self) {
            self.frames
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner())
                .clear();
        }
    }

    /// A full mesh of in-process channels: one unbounded channel per ordered pair of
    /// parties. Each endpoint is moved into the thread of its party.
    pub struct InMemoryWireMesh;

    impl InMemoryWireMesh {
        /// Endpoints for `parties` parties of session `session_id`, and the shared log.
        pub fn connect(
            parties: usize,
            session_id: [u8; 32],
        ) -> (Vec<InMemoryEndpoint>, Arc<MeshStats>) {
            let stats = Arc::new(MeshStats::default());
            let mut senders: Vec<Vec<Tx>> = (0..parties)
                .map(|_| (0..parties).map(|_| None).collect())
                .collect();
            let mut receivers: Vec<Vec<Rx>> = (0..parties)
                .map(|_| (0..parties).map(|_| None).collect())
                .collect();
            for from in 0..parties {
                for to in (0..parties).filter(|&to| to != from) {
                    let (tx, rx) = channel();
                    senders[from][to] = Some(tx);
                    receivers[to][from] = Some(rx);
                }
            }
            let endpoints = senders
                .into_iter()
                .zip(receivers)
                .enumerate()
                .map(|(party, (tx, rx))| InMemoryEndpoint {
                    seq: FrameSequencer::new(session_id, party, parties),
                    tx,
                    rx,
                    stats: stats.clone(),
                    timeout: Duration::from_secs(30),
                })
                .collect();
            (endpoints, stats)
        }
    }

    /// One party's end of an [`InMemoryWireMesh`].
    pub struct InMemoryEndpoint {
        seq: FrameSequencer,
        tx: Vec<Tx>,
        rx: Vec<Rx>,
        stats: Arc<MeshStats>,
        timeout: Duration,
    }

    impl InMemoryEndpoint {
        fn recv_packet(&mut self, from_party: usize) -> Result<Vec<u8>, TransportError> {
            let rx = self
                .rx
                .get(from_party)
                .and_then(Option::as_ref)
                .ok_or(TransportError::UnknownPeer { peer: from_party })?;
            rx.recv_timeout(self.timeout).map_err(|e| match e {
                RecvTimeoutError::Timeout => TransportError::Timeout { peer: from_party },
                RecvTimeoutError::Disconnected => TransportError::Closed { peer: from_party },
            })
        }

        /// How long [`WireTransport::recv_frame`] waits for a silent peer.
        pub fn set_timeout(&mut self, timeout: Duration) {
            self.timeout = timeout;
        }

        pub fn stats(&self) -> &Arc<MeshStats> {
            &self.stats
        }

        /// Put arbitrary bytes on the link to `to`, bypassing the frame codec. For tests
        /// that play a party which does not follow the framing.
        pub fn send_raw(&mut self, to: usize, raw: Vec<u8>) -> Result<(), TransportError> {
            let tx = self
                .tx
                .get(to)
                .and_then(Option::as_ref)
                .ok_or(TransportError::UnknownPeer { peer: to })?;
            self.stats.record(SentFrame {
                from: self.seq.party(),
                to,
                round_tag: u32::MAX,
                wire_bytes: raw.len(),
            });
            tx.send(raw)
                .map_err(|_| TransportError::Closed { peer: to })
        }
    }

    impl WireTransport for InMemoryEndpoint {
        fn party(&self) -> usize {
            self.seq.party()
        }

        fn parties(&self) -> usize {
            self.seq.parties()
        }

        fn send_frame(
            &mut self,
            to_party: usize,
            round_tag: u32,
            payload: &[u8],
        ) -> Result<(), TransportError> {
            let frame = self.seq.seal(to_party, round_tag, payload)?;
            let tx = self.tx[to_party]
                .as_ref()
                .ok_or(TransportError::UnknownPeer { peer: to_party })?;
            self.stats.record(SentFrame {
                from: self.seq.party(),
                to: to_party,
                round_tag,
                wire_bytes: frame.len(),
            });
            tx.send(frame)
                .map_err(|_| TransportError::Closed { peer: to_party })
        }

        fn recv_frame(
            &mut self,
            from_party: usize,
            expected_round_tag: u32,
        ) -> Result<Vec<u8>, TransportError> {
            let raw = self.recv_packet(from_party)?;
            self.seq.open(from_party, expected_round_tag, &raw)
        }

        fn recv_authenticated_envelope(
            &mut self,
            from_party: usize,
            _round: u32,
        ) -> Result<Vec<u8>, TransportError> {
            let raw = self.recv_packet(from_party)?;
            self.seq.open_authenticated_envelope(from_party, &raw)
        }
    }

    /// A full mesh of loopback TCP connections, one stream per pair of parties, with the
    /// same frames as the channel mesh written to the socket. Sends block once the socket
    /// buffers of a link are full, so a round in which every party sends before it reads
    /// must keep its frames below the buffer size (the protocols here send at most a few
    /// tens of kilobytes per round and link).
    pub struct TcpWireMesh;

    impl TcpWireMesh {
        /// Connect `parties` endpoints over `127.0.0.1` and return them with the shared log.
        pub fn loopback(
            parties: usize,
            session_id: [u8; 32],
        ) -> std::io::Result<(Vec<TcpEndpoint>, Arc<MeshStats>)> {
            Self::with_timeout(Duration::from_secs(30)).loopback(parties, session_id)
        }

        /// Configure finite read and write timeouts for every socket in the mesh.
        pub fn with_timeout(timeout: Duration) -> TcpWireMeshBuilder {
            TcpWireMeshBuilder { timeout }
        }
    }

    pub struct TcpWireMeshBuilder {
        timeout: Duration,
    }

    impl TcpWireMeshBuilder {
        pub fn loopback(
            self,
            parties: usize,
            session_id: [u8; 32],
        ) -> std::io::Result<(Vec<TcpEndpoint>, Arc<MeshStats>)> {
            if self.timeout.is_zero() {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::InvalidInput,
                    "timeout must be nonzero",
                ));
            }
            let stats = Arc::new(MeshStats::default());
            let mut streams: Vec<Vec<Option<TcpStream>>> = (0..parties)
                .map(|_| (0..parties).map(|_| None).collect())
                .collect();
            let pairs = (0..parties).flat_map(|lo| (lo + 1..parties).map(move |hi| (lo, hi)));
            for (lo, hi) in pairs {
                let listener = TcpListener::bind((Ipv4Addr::LOCALHOST, 0))?;
                let dialer = TcpStream::connect(listener.local_addr()?)?;
                let (accepted, _) = listener.accept()?;
                dialer.set_nodelay(true)?;
                accepted.set_nodelay(true)?;
                for stream in [&dialer, &accepted] {
                    stream.set_read_timeout(Some(self.timeout))?;
                    stream.set_write_timeout(Some(self.timeout))?;
                }
                streams[lo][hi] = Some(dialer);
                streams[hi][lo] = Some(accepted);
            }
            let endpoints = streams
                .into_iter()
                .enumerate()
                .map(|(party, streams)| TcpEndpoint {
                    seq: FrameSequencer::new(session_id, party, parties),
                    streams,
                    receiving: (0..parties).map(|_| PartialFrame::default()).collect(),
                    stats: stats.clone(),
                })
                .collect();
            Ok((endpoints, stats))
        }
    }

    // Retained across read deadlines. read_exact discards the number of bytes read
    // before a timeout, which would turn the next payload bytes into a new header.
    #[derive(Default)]
    struct PartialFrame {
        bytes: Vec<u8>,
        filled: usize,
    }

    impl PartialFrame {
        fn read(&mut self, stream: &mut TcpStream, peer: usize) -> Result<Vec<u8>, TransportError> {
            if self.bytes.is_empty() {
                self.bytes.resize(FRAME_HEADER_BYTES, 0);
            }
            loop {
                while self.filled < self.bytes.len() {
                    match stream.read(&mut self.bytes[self.filled..]) {
                        Ok(0) => return Err(TransportError::Closed { peer }),
                        Ok(n) => self.filled += n,
                        Err(e) if e.kind() == std::io::ErrorKind::Interrupted => continue,
                        Err(e) => return Err(io_error(peer, &e)),
                    }
                }
                let (_, len) = decode_header(&self.bytes)?;
                let total = FRAME_HEADER_BYTES + len;
                if self.bytes.len() == total {
                    self.filled = 0;
                    return Ok(core::mem::take(&mut self.bytes));
                }
                self.bytes.resize(total, 0);
            }
        }
    }

    /// One party's end of a [`TcpWireMesh`].
    pub struct TcpEndpoint {
        seq: FrameSequencer,
        streams: Vec<Option<TcpStream>>,
        receiving: Vec<PartialFrame>,
        stats: Arc<MeshStats>,
    }

    impl TcpEndpoint {
        fn recv_packet(&mut self, from_party: usize) -> Result<Vec<u8>, TransportError> {
            let stream = self
                .streams
                .get_mut(from_party)
                .and_then(Option::as_mut)
                .ok_or(TransportError::UnknownPeer { peer: from_party })?;
            let raw = match self.receiving[from_party].read(stream, from_party) {
                Ok(raw) => raw,
                Err(err) => {
                    // An invalid length/magic loses the TCP frame boundary. There is no
                    // safe resynchronization marker in this codec, so close only this
                    // malformed stream. A partial read deadline must retain all bytes.
                    if err.is_fatal_link_error() || err == TransportError::Malformed {
                        self.streams[from_party] = None;
                        self.receiving[from_party] = PartialFrame::default();
                    }
                    return Err(err);
                }
            };
            Ok(raw)
        }

        /// How long [`WireTransport::recv_frame`] waits for a silent peer.
        pub fn set_timeout(&mut self, timeout: Duration) -> std::io::Result<()> {
            for stream in self.streams.iter().flatten() {
                stream.set_read_timeout(Some(timeout))?;
                stream.set_write_timeout(Some(timeout))?;
            }
            Ok(())
        }

        pub fn stats(&self) -> &Arc<MeshStats> {
            &self.stats
        }
    }

    fn io_error(peer: usize, e: &std::io::Error) -> TransportError {
        match e.kind() {
            std::io::ErrorKind::WouldBlock | std::io::ErrorKind::TimedOut => {
                TransportError::Timeout { peer }
            }
            _ => TransportError::Closed { peer },
        }
    }

    impl WireTransport for TcpEndpoint {
        fn party(&self) -> usize {
            self.seq.party()
        }

        fn parties(&self) -> usize {
            self.seq.parties()
        }

        fn send_frame(
            &mut self,
            to_party: usize,
            round_tag: u32,
            payload: &[u8],
        ) -> Result<(), TransportError> {
            let frame = self.seq.seal(to_party, round_tag, payload)?;
            let stream = self.streams[to_party]
                .as_mut()
                .ok_or(TransportError::UnknownPeer { peer: to_party })?;
            self.stats.record(SentFrame {
                from: self.seq.party(),
                to: to_party,
                round_tag,
                wire_bytes: frame.len(),
            });
            stream.write_all(&frame).map_err(|e| io_error(to_party, &e))
        }

        fn recv_frame(
            &mut self,
            from_party: usize,
            expected_round_tag: u32,
        ) -> Result<Vec<u8>, TransportError> {
            let raw = self.recv_packet(from_party)?;
            self.seq.open(from_party, expected_round_tag, &raw)
        }

        fn recv_authenticated_envelope(
            &mut self,
            from_party: usize,
            _round: u32,
        ) -> Result<Vec<u8>, TransportError> {
            let raw = self.recv_packet(from_party)?;
            self.seq.open_authenticated_envelope(from_party, &raw)
        }
    }
    #[cfg(test)]
    mod tcp_safety_tests {
        use super::*;
        use crate::wire_channel::{FrameHeader, encode_frame};
        #[test]
        fn partial_header_and_payload_survive_multiple_deadlines() {
            let (mut ep, _) = TcpWireMesh::with_timeout(Duration::from_millis(10))
                .loopback(2, [9; 32])
                .unwrap();
            let frame = ep[0].seq.seal(1, 7, b"partial payload").unwrap();
            ep[0].streams[1]
                .as_mut()
                .unwrap()
                .write_all(&frame[..11])
                .unwrap();
            assert_eq!(
                ep[1].recv_frame(0, 7),
                Err(TransportError::Timeout { peer: 0 })
            );
            assert_eq!(ep[1].receiving[0].filled, 11);
            ep[0].streams[1]
                .as_mut()
                .unwrap()
                .write_all(&frame[11..FRAME_HEADER_BYTES + 3])
                .unwrap();
            assert_eq!(
                ep[1].recv_frame(0, 7),
                Err(TransportError::Timeout { peer: 0 })
            );
            assert_eq!(ep[1].receiving[0].filled, FRAME_HEADER_BYTES + 3);
            ep[0].streams[1]
                .as_mut()
                .unwrap()
                .write_all(&frame[FRAME_HEADER_BYTES + 3..])
                .unwrap();
            assert_eq!(ep[1].recv_frame(0, 7).unwrap(), b"partial payload");
            ep[0].send_frame(1, 8, b"next frame").unwrap();
            assert_eq!(ep[1].recv_frame(0, 8).unwrap(), b"next frame");
        }

        #[test]
        fn deadlines_and_oversized_header() {
            let (mut endpoints, _) = TcpWireMesh::with_timeout(Duration::from_millis(25))
                .loopback(2, [0; 32])
                .unwrap();
            let stream = endpoints[0].streams[1].as_mut().unwrap();
            // Kernels round socket deadlines up to their timer resolution.
            for timeout in [
                stream.read_timeout().unwrap(),
                stream.write_timeout().unwrap(),
            ] {
                let timeout = timeout.expect("socket deadline is configured");
                assert!(timeout >= Duration::from_millis(25));
                assert!(timeout <= Duration::from_millis(50));
            }
            let header = FrameHeader {
                session_id: [0; 32],
                from: 0,
                to: 1,
                round_tag: 0,
                seq: 0,
            };
            let mut raw = encode_frame(&header, &[]).unwrap();
            raw[52..56].copy_from_slice(&u32::MAX.to_be_bytes());
            stream.write_all(&raw).unwrap();
            assert_eq!(
                endpoints[1].recv_frame(0, 0),
                Err(TransportError::Malformed)
            );
            assert_eq!(
                endpoints[0].recv_frame(1, 0),
                Err(TransportError::Closed { peer: 1 })
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const SESSION: [u8; 32] = [7; 32];

    #[test]
    fn abort_receive_preserves_authenticated_evidence_without_reopening_links() {
        for encrypted in [false, true] {
            for tamper in [false, true] {
                let (endpoints, _) = InMemoryWireMesh::connect(3, SESSION);
                let mut channels: Vec<_> = endpoints
                    .into_iter()
                    .map(|endpoint| {
                        let mut channel =
                            MacSealedWireChannel::new(endpoint, SESSION, vec![[3; 32]; 3]).unwrap();
                        channel.encrypted = encrypted;
                        channel
                    })
                    .collect();
                let mut carol = channels.pop().unwrap();
                let mut bob = channels.pop().unwrap();
                let mut alice = channels.pop().unwrap();
                let mut evidence = bob.seal(0, 7, b"opening").unwrap();
                if tamper {
                    *evidence.last_mut().unwrap() ^= 1;
                }
                bob.transport.send_frame(0, 7, &evidence).unwrap();
                drop(bob);
                carol.send_frame(0, 7, b"other opening").unwrap();
                assert_eq!(
                    alice.send_frame(1, 7, b"too late"),
                    Err(TransportError::Closed { peer: 1 })
                );
                assert_eq!(
                    alice.recv_frame(1, 7),
                    Err(TransportError::Closed { peer: 1 })
                );
                let expected = if tamper {
                    Err(TransportError::AuthenticationFailed)
                } else {
                    Ok(b"opening".to_vec())
                };
                assert_eq!(alice.recv_frame_for_abort(1, 7), expected);
                assert_eq!(alice.sequencer.recv_seq[1], u64::from(!tamper));
                // Even the unaffected peer is now abort-only; no successful receive can
                // restore ordinary protocol I/O or make a failed session usable again.
                assert_eq!(
                    alice.send_frame(2, 7, b"resume"),
                    Err(TransportError::Closed { peer: 2 })
                );
                assert_eq!(
                    alice.recv_frame(2, 7),
                    Err(TransportError::Closed { peer: 2 })
                );
                assert_eq!(
                    alice.recv_frame_for_abort(2, 7),
                    Ok(b"other opening".to_vec())
                );
                assert_eq!(
                    alice.recv_frame(2, 7),
                    Err(TransportError::Closed { peer: 2 })
                );
            }
        }
    }

    #[test]
    fn frame_layout_is_canonical_and_decoding_is_strict() {
        let header = FrameHeader {
            session_id: SESSION,
            from: 2,
            to: 0,
            round_tag: 0x0102_0304,
            seq: 9,
        };
        let frame = encode_frame(&header, b"payload").unwrap();
        assert_eq!(frame.len(), FRAME_HEADER_BYTES + 7);
        assert_eq!(&frame[..4], b"QSWF");
        assert_eq!(&frame[4..36], &SESSION);
        assert_eq!(&frame[36..40], &[0, 2, 0, 0]);
        assert_eq!(&frame[40..44], &[1, 2, 3, 4]);
        assert_eq!(&frame[44..52], &9u64.to_be_bytes());
        assert_eq!(&frame[52..56], &7u32.to_be_bytes());
        assert_eq!(decode_frame(&frame), Ok((header, &b"payload"[..])));
        assert_eq!(
            decode_frame(&frame[..frame.len() - 1]),
            Err(TransportError::Malformed)
        );
        let mut longer = frame.clone();
        longer.push(0);
        assert_eq!(decode_frame(&longer), Err(TransportError::Malformed));
        let mut bad_magic = frame.clone();
        bad_magic[0] ^= 1;
        assert_eq!(decode_frame(&bad_magic), Err(TransportError::Malformed));
        assert_eq!(decode_frame(&frame[..20]), Err(TransportError::Malformed));
        let empty = encode_frame(&header, b"").unwrap();
        assert_eq!(decode_frame(&empty), Ok((header, &b""[..])));
    }

    #[test]
    fn sequencer_rejects_foreign_replayed_misrouted_and_wrong_round_frames() {
        let mut alice = FrameSequencer::new(SESSION, 0, 3);
        let mut bob = FrameSequencer::new(SESSION, 1, 3);
        let first = alice.seal(1, 5, b"one").unwrap();
        let second = alice.seal(1, 6, b"two").unwrap();
        assert_eq!(bob.open(0, 5, &first), Ok(b"one".to_vec()));
        // Replay of the first frame.
        assert_eq!(
            bob.open(0, 5, &first),
            Err(TransportError::SequenceMismatch {
                expected: 1,
                got: 0
            })
        );
        // The second frame is for round 6; asking for round 7 consumes and refuses it.
        assert_eq!(
            bob.open(0, 7, &second),
            Err(TransportError::RoundTagMismatch {
                expected: 7,
                got: 6
            })
        );
        let third = alice.seal(1, 7, b"three").unwrap();
        assert_eq!(bob.open(0, 7, &third), Ok(b"three".to_vec()));

        // A frame for party 2 presented to party 1, and a frame claimed to come from 2.
        let for_carol = alice.seal(2, 5, b"x").unwrap();
        assert_eq!(
            bob.open(0, 5, &for_carol),
            Err(TransportError::RouteMismatch)
        );
        let fourth = alice.seal(1, 5, b"y").unwrap();
        assert_eq!(bob.open(2, 5, &fourth), Err(TransportError::RouteMismatch));

        // Another session.
        let mut mallory = FrameSequencer::new([8; 32], 0, 3);
        let foreign = mallory.seal(1, 5, b"z").unwrap();
        assert_eq!(
            bob.open(0, 5, &foreign),
            Err(TransportError::SessionMismatch)
        );

        assert_eq!(
            alice.seal(0, 5, b""),
            Err(TransportError::UnknownPeer { peer: 0 })
        );
        assert_eq!(
            alice.seal(3, 5, b""),
            Err(TransportError::UnknownPeer { peer: 3 })
        );
    }

    #[test]
    fn channel_mesh_delivers_across_threads_and_counts_wire_bytes() {
        let (endpoints, stats) = InMemoryWireMesh::connect(3, SESSION);
        let results: Vec<Vec<u8>> = std::thread::scope(|scope| {
            let handles: Vec<_> = endpoints
                .into_iter()
                .map(|mut ep| {
                    scope.spawn(move || {
                        let me = ep.party();
                        for peer in (0..3).filter(|&p| p != me) {
                            ep.send_frame(peer, 1, &[me as u8; 10]).unwrap();
                        }
                        let mut got = Vec::new();
                        for peer in (0..3).filter(|&p| p != me) {
                            got.extend(ep.recv_frame(peer, 1).unwrap());
                        }
                        got
                    })
                })
                .collect();
            handles.into_iter().map(|h| h.join().unwrap()).collect()
        });
        assert_eq!(results[0], [[1u8; 10], [2u8; 10]].concat());
        assert_eq!(results[1], [[0u8; 10], [2u8; 10]].concat());
        assert_eq!(results[2], [[0u8; 10], [1u8; 10]].concat());
        assert_eq!(stats.total_frames(), 6);
        assert_eq!(stats.total_bytes(), 6 * (FRAME_HEADER_BYTES as u64 + 10));
        assert_eq!(stats.bytes_sent_by(1), 2 * (FRAME_HEADER_BYTES as u64 + 10));
        assert_eq!(stats.frames_sent_by(2, |tag| tag == 1), 2);
    }

    #[test]
    fn channel_mesh_reports_closed_links_timeouts_and_raw_garbage() {
        let (mut endpoints, _) = InMemoryWireMesh::connect(3, SESSION);
        let mut carol = endpoints.pop().unwrap();
        let mut bob = endpoints.pop().unwrap();
        let mut alice = endpoints.pop().unwrap();
        alice.set_timeout(std::time::Duration::from_millis(20));
        assert_eq!(
            alice.recv_frame(1, 1),
            Err(TransportError::Timeout { peer: 1 })
        );
        bob.send_raw(0, b"not a frame".to_vec()).unwrap();
        assert_eq!(alice.recv_frame(1, 1), Err(TransportError::Malformed));
        carol.send_frame(0, 4, b"last words").unwrap();
        drop(carol);
        assert_eq!(alice.recv_frame(2, 4), Ok(b"last words".to_vec()));
        assert_eq!(
            alice.recv_frame(2, 4),
            Err(TransportError::Closed { peer: 2 })
        );
        assert_eq!(
            alice.send_frame(2, 4, b"anyone?"),
            Err(TransportError::Closed { peer: 2 })
        );
        assert_eq!(
            alice.recv_frame(0, 1),
            Err(TransportError::UnknownPeer { peer: 0 })
        );
    }

    #[test]
    fn socket_mesh_carries_the_same_frames() {
        let (endpoints, stats) = TcpWireMesh::loopback(3, SESSION).unwrap();
        let big = vec![0xA5u8; 20_000];
        let results: Vec<usize> = std::thread::scope(|scope| {
            let handles: Vec<_> = endpoints
                .into_iter()
                .map(|mut ep| {
                    let big = &big;
                    scope.spawn(move || {
                        let me = ep.party();
                        for peer in (0..3).filter(|&p| p != me) {
                            ep.send_frame(peer, 2, big).unwrap();
                            ep.send_frame(peer, 3, &[me as u8]).unwrap();
                        }
                        let mut total = 0;
                        for peer in (0..3).filter(|&p| p != me) {
                            let payload = ep.recv_frame(peer, 2).unwrap();
                            assert_eq!(&payload, big);
                            assert_eq!(ep.recv_frame(peer, 3).unwrap(), vec![peer as u8]);
                            total += payload.len();
                        }
                        total
                    })
                })
                .collect();
            handles.into_iter().map(|h| h.join().unwrap()).collect()
        });
        assert_eq!(results, vec![40_000; 3]);
        assert_eq!(
            stats.total_bytes(),
            6 * (2 * FRAME_HEADER_BYTES as u64 + 20_001)
        );
    }
}

#[cfg(test)]
mod frame_cap_tests {
    use super::*;
    #[test]
    fn oversized_header_is_rejected_without_payload() {
        let mut raw = [0u8; FRAME_HEADER_BYTES];
        raw[..4].copy_from_slice(&FRAME_MAGIC);
        raw[52..56].copy_from_slice(&((MAX_FRAME_PAYLOAD + 1) as u32).to_be_bytes());
        assert_eq!(decode_header(&raw), Err(TransportError::Malformed));
        raw[52..56].copy_from_slice(&(MAX_FRAME_PAYLOAD as u32).to_be_bytes());
        assert_eq!(
            decode_header(&raw).unwrap().1 + FRAME_HEADER_BYTES,
            MAX_WIRE_FRAME_BYTES
        );
    }
}

#[cfg(test)]
mod authenticated_tests {
    use super::*;

    #[test]
    fn rejected_packet_and_timeout_do_not_latch_confidential_link() {
        let (mut endpoints, _) = InMemoryWireMesh::connect(2, [0x39; 32]);
        let mut bob = endpoints.pop().unwrap();
        bob.set_timeout(std::time::Duration::from_millis(10));
        let alice = endpoints.pop().unwrap();
        let mut alice = ConfidentialWireChannel::new(alice, [2; 32], vec![[3; 32]; 2]).unwrap();
        let mut bob = ConfidentialWireChannel::new(bob, [2; 32], vec![[3; 32]; 2]).unwrap();
        assert_eq!(
            bob.recv_frame(0, 7),
            Err(TransportError::Timeout { peer: 0 })
        );
        let valid = alice
            .inner
            .seal(1, 7, b"retry authenticated packet")
            .unwrap();
        let mut invalid = valid.clone();
        *invalid.last_mut().unwrap() ^= 1;
        // Inject without advancing the honest sender's outer sequence. The old
        // double sequencer accepted this envelope, then permanently rejected the
        // real sequence-0 packet even though its inner MAC was valid.
        let injected = encode_frame(
            &FrameHeader {
                session_id: [0x39; 32],
                from: 0,
                to: 1,
                round_tag: 7,
                seq: 0,
            },
            &invalid,
        )
        .unwrap();
        alice.inner.transport.send_raw(1, injected).unwrap();
        assert_eq!(
            bob.recv_frame(0, 7),
            Err(TransportError::AuthenticationFailed)
        );
        // Transport retransmission retains the authenticated packet's sequence/key.
        alice.inner.transport.send_frame(1, 7, &valid).unwrap();
        assert_eq!(bob.recv_frame(0, 7).unwrap(), b"retry authenticated packet");
        alice.send_frame(1, 8, b"following ratchet step").unwrap();
        assert_eq!(bob.recv_frame(0, 8).unwrap(), b"following ratchet step");
    }

    #[test]
    fn encrypted_frames_hide_payload_and_reject_mode_and_key_confusion() {
        let (mut endpoints, _) = InMemoryWireMesh::connect(2, [1; 32]);
        let bob = endpoints.pop().unwrap();
        let alice = endpoints.pop().unwrap();
        let mut alice =
            MacSealedWireChannel::new_encrypted(alice, [2; 32], vec![[3; 32]; 2]).unwrap();
        let mut bob = MacSealedWireChannel::new_encrypted(bob, [2; 32], vec![[3; 32]; 2]).unwrap();
        let payload = [0x5A; 300];
        let raw = alice.seal(1, 1, &payload).unwrap();
        assert_ne!(&raw[FRAME_HEADER_BYTES + 1..raw.len() - 32], &payload);
        for index in 0..raw.len() {
            let mut tampered = raw.clone();
            tampered[index] ^= 1;
            assert!(bob.open(0, 1, &tampered).is_err());
        }
        assert_ne!(alice.keys[1], bob.recv_keys[0]);
        bob.encrypted = false;
        assert_eq!(
            bob.open(0, 1, &raw),
            Err(TransportError::AuthenticationFailed)
        );
        bob.encrypted = true;
        bob.recv_keys[0][0] ^= 1;
        assert_eq!(
            bob.open(0, 1, &raw),
            Err(TransportError::AuthenticationFailed)
        );
        bob.recv_keys[0][0] ^= 1;
        assert_eq!(bob.open(0, 1, &raw).unwrap(), payload);
        assert_eq!(alice.keys[1], bob.recv_keys[0]);
        assert_ne!(alice.keys[1], alice.recv_keys[1]);
        assert!(bob.open(0, 1, &raw).is_err());
        alice.send_frame(1, 2, &payload).unwrap();
        assert_eq!(bob.recv_frame(0, 2).unwrap(), payload);
    }

    #[test]
    fn authenticated_tcp_roundtrip_and_adversarial_frames() {
        let (mut endpoints, _) = TcpWireMesh::loopback(2, [1; 32]).unwrap();
        let bob = endpoints.pop().unwrap();
        let alice = endpoints.pop().unwrap();
        let mut alice = MacSealedWireChannel::new(alice, [2; 32], vec![[3; 32]; 2]).unwrap();
        let mut bob = MacSealedWireChannel::new(bob, [2; 32], vec![[3; 32]; 2]).unwrap();
        alice.send_frame(1, 7, b"share").unwrap();
        assert_eq!(bob.recv_frame(0, 7).unwrap(), b"share");
        let valid = alice.seal(1, 7, b"next").unwrap();
        for index in 0..valid.len() {
            let mut tampered = valid.clone();
            tampered[index] ^= 1;
            assert_eq!(
                bob.open(0, 7, &tampered),
                Err(TransportError::AuthenticationFailed)
            );
        }
        assert_eq!(bob.open(0, 7, &valid).unwrap(), b"next");
        assert!(matches!(
            bob.open(0, 7, &valid),
            Err(TransportError::SequenceMismatch { .. })
        ));
        alice.sequencer = FrameSequencer::new([9; 32], 0, 2);
        let foreign = alice.seal(1, 7, b"foreign").unwrap();
        assert_eq!(
            bob.open(0, 7, &foreign),
            Err(TransportError::SessionMismatch)
        );
    }

    #[test]
    fn confidential_wire_channel_blocks_reflection_u64_max_wraparound_and_nonce_reuse() {
        let (mut endpoints, _) = InMemoryWireMesh::connect(2, [4; 32]);
        let _bob_ep = endpoints.pop().unwrap();
        let alice_ep = endpoints.pop().unwrap();
        let shared = vec![[0x5C; 32]; 2];

        // Even unencrypted `MacSealedWireChannel::new` derives distinct directional keys
        // and wipes the local party slot.
        let plain_alice = MacSealedWireChannel::new(alice_ep, [5; 32], shared.clone()).unwrap();
        assert_eq!(plain_alice.keys[0], [0u8; 32]);
        assert_eq!(plain_alice.recv_keys[0], [0u8; 32]);
        assert_ne!(plain_alice.keys[1], plain_alice.recv_keys[1]);
        assert_ne!(
            derive_enc_subkey(&plain_alice.keys[1]),
            derive_mac_subkey(&plain_alice.keys[1]),
        );

        let (mut endpoints, _) = InMemoryWireMesh::connect(2, [4; 32]);
        let bob_ep = endpoints.pop().unwrap();
        let alice_ep = endpoints.pop().unwrap();
        let mut alice = ConfidentialWireChannel::new(alice_ep, [6; 32], shared.clone()).unwrap();
        let mut bob = ConfidentialWireChannel::new(bob_ep, [6; 32], shared).unwrap();

        // 1. Reflection attack: Alice's outbound frame cannot be fed back into Alice's inbound
        //    `open` (neither as self-peer 0 nor masquerading as peer 1, even if header route bytes
        //    are flipped).
        let outbound = alice.seal(1, 11, b"secret share").unwrap();
        assert_eq!(
            alice.open(0, 11, &outbound),
            Err(TransportError::UnknownPeer { peer: 0 })
        );
        assert_eq!(
            alice.open(1, 11, &outbound),
            Err(TransportError::AuthenticationFailed)
        );
        let mut swapped_route = outbound.clone();
        swapped_route[36..38].copy_from_slice(&1u16.to_be_bytes());
        swapped_route[38..40].copy_from_slice(&0u16.to_be_bytes());
        assert_eq!(
            alice.open(1, 11, &swapped_route),
            Err(TransportError::AuthenticationFailed)
        );
        assert_eq!(bob.open(0, 11, &outbound).unwrap(), b"secret share");

        // 2. Oversized `seal` error neither advances sequence nor mutates ratchet key, so the
        //    subsequent valid frame synchronizes cleanly without nonce reuse.
        let key_before_err = alice.inner.keys[1];
        let seq_before_err = alice.inner.sequencer.send_seq[1];
        assert_eq!(
            alice.seal(1, 12, &vec![0u8; MAX_FRAME_PAYLOAD]),
            Err(TransportError::PayloadTooLarge)
        );
        assert_eq!(alice.inner.keys[1], key_before_err);
        assert_eq!(alice.inner.sequencer.send_seq[1], seq_before_err);
        let valid_after_err = alice.seal(1, 12, b"clean").unwrap();
        assert_eq!(bob.open(0, 12, &valid_after_err).unwrap(), b"clean");

        // 3. Sequence counter at `u64::MAX` fails closed with `SequenceExhausted` on both send
        //    and receive without wrapping to `0`.
        alice.inner.sequencer.send_seq[1] = u64::MAX - 1;
        bob.inner.sequencer.recv_seq[0] = u64::MAX - 1;
        let penultimate = alice.seal(1, 13, b"penultimate").unwrap();
        assert_eq!(alice.inner.sequencer.send_seq[1], u64::MAX);
        assert_eq!(bob.open(0, 13, &penultimate).unwrap(), b"penultimate");
        assert_eq!(bob.inner.sequencer.recv_seq[0], u64::MAX);

        assert_eq!(
            alice.seal(1, 14, b"overflow"),
            Err(TransportError::SequenceExhausted)
        );
        assert_eq!(alice.inner.sequencer.send_seq[1], u64::MAX);

        // Craft an authenticated frame at `seq = u64::MAX` to verify `open` also refuses wraparound.
        let mut raw_max = encode_frame(
            &FrameHeader {
                session_id: [6; 32],
                from: 0,
                to: 1,
                round_tag: 14,
                seq: u64::MAX,
            },
            &[1u8, b'x'],
        )
        .unwrap();
        let enc_key = derive_enc_subkey(&alice.inner.keys[1]);
        let (hdr, body) = raw_max.split_at_mut(FRAME_HEADER_BYTES);
        wire_crypt(&enc_key, hdr, &mut body[1..]);
        let mac_key = derive_mac_subkey(&alice.inner.keys[1]);
        let tag = wire_mac(&mac_key, &raw_max);
        raw_max.extend_from_slice(&tag);
        assert_eq!(
            bob.open(0, 14, &raw_max),
            Err(TransportError::SequenceExhausted)
        );
        assert_eq!(bob.inner.sequencer.recv_seq[0], u64::MAX);

        // 4. Underlying transport send error permanently closes that peer link on `ConfidentialWireChannel`.
        drop(bob);
        assert_eq!(
            alice.send_frame(1, 15, b"gone"),
            Err(TransportError::SequenceExhausted)
        );
        alice.inner.sequencer.send_seq[1] = 10;
        assert_eq!(
            alice.send_frame(1, 15, b"gone"),
            Err(TransportError::Closed { peer: 1 })
        );
        assert_eq!(
            alice.seal(1, 15, b"after transport failure"),
            Err(TransportError::Closed { peer: 1 })
        );
    }

    #[test]
    fn sealed_open_rejects_every_truncation_and_extension_without_advancing_state() {
        for encrypted in [false, true] {
            let (mut endpoints, _) = InMemoryWireMesh::connect(2, [1; 32]);
            let bob = endpoints.pop().unwrap();
            let alice = endpoints.pop().unwrap();
            let keys = vec![[3; 32]; 2];
            let (mut alice, mut bob) = if encrypted {
                (
                    MacSealedWireChannel::new_encrypted(alice, [2; 32], keys.clone()).unwrap(),
                    MacSealedWireChannel::new_encrypted(bob, [2; 32], keys).unwrap(),
                )
            } else {
                (
                    MacSealedWireChannel::new(alice, [2; 32], keys.clone()).unwrap(),
                    MacSealedWireChannel::new(bob, [2; 32], keys).unwrap(),
                )
            };
            let raw = alice.seal(1, 7, b"abc").unwrap();
            for len in 0..raw.len() {
                assert!(
                    bob.open(0, 7, &raw[..len]).is_err(),
                    "prefix {len} enc={encrypted}"
                );
            }
            for extra in 1..=33 {
                let mut longer = raw.clone();
                longer.resize(raw.len() + extra, 0);
                assert!(
                    bob.open(0, 7, &longer).is_err(),
                    "extended {extra} enc={encrypted}"
                );
            }
            assert_eq!(bob.sequencer.recv_seq[0], 0);
            assert_eq!(bob.open(0, 7, &raw).unwrap(), b"abc");
        }
    }

    /// A peer holding the link key can MAC any bytes: the strict decode after the MAC must
    /// still refuse lying length fields and an empty body without panicking or advancing.
    #[test]
    fn authenticated_but_malformed_inner_frames_are_refused_after_the_mac() {
        let (mut endpoints, _) = InMemoryWireMesh::connect(2, [1; 32]);
        let bob = endpoints.pop().unwrap();
        let alice = endpoints.pop().unwrap();
        let mut alice = MacSealedWireChannel::new(alice, [2; 32], vec![[3; 32]; 2]).unwrap();
        let mut bob = MacSealedWireChannel::new(bob, [2; 32], vec![[3; 32]; 2]).unwrap();
        let honest = alice.seal(1, 7, b"abc").unwrap();
        let frame = &honest[..honest.len() - 32];
        let remac = |inner: &[u8]| {
            let mut mac_key = derive_mac_subkey(&alice.keys[1]);
            let mut out = inner.to_vec();
            out.extend_from_slice(&wire_mac(&mac_key, inner));
            qsag_core::wipe::wipe_bytes32(&mut mac_key);
            out
        };
        for lie in [0u32, 1, 3, 5, u32::MAX, MAX_FRAME_PAYLOAD as u32 + 1] {
            let mut inner = frame.to_vec();
            inner[52..56].copy_from_slice(&lie.to_be_bytes());
            assert_eq!(
                bob.open(0, 7, &remac(&inner)),
                Err(TransportError::Malformed)
            );
        }
        let header = decode_frame(frame).unwrap().0;
        let empty_body = encode_frame(&header, &[]).unwrap();
        assert!(bob.open(0, 7, &remac(&empty_body)).is_err());
        assert_eq!(bob.sequencer.recv_seq[0], 0);
        assert_eq!(bob.open(0, 7, &honest).unwrap(), b"abc");
    }

    #[test]
    fn header_decoders_never_panic_on_arbitrary_prefixes() {
        let mut x = 0x9E37_79B9u32;
        let mut garbage = [0u8; FRAME_HEADER_BYTES + 40];
        for b in garbage.iter_mut() {
            x ^= x << 13;
            x ^= x >> 17;
            x ^= x << 5;
            *b = x as u8;
        }
        garbage[..4].copy_from_slice(&FRAME_MAGIC);
        for len in 0..=garbage.len() {
            let _ = decode_header(&garbage[..len]);
            assert!(decode_frame(&garbage[..len]).is_err(), "len={len}");
        }
    }
}
