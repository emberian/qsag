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
pub const MAX_FRAME_PAYLOAD: usize = 1 << 26;
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
        let next = self.send_seq[to].checked_add(1).ok_or(TransportError::SequenceExhausted)?;
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
        self.recv_seq[from] = self.recv_seq[from].checked_add(1).ok_or(TransportError::SequenceExhausted)?;
        if header.round_tag != expected_round_tag {
            return Err(TransportError::RoundTagMismatch {
                expected: expected_round_tag,
                got: header.round_tag,
            });
        }
        Ok(payload.to_vec())
    }
}

fn wire_mac(key: &[u8; 32], frame: &[u8]) -> [u8; 32] {
    let mut xof = qsag_core::sponge::keccak::Cshake256Xof::new(b"QSAG.QUORUM.WIRE_MAC/v1");
    xof.absorb(key);
    xof.absorb(frame);
    let mut tag = [0; 32];
    xof.squeeze(&mut tag);
    tag
}

fn wire_crypt(key: &[u8; 32], header: &[u8], payload: &mut [u8]) {
    let mut xof = qsag_core::sponge::keccak::Cshake256Xof::new(b"QSAG.QUORUM.WIRE_STREAM/v1");
    xof.absorb(key);
    xof.absorb(header);
    let mut block = [0; 136];
    for chunk in payload.chunks_mut(block.len()) {
        xof.squeeze(&mut block[..chunk.len()]);
        for (byte, pad) in chunk.iter_mut().zip(&block) { *byte ^= pad; }
    }
    qsag_core::wipe::wipe_bytes(&mut block);
}

/// Authenticated framing over any mesh endpoint, including `TcpEndpoint`.
///
/// Provision the same independent 32-byte secret at both ends of each pair.
/// A session ID must be fresh whenever endpoints are recreated: counters cannot
/// be reset under the same key/session pair. Headers, lengths, rounds, direction,
/// sequence numbers and payloads are MAC-bound. Use `new_encrypted` for secret
/// shares; `new` authenticates while leaving payloads visible.
