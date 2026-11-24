//! Framed communication between enrolled parties. Protocols requiring secrecy must use
//! confidential authenticated links. Transport sessions bind the roster and reject replay.
use crate::wipe::SecretBuffer;
use alloc::vec::Vec;
use core::fmt;

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

    /// Exchange one frame per peer, in sender order, including the local slot.
    /// Complementary send/receive order supports bounded, blocking links.
    fn exchange_frames(
        &mut self,
        tag: u32,
        frames: &[Vec<u8>],
    ) -> Result<Vec<Vec<u8>>, TransportError> {
        let local = self.party();
        if local >= self.parties() || frames.len() != self.parties() {
            return Err(TransportError::RouteMismatch);
        }
        let mut received = SecretBuffer(Vec::with_capacity(frames.len()));
        for (peer, frame) in frames.iter().enumerate() {
            let message = if peer == local {
                frame.clone()
            } else if peer < local {
                let message = SecretBuffer(self.recv_frame(peer, tag)?);
                self.send_frame(peer, tag, frame)?;
                message.into_inner()
            } else {
                self.send_frame(peer, tag, frame)?;
                self.recv_frame(peer, tag)?
            };
            received.push(message);
        }
        Ok(received.into_inner())
    }

    /// Consistent authenticated broadcast with abort. Every accepting endpoint checks
    /// all peers' digests of the entire sender-ordered transcript before returning it.
    fn broadcast(&mut self, tag: u32, payload: &[u8]) -> Result<Vec<Vec<u8>>, TransportError> {
        use crate::sponge::keccak::cshake256_32_multi_frame;
        let copies = SecretBuffer(alloc::vec![payload.to_vec(); self.parties()]);
        let received = SecretBuffer(self.exchange_frames(tag, &copies)?);
        let fields: Vec<_> = received.iter().map(Vec::as_slice).collect();
        let digest = cshake256_32_multi_frame(b"QSAG.WIRE.BROADCAST.V1", &fields);
        let echoes = self.exchange_frames(tag, &alloc::vec![digest.to_vec(); self.parties()])?;
        if echoes.iter().any(|echo| echo != &digest) {
            return Err(TransportError::AuthenticationFailed);
        }
        Ok(received.into_inner())
    }

    /// Salted commit-before-open on the broadcast channel. Callers supply a fresh
    /// private salt and a binding for the protocol session and operation.
    fn commit_open(
        &mut self,
        tag: u32,
        binding: &[u8; 32],
        salt: [u8; 32],
        payload: &[u8],
    ) -> Result<Vec<Vec<u8>>, TransportError> {
        use crate::sponge::keccak::cshake256_32_multi_frame;
        let size = payload
            .len()
            .checked_add(salt.len())
            .ok_or(TransportError::PayloadTooLarge)?;
        let mut opening = SecretBuffer(Vec::with_capacity(size));
        opening.extend_from_slice(&salt);
        opening.extend_from_slice(payload);
        let commitment = |peer: usize, row: &[u8]| {
            cshake256_32_multi_frame(
                b"QSAG.WIRE.COMMIT.V1",
                &[
                    binding,
                    &tag.to_be_bytes(),
                    &(peer as u64).to_be_bytes(),
                    row,
                ],
            )
        };
        let commits = self.broadcast(tag, &commitment(self.party(), &opening))?;
        let mut rows = SecretBuffer(self.broadcast(tag, &opening)?);
        if rows.len() != self.parties() || commits.len() != rows.len() {
            return Err(TransportError::Malformed);
        }
        for (i, (row, c)) in rows.iter_mut().zip(commits).enumerate() {
            if row.len() < 32 || c != commitment(i, row) {
                return Err(TransportError::AuthenticationFailed);
            }
            let payload = row[32..].to_vec();
            crate::wipe::wipe(row);
            *row = payload;
        }
        Ok(rows.into_inner())
    }
}
