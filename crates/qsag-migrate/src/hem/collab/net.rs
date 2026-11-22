//! Message transport between custodians: confidential, authenticated pairwise links.
//!
//! A [`Transport`] gives one custodian an ordered, reliable byte-message link to every
//! other custodian. The only implementation is [`Framed`], which runs the workspace's
//! sealed channel (`qsag_quorum::wire_channel::ConfidentialWireChannel`) over one raw
//! [`Link`] per peer. A message is cut into fragments of at most [`MAX_FRAGMENT_BYTES`];
//! each fragment is `more[1] || data` (`more` is 1 on every fragment but the last, and a
//! fragment with `more = 1` is full) and travels in one sealed frame
//!
//! ```text
//! "QSWF" || session[32] || from_be[2] || to_be[2] || round_tag_be[4] || seq_be[8]
//!        || len_be[4] || 0x01 || deployment_id[32] || ciphertext(fragment) || tag[32]
//! ```
//!
//! with `round_tag` = [`ROUND_TAG`]. There is no plaintext transport in this module.
//!
//! # What the channel guarantees
//!
//! Against anyone who does not hold the pairwise secret of a link, and who may read,
//! alter, drop, replay, reorder and inject bytes on every link:
//!
//! * **Confidentiality.** Fragments are encrypted with a cSHAKE256 keystream keyed by a
//!   per-direction chain key that is advanced, and its predecessor erased, after every
//!   frame. The header (session, parties, sequence number, length) is in clear: message
//!   lengths, timing and who talks to whom are visible.
//! * **Integrity.** Encrypt-then-MAC: a 32-byte cSHAKE256 tag under a separate subkey
//!   covers the whole frame, header included, and is checked in constant time before
//!   anything is parsed or decrypted. [`Transport::recv`] returns only bytes the peer
//!   sealed for this party, this session and this position of the link.
//! * **Replay and reorder rejection.** A frame is accepted only with the next sequence
//!   number of its directed link, and the keys of that position exist only until it is
//!   used. A replayed, reordered or dropped-then-skipped frame is refused. A refused
//!   frame changes no state, so the honest frame that follows it is still accepted and
//!   a message whose fragments are interleaved with injected frames is reassembled
//!   intact or not at all.
//! * **Direction and link separation.** The keys of `a -> b` are derived from the
//!   pairwise secret, the session id and the ordered pair `(a, b)`. A frame reflected to
//!   its sender, delivered to a third custodian, presented as coming from another peer
//!   or taken from another session fails authentication even when every pair was
//!   provisioned with the same secret.
//!
//! It does not hide the traffic pattern, it does not survive an attacker who can drop
//! frames (the session aborts), and it authenticates a link, not a statement: the peer
//! itself can send anything, which is what the engine's MACs are for.
//!
//! # What it assumes
//!
//! * **Pairwise secrets provisioned out of band.** `keys[p]` is a uniform 32-byte secret
//!   known to this custodian and custodian `p` only. This module contains no key
//!   exchange. A deployment takes the secret from what its custodians already have: a
//!   key enrolled for each pair when the custody group is formed, or the exported key
//!   of the mutually authenticated key agreement its operators already run between the
//!   custodians' hosts (a post-quantum one if the witness must stay private from a
//!   later quantum adversary), bound to both custodians' identities. The same long-term
//!   secret may serve many sessions, because every key in use is derived from it
//!   together with the session id and the direction; whoever keeps the long-term
//!   secret can re-derive the keys of past sessions, so erase it or rotate it when
//!   earlier sessions must stay private after a later compromise.
//! * **A fresh session id per mesh.** Sequence numbers start at zero whenever endpoints
//!   are created. Two meshes with the same pairwise secret and the same session id use
//!   the same keystream, so the session id must never repeat for a pair (take it from a
//!   transcript that includes a nonce from every custodian).
//! * **Reliable ordered links.** A [`Link`] delivers whole frames in order, like a
//!   thread channel or a TCP stream.

use alloc::vec::Vec;

use qsag_quorum::wire_channel::{
    self as wire, ConfidentialWireChannel, TransportError, WireTransport,
};

/// Round tag of every sealed frame of this transport (`"QSCF"`). It is MAC-bound, so a
/// frame of another protocol run over the same channel construction is not a frame here.
pub const ROUND_TAG: u32 = u32::from_be_bytes(*b"QSCF");
/// Largest frame a [`Link`] is asked to carry.
pub const MAX_SEALED_FRAME_BYTES: usize = wire::MAX_FRAME_PAYLOAD;
/// Bytes a sealed frame adds to its fragment: header, mode byte and tag.
pub const SEALED_FRAME_OVERHEAD_BYTES: usize = wire::SEALED_FRAME_OVERHEAD;
/// Largest piece of a message in one sealed frame.
pub const MAX_FRAGMENT_BYTES: usize = MAX_SEALED_FRAME_BYTES - SEALED_FRAME_OVERHEAD_BYTES - 1;
/// Largest message of one [`Transport::send`].
pub const MAX_MESSAGE_BYTES: usize = 1 << 30;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NetError {
    /// The link to `peer` is closed, or its sequence space is used up.
    Closed {
        peer: usize,
    },
    /// `peer` is the local party or not a party.
    UnknownPeer {
        peer: usize,
    },
    /// What arrived from `peer` is not the next sealed frame of that link: it fails
    /// authentication (altered, wrong key, wrong direction, another link or session), is
    /// replayed or out of order, or is an authentic frame that is not a fragment.
    BadFrame {
        peer: usize,
    },
    PayloadTooLarge,
}

/// One custodian's links to the others.
pub trait Transport {
    fn parties(&self) -> usize;
    fn me(&self) -> usize;
    fn send(&mut self, to: usize, payload: &[u8]) -> Result<(), NetError>;
    /// Blocks until the next message from `from` arrives.
    fn recv(&mut self, from: usize) -> Result<Vec<u8>, NetError>;
}

/// A [`Link`] can carry no more frames.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LinkClosed;

/// A raw bidirectional pipe to one peer that carries whole sealed frames, in order. It
/// sees ciphertext only and is trusted for nothing but delivery.
pub trait Link {
    /// `frame` has at most [`MAX_SEALED_FRAME_BYTES`] bytes.
    fn send_frame(&mut self, frame: &[u8]) -> Result<(), LinkClosed>;
    /// The next frame, exactly the bytes one `send_frame` of the peer was given.
    fn recv_frame(&mut self) -> Result<Vec<u8>, LinkClosed>;
}

/// The raw links of one party as the carrier beneath the sealed channel. It moves sealed
/// frames and checks nothing: every check is the channel's, on authenticated bytes.
struct Links<L: Link> {
    me: usize,
    /// `links[p]` for every `p != me`; the slot of `me` is `None`.
    links: Vec<Option<L>>,
}

impl<L: Link> Links<L> {
    fn link(&mut self, peer: usize) -> Result<&mut L, TransportError> {
        self.links
            .get_mut(peer)
            .and_then(Option::as_mut)
            .ok_or(TransportError::UnknownPeer { peer })
    }
}

impl<L: Link> WireTransport for Links<L> {
    fn party(&self) -> usize {
        self.me
    }

    fn parties(&self) -> usize {
        self.links.len()
    }

    fn send_frame(&mut self, to: usize, _round: u32, sealed: &[u8]) -> Result<(), TransportError> {
        self.link(to)?
            .send_frame(sealed)
            .map_err(|LinkClosed| TransportError::Closed { peer: to })
    }

    fn recv_frame(&mut self, from: usize, round: u32) -> Result<Vec<u8>, TransportError> {
        self.recv_authenticated_envelope(from, round)
    }

    fn recv_authenticated_envelope(
        &mut self,
        from: usize,
        _round: u32,
    ) -> Result<Vec<u8>, TransportError> {
        self.link(from)?
            .recv_frame()
            .map_err(|LinkClosed| TransportError::Closed { peer: from })
    }
}

fn net_error(e: TransportError, peer: usize) -> NetError {
    match e {
        TransportError::UnknownPeer { peer } => NetError::UnknownPeer { peer },
        TransportError::PayloadTooLarge => NetError::PayloadTooLarge,
        TransportError::Closed { .. }
        | TransportError::Timeout { .. }
        | TransportError::SequenceExhausted => NetError::Closed { peer },
        TransportError::Malformed
        | TransportError::SessionMismatch
        | TransportError::AuthenticationFailed
        | TransportError::RouteMismatch
        | TransportError::RoundTagMismatch { .. }
        | TransportError::SequenceMismatch { .. } => NetError::BadFrame { peer },
    }
}

/// The sealed [`Transport`] over one [`Link`] per peer; see the module documentation for
/// what it guarantees and assumes.
pub struct Framed<L: Link> {
    channel: ConfidentialWireChannel<Links<L>>,
    /// Fragments of the message being received from each peer.
    partial: Vec<Vec<u8>>,
}

impl<L: Link> Framed<L> {
    /// `links[p]` must be `Some` exactly for `p != me`, and `keys[p]` is the secret this
    /// party shares with `p` alone (`keys[me]` is ignored). `session` must be new for
    /// these keys. `keys` is erased before this returns.
    pub fn new(
        deployment_id: [u8; 32],
        session: [u8; 32],
        me: usize,
        links: Vec<Option<L>>,
        mut keys: Vec<[u8; 32]>,
    ) -> Option<Self> {
        let n = links.len();
        let shaped = n >= 2
            && n <= u16::MAX as usize
            && me < n
            && keys.len() == n
            && links
                .iter()
                .enumerate()
                .all(|(p, l)| l.is_some() == (p != me));
        if !shaped {
            keys.iter_mut().for_each(qsag_core::wipe::wipe_bytes32);
            return None;
        }
        let channel =
            ConfidentialWireChannel::new(Links { me, links }, deployment_id, session, keys).ok()?;
        Some(Self {
            channel,
            partial: (0..n).map(|_| Vec::new()).collect(),
        })
    }
}

impl<L: Link> Drop for Framed<L> {
    fn drop(&mut self) {
        qsag_core::wipe::wipe(&mut self.partial);
    }
}

impl<L: Link> Transport for Framed<L> {
    fn parties(&self) -> usize {
        self.channel.parties()
    }

    fn me(&self) -> usize {
        self.channel.party()
    }

    fn send(&mut self, to: usize, payload: &[u8]) -> Result<(), NetError> {
        if payload.len() > MAX_MESSAGE_BYTES {
            return Err(NetError::PayloadTooLarge);
        }
        let mut fragment = qsag_core::wipe::SecretScratch::with_capacity(1 + payload.len().min(MAX_FRAGMENT_BYTES));
        let mut rest = payload;
        let sent = loop {
            let (data, tail) = rest.split_at(rest.len().min(MAX_FRAGMENT_BYTES));
            fragment.clear();
            fragment.push(u8::from(!tail.is_empty()));
            fragment.extend_from_slice(data);
            if let Err(e) = self.channel.send_frame(to, ROUND_TAG, &fragment) {
                break Err(net_error(e, to));
            }
            if tail.is_empty() {
                break Ok(());
            }
            rest = tail;
        };
        sent
    }

    fn recv(&mut self, from: usize) -> Result<Vec<u8>, NetError> {
        loop {
            // A refused frame leaves the channel and `partial[from]` as they were.
            let mut fragment = self
                .channel
                .recv_frame(from, ROUND_TAG)
                .map_err(|e| net_error(e, from))?;
            let partial = &mut self.partial[from];
            let more = match fragment.split_first() {
                Some((&more, data))
                    if more <= 1
                        && (more == 0 || data.len() == MAX_FRAGMENT_BYTES)
                        && partial.len() + data.len() <= MAX_MESSAGE_BYTES =>
                {
                    qsag_core::wipe::secret_vec_extend_from_slice(partial, data);
                    Some(more == 1)
                }
                _ => None,
            };
            qsag_core::wipe::wipe_bytes(&mut fragment);
            match more {
                Some(true) => {}
                Some(false) => return Ok(core::mem::take(partial)),
                // Authentic and not a fragment: the peer left the protocol.
                None => {
                    qsag_core::wipe::wipe_bytes(partial);
                    partial.clear();
                    return Err(NetError::BadFrame { peer: from });
                }
            }
        }
    }
}

#[cfg(any(feature = "std", test))]
pub use with_std::*;

#[cfg(any(feature = "std", test))]
mod with_std {
    use super::*;
    use std::io::{Read, Write};
    use std::sync::mpsc::{Receiver, Sender, channel};

    /// A [`Link`] over a pair of thread channels.
    pub struct ChannelLink {
        tx: Sender<Vec<u8>>,
        rx: Receiver<Vec<u8>>,
    }

    impl Link for ChannelLink {
        fn send_frame(&mut self, frame: &[u8]) -> Result<(), LinkClosed> {
            self.tx.send(frame.to_vec()).map_err(|_| LinkClosed)
        }

        fn recv_frame(&mut self) -> Result<Vec<u8>, LinkClosed> {
            self.rx.recv().map_err(|_| LinkClosed)
        }
    }

    /// A [`Link`] over a byte stream such as a socket: every sealed frame is written as
    /// `len_be[4] || frame`.
    pub struct StreamLink<S: Read + Write>(pub S);

    impl<S: Read + Write> Link for StreamLink<S> {
        fn send_frame(&mut self, frame: &[u8]) -> Result<(), LinkClosed> {
            let len = u32::try_from(frame.len()).map_err(|_| LinkClosed)?;
            self.0
                .write_all(&len.to_be_bytes())
                .and_then(|()| self.0.write_all(frame))
                .and_then(|()| self.0.flush())
                .map_err(|_| LinkClosed)
        }

        fn recv_frame(&mut self) -> Result<Vec<u8>, LinkClosed> {
            let mut len = [0u8; 4];
            self.0.read_exact(&mut len).map_err(|_| LinkClosed)?;
            let len = u32::from_be_bytes(len) as usize;
            // An unauthenticated length: beyond the cap the frame boundary is lost.
            if len > MAX_SEALED_FRAME_BYTES {
                return Err(LinkClosed);
            }
            let mut frame = alloc::vec![0u8; len];
            self.0.read_exact(&mut frame).map_err(|_| LinkClosed)?;
            Ok(frame)
        }
    }

    /// The pairwise secret [`channel_mesh`] gives the pair `lo < hi`. Anyone who knows the
    /// session id can compute it.
    fn in_process_pairwise_key(session: &[u8; 32], lo: usize, hi: usize) -> [u8; 32] {
        let mut xof = qsag_core::sponge::keccak::Cshake256Xof::new(
            b"QSAG.MIGRATE.COLLAB.IN_PROCESS_LINK_KEY/v1",
        );
        xof.absorb(session);
        xof.absorb(&(lo as u64).to_be_bytes());
        xof.absorb(&(hi as u64).to_be_bytes());
        let mut key = [0u8; 32];
        xof.squeeze(&mut key);
        key
    }

    /// Sealed transports of `parties` custodians joined pairwise by thread channels, in
    /// party order, for tests and for custodians that are threads of one process. The
    /// pairwise secrets are derived from `session` alone, so they protect nothing once the
    /// frames leave the process: custodians on separate hosts call [`Framed::new`] with
    /// provisioned secrets.
    pub fn channel_mesh(session: [u8; 32], parties: usize) -> Vec<Framed<ChannelLink>> {
        let mut links: Vec<Vec<Option<ChannelLink>>> = (0..parties)
            .map(|_| (0..parties).map(|_| None).collect())
            .collect();
        let mut rows = links.as_mut_slice();
        let mut a = 0;
        while let Some((row_a, rest)) = rows.split_first_mut() {
            for (offset, row_b) in rest.iter_mut().enumerate() {
                let (tx_ab, rx_ab) = channel();
                let (tx_ba, rx_ba) = channel();
                row_a[a + 1 + offset] = Some(ChannelLink {
                    tx: tx_ab,
                    rx: rx_ba,
                });
                row_b[a] = Some(ChannelLink {
                    tx: tx_ba,
                    rx: rx_ab,
                });
            }
            rows = rest;
            a += 1;
        }
        links
            .into_iter()
            .enumerate()
            .map(|(me, l)| {
                let keys = (0..parties)
                    .map(|p| in_process_pairwise_key(&session, me.min(p), me.max(p)))
                    .collect();
                Framed::new([0xDA; 32], session, me, l, keys).expect("a full mesh")
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::VecDeque;
    use std::sync::{Arc, Mutex};

    /// The frames in flight on one directed link, readable and writable by the test.
    type Wire = Arc<Mutex<VecDeque<Vec<u8>>>>;

    /// A link whose two directions are queues the test can read, edit and feed. An empty
    /// queue reads as a closed link.
    struct TapLink {
        out: Wire,
        inp: Wire,
    }

    impl Link for TapLink {
        fn send_frame(&mut self, frame: &[u8]) -> Result<(), LinkClosed> {
            self.out.lock().unwrap().push_back(frame.to_vec());
            Ok(())
        }

        fn recv_frame(&mut self) -> Result<Vec<u8>, LinkClosed> {
            self.inp.lock().unwrap().pop_front().ok_or(LinkClosed)
        }
    }

    /// `parties` sealed endpoints over tapped links and `wires[from][to]`. `key(a, b)` is
    /// the secret party `a` holds for its link with `b`.
    fn tap_mesh(
        session: [u8; 32],
        parties: usize,
        key: impl Fn(usize, usize) -> [u8; 32],
    ) -> (Vec<Framed<TapLink>>, Vec<Vec<Wire>>) {
        let wires: Vec<Vec<Wire>> = (0..parties)
            .map(|_| (0..parties).map(|_| Wire::default()).collect())
            .collect();
        let mesh = (0..parties)
            .map(|me| {
                let links = (0..parties)
                    .map(|p| {
                        (p != me).then(|| TapLink {
                            out: wires[me][p].clone(),
                            inp: wires[p][me].clone(),
                        })
                    })
                    .collect();
                let keys = (0..parties).map(|p| key(me, p)).collect();
                Framed::new([0xDA; 32], session, me, links, keys).unwrap()
            })
            .collect();
        (mesh, wires)
    }

    fn take(wire: &Wire) -> Vec<u8> {
        wire.lock().unwrap().pop_front().expect("a frame in flight")
    }

    fn put(wire: &Wire, frame: &[u8]) {
        wire.lock().unwrap().push_back(frame.to_vec());
    }

    const SESSION: [u8; 32] = [7u8; 32];
    const BAD: Result<Vec<u8>, NetError> = Err(NetError::BadFrame { peer: 0 });

    /// Every pair holds the same secret, so only the derivation separates links.
    fn one_key(_: usize, _: usize) -> [u8; 32] {
        [0x5c; 32]
    }

    fn pattern(len: usize) -> Vec<u8> {
        (0..len).map(|i| (i * 131 + i / 251 + 17) as u8).collect()
    }

    #[test]
    fn a_payload_never_appears_in_clear_on_the_link() {
        let (mut mesh, wires) = tap_mesh(SESSION, 2, one_key);
        let payload = pattern(700);
        mesh[0].send(1, &payload).unwrap();
        mesh[0].send(1, &payload).unwrap();
        let first = take(&wires[0][1]);
        let second = take(&wires[0][1]);
        assert_eq!(first.len(), payload.len() + 1 + SEALED_FRAME_OVERHEAD_BYTES);
        for frame in [&first, &second] {
            for piece in payload.windows(8) {
                assert!(!frame.windows(8).any(|w| w == piece));
            }
        }
        // The same message twice is not the same ciphertext.
        let body = wire::FRAME_HEADER_BYTES + 33..first.len() - 32;
        assert!(
            first[body.clone()]
                .windows(8)
                .all(|w| !second[body.clone()].windows(8).any(|v| v == w))
        );
        put(&wires[0][1], &first);
        put(&wires[0][1], &second);
        assert_eq!(mesh[1].recv(0).unwrap(), payload);
        assert_eq!(mesh[1].recv(0).unwrap(), payload);
    }

    #[test]
    fn a_flipped_bit_anywhere_in_a_sealed_frame_is_refused() {
        let (mut mesh, wires) = tap_mesh(SESSION, 2, one_key);
        mesh[0].send(1, b"forty-two shares").unwrap();
        let frame = take(&wires[0][1]);
        for at in 0..frame.len() {
            let mut flipped = frame.clone();
            flipped[at] ^= 1 << (at % 8);
            put(&wires[0][1], &flipped);
            assert_eq!(mesh[1].recv(0), BAD, "byte {at}");
        }
        let mut longer = frame.clone();
        longer.push(0);
        put(&wires[0][1], &longer);
        assert_eq!(mesh[1].recv(0), BAD);
        put(&wires[0][1], &frame[..frame.len() - 1]);
        assert_eq!(mesh[1].recv(0), BAD);
        // None of the refusals moved the link.
        put(&wires[0][1], &frame);
        assert_eq!(mesh[1].recv(0).unwrap(), b"forty-two shares");
    }

    #[test]
    fn replayed_and_reordered_frames_are_refused() {
        let (mut mesh, wires) = tap_mesh(SESSION, 2, one_key);
        mesh[0].send(1, b"one").unwrap();
        mesh[0].send(1, b"two").unwrap();
        let one = take(&wires[0][1]);
        let two = take(&wires[0][1]);
        put(&wires[0][1], &two);
        assert_eq!(mesh[1].recv(0), BAD);
        put(&wires[0][1], &one);
        assert_eq!(mesh[1].recv(0).unwrap(), b"one");
        put(&wires[0][1], &one);
        assert_eq!(mesh[1].recv(0), BAD);
        put(&wires[0][1], &two);
        assert_eq!(mesh[1].recv(0).unwrap(), b"two");
        put(&wires[0][1], &two);
        assert_eq!(mesh[1].recv(0), BAD);
        put(&wires[0][1], &one);
        assert_eq!(mesh[1].recv(0), BAD);
    }

    #[test]
    fn frames_on_the_wrong_link_direction_or_session_are_refused() {
        let (mut mesh, wires) = tap_mesh(SESSION, 3, one_key);
        mesh[0].send(1, b"for b only").unwrap();
        let frame = take(&wires[0][1]);
        // Delivered to c on its link from a.
        put(&wires[0][2], &frame);
        assert_eq!(mesh[2].recv(0), BAD);
        // Delivered to b on its link from c.
        put(&wires[2][1], &frame);
        assert_eq!(mesh[1].recv(2), Err(NetError::BadFrame { peer: 2 }));
        // Reflected to a on its link from b.
        put(&wires[1][0], &frame);
        assert_eq!(mesh[0].recv(1), Err(NetError::BadFrame { peer: 1 }));
        // Relabelled as b -> a and reflected.
        let mut relabelled = frame.clone();
        relabelled[36..38].copy_from_slice(&1u16.to_be_bytes());
        relabelled[38..40].copy_from_slice(&0u16.to_be_bytes());
        put(&wires[1][0], &relabelled);
        assert_eq!(mesh[0].recv(1), Err(NetError::BadFrame { peer: 1 }));
        // The same parties and secrets in another session.
        let (mut other, other_wires) = tap_mesh([8u8; 32], 3, one_key);
        other[0].send(1, b"for b only").unwrap();
        put(&wires[0][1], &take(&other_wires[0][1]));
        assert_eq!(mesh[1].recv(0), BAD);
        put(&other_wires[0][1], &frame);
        assert_eq!(other[1].recv(0), BAD);
        // The frame is good where it belongs.
        put(&wires[0][1], &frame);
        assert_eq!(mesh[1].recv(0).unwrap(), b"for b only");
    }

    #[test]
    fn a_wrong_pairwise_key_is_refused() {
        // Party 1 holds a secret for party 0 that differs in one bit.
        let (mut mesh, _) = tap_mesh(SESSION, 2, |a, _| {
            let mut key = [0x5c; 32];
            key[31] ^= a as u8;
            key
        });
        mesh[0].send(1, b"hello").unwrap();
        assert_eq!(mesh[1].recv(0), BAD);
        mesh[1].send(0, b"hello").unwrap();
        assert_eq!(mesh[0].recv(1), Err(NetError::BadFrame { peer: 1 }));
        // The same exchange with the secret both hold.
        let (mut mesh, _) = tap_mesh(SESSION, 2, one_key);
        mesh[0].send(1, b"hello").unwrap();
        assert_eq!(mesh[1].recv(0).unwrap(), b"hello");
    }

    #[test]
    fn long_messages_are_fragmented_and_reassembled_or_refused_whole() {
        let (mut mesh, wires) = tap_mesh(SESSION, 2, one_key);
        let wire = &wires[0][1];
        let long = pattern(2 * MAX_FRAGMENT_BYTES + 5);
        mesh[0].send(1, &long).unwrap();
        mesh[0].send(1, b"").unwrap();
        mesh[0].send(1, &long[..MAX_FRAGMENT_BYTES]).unwrap();
        let frames: Vec<Vec<u8>> = wire.lock().unwrap().drain(..).collect();
        assert_eq!(
            frames.iter().map(Vec::len).collect::<Vec<_>>(),
            [
                MAX_SEALED_FRAME_BYTES,
                MAX_SEALED_FRAME_BYTES,
                5 + 1 + SEALED_FRAME_OVERHEAD_BYTES,
                1 + SEALED_FRAME_OVERHEAD_BYTES,
                MAX_SEALED_FRAME_BYTES,
            ]
        );
        // The middle fragment is dropped: the tail does not pass for a message.
        put(wire, &frames[0]);
        put(wire, &frames[2]);
        assert_eq!(mesh[1].recv(0), BAD);
        // An injected frame between fragments neither splits nor truncates the message.
        put(wire, &frames[2][..40]);
        put(wire, &frames[1]);
        assert_eq!(mesh[1].recv(0), BAD);
        put(wire, &frames[2]);
        assert!(mesh[1].recv(0).unwrap() == long);
        put(wire, &frames[3]);
        assert_eq!(mesh[1].recv(0).unwrap(), b"");
        put(wire, &frames[4]);
        assert!(mesh[1].recv(0).unwrap() == long[..MAX_FRAGMENT_BYTES]);
        assert_eq!(
            mesh[0].send(1, &alloc::vec![0u8; MAX_MESSAGE_BYTES + 1]),
            Err(NetError::PayloadTooLarge)
        );
    }

    #[test]
    fn endpoints_need_a_full_mesh_and_a_key_per_party() {
        let links = || {
            alloc::vec![
                None,
                Some(TapLink {
                    out: Wire::default(),
                    inp: Wire::default()
                })
            ]
        };
        assert!(Framed::new([0xDA; 32], SESSION, 0, links(), alloc::vec![[1; 32]; 2]).is_some());
        assert!(Framed::new([0xDA; 32], SESSION, 1, links(), alloc::vec![[1; 32]; 2]).is_none());
        assert!(Framed::new([0xDA; 32], SESSION, 0, links(), alloc::vec![[1; 32]; 1]).is_none());
        assert!(Framed::new([0xDA; 32], SESSION, 0, links(), alloc::vec![[1; 32]; 3]).is_none());
        assert!(
            Framed::<TapLink>::new(
                [0xDA; 32],
                SESSION,
                0,
                alloc::vec![None],
                alloc::vec![[1; 32]]
            )
            .is_none()
        );
    }

    #[test]
    fn channel_mesh_delivers_in_order_and_reports_a_closed_peer() {
        let mut mesh = channel_mesh([1u8; 32], 3);
        let mut c = mesh.pop().unwrap();
        let mut b = mesh.pop().unwrap();
        let mut a = mesh.pop().unwrap();
        assert_eq!((a.me(), a.parties()), (0, 3));
        a.send(1, b"one").unwrap();
        a.send(1, b"two").unwrap();
        c.send(1, b"from c").unwrap();
        assert_eq!(b.recv(0).unwrap(), b"one");
        assert_eq!(b.recv(2).unwrap(), b"from c");
        assert_eq!(b.recv(0).unwrap(), b"two");
        assert_eq!(a.send(0, b"self"), Err(NetError::UnknownPeer { peer: 0 }));
        assert_eq!(a.recv(3), Err(NetError::UnknownPeer { peer: 3 }));
        drop(c);
        assert_eq!(b.recv(2), Err(NetError::Closed { peer: 2 }));
        assert_eq!(b.send(2, b"anyone?"), Err(NetError::Closed { peer: 2 }));
    }

    /// A stream that records what is written to it.
    struct Recorded<S>(S, Arc<Mutex<Vec<u8>>>);

    impl<S: std::io::Read> std::io::Read for Recorded<S> {
        fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
            self.0.read(buf)
        }
    }

    impl<S: std::io::Write> std::io::Write for Recorded<S> {
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            let n = self.0.write(buf)?;
            self.1.lock().unwrap().extend_from_slice(&buf[..n]);
            Ok(n)
        }

        fn flush(&mut self) -> std::io::Result<()> {
            self.0.flush()
        }
    }

    /// Two custodians over a real socket pair. The bytes on the socket hide the payload,
    /// and a recorded frame written to the socket again is refused.
    #[test]
    fn stream_links_carry_sealed_frames_over_sockets() {
        use std::io::Write;
        use std::os::unix::net::UnixStream;
        let session = [3u8; 32];
        let keys = || alloc::vec![[0x77u8; 32]; 2];
        let (sa, sb) = UnixStream::pair().unwrap();
        let mut replayer = sa.try_clone().unwrap();
        let written = Arc::new(Mutex::new(Vec::new()));
        let sa = Recorded(sa, written.clone());
        let mut a = Framed::new(
            [0xDA; 32],
            session,
            0,
            alloc::vec![None, Some(StreamLink(sa))],
            keys(),
        )
        .unwrap();
        let mut b = Framed::new(
            [0xDA; 32],
            session,
            1,
            alloc::vec![Some(StreamLink(sb)), None],
            keys(),
        )
        .unwrap();
        let big = pattern(200_000);
        let sender = {
            let big = big.clone();
            std::thread::spawn(move || {
                a.send(1, b"hello, custodian").unwrap();
                a.send(1, &big).unwrap();
                a.recv(1)
            })
        };
        assert_eq!(b.recv(0).unwrap(), b"hello, custodian");
        assert_eq!(b.recv(0).unwrap(), big);
        b.send(0, b"done").unwrap();
        assert_eq!(sender.join().unwrap().unwrap(), b"done");

        let written = written.lock().unwrap().clone();
        let first = 4 + 16 + 1 + SEALED_FRAME_OVERHEAD_BYTES;
        assert_eq!(
            written.len(),
            first + 4 + 200_000 + 1 + SEALED_FRAME_OVERHEAD_BYTES
        );
        assert_eq!(written[..4], (first as u32 - 4).to_be_bytes());
        assert!(!written.windows(8).any(|w| w == b"hello, c"));
        assert!(!written.windows(8).any(|w| w == &big[..8]));
        replayer.write_all(&written[..first]).unwrap();
        assert_eq!(b.recv(0), BAD);
    }
}
