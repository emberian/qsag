//! Interactive KOS OT adapter over established Ring-LWE base-OT channels.
//! Establish channels using the production `qsag_core::preprocessing` base-OT
//! round states, over mutually authenticated confidential transports. This
//! adapter inherits their security bounds; it makes no new QROM security claim.
use crate::{ParallelSeededDkgOt, ParallelSeededError};
use alloc::{collections::BTreeMap, collections::BTreeSet, vec::Vec};
use qsag_accel::ct::{ct_zeroize_bytes, ct_zeroize_u64s, ct_zeroize_u128s};
use qsag_accel::keccak::cshake256_framed_32;
use qsag_core::preprocessing::{
    KosOtChallengeMsg, KosOtProofMsg, KosOtUColsMsg, OtExtReceiverChannel, OtExtSenderChannel,
    OtPadPair, PartyPrivateRng,
};

/// Eight pads with the existing six-frame, fixed-width cSHAKE encoding.
fn pad_batch(
    context: &[u8; 32],
    sender: u16,
    receiver: u16,
    indices: [usize; 8],
    count: usize,
    raw: [&[u8; 48]; 8],
) -> [u128; 8] {
    const MIDSTATE: [u64; 25] =
        qsag_core::sponge::keccak::cshake256_static_midstate(b"QSAG.CUSTODY.OT.PAD.V1");
    // The six length-framed fields occupy 156 bytes, hence exactly two rate blocks.
    // Assemble their little-endian words directly, without eight temporary byte buffers.
    let mut prefix = MIDSTATE;
    prefix[0] ^= 6;
    prefix[1] ^= 48;
    prefix[8] ^= 32;
    for (word, bytes) in prefix[9..13]
        .iter_mut()
        .zip(context.as_chunks::<8>().0.iter())
    {
        *word ^= u64::from_le_bytes(*bytes);
    }
    prefix[13] ^= 2;
    prefix[14] ^= u64::from(sender.swap_bytes()) | (2 << 16);
    prefix[15] ^= (u64::from(receiver.swap_bytes()) << 16) | (8 << 32);
    let mut states = [prefix; 8];
    for lane in 0..8 {
        for (word, bytes) in states[lane][2..8]
            .iter_mut()
            .zip(raw[lane].as_chunks::<8>().0.iter())
        {
            *word ^= u64::from_le_bytes(*bytes);
        }
        // The big-endian index straddles the 136-byte rate boundary at offset 132.
        states[lane][16] ^= (indices[lane] as u64).swap_bytes() << 32;
    }
    qsag_core::sponge::keccak::keccak_f1600_batch(&mut states);
    let count = (count as u64).swap_bytes();
    for lane in 0..8 {
        states[lane][0] ^= ((indices[lane] as u64).swap_bytes() >> 32) | (8 << 32);
        states[lane][1] ^= count << 32;
        states[lane][2] ^= (count >> 32) | (4 << 32);
        states[lane][16] ^= 1 << 63;
    }
    qsag_core::sponge::keccak::keccak_f1600_batch(&mut states);
    let result =
        core::array::from_fn(|lane| states[lane][0] as u128 | ((states[lane][1] as u128) << 64));
    for state in &mut states {
        ct_zeroize_u64s(state);
    }
    result
}

pub enum CommittedOtMessage {
    Abort,
    Columns(KosOtUColsMsg),
    Challenge(KosOtChallengeMsg),
    Proof(KosOtProofMsg),
    Ciphertexts(Vec<[u128; 2]>),
}
/// Implement using a mutually authenticated channel. Bind endpoint IDs and the
/// full context to every frame, reject unexpected contexts and bound decoding
/// allocations before receiving a payload. No clear OT alternatives traverse it.
pub trait AuthenticatedOtWire {
    fn send(
        &mut self,
        peer: u16,
        context: [u8; 32],
        message: CommittedOtMessage,
    ) -> Result<(), ParallelSeededError>;
    fn receive(
        &mut self,
        peer: u16,
        context: [u8; 32],
    ) -> Result<CommittedOtMessage, ParallelSeededError>;
}

/// Per-custodian production OT engine. Owns uncloneable, direction-specific base
/// channels, local randomness, and replay state. Any protocol error poisons it.
pub struct CommittedCorrelatedOt<W> {
    party: u16,
    peers: BTreeMap<u16, (OtExtSenderChannel, OtExtReceiverChannel)>,
    used: BTreeSet<(u16, [u8; 32], bool)>,
    rng: PartyPrivateRng,
    wire: W,
    failed: bool,
}
fn invalid() -> ParallelSeededError {
    ParallelSeededError::InvalidThresholdParameters
}
const MAX_OTS: usize = 262_144;
impl<W: AuthenticatedOtWire> CommittedCorrelatedOt<W> {
    /// `entropy` must be fresh private CSPRNG output, never pair-shared entropy.
    pub fn new(
        party: u16,
        peers: Vec<(u16, OtExtSenderChannel, OtExtReceiverChannel)>,
        mut entropy: [u8; 32],
        wire: W,
    ) -> Result<Self, ParallelSeededError> {
        let rng = PartyPrivateRng::from_seed(entropy, b"QSAG.CUSTODY.KOS.V1");
        ct_zeroize_bytes(&mut entropy);
        let mut channels = BTreeMap::new();
        for (peer, sender, receiver) in peers {
            if peer == party
                || sender.sender_id != usize::from(party)
                || sender.receiver_id != usize::from(peer)
                || receiver.sender_id != usize::from(peer)
                || receiver.receiver_id != usize::from(party)
                || channels.insert(peer, (sender, receiver)).is_some()
            {
                return Err(invalid());
            }
        }
        Ok(Self {
            party,
            peers: channels,
            used: BTreeSet::new(),
            rng,
            wire,
            failed: false,
        })
    }
    pub fn party_id(&self) -> u16 {
        self.party
    }
    fn begin(
        &mut self,
        peer: u16,
        context: [u8; 32],
        sending: bool,
        count: usize,
    ) -> Result<(), ParallelSeededError> {
        if self.failed
            || count == 0
            || count > MAX_OTS
            || !self.peers.contains_key(&peer)
            || !self.used.insert((peer, context, sending))
        {
            self.failed = true;
            return Err(invalid());
        }
        Ok(())
    }
    pub fn send_values(
        &mut self,
        peer: u16,
        context: [u8; 32],
        alternatives: &[[u128; 2]],
    ) -> Result<(), ParallelSeededError> {
        self.begin(peer, context, true, alternatives.len())?;
        let result = (|| {
            let CommittedOtMessage::Columns(columns) = self.wire.receive(peer, context)? else {
                return Err(invalid());
            };
            if columns.u_cols.len() != 128
                || columns
                    .u_cols
                    .iter()
                    .any(|c| c.len() != alternatives.len().div_ceil(64) + 4)
            {
                return Err(invalid());
            }
            let channel = &mut self.peers.get_mut(&peer).ok_or_else(invalid)?.0;
            let (pending, challenge) = channel
                .round2_sample_challenge(&columns, &mut self.rng)
                .map_err(|_| invalid())?;
            self.wire
                .send(peer, context, CommittedOtMessage::Challenge(challenge))?;
            let CommittedOtMessage::Proof(proof) = self.wire.receive(peer, context)? else {
                return Err(invalid());
            };
            let mut pads = channel
                .round4_verify_and_finish(pending, &proof)
                .map_err(|_| invalid())?;
            // The extension pads cover whole 64-OT words; only the first `len` are used.
            let ciphertexts = (pads.len() >= alternatives.len())
                .then(|| encrypt_alternatives(&context, self.party, peer, &pads, alternatives));
            for (a, b) in &mut pads {
                ct_zeroize_bytes(a);
                ct_zeroize_bytes(b);
            }
            self.wire.send(
                peer,
                context,
                CommittedOtMessage::Ciphertexts(ciphertexts.ok_or_else(invalid)?),
            )
        })();
        if result.is_err() {
            let _ = self.wire.send(peer, context, CommittedOtMessage::Abort);
        }
        self.failed |= result.is_err();
        result
    }
    pub fn receive_values(
        &mut self,
        peer: u16,
        context: [u8; 32],
        choices: &[bool],
    ) -> Result<Vec<u128>, ParallelSeededError> {
        let mut words = alloc::vec![0u64; choices.len().div_ceil(64)];
        for (i, &choice) in choices.iter().enumerate() {
            words[i / 64] |= u64::from(choice) << (i % 64);
        }
        let result = self.receive_packed(peer, context, &words, choices.len());
        ct_zeroize_u64s(&mut words);
        result
    }
    /// As [`Self::receive_values`], with choice `i` at bit `i % 64` of `choice_words[i / 64]`.
    /// Bits at and above `count` in the last word must be zero.
    pub fn receive_packed(
        &mut self,
        peer: u16,
        context: [u8; 32],
        choice_words: &[u64],
        count: usize,
    ) -> Result<Vec<u128>, ParallelSeededError> {
        self.begin(peer, context, false, count)?;
        let result = (|| {
            if choice_words.len() != count.div_ceil(64)
                || (!count.is_multiple_of(64)
                    && choice_words[count / 64] >> (count % 64) != 0)
            {
                return Err(invalid());
            }
            let channel = &mut self.peers.get_mut(&peer).ok_or_else(invalid)?.1;
            let (pending, columns) = channel.round1_send_u_cols(choice_words, &mut self.rng);
            self.wire
                .send(peer, context, CommittedOtMessage::Columns(columns))?;
            let CommittedOtMessage::Challenge(challenge) = self.wire.receive(peer, context)? else {
                return Err(invalid());
            };
            let (proof, mut pads) = channel.round3_prove_and_finish(pending, &challenge);
            // Wipe pads on transport and malformed-message error paths too.
            let output = (|| {
                self.wire
                    .send(peer, context, CommittedOtMessage::Proof(proof))?;
                let CommittedOtMessage::Ciphertexts(ciphertexts) =
                    self.wire.receive(peer, context)?
                else {
                    return Err(invalid());
                };
                if ciphertexts.len() != count || pads.len() < count {
                    return Err(invalid());
                }
                Ok(decrypt_chosen(
                    &context,
                    peer,
                    self.party,
                    &pads,
                    choice_words,
                    &ciphertexts,
                ))
            })();
            for pad in &mut pads {
                ct_zeroize_bytes(pad);
            }
            output
        })();
        if result.is_err() {
            let _ = self.wire.send(peer, context, CommittedOtMessage::Abort);
        }
        self.failed |= result.is_err();
        result
    }
}
/// One ciphertext pair per OT: each alternative under the pad of its own branch.
/// Pads are hashed eight at a time, four OTs per batch; a short tail repeats the
/// last OT in the unused lanes and discards those outputs.
fn encrypt_alternatives(
    context: &[u8; 32],
    sender: u16,
    receiver: u16,
    pads: &[OtPadPair],
    alternatives: &[[u128; 2]],
) -> Vec<[u128; 2]> {
    let count = alternatives.len();
    let mut ciphertexts = Vec::with_capacity(count);
    for base in (0..count).step_by(4) {
        let indices = core::array::from_fn(|lane| (base + lane / 2).min(count - 1));
        let mut batch = pad_batch(
            context,
            sender,
            receiver,
            indices,
            count,
            core::array::from_fn(|lane| {
                if lane % 2 == 0 {
                    &pads[indices[lane]].0
                } else {
                    &pads[indices[lane]].1
                }
            }),
        );
        for lane in 0..(count - base).min(4) {
            ciphertexts.push([
                alternatives[base + lane][0] ^ batch[2 * lane],
                alternatives[base + lane][1] ^ batch[2 * lane + 1],
            ]);
        }
        ct_zeroize_u128s(&mut batch);
    }
    ciphertexts
}
/// The chosen alternative of every OT. Choice `i` is bit `i % 64` of
/// `choice_words[i / 64]`; selection is by mask, never by index or branch.
fn decrypt_chosen(
    context: &[u8; 32],
    sender: u16,
    receiver: u16,
    pads: &[[u8; 48]],
    choice_words: &[u64],
    ciphertexts: &[[u128; 2]],
) -> Vec<u128> {
    let count = ciphertexts.len();
    let mut output = Vec::with_capacity(count);
    for base in (0..count).step_by(8) {
        let indices = core::array::from_fn(|lane| (base + lane).min(count - 1));
        let mut batch = pad_batch(
            context,
            sender,
            receiver,
            indices,
            count,
            core::array::from_fn(|lane| &pads[indices[lane]]),
        );
        for (lane, pad) in batch.iter().enumerate().take((count - base).min(8)) {
            let i = base + lane;
            let mask = 0u128.wrapping_sub(u128::from((choice_words[i / 64] >> (i % 64)) & 1));
            let selected = (ciphertexts[i][0] & !mask) | (ciphertexts[i][1] & mask);
            output.push(selected ^ pad);
        }
        ct_zeroize_u128s(&mut batch);
    }
    output
}
fn chunk_context(context: &[u8; 32], index: usize, total_bits: usize) -> [u8; 32] {
    cshake256_framed_32(
        b"QSAG.CUSTODY.OT.CHUNK.V1",
        &[
            context,
            &(index as u64).to_be_bytes(),
            &(total_bits as u64).to_be_bytes(),
        ],
    )
}
impl<W: AuthenticatedOtWire> ParallelSeededDkgOt for CommittedCorrelatedOt<W> {
    fn send(
        &mut self,
        peer: u16,
        context: [u8; 32],
        alternatives: &[[u128; 2]],
    ) -> Result<(), ParallelSeededError> {
        if alternatives.is_empty() || !alternatives.len().is_multiple_of(128) {
            return Err(invalid());
        }
        for (index, chunk) in alternatives.chunks(MAX_OTS).enumerate() {
            self.send_values(
                peer,
                chunk_context(&context, index, alternatives.len()),
                chunk,
            )?;
        }
        Ok(())
    }
    fn receive(
        &mut self,
        peer: u16,
        context: [u8; 32],
        choices: &[u128],
    ) -> Result<Vec<u128>, ParallelSeededError> {
        let total = choices.len().checked_mul(128).ok_or_else(invalid)?;
        if total == 0 {
            return Err(invalid());
        }
        let mut output = Vec::with_capacity(total);
        let mut words = alloc::vec![0u64; choices.len().min(MAX_OTS / 128) * 2];
        for (index, chunk) in choices.chunks(MAX_OTS / 128).enumerate() {
            let words = &mut words[..chunk.len() * 2];
            for (pair, &choice) in words.as_chunks_mut::<2>().0.iter_mut().zip(chunk) {
                *pair = [choice as u64, (choice >> 64) as u64];
            }
            let result = self.receive_packed(
                peer,
                chunk_context(&context, index, total),
                words,
                chunk.len() * 128,
            );
            ct_zeroize_u64s(words);
            match result {
                Ok(mut values) => {
                    output.extend_from_slice(&values);
                    ct_zeroize_u128s(&mut values);
                }
                Err(error) => {
                    ct_zeroize_u128s(&mut output);
                    return Err(error);
                }
            }
        }
        Ok(output)
    }
}

#[cfg(all(test, feature = "std"))]
mod tests {
    use super::*;
    use std::sync::mpsc::{Receiver, Sender};
    struct Wire(
        Sender<([u8; 32], CommittedOtMessage)>,
        Receiver<([u8; 32], CommittedOtMessage)>,
    );
    impl AuthenticatedOtWire for Wire {
        fn send(
            &mut self,
            _: u16,
            context: [u8; 32],
            message: CommittedOtMessage,
        ) -> Result<(), ParallelSeededError> {
            self.0.send((context, message)).map_err(|_| invalid())
        }
        fn receive(
            &mut self,
            _: u16,
            context: [u8; 32],
        ) -> Result<CommittedOtMessage, ParallelSeededError> {
            let (actual, message) = self
                .1
                .recv_timeout(std::time::Duration::from_secs(30))
                .map_err(|_| invalid())?;
            if actual != context {
                return Err(invalid());
            }
            Ok(message)
        }
    }
    /// Two engines over freshly established production base-OT channels, one per direction.
    fn engine_pair() -> (CommittedCorrelatedOt<Wire>, CommittedCorrelatedOt<Wire>) {
        use qsag_core::preprocessing::try_establish_rlwe_ot_ext_channel;
        // The independent directional base handshakes can run concurrently;
        // neither borrows entropy or protocol state from the other direction.
        let forward = std::thread::spawn(|| {
            let mut a = PartyPrivateRng::from_seed([1; 32], b"test a forward");
            let mut b = PartyPrivateRng::from_seed([2; 32], b"test b forward");
            try_establish_rlwe_ot_ext_channel([3; 32], 0, 1, &mut a, &mut b).unwrap()
        });
        let reverse = std::thread::spawn(|| {
            let mut a = PartyPrivateRng::from_seed([8; 32], b"test a reverse");
            let mut b = PartyPrivateRng::from_seed([9; 32], b"test b reverse");
            try_establish_rlwe_ot_ext_channel([4; 32], 1, 0, &mut b, &mut a).unwrap()
        });
        let (s0, r1) = forward.join().unwrap();
        let (s1, r0) = reverse.join().unwrap();
        let (tx0, rx1) = std::sync::mpsc::channel();
        let (tx1, rx0) = std::sync::mpsc::channel();
        (
            CommittedCorrelatedOt::new(0, alloc::vec![(1, s0, r0)], [5; 32], Wire(tx0, rx0))
                .unwrap(),
            CommittedCorrelatedOt::new(1, alloc::vec![(0, s1, r1)], [6; 32], Wire(tx1, rx1))
                .unwrap(),
        )
    }

    /// One call larger than a single extension: both ends must cut it at the same place
    /// and derive the same per-chunk contexts.
    #[test]
    fn production_ot_splits_a_long_call_identically_on_both_ends() {
        let (mut left, mut right) = engine_pair();
        let words: Vec<u128> = (0..MAX_OTS as u128 / 128 + 1)
            .map(|i| (i + 1).wrapping_mul(0x9e37_79b9_7f4a_7c15_f39c_c060_5ced_c835))
            .collect();
        let total = words.len() * 128;
        let alternative = |i: usize| [i as u128, (i as u128) << 64 | 1];
        let sender = std::thread::spawn(move || {
            let pairs: Vec<_> = (0..total).map(alternative).collect();
            ParallelSeededDkgOt::send(&mut left, 1, [9; 32], &pairs).unwrap();
        });
        let values = ParallelSeededDkgOt::receive(&mut right, 0, [9; 32], &words).unwrap();
        sender.join().unwrap();
        assert_eq!(values.len(), total);
        for (i, value) in values.iter().enumerate() {
            let bit = ((words[i / 128] >> (i % 128)) & 1) as usize;
            assert_eq!(*value, alternative(i)[bit], "OT {i}");
        }
    }

    #[test]
    fn production_base_ot_roundtrip_and_replay_rejection() {
        let (mut left, mut right) = engine_pair();
        let pairs: Vec<_> = (0u128..65).map(|i| [i, 1000 + i]).collect();
        let choices: Vec<_> = (0..65).map(|i| i % 2 == 1).collect();
        // The Gilboa-facing entry points: 128 OTs per packed choice word, least significant
        // bit first.
        let word_pairs: Vec<_> = (0u128..256).map(|i| [i, 1000 + i]).collect();
        let words = [0x8000_0000_0000_0001_0000_0000_0000_0005u128, u128::MAX - 2];
        let sender = std::thread::spawn(move || {
            left.send_values(1, [7; 32], &pairs).unwrap();
            ParallelSeededDkgOt::send(&mut left, 1, [8; 32], &word_pairs).unwrap();
            // A replayed context is refused and poisons the engine.
            assert!(left.send_values(1, [7; 32], &pairs).is_err());
        });
        let values = right.receive_values(0, [7; 32], &choices).unwrap();
        assert_eq!(
            values,
            (0u128..65)
                .map(|i| i + if i % 2 == 1 { 1000 } else { 0 })
                .collect::<Vec<_>>()
        );
        let values = ParallelSeededDkgOt::receive(&mut right, 0, [8; 32], &words).unwrap();
        assert_eq!(
            values,
            (0u128..256)
                .map(|i| i + 1000 * ((words[(i / 128) as usize] >> (i % 128)) & 1))
                .collect::<Vec<_>>()
        );
        assert!(right.receive_values(0, [7; 32], &choices).is_err());
        sender.join().unwrap();
    }
}

#[cfg(test)]
mod pad_tests {
    use super::*;
    #[cfg(feature = "std")]
    #[test]
    #[ignore = "pad throughput benchmark"]
    fn benchmark_pad_batches() {
        let context = [0xa7; 32];
        let raw = [[0x32; 48]; 8];
        let start = std::time::Instant::now();
        for base in (0..MAX_OTS).step_by(8) {
            core::hint::black_box(pad_batch(
                &context,
                17,
                42,
                core::array::from_fn(|i| base + i),
                MAX_OTS,
                core::array::from_fn(|i| &raw[i]),
            ));
        }
        std::eprintln!("batched {MAX_OTS} pads: {:?}", start.elapsed());
        let start = std::time::Instant::now();
        for index in 0..MAX_OTS {
            core::hint::black_box(cshake256_framed_32(
                b"QSAG.CUSTODY.OT.PAD.V1",
                &[
                    &raw[index % 8],
                    &context,
                    &17u16.to_be_bytes(),
                    &42u16.to_be_bytes(),
                    &(index as u64).to_be_bytes(),
                    &(MAX_OTS as u64).to_be_bytes(),
                ],
            ));
        }
        std::eprintln!("scalar {MAX_OTS} pads: {:?}", start.elapsed());
    }

    fn reference_pad(
        context: &[u8; 32],
        sender: u16,
        receiver: u16,
        raw: &[u8; 48],
        index: usize,
        count: usize,
    ) -> u128 {
        let digest = cshake256_framed_32(
            b"QSAG.CUSTODY.OT.PAD.V1",
            &[
                raw,
                context,
                &sender.to_be_bytes(),
                &receiver.to_be_bytes(),
                &(index as u64).to_be_bytes(),
                &(count as u64).to_be_bytes(),
            ],
        );
        u128::from_le_bytes(core::array::from_fn(|i| digest[i]))
    }

    /// Both batched loops against one-pad-at-a-time hashing, at every length that leaves a
    /// partial four-OT sender batch, a partial eight-OT receiver batch or a partial choice word.
    #[test]
    fn batched_encryption_and_selection_match_the_scalar_reference_at_every_tail() {
        let context = [0x3c; 32];
        let (sender, receiver) = (0x0102, 0xfffe);
        for count in (1..=33).chain([63, 64, 65, 127, 128, 129, 257]) {
            let pads: Vec<OtPadPair> = (0..count)
                .map(|i| {
                    (
                        core::array::from_fn(|j| (i * 7 + j * 3 + 1) as u8),
                        core::array::from_fn(|j| (i * 11 + j * 5 + 2) as u8),
                    )
                })
                .collect();
            let alternatives: Vec<[u128; 2]> = (0..count as u128)
                .map(|i| {
                    [
                        (i + 1).wrapping_mul(0x9e37_79b9_7f4a_7c15_f39c_c060_5ced_c835),
                        (i + 2).wrapping_mul(0xbf58_476d_1ce4_e5b9_94d0_49bb_1331_11eb),
                    ]
                })
                .collect();
            let ciphertexts = encrypt_alternatives(&context, sender, receiver, &pads, &alternatives);
            assert_eq!(ciphertexts.len(), count);
            for (i, ((cipher, plain), pad)) in
                ciphertexts.iter().zip(&alternatives).zip(&pads).enumerate()
            {
                let expected = [
                    plain[0] ^ reference_pad(&context, sender, receiver, &pad.0, i, count),
                    plain[1] ^ reference_pad(&context, sender, receiver, &pad.1, i, count),
                ];
                assert_eq!(*cipher, expected, "count {count} index {i}");
            }
            // Choice patterns: all zero, all one, alternating, and a dense mix.
            for pattern in [0u64, u64::MAX, 0xaaaa_aaaa_aaaa_aaaa, 0x9d39_247e_3377_6d41] {
                let mut words: Vec<u64> = (0..count.div_ceil(64))
                    .map(|w| pattern.rotate_left(w as u32 * 7))
                    .collect();
                if !count.is_multiple_of(64) {
                    words[count / 64] &= (1u64 << (count % 64)) - 1;
                }
                let bit = |i: usize| (words[i / 64] >> (i % 64)) & 1 == 1;
                let chosen_pads: Vec<[u8; 48]> = (0..count)
                    .map(|i| if bit(i) { pads[i].1 } else { pads[i].0 })
                    .collect();
                let chosen =
                    decrypt_chosen(&context, sender, receiver, &chosen_pads, &words, &ciphertexts);
                let expected: Vec<u128> = (0..count)
                    .map(|i| alternatives[i][usize::from(bit(i))])
                    .collect();
                assert_eq!(chosen, expected, "count {count} pattern {pattern:#x}");
            }
        }
    }

    #[test]
    fn batched_pad_matches_framed_reference() {
        for count in [1usize, 3, 4, 7, 8, 9, 127, 65536, MAX_OTS] {
            let context = [0xa7; 32];
            let raw: [[u8; 48]; 8] =
                core::array::from_fn(|i| core::array::from_fn(|j| (i * 53 + j) as u8));
            let indices = [0, 1, count - 1, usize::MAX, 255, 256, 65535, 65536];
            let batch = pad_batch(
                &context,
                0x1234,
                0xabcd,
                indices,
                count,
                core::array::from_fn(|i| &raw[i]),
            );
            for lane in 0..8 {
                let reference = cshake256_framed_32(
                    b"QSAG.CUSTODY.OT.PAD.V1",
                    &[
                        &raw[lane],
                        &context,
                        &0x1234u16.to_be_bytes(),
                        &0xabcdu16.to_be_bytes(),
                        &(indices[lane] as u64).to_be_bytes(),
                        &(count as u64).to_be_bytes(),
                    ],
                );
                assert_eq!(
                    batch[lane],
                    u128::from_le_bytes(core::array::from_fn(|i| reference[i]))
                );
            }
        }
    }
}
