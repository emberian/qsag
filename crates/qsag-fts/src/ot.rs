//! Interactive KOS OT adapter over established Ring-LWE base-OT channels.
//! Establish channels using the production `qsag_core::preprocessing` base-OT
//! round states, over mutually authenticated confidential transports. This
//! adapter inherits their security bounds; it makes no new QROM security claim.
use crate::{ParallelSeededDkgOt, ParallelSeededError};
use alloc::{collections::BTreeMap, collections::BTreeSet, vec::Vec};
use qsag_accel::{ct::ct_zeroize_bytes, keccak::cshake256_framed_32};
use qsag_core::preprocessing::{
    KosOtChallengeMsg, KosOtProofMsg, KosOtUColsMsg, OtExtReceiverChannel, OtExtSenderChannel,
    PartyPrivateRng,
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
    for (word, bytes) in prefix[9..13].iter_mut().zip(context.chunks_exact(8)) {
        *word ^= u64::from_le_bytes(core::array::from_fn(|i| bytes[i]));
    }
    prefix[13] ^= 2;
    prefix[14] ^= u64::from(sender.swap_bytes()) | (2 << 16);
    prefix[15] ^= (u64::from(receiver.swap_bytes()) << 16) | (8 << 32);
    let mut states = [prefix; 8];
    for lane in 0..8 {
        for (word, bytes) in states[lane][2..8].iter_mut().zip(raw[lane].chunks_exact(8)) {
            *word ^= u64::from_le_bytes(core::array::from_fn(|i| bytes[i]));
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
        qsag_accel::ct::ct_zeroize_u64s(state);
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
            let mut ciphertexts = Vec::with_capacity(alternatives.len());
            for base in (0..alternatives.len()).step_by(4) {
                let indices =
                    core::array::from_fn(|lane| (base + lane / 2).min(alternatives.len() - 1));
                let mut batch = pad_batch(
                    &context,
                    self.party,
                    peer,
                    indices,
                    alternatives.len(),
                    core::array::from_fn(|lane| {
                        if lane % 2 == 0 {
                            &pads[indices[lane]].0
                        } else {
                            &pads[indices[lane]].1
                        }
                    }),
                );
                for lane in 0..(alternatives.len() - base).min(4) {
                    ciphertexts.push([
                        alternatives[base + lane][0] ^ batch[2 * lane],
                        alternatives[base + lane][1] ^ batch[2 * lane + 1],
                    ]);
                }
                qsag_core::wipe::wipe_u128s(&mut batch);
            }
            for (a, b) in &mut pads {
                ct_zeroize_bytes(a);
                ct_zeroize_bytes(b);
            }
            self.wire
                .send(peer, context, CommittedOtMessage::Ciphertexts(ciphertexts))
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
        self.begin(peer, context, false, choices.len())?;
        let result = (|| {
            let mut words = alloc::vec![0u64; choices.len().div_ceil(64)];
            for (i, &choice) in choices.iter().enumerate() {
                words[i / 64] |= u64::from(choice) << (i % 64);
            }
            let channel = &mut self.peers.get_mut(&peer).ok_or_else(invalid)?.1;
            let (pending, columns) = channel.round1_send_u_cols(&words, &mut self.rng);
            qsag_accel::ct::ct_zeroize_u64s(&mut words);
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
                if ciphertexts.len() != choices.len() {
                    return Err(invalid());
                }
                let mut output = Vec::with_capacity(choices.len());
                for base in (0..choices.len()).step_by(8) {
                    let indices = core::array::from_fn(|lane| (base + lane).min(choices.len() - 1));
                    let mut batch = pad_batch(
                        &context,
                        peer,
                        self.party,
                        indices,
                        choices.len(),
                        core::array::from_fn(|lane| &pads[indices[lane]]),
                    );
                    for (lane, pad) in batch.iter().enumerate().take((choices.len() - base).min(8))
                    {
                        let i = base + lane;
                        let mask = 0u128.wrapping_sub(u128::from(choices[i]));
                        let selected = (ciphertexts[i][0] & !mask) | (ciphertexts[i][1] & mask);
                        output.push(selected ^ pad);
                    }
                    qsag_core::wipe::wipe_u128s(&mut batch);
                }
                Ok(output)
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
        for (index, chunk) in choices.chunks(MAX_OTS / 128).enumerate() {
            let mut bits: Vec<bool> = chunk
                .iter()
                .flat_map(|word| (0..128).map(move |i| (word >> i) & 1 != 0))
                .collect();
            let result = self.receive_values(peer, chunk_context(&context, index, total), &bits);
            bits.fill(false);
            core::hint::black_box(&mut bits);
            match result {
                Ok(mut values) => {
                    output.extend_from_slice(&values);
                    qsag_accel::ct::ct_zeroize_u128s(&mut values);
                }
                Err(error) => {
                    qsag_accel::ct::ct_zeroize_u128s(&mut output);
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
    #[test]
    #[ignore = "full production Ring-LWE bootstrap soak; run explicitly with the remote resource limit"]
    fn production_base_ot_roundtrip_and_replay_rejection() {
        use qsag_core::preprocessing::try_establish_rlwe_ot_ext_channel;
        // The independent directional base handshakes can run concurrently;
        // neither borrows entropy or protocol state from the other direction.
        let forward = std::thread::spawn(|| {
            let mut a = PartyPrivateRng::from_seed([1; 32], b"test a forward");
            let mut b = PartyPrivateRng::from_seed([2; 32], b"test b forward");
            let channels =
                try_establish_rlwe_ot_ext_channel([3; 32], 0, 1, &mut a, &mut b).unwrap();
            std::eprintln!("production forward base OT established");
            channels
        });
        let reverse = std::thread::spawn(|| {
            let mut a = PartyPrivateRng::from_seed([8; 32], b"test a reverse");
            let mut b = PartyPrivateRng::from_seed([9; 32], b"test b reverse");
            let channels =
                try_establish_rlwe_ot_ext_channel([4; 32], 1, 0, &mut b, &mut a).unwrap();
            std::eprintln!("production reverse base OT established");
            channels
        });
        let (s0, r1) = forward.join().unwrap();
        let (s1, r0) = reverse.join().unwrap();
        let (tx0, rx1) = std::sync::mpsc::channel();
        let (tx1, rx0) = std::sync::mpsc::channel();
        let mut left =
            CommittedCorrelatedOt::new(0, alloc::vec![(1, s0, r0)], [5; 32], Wire(tx0, rx0))
                .unwrap();
        let mut right =
            CommittedCorrelatedOt::new(1, alloc::vec![(0, s1, r1)], [6; 32], Wire(tx1, rx1))
                .unwrap();
        let pairs: Vec<_> = (0u128..65).map(|i| [i, 1000 + i]).collect();
        let choices: Vec<_> = (0..65).map(|i| i % 2 == 1).collect();
        let sender = std::thread::spawn(move || {
            left.send_values(1, [7; 32], &pairs).unwrap();
            assert!(left.send_values(1, [7; 32], &pairs).is_err());
        });
        let values = right.receive_values(0, [7; 32], &choices).unwrap();
        assert_eq!(
            values,
            (0u128..65)
                .map(|i| i + if i % 2 == 1 { 1000 } else { 0 })
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
