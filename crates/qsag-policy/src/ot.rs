//! Committed correlated OT for policy guard provisioning.
use crate::PolicyViolation;
use alloc::{collections::BTreeMap, collections::BTreeSet, vec::Vec};
use qsag_accel::ct::{ct_zeroize_bytes, ct_zeroize_u64s, ct_zeroize_u128s};
#[cfg(test)]
use qsag_accel::keccak::cshake256_framed_32;
use qsag_asm::wipe::{SecretBuffer, SecretVec};
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
    for index in 0..8 {
        for (word, bytes) in states[index][2..8]
            .iter_mut()
            .zip(raw[index].as_chunks::<8>().0.iter())
        {
            *word ^= u64::from_le_bytes(*bytes);
        }
        // The big-endian index straddles the 136-byte rate boundary at offset 132.
        states[index][16] ^= (indices[index] as u64).swap_bytes() << 32;
    }
    qsag_core::sponge::keccak::keccak_f1600_batch(&mut states);
    let count = (count as u64).swap_bytes();
    for index in 0..8 {
        states[index][0] ^= ((indices[index] as u64).swap_bytes() >> 32) | (8 << 32);
        states[index][1] ^= count << 32;
        states[index][2] ^= (count >> 32) | (4 << 32);
        states[index][16] ^= 1 << 63;
    }
    qsag_core::sponge::keccak::keccak_f1600_batch(&mut states);
    let result =
        core::array::from_fn(|index| states[index][0] as u128 | ((states[index][1] as u128) << 64));
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
    ) -> Result<(), PolicyViolation>;
    fn receive(
        &mut self,
        peer: u16,
        context: [u8; 32],
    ) -> Result<CommittedOtMessage, PolicyViolation>;
}

/// Per-custodian production OT engine. Owns uncloneable, direction-specific base
/// channels, local randomness, and replay state. Any protocol error poisons it.
pub struct CommittedCorrelatedOt<W> {
    party: u16,
    /// Direction-specific extension channels.
    peers: BTreeMap<u16, (OtExtSenderChannel, OtExtReceiverChannel)>,
    used: BTreeSet<(u16, [u8; 32], bool)>,
    rng: PartyPrivateRng,
    wire: W,
    failed: bool,
}
fn invalid() -> PolicyViolation {
    PolicyViolation::BarrierBdozMacFailed
}
pub(crate) const MAX_OTS: usize = 262_144;
impl<W: AuthenticatedOtWire> CommittedCorrelatedOt<W> {
    /// `entropy` must be fresh private CSPRNG output, never pair-shared entropy.
    pub fn new(
        party: u16,
        peers: Vec<(u16, OtExtSenderChannel, OtExtReceiverChannel)>,
        mut entropy: [u8; 32],
        wire: W,
    ) -> Result<Self, PolicyViolation> {
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
    ) -> Result<(), PolicyViolation> {
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
    ) -> Result<(), PolicyViolation> {
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
    ) -> Result<Vec<u128>, PolicyViolation> {
        let mut words = SecretBuffer(alloc::vec![0u64; choices.len().div_ceil(64)]);
        for (i, &choice) in choices.iter().enumerate() {
            words[i / 64] |= u64::from(choice) << (i % 64);
        }
        self.receive_packed(peer, context, &words, choices.len())
            .map(SecretBuffer::into_inner)
    }
    /// As [`Self::receive_values`], with choice `i` at bit `i % 64` of `choice_words[i / 64]`.
    /// Bits at and above `count` in the last word must be zero.
    pub fn receive_packed(
        &mut self,
        peer: u16,
        context: [u8; 32],
        choice_words: &[u64],
        count: usize,
    ) -> Result<SecretVec<u128>, PolicyViolation> {
        self.begin(peer, context, false, count)?;
        let result = (|| {
            if choice_words.len() != count.div_ceil(64)
                || (!count.is_multiple_of(64) && choice_words[count / 64] >> (count % 64) != 0)
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
/// last OT in the unused positions and discards those outputs.
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
        let indices = core::array::from_fn(|index| (base + index / 2).min(count - 1));
        let mut batch = pad_batch(
            context,
            sender,
            receiver,
            indices,
            count,
            core::array::from_fn(|index| {
                if index % 2 == 0 {
                    &pads[indices[index]].0
                } else {
                    &pads[indices[index]].1
                }
            }),
        );
        for index in 0..(count - base).min(4) {
            ciphertexts.push([
                alternatives[base + index][0] ^ batch[2 * index],
                alternatives[base + index][1] ^ batch[2 * index + 1],
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
) -> SecretVec<u128> {
    let count = ciphertexts.len();
    let mut output = SecretVec::<u128>::with_capacity(count);
    for base in (0..count).step_by(8) {
        let indices = core::array::from_fn(|index| (base + index).min(count - 1));
        let mut batch = pad_batch(
            context,
            sender,
            receiver,
            indices,
            count,
            core::array::from_fn(|index| &pads[indices[index]]),
        );
        for (index, pad) in batch.iter().enumerate().take((count - base).min(8)) {
            let i = base + index;
            let mask = 0u128.wrapping_sub(u128::from((choice_words[i / 64] >> (i % 64)) & 1));
            let selected = (ciphertexts[i][0] & !mask) | (ciphertexts[i][1] & mask);
            output.push(selected ^ pad);
        }
        ct_zeroize_u128s(&mut batch);
    }
    output
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
            let ciphertexts =
                encrypt_alternatives(&context, sender, receiver, &pads, &alternatives);
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
                let chosen = decrypt_chosen(
                    &context,
                    sender,
                    receiver,
                    &chosen_pads,
                    &words,
                    &ciphertexts,
                );
                let expected: Vec<u128> = (0..count)
                    .map(|i| alternatives[i][usize::from(bit(i))])
                    .collect();
                assert_eq!(*chosen, expected, "count {count} pattern {pattern:#x}");
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
            for index in 0..8 {
                let reference = cshake256_framed_32(
                    b"QSAG.CUSTODY.OT.PAD.V1",
                    &[
                        &raw[index],
                        &context,
                        &0x1234u16.to_be_bytes(),
                        &0xabcdu16.to_be_bytes(),
                        &(indices[index] as u64).to_be_bytes(),
                        &(count as u64).to_be_bytes(),
                    ],
                );
                assert_eq!(
                    batch[index],
                    u128::from_le_bytes(core::array::from_fn(|i| reference[i]))
                );
            }
        }
    }
}
