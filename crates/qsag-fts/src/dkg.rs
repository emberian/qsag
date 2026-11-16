//! Per-party setup over authenticated broadcast, private channels and pairwise
//! oblivious products. No function accepts another party's private state.
//!
//! Deployments must supply a reviewed product backend and independent private
//! entropy. The Gilboa adapter below reduces products to binary OT.
//!
//! # Active consistency check
//!
//! [`finalize_parallel_seeded_dkg_party`] returns a [`ParallelSeededDkgUnverifiedOutput`]: the
//! key share and preprocessing are not released until a five-message check passes.
//!
//! 1. Every party broadcasts a commitment to a fresh check coin, then opens it once all
//!    commitments are frozen. The joint coin is therefore fixed only after every share and MAC
//!    share already exists.
//! 2. **Products.** Every product of a power tuple `(a, ..., a^7)` has the factor `a`:
//!    `a^3 = a^2*a`, `a^5 = a^4*a`, `a^7 = a^6*a`. They are combined with powers `s, s^2, s^3`
//!    of a coin-derived challenge into one claim `C = X*a` and checked against one sacrificial
//!    product `w = u*a`: parties open `rho = X + u`, and the shared value `C + w + rho*a` must
//!    be zero. Each output Beaver triple is checked against its own sacrificial triple
//!    `(u, v, w)` under a challenge `t`: parties open `rho = t*x + u` and `sigma = y + v`, and
//!    `t*c + w + sigma*u + rho*v + rho*sigma` must be zero.
//! 3. **Squares.** Squaring is additive in this field, so `a^2 = a*a`, `a^4 = a^2*a^2` and
//!    `a^6 = a^3*a^3` need no product. With coin-derived weights `theta`, parties open
//!    `A = r + sum theta*x` over every value `x` being squared, masked by an authenticated
//!    random `r`, and the shared value `r2 + sum theta^2*y - A^2` over the claimed squares `y`
//!    and the claimed `r2 = r^2` must be zero.
//! 4. **Share commitment.** Every output value is folded with coin-derived weights
//!    into one opening masked by a sacrificial authenticated random value.
//! 5. **MAC check.** All opened values, and the claimed zeros, are verified in one batched check
//!    on both MAC lanes; each party commits to its MAC tag before any tag is opened.
//!
//! A relation that is false on the authenticated values, or a MAC share that is not the global
//! key times the value, survives with probability about `2^-127` over the joint coin. Any failure
//! discards the ceremony; nothing from it may be reused.
//!
//! Not covered: the check does not identify the cheater, and it is not a simulation proof for
//! the OT backend. A party that sends inconsistent correction words can still stake the
//! ceremony on a guess of `k` bits of a peer's OT choices, succeeding with probability `2^-k`
//! and otherwise aborting it. With [`ParallelSeededGilboaProducts`] those choices are the
//! peer's share of a power mask `a` (in a product) or of the MAC key (in a MAC), never a
//! share of the signing key.
use super::*;

/// Public agreement, fixed before anyone publishes a coin commitment.
#[derive(Clone)]
pub struct ParallelSeededDkgConfig {
    pub params: ParallelSeededParams,
    pub roster: Vec<u16>,
    pub session: [u8; 32],
    pub power_count: usize,
    pub beaver_count: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParallelSeededDkgRound1Commit {
    pub party_id: u16,
    pub context: [u8; 32],
    pub digest: [u8; 32],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParallelSeededDkgRound2Open {
    pub party_id: u16,
    pub context: [u8; 32],
    pub coin: [u8; 32],
}

/// Deliver only to `recipient`, over a confidential authenticated pair channel.
/// This package contains no seeds for any other pair. Never broadcast it.
pub struct ParallelSeededDkgSharePackage {
    pub sender: u16,
    pub recipient: u16,
    pub context: [u8; 32],
    pub seed: [u8; 32],
}
impl Drop for ParallelSeededDkgSharePackage {
    fn drop(&mut self) {
        ct_zeroize_bytes(&mut self.seed);
    }
}

/// Not cloneable: freezing the broadcast and finalizing consume one ceremony.
pub struct ParallelSeededDkgRound1State {
    config: ParallelSeededDkgConfig,
    party_id: u16,
    context: [u8; 32],
    entropy: [u8; 32],
    coin: [u8; 32],
    commits: Option<Vec<ParallelSeededDkgRound1Commit>>,
    packages_sent: bool,
    /// `(index, delta)`: this party authenticates `value[index] + delta` instead.
    #[cfg(test)]
    pub(crate) value_faults: Vec<(usize, u128)>,
    /// `(index, delta)`: this party shifts its share `index` of the first products, three per
    /// tuple (`a^3`, `a^5`, `u*a`), before deriving `a^6` and `a^7` from them.
    #[cfg(test)]
    pub(crate) product_faults: Vec<(usize, u128)>,
}
impl Drop for ParallelSeededDkgRound1State {
    fn drop(&mut self) {
        ct_zeroize_bytes(&mut self.entropy);
        ct_zeroize_bytes(&mut self.coin);
    }
}
impl ParallelSeededDkgRound1State {
    /// `entropy` must be fresh, uniform, private and independent for each party.
    pub fn begin(
        config: ParallelSeededDkgConfig,
        party_id: u16,
        mut entropy: [u8; 32],
    ) -> Result<Self, ParallelSeededError> {
        let valid = config.params.validate().is_ok()
            && config.roster.len() >= 2
            && config.roster.len() <= 255
            && config.roster.windows(2).all(|w| w[0] < w[1])
            && config.roster.contains(&party_id)
            && config.power_count > 0
            // Up to 32 custody leaves per independently authenticated batch.
            && config.power_count <= 1_048_576
            && config.beaver_count <= DEFAULT_BEAVER_TRIPLE_POOL;
        if !valid {
            ct_zeroize_bytes(&mut entropy);
            return Err(ParallelSeededError::InvalidThresholdParameters);
        }
        let mut encoded = Vec::new();
        for id in &config.roster {
            encoded.extend_from_slice(&id.to_be_bytes());
        }
        for value in [
            config.params.tree_height,
            config.params.winternitz_w,
            config.params.num_chains,
            config.params.target_sum,
            config.power_count,
            config.beaver_count,
        ] {
            encoded.extend_from_slice(&(value as u64).to_be_bytes());
        }
        let context = cshake256_framed_32(b"QSAG.DKG.CONTEXT.V1", &[&config.session, &encoded]);
        let coin = cshake256_framed_32(
            b"QSAG.DKG.COIN.V1",
            &[&entropy, &context, &party_id.to_be_bytes()],
        );
        let state = Self {
            config,
            party_id,
            context,
            entropy,
            coin,
            commits: None,
            packages_sent: false,
            #[cfg(test)]
            value_faults: Vec::new(),
            #[cfg(test)]
            product_faults: Vec::new(),
        };
        ct_zeroize_bytes(&mut entropy);
        Ok(state)
    }
    pub fn commitment(&self) -> ParallelSeededDkgRound1Commit {
        ParallelSeededDkgRound1Commit {
            party_id: self.party_id,
            context: self.context,
            digest: coin_digest(&self.context, self.party_id, &self.coin),
        }
    }
    /// Freeze an identical authenticated broadcast at every party before opening.
    /// Refuses duplicate, missing, foreign, or changed own commitments.
    pub fn open(
        &mut self,
        commits: &[ParallelSeededDkgRound1Commit],
    ) -> Result<ParallelSeededDkgRound2Open, ParallelSeededError> {
        if self.commits.is_some()
            || commits.len() != self.config.roster.len()
            || commits
                .iter()
                .zip(&self.config.roster)
                .any(|(c, id)| c.party_id != *id || c.context != self.context)
            || !commits.contains(&self.commitment())
        {
            return Err(ParallelSeededError::InvalidThresholdParameters);
        }
        self.commits = Some(commits.to_vec());
        Ok(ParallelSeededDkgRound2Open {
            party_id: self.party_id,
            context: self.context,
            coin: self.coin,
        })
    }
    fn frozen_context(&self) -> Result<[u8; 32], ParallelSeededError> {
        let mut bytes = Vec::new();
        for c in self
            .commits
            .as_ref()
            .ok_or(ParallelSeededError::InvalidThresholdParameters)?
        {
            bytes.extend_from_slice(&c.digest);
        }
        Ok(cshake256_framed_32(
            b"QSAG.DKG.FROZEN.V1",
            &[&self.context, &bytes],
        ))
    }
    fn pair_seed(&self, peer: u16, context: &[u8; 32]) -> [u8; 32] {
        cshake256_framed_32(
            b"QSAG.DKG.PAIR.V1",
            &[
                &self.entropy,
                context,
                &self.party_id.to_be_bytes(),
                &peer.to_be_bytes(),
            ],
        )
    }
    pub fn private_packages(
        &mut self,
    ) -> Result<Vec<ParallelSeededDkgSharePackage>, ParallelSeededError> {
        if self.packages_sent {
            return Err(ParallelSeededError::InvalidThresholdParameters);
        }
        let context = self.frozen_context()?;
        self.packages_sent = true;
        Ok(self
            .config
            .roster
            .iter()
            .filter(|&&id| id > self.party_id)
            .map(|&recipient| ParallelSeededDkgSharePackage {
                sender: self.party_id,
                recipient,
                context,
                seed: self.pair_seed(recipient, &context),
            })
            .collect())
    }
    fn sample(&self, label: &[u8], count: usize) -> SecretVec<u128> {
        SecretBuffer(xof_field_elements(
            b"QSAG.DKG.PRIVATE.V1",
            &[
                &self.entropy,
                &self.context,
                &self.party_id.to_be_bytes(),
                label,
            ],
            count,
        ))
    }
}
/// `count` field elements from one framed cSHAKE256 stream, sixteen little-endian bytes each.
/// The byte stream is wiped: for a private sample it is as secret as the elements.
fn xof_field_elements(label: &[u8], frames: &[&[u8]], count: usize) -> Vec<u128> {
    let mut raw = vec![0u8; count * 16];
    cshake256_framed_xof(label, frames, &mut raw);
    let values = raw
        .as_chunks::<16>()
        .0
        .iter()
        .map(|b| u128::from_le_bytes(*b))
        .collect();
    ct_zeroize_bytes(&mut raw);
    values
}
fn coin_digest(context: &[u8; 32], id: u16, coin: &[u8; 32]) -> [u8; 32] {
    cshake256_framed_32(b"QSAG.DKG.COMMIT.V1", &[context, &id.to_be_bytes(), coin])
}

/// Pairwise oblivious product functionality. Every roster member invokes each
/// operation in the same public order. Only sender/receiver get private operands
/// and return additive shares; all others get and return empty slices.
/// The two outputs must sum to sender_input * receiver_input componentwise.
/// Bind authentication, replay protection, size and role to `context`. Neither
/// endpoint may learn the other operand. Backend errors abort the entire DKG.
/// Security against malicious setup requires consistent inputs across operations.
pub trait ParallelSeededDkgProducts {
    fn party_id(&self) -> u16;
    fn product_shares(
        &mut self,
        context: [u8; 32],
        sender: u16,
        receiver: u16,
        operand: &[u128],
    ) -> Result<Vec<u128>, ParallelSeededError>;

    /// One batched multiplication over every ordered pair of `roster` at once. Receiver
    /// operand `j` multiplies the `width` sender operands `j*width..(j+1)*width`. Returns
    /// this party's shares summed over the pairs it is an endpoint of; its own diagonal
    /// term is not included. The default runs [`Self::product_shares`] pair by pair.
    fn cross_products(
        &mut self,
        context: [u8; 32],
        roster: &[u16],
        width: usize,
        sender_operand: &[u128],
        receiver_operand: &[u128],
    ) -> Result<Vec<u128>, ParallelSeededError> {
        if width == 0 || receiver_operand.len().checked_mul(width) != Some(sender_operand.len())
            || !valid_product_roster(roster, self.party_id())
        {
            return Err(ParallelSeededError::InvalidThresholdParameters);
        }
        let id = self.party_id();
        let repeated = SecretBuffer(
            receiver_operand
                .iter()
                .flat_map(|&y| core::iter::repeat_n(y, width))
                .collect::<Vec<u128>>(),
        );
        let mut total = SecretBuffer(vec![0u128; sender_operand.len()]);
        for &sender in roster {
            for &receiver in roster {
                if sender == receiver {
                    continue;
                }
                let pair = cshake256_framed_32(
                    b"QSAG.DKG.PRODUCT.PAIR.V1",
                    &[
                        &context,
                        &sender.to_be_bytes(),
                        &receiver.to_be_bytes(),
                        &(sender_operand.len() as u64).to_be_bytes(),
                    ],
                );
                let operand: &[u128] = if id == sender {
                    sender_operand
                } else if id == receiver {
                    &repeated
                } else {
                    &[]
                };
                let part = SecretBuffer(self.product_shares(pair, sender, receiver, operand)?);
                if part.len() != operand.len() {
                    return Err(ParallelSeededError::BdozMacCheckFailed);
                }
                for (sum, contribution) in total.iter_mut().zip(part.iter()) {
                    *sum ^= contribution;
                }
            }
        }
        Ok(core::mem::take(&mut total.0))
    }

    /// As [`Self::cross_products`] with one sender operand, `key`, for every receiver value:
    /// the cross terms of a MAC under this party's key share.
    fn keyed_products(
        &mut self,
        context: [u8; 32],
        roster: &[u16],
        key: u128,
        values: &[u128],
    ) -> Result<Vec<u128>, ParallelSeededError> {
        let keys = SecretBuffer(vec![key; values.len()]);
        self.cross_products(context, roster, 1, &keys, values)
    }
}

/// One peer's part of a [`ParallelSeededDkgOt::random_ots`] call.
pub struct ParallelSeededDkgOtPeer<'a> {
    pub peer: u16,
    /// Random OTs this party sends to `peer`, in words of 128 OTs.
    pub send_words: usize,
    /// This party's packed choices toward `peer`, least significant bit first.
    pub choices: &'a [u128],
}

/// Random-OT pads exchanged with one peer, 48 bytes per OT: both pads of every OT this
/// party sent, and the chosen pad of every OT it received. Wiped on drop.
pub struct ParallelSeededDkgOtPads {
    pub sent: Vec<([u8; 48], [u8; 48])>,
    pub received: Vec<[u8; 48]>,
}
impl Drop for ParallelSeededDkgOtPads {
    fn drop(&mut self) {
        for (zero, one) in &mut self.sent {
            ct_zeroize_bytes(zero);
            ct_zeroize_bytes(one);
        }
        for pad in &mut self.received {
            ct_zeroize_bytes(pad);
        }
    }
}

/// Binary OT backend for the Gilboa adapter. `receive` returns one field element
/// per bit, least significant bit first, for each packed 128-bit choice word.
/// Sending both alternatives on a private channel does NOT implement this trait.
/// Implementations must hide choices from the sender and unchosen messages from
/// the receiver, authenticate peers, and reject repeated contexts.
///
/// [`Self::random_ots`] and the word messages run with every peer at once: each party
/// sends to all of its peers before it reads from any of them, so a transport must
/// accept a message without waiting for the peer to read it.
pub trait ParallelSeededDkgOt {
    /// Random OTs with every listed peer, in both directions. The receiver of an OT
    /// learns exactly the pad its choice bit selects; the sender learns both pads and
    /// nothing about the choice. One result per entry of `peers`, in the same order.
    fn random_ots(
        &mut self,
        context: [u8; 32],
        peers: &[ParallelSeededDkgOtPeer<'_>],
    ) -> Result<Vec<ParallelSeededDkgOtPads>, ParallelSeededError>;
    /// Authenticated message of field elements to `peer`. Confidentiality is not required:
    /// the adapter masks every word with OT pads first.
    fn send_words(
        &mut self,
        peer: u16,
        context: [u8; 32],
        words: Vec<u128>,
    ) -> Result<(), ParallelSeededError>;
    /// The message `peer` sent under `context`; any other length than `count` is refused.
    fn receive_words(
        &mut self,
        peer: u16,
        context: [u8; 32],
        count: usize,
    ) -> Result<Vec<u128>, ParallelSeededError>;
    fn send(
        &mut self,
        peer: u16,
        context: [u8; 32],
        alternatives: &[[u128; 2]],
    ) -> Result<(), ParallelSeededError>;
    fn receive(
        &mut self,
        peer: u16,
        context: [u8; 32],
        choices: &[u128],
    ) -> Result<SecretVec<u128>, ParallelSeededError>;
}

// Product adapters are public entry points too: duplicate peers would reuse OT
// contexts, and noncanonical ordering can deadlock a pairwise transport.
fn valid_product_roster(roster: &[u16], party_id: u16) -> bool {
    !roster.is_empty() && roster.len() <= 255
        && roster.windows(2).all(|w| w[0] < w[1])
        && roster.binary_search(&party_id).is_ok()
}

/// Field products per chosen-message OT call of [`ParallelSeededDkgProducts::product_shares`].
const GILBOA_PRODUCT_BATCH: usize = 32;
/// Receiver operands per random-OT flight: 128 OTs each, one extension of `ot::MAX_OTS`.
const GILBOA_FLIGHT_WORDS: usize = crate::ot::MAX_OTS / 128;
/// Values per fixed-key correction message, 128 words each.
const KEYED_BLOCK: usize = 4096;

/// Multiplication by `z` modulo `z^128 + z^7 + z^2 + z + 1`, without a secret-dependent branch.
#[inline]
fn mul_z(value: u128) -> u128 {
    (value << 1) ^ (0x87 & 0u128.wrapping_sub(value >> 127))
}
#[inline]
fn pad_word(pad: &[u8; 48], segment: usize) -> u128 {
    u128::from_le_bytes(pad.as_chunks::<16>().0[segment])
}
/// Up to eight cSHAKE256 streams over the 80-byte inputs `seed || context`, each `count`
/// little-endian field elements: stream `i` fills `rows[i*count..(i+1)*count]`.
fn expand_seed_group(seeds: &[&[u8; 48]], context: &[u8; 32], count: usize, rows: &mut [u128]) {
    const MIDSTATE: [u64; 25] =
        qsag_core::sponge::keccak::cshake256_static_midstate(b"QSAG.DKG.KEYED.PRG.V1");
    let mut states = qsag_asm::KeccakState8x::default();
    for (word, row) in states.0.iter_mut().enumerate() {
        *row = [MIDSTATE[word]; 8];
    }
    for (lane, seed) in seeds.iter().enumerate() {
        for (word, bytes) in seed.as_chunks::<8>().0.iter().enumerate() {
            states.0[word][lane] ^= u64::from_le_bytes(*bytes);
        }
    }
    for (word, bytes) in context.as_chunks::<8>().0.iter().enumerate() {
        let value = u64::from_le_bytes(*bytes);
        for lane in &mut states.0[6 + word] {
            *lane ^= value;
        }
    }
    // The cSHAKE suffix follows the 80 input bytes; the last rate bit closes the block.
    for lane in 0..8 {
        states.0[10][lane] ^= 0x04;
        states.0[16][lane] ^= 1 << 63;
    }
    // A rate block holds seventeen words, so an element can straddle two permutations.
    let mut low = [0u64; 8];
    let mut word = 0;
    while word < 2 * count {
        qsag_asm::keccak_f1600_x8(&mut states);
        for squeezed in states.0.iter().take(17) {
            if word == 2 * count {
                break;
            }
            if word % 2 == 0 {
                low = *squeezed;
            } else {
                for (lane, row) in rows.chunks_mut(count).enumerate() {
                    row[word / 2] = u128::from(low[lane]) | (u128::from(squeezed[lane]) << 64);
                }
            }
            word += 1;
        }
    }
    qsag_asm::volatile_fill(&mut low, 0);
    qsag_asm::volatile_fill(&mut states.0, [0; 8]);
}
/// `acc[j] = acc[j] * z^step + row[j]`.
fn horner_step(acc: &mut [u128], row: &[u128], step: usize) {
    for (acc, &value) in acc.iter_mut().zip(row) {
        for _ in 0..step {
            *acc = mul_z(*acc);
        }
        *acc ^= value;
    }
}
/// `sum_i rows[i*len + j] * z^i` for every column `j`, by Horner from the highest row.
fn fold_rows(rows: &[u128], len: usize) -> SecretVec<u128> {
    let mut folded = SecretBuffer(vec![0u128; len]);
    for row in rows.chunks(len).rev() {
        horner_step(&mut folded, row, 1);
    }
    folded
}
/// Adds the unit folds of each peer in turn, an equal number per peer, to `shares`: unit `g`
/// holds the rows from `g * KEYED_UNIT`, so it enters at `z^(g * KEYED_UNIT)`.
fn add_unit_folds(shares: &mut [u128], folds: &[SecretVec<u128>], peers: usize) {
    if peers == 0 {
        return;
    }
    for folds in folds.chunks(folds.len() / peers) {
        let mut folded = SecretBuffer(vec![0u128; shares.len()]);
        for fold in folds.iter().rev() {
            horner_step(&mut folded, fold, KEYED_UNIT);
        }
        for (share, value) in shares.iter_mut().zip(folded.iter()) {
            *share ^= value;
        }
    }
}
/// Seeds per unit of fixed-key work: one eight-lane Keccak batch.
const KEYED_UNIT: usize = 8;
/// Value holder, for up to eight seed pairs of one peer: writes the correction rows
/// `t0 + t1 + x` and returns the fold of the kept `t0` rows.
fn keyed_value_unit(
    pairs: &[([u8; 48], [u8; 48])],
    context: &[u8; 32],
    values: &[u128],
    corrections: &mut [u128],
) -> SecretVec<u128> {
    let count = values.len();
    let zeros: Vec<&[u8; 48]> = pairs.iter().map(|pair| &pair.0).collect();
    let ones: Vec<&[u8; 48]> = pairs.iter().map(|pair| &pair.1).collect();
    let mut kept = SecretBuffer(vec![0u128; pairs.len() * count]);
    expand_seed_group(&zeros, context, count, &mut kept);
    expand_seed_group(&ones, context, count, corrections);
    for (row, kept) in corrections.chunks_mut(count).zip(kept.chunks(count)) {
        for ((word, &kept), &value) in row.iter_mut().zip(kept).zip(values) {
            *word ^= kept ^ value;
        }
    }
    fold_rows(&kept, count)
}
/// Key holder, for up to eight chosen seeds of one peer: the fold of the chosen streams,
/// each corrected where its key bit (from bit 0 of `key_bits`) is set.
fn keyed_key_unit(
    chosen: &[[u8; 48]],
    context: &[u8; 32],
    key_bits: u128,
    corrections: &[u128],
) -> SecretVec<u128> {
    let count = corrections.len() / chosen.len();
    let seeds: Vec<&[u8; 48]> = chosen.iter().collect();
    let mut rows = SecretBuffer(vec![0u128; corrections.len()]);
    expand_seed_group(&seeds, context, count, &mut rows);
    for (bit, (row, corrections)) in rows
        .chunks_mut(count)
        .zip(corrections.chunks(count))
        .enumerate()
    {
        let mask = 0u128.wrapping_sub((key_bits >> bit) & 1);
        for (word, &correction) in row.iter_mut().zip(corrections) {
            *word ^= mask & correction;
        }
    }
    fold_rows(&rows, count)
}
/// `job` on every item, in order. With the standard library the items are split over up to
/// sixteen threads; without it they run in turn.
pub(crate) fn in_parallel<T: Send, R: Send>(items: Vec<T>, job: impl Fn(T) -> R + Sync) -> Vec<R> {
    #[cfg(feature = "std")]
    if items.len() > 1 {
        let threads = std::thread::available_parallelism()
            .map_or(1, usize::from)
            .min(16);
        let share = items.len().div_ceil(threads);
        let job = &job;
        let mut items = items.into_iter();
        return std::thread::scope(|scope| {
            let mut handles = Vec::with_capacity(threads);
            loop {
                let batch: Vec<T> = items.by_ref().take(share).collect();
                if batch.is_empty() {
                    break;
                }
                handles.push(scope.spawn(move || batch.into_iter().map(job).collect::<Vec<R>>()));
            }
            handles
                .into_iter()
                .flat_map(|handle| match handle.join() {
                    Ok(results) => results,
                    Err(panic) => std::panic::resume_unwind(panic),
                })
                .collect()
        });
    }
    items.into_iter().map(job).collect()
}

/// GF(2^128) Gilboa multiplication over binary OT.
/// Background: <https://tlsnotary.org/docs/mpc/mac/>.
///
/// [`ParallelSeededDkgProducts::cross_products`] runs 128 random OTs per receiver operand
/// with every peer at once. The 48-byte pad of each OT masks up to three sender operands
/// that share the receiver operand, and the sender transmits one correction word per
/// operand and OT.
///
/// [`ParallelSeededDkgProducts::keyed_products`] runs 128 random OTs per peer and call, on
/// the bits of the key. Their pads seed 128 cSHAKE256 streams; the value holder sends
/// `t0 + t1 + x` per stream and value, and both shares are the streams folded by powers of
/// `z`. A value therefore costs stream output, not OTs, and no value is an OT choice.
///
/// Randomness is local, never a pair-shared seed. Use a fresh adapter per DKG.
pub struct ParallelSeededGilboaProducts<T> {
    party_id: u16,
    entropy: [u8; 32],
    ot: T,
}
impl<T> ParallelSeededGilboaProducts<T> {
    pub fn new(party_id: u16, entropy: [u8; 32], ot: T) -> Self {
        Self {
            party_id,
            entropy,
            ot,
        }
    }
}
impl<T> Drop for ParallelSeededGilboaProducts<T> {
    fn drop(&mut self) {
        ct_zeroize_bytes(&mut self.entropy);
    }
}
impl<T: ParallelSeededDkgOt> ParallelSeededDkgProducts for ParallelSeededGilboaProducts<T> {
    fn party_id(&self) -> u16 {
        self.party_id
    }
    fn product_shares(
        &mut self,
        context: [u8; 32],
        sender: u16,
        receiver: u16,
        operand: &[u128],
    ) -> Result<Vec<u128>, ParallelSeededError> {
        if sender == receiver {
            return Err(ParallelSeededError::InvalidThresholdParameters);
        }
        if self.party_id != sender && self.party_id != receiver {
            if !operand.is_empty() {
                return Err(ParallelSeededError::InvalidThresholdParameters);
            }
            return Ok(Vec::new());
        }
        let mut shares = SecretBuffer(Vec::with_capacity(operand.len()));
        // Bound temporary OT storage independently of the preprocessing pool.
        for (batch, inputs) in operand.chunks(GILBOA_PRODUCT_BATCH).enumerate() {
            let context = cshake256_framed_32(
                b"QSAG.DKG.OT.BATCH.V1",
                &[
                    &context,
                    &sender.to_be_bytes(),
                    &receiver.to_be_bytes(),
                    &(batch as u64).to_be_bytes(),
                    &(operand.len() as u64).to_be_bytes(),
                ],
            );
            if self.party_id == sender {
                // Guards, so a failing or unwinding OT backend still erases the pads.
                let mut raw = SecretBuffer(vec![0u8; inputs.len() * 128 * 16]);
                cshake256_framed_xof(b"QSAG.DKG.OT.PADS.V1", &[&self.entropy, &context], &mut raw);
                let mut alternatives = SecretVec::<[u128; 2]>::with_capacity(inputs.len() * 128);
                for (&x, pads) in inputs.iter().zip(raw.as_chunks::<{ 128 * 16 }>().0.iter()) {
                    // Successive x*z^bit values need one shift/reduction each, not
                    // 128 independent general field multiplications. Reduction is
                    // branchless modulo z^128 + z^7 + z^2 + z + 1.
                    let mut term = SecretBuffer([x]);
                    let mut share = 0;
                    for pad in pads.as_chunks::<16>().0.iter() {
                        let r = u128::from_le_bytes(*pad);
                        share ^= r;
                        alternatives.push([r, r ^ term[0]]);
                        term[0] = (term[0] << 1) ^ (0x87 & 0u128.wrapping_sub(term[0] >> 127));
                    }
                    shares.push(share);
                }
                self.ot.send(receiver, context, &alternatives)?;
            } else {
                let selected = self.ot.receive(sender, context, inputs)?;
                if selected.len() != inputs.len() * 128 {
                    return Err(ParallelSeededError::BdozMacCheckFailed);
                }
                shares.0.extend(
                    selected
                        .0
                        .as_chunks::<128>()
                        .0
                        .iter()
                        .map(|bits| bits.iter().fold(0, |a, b| a ^ b)),
                );
            }
        }
        Ok(core::mem::take(&mut shares.0))
    }

    fn cross_products(
        &mut self,
        context: [u8; 32],
        roster: &[u16],
        width: usize,
        sender_operand: &[u128],
        receiver_operand: &[u128],
    ) -> Result<Vec<u128>, ParallelSeededError> {
        if width == 0
            || width > 3
            || receiver_operand.len().checked_mul(width) != Some(sender_operand.len())
            || !valid_product_roster(roster, self.party_id)
        {
            return Err(ParallelSeededError::InvalidThresholdParameters);
        }
        let peers: Vec<u16> = roster
            .iter()
            .copied()
            .filter(|&id| id != self.party_id)
            .collect();
        let mut shares = SecretBuffer(vec![0u128; sender_operand.len()]);
        for (flight, ((xs, ys), shares)) in sender_operand
            .chunks(GILBOA_FLIGHT_WORDS * width)
            .zip(receiver_operand.chunks(GILBOA_FLIGHT_WORDS))
            .zip(shares.chunks_mut(GILBOA_FLIGHT_WORDS * width))
            .enumerate()
        {
            let context = cshake256_framed_32(
                b"QSAG.DKG.GILBOA.FLIGHT.V1",
                &[
                    &context,
                    &(flight as u64).to_be_bytes(),
                    &(receiver_operand.len() as u64).to_be_bytes(),
                    &(width as u64).to_be_bytes(),
                ],
            );
            let plan: Vec<_> = peers
                .iter()
                .map(|&peer| ParallelSeededDkgOtPeer {
                    peer,
                    send_words: ys.len(),
                    choices: ys,
                })
                .collect();
            let pads = self.ot.random_ots(context, &plan)?;
            if pads.len() != peers.len()
                || pads
                    .iter()
                    .any(|p| p.sent.len() != ys.len() * 128 || p.received.len() != ys.len() * 128)
            {
                return Err(ParallelSeededError::BdozMacCheckFailed);
            }
            // As OT sender: keep the zero pad, send `pad0 + pad1 + x*z^bit` per operand.
            for (&peer, pads) in peers.iter().zip(&pads) {
                let mut corrections = Vec::with_capacity(xs.len() * 128);
                for ((terms, pads), shares) in xs
                    .chunks(width)
                    .zip(pads.sent.chunks(128))
                    .zip(shares.chunks_mut(width))
                {
                    let mut term = SecretBuffer([0u128; 3]);
                    term[..width].copy_from_slice(terms);
                    for (zero, one) in pads {
                        for segment in 0..width {
                            let pad = pad_word(zero, segment);
                            shares[segment] ^= pad;
                            corrections.push(pad ^ pad_word(one, segment) ^ term[segment]);
                            term[segment] = mul_z(term[segment]);
                        }
                    }
                }
                self.ot.send_words(peer, context, corrections)?;
            }
            // As OT receiver: the chosen pad, plus the correction where the bit is set.
            for (&peer, pads) in peers.iter().zip(&pads) {
                let corrections = self.ot.receive_words(peer, context, xs.len() * 128)?;
                if corrections.len() != xs.len() * 128 {
                    return Err(ParallelSeededError::BdozMacCheckFailed);
                }
                for (((&y, pads), corrections), shares) in ys
                    .iter()
                    .zip(pads.received.chunks(128))
                    .zip(corrections.chunks(128 * width))
                    .zip(shares.chunks_mut(width))
                {
                    for (bit, (pad, corrections)) in
                        pads.iter().zip(corrections.chunks(width)).enumerate()
                    {
                        let mask = 0u128.wrapping_sub((y >> bit) & 1);
                        for segment in 0..width {
                            shares[segment] ^=
                                pad_word(pad, segment) ^ (mask & corrections[segment]);
                        }
                    }
                }
            }
        }
        Ok(core::mem::take(&mut shares.0))
    }

    fn keyed_products(
        &mut self,
        context: [u8; 32],
        roster: &[u16],
        key: u128,
        values: &[u128],
    ) -> Result<Vec<u128>, ParallelSeededError> {
        if !valid_product_roster(roster, self.party_id) {
            return Err(ParallelSeededError::InvalidThresholdParameters);
        }
        let mut shares = SecretBuffer(vec![0u128; values.len()]);
        if values.is_empty() {
            return Ok(core::mem::take(&mut shares.0));
        }
        let peers: Vec<u16> = roster
            .iter()
            .copied()
            .filter(|&id| id != self.party_id)
            .collect();
        let context = cshake256_framed_32(
            b"QSAG.DKG.KEYED.SEEDS.V1",
            &[&context, &(values.len() as u64).to_be_bytes()],
        );
        let key = SecretBuffer([key]);
        let plan: Vec<_> = peers
            .iter()
            .map(|&peer| ParallelSeededDkgOtPeer {
                peer,
                send_words: 1,
                choices: &key[..],
            })
            .collect();
        let seeds = self.ot.random_ots(context, &plan)?;
        if seeds.len() != peers.len()
            || seeds
                .iter()
                .any(|s| s.sent.len() != 128 || s.received.len() != 128)
        {
            return Err(ParallelSeededError::BdozMacCheckFailed);
        }
        for (block, (values, shares)) in values
            .chunks(KEYED_BLOCK)
            .zip(shares.chunks_mut(KEYED_BLOCK))
            .enumerate()
        {
            let context = cshake256_framed_32(
                b"QSAG.DKG.KEYED.BLOCK.V1",
                &[&context, &(block as u64).to_be_bytes()],
            );
            let count = values.len();
            let context = &context;
            // As value holder: both streams of every seed pair; the peer learns one of them.
            let mut corrections: Vec<Vec<u128>> =
                peers.iter().map(|_| vec![0u128; 128 * count]).collect();
            let mut units = Vec::with_capacity(peers.len() * 128 / KEYED_UNIT);
            for (seeds, corrections) in seeds.iter().zip(&mut corrections) {
                units.extend(
                    seeds
                        .sent
                        .chunks(KEYED_UNIT)
                        .zip(corrections.chunks_mut(KEYED_UNIT * count)),
                );
            }
            let folds = in_parallel(units, |(pairs, rows)| {
                keyed_value_unit(pairs, context, values, rows)
            });
            add_unit_folds(shares, &folds, peers.len());
            for (&peer, corrections) in peers.iter().zip(corrections) {
                self.ot.send_words(peer, *context, corrections)?;
            }
            // As key holder: the stream of the chosen seed, corrected where the key bit is set.
            let mut corrections = Vec::with_capacity(peers.len());
            for &peer in &peers {
                let words = self.ot.receive_words(peer, *context, 128 * count)?;
                if words.len() != 128 * count {
                    return Err(ParallelSeededError::BdozMacCheckFailed);
                }
                corrections.push(words);
            }
            let mut units = Vec::with_capacity(peers.len() * 128 / KEYED_UNIT);
            for (seeds, corrections) in seeds.iter().zip(&corrections) {
                units.extend(
                    seeds
                        .received
                        .chunks(KEYED_UNIT)
                        .zip(corrections.chunks(KEYED_UNIT * count))
                        .enumerate()
                        .map(|(unit, (chosen, rows))| {
                            (key[0] >> (unit * KEYED_UNIT), chosen, rows)
                        }),
                );
            }
            let folds = in_parallel(units, |(key_bits, chosen, rows)| {
                keyed_key_unit(chosen, context, key_bits, rows)
            });
            add_unit_folds(shares, &folds, peers.len());
        }
        Ok(core::mem::take(&mut shares.0))
    }
}

struct Products<'a, T> {
    backend: &'a mut T,
    roster: &'a [u16],
    context: [u8; 32],
    sequence: u64,
}
impl<T: ParallelSeededDkgProducts> Products<'_, T> {
    fn next_context(&mut self, len: usize) -> [u8; 32] {
        let context = cshake256_framed_32(
            b"QSAG.DKG.PRODUCT.V1",
            &[
                &self.context,
                &self.sequence.to_be_bytes(),
                &(len as u64).to_be_bytes(),
            ],
        );
        self.sequence += 1;
        context
    }
    fn add_cross_terms(
        mut local: SecretVec<u128>,
        cross: Vec<u128>,
    ) -> Result<SecretVec<u128>, ParallelSeededError> {
        let cross = SecretBuffer(cross);
        if cross.len() != local.len() {
            return Err(ParallelSeededError::BdozMacCheckFailed);
        }
        for (sum, contribution) in local.iter_mut().zip(cross.iter()) {
            *sum ^= contribution;
        }
        Ok(local)
    }
    /// Shares of `x[j*width + k] * y[j]`.
    fn multiply(
        &mut self,
        width: usize,
        x: &[u128],
        y: &[u128],
    ) -> Result<SecretVec<u128>, ParallelSeededError> {
        if width == 0 || y.len().checked_mul(width) != Some(x.len()) {
            return Err(ParallelSeededError::InvalidThresholdParameters);
        }
        let local = SecretBuffer(
            x.chunks(width)
                .zip(y)
                .flat_map(|(xs, &b)| xs.iter().map(move |&a| gf2_128_mul(a, b)))
                .collect::<Vec<u128>>(),
        );
        let context = self.next_context(x.len());
        let cross = self
            .backend
            .cross_products(context, self.roster, width, x, y)?;
        Self::add_cross_terms(local, cross)
    }
    /// Shares of `key * values[j]`, where every party contributes its own key share.
    fn authenticate(
        &mut self,
        key: u128,
        values: &[u128],
    ) -> Result<SecretVec<u128>, ParallelSeededError> {
        let local = SecretBuffer(
            values
                .iter()
                .map(|&value| gf2_128_mul(key, value))
                .collect::<Vec<u128>>(),
        );
        let context = self.next_context(values.len());
        let cross = self
            .backend
            .keyed_products(context, self.roster, key, values)?;
        Self::add_cross_terms(local, cross)
    }
}

/// A genuine Beaver triple, separate from the historical power-pool alias: this
/// party's additive value shares and two MAC shares. Single use, so not `Clone`;
/// the shares stay inside the crate, wiped on drop.
/// ```compile_fail
/// fn leak(triple: &qsag_fts::ParallelSeededDkgBeaverShare) -> [u128; 3] { triple.values }
/// ```
/// ```compile_fail
/// fn leak(triple: &qsag_fts::ParallelSeededDkgBeaverShare) -> [[u128; 2]; 3] { triple.macs }
/// ```
/// ```compile_fail
/// fn forge() -> qsag_fts::ParallelSeededDkgBeaverShare {
///     qsag_fts::ParallelSeededDkgBeaverShare { values: [0; 3], macs: [[0; 2]; 3] }
/// }
/// ```
/// ```compile_fail
/// fn dup(t: &qsag_fts::ParallelSeededDkgBeaverShare) -> qsag_fts::ParallelSeededDkgBeaverShare {
///     t.clone()
/// }
/// ```
pub struct ParallelSeededDkgBeaverShare {
    pub(super) values: [u128; 3],
    pub(super) macs: [[u128; 2]; 3],
}
impl fmt::Debug for ParallelSeededDkgBeaverShare {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("ParallelSeededDkgBeaverShare(<REDACTED>)")
    }
}
impl Drop for ParallelSeededDkgBeaverShare {
    fn drop(&mut self) {
        ct_zeroize_u128s(&mut self.values);
        for mac in &mut self.macs {
            ct_zeroize_u128s(mac);
        }
    }
}
/// The key share and preprocessing released by
/// [`ParallelSeededDkgUnverifiedOutput::activate`], and only by it: the share is not a
/// public field, so a caller cannot assemble an "activated" output around a share that
/// never passed the consistency check.
/// ```compile_fail
/// fn forge(share: qsag_fts::ParallelSeededPartyShare) -> qsag_fts::ParallelSeededDkgOutput {
///     qsag_fts::ParallelSeededDkgOutput {
///         pk_seed_bytes: [0; 32],
///         share,
///         beaver_triples: Vec::new(),
///     }
/// }
/// ```
/// ```compile_fail
/// fn take(output: qsag_fts::ParallelSeededDkgOutput) -> qsag_fts::ParallelSeededPartyShare {
///     output.share
/// }
/// ```
/// Positive control: the public seed, the preprocessing count and the share for a
/// signing session remain reachable.
/// ```
/// fn inspect(output: &mut qsag_fts::ParallelSeededDkgOutput) -> ([u8; 32], usize, bool) {
///     let poisoned = output.share_mut().is_poisoned();
///     (output.pk_seed_bytes, output.beaver_triples.len(), poisoned)
/// }
/// ```
pub struct ParallelSeededDkgOutput {
    pub pk_seed_bytes: [u8; 32],
    pub(crate) share: ParallelSeededPartyShare,
    pub beaver_triples: Vec<ParallelSeededDkgBeaverShare>,
}
impl ParallelSeededDkgOutput {
    /// The activated key share, for [`ParallelSeededSignSession::begin`] and
    /// [`ParallelSeededSignSession::begin_leaf_preparation`].
    pub fn share_mut(&mut self) -> &mut ParallelSeededPartyShare {
        &mut self.share
    }
}

/// Public index layout of the authenticated value vector: four key lanes, the power tuples
/// `(a, ..., a^7)`, the output triples and one sacrificial triple for each, one sacrificial
/// pair `(u, u*a)` per power tuple, the square-check mask pair `(r, r^2)`, and the fold mask.
#[derive(Clone, Copy)]
struct CheckLayout {
    power_count: usize,
    output_triples: usize,
}
impl CheckLayout {
    fn new(power_count: usize, output_triples: usize) -> Option<Self> {
        // The whole value vector, including the trailing masks, must be addressable.
        power_count
            .checked_mul(9)?
            .checked_add(output_triples.checked_mul(6)?)?
            .checked_add(7)?;
        Some(Self {
            power_count,
            output_triples,
        })
    }
    /// Value `a^(exponent + 1)` of tuple `index`.
    fn power(&self, index: usize, exponent: usize) -> usize {
        4 + 7 * index + exponent
    }
    /// Output triples first, then their sacrificial triples.
    fn total_triples(&self) -> usize {
        2 * self.output_triples
    }
    fn triple(&self, index: usize, part: usize) -> usize {
        self.power(self.power_count, 0) + 3 * index + part
    }
    /// The sacrificial pair of power tuple `index`: `u` at part 0, `u*a` at part 1.
    fn sacrifice(&self, index: usize, part: usize) -> usize {
        self.triple(self.total_triples(), 0) + 2 * index + part
    }
    fn square_mask(&self, part: usize) -> usize {
        self.sacrifice(self.power_count, 0) + part
    }
    /// Values handed to the caller after activation; all of them enter the masked opening.
    fn output_value_count(&self) -> usize {
        self.triple(self.output_triples, 0)
    }
    fn mask_index(&self) -> usize {
        self.square_mask(2)
    }
    fn value_count(&self) -> usize {
        self.mask_index() + 1
    }
    /// Challenges: one per output triple, then two per power tuple.
    fn challenge_count(&self) -> usize {
        self.output_triples + 2 * self.power_count
    }
    /// MAC weights: three per output triple, two per power tuple, two for the squares, one
    /// for the folded outputs.
    fn mac_weight_count(&self) -> usize {
        3 * self.output_triples + 2 * self.power_count + 3
    }
}

/// The two coin-derived challenges of one power tuple, with the powers the check uses.
///
/// `s` combines the three products that share the factor `a`. Every weight has positive
/// degree, so the sacrificial product is the constant term of the checked polynomial and
/// cannot absorb an error in a power. `theta` weights the three squarings: a square root
/// `theta^k` is paired with its image `theta^(2k)`, because squaring is additive.
struct PowerChallenge {
    s: [u128; 3],
    theta: [u128; 3],
}
impl PowerChallenge {
    fn new(challenge: &[u128; 2]) -> Self {
        let [s, theta] = *challenge;
        let (s2, theta2) = (gf2_128_mul(s, s), gf2_128_mul(theta, theta));
        Self {
            s: [s, s2, gf2_128_mul(s2, s)],
            theta: [theta, theta2, gf2_128_mul(theta2, theta)],
        }
    }
    fn combine(weights: &[u128; 3], values: [u128; 3]) -> u128 {
        gf2_128_mul(weights[0], values[0])
            ^ gf2_128_mul(weights[1], values[1])
            ^ gf2_128_mul(weights[2], values[2])
    }
    /// `s*x + s^2*y + s^3*z`: the same combination of three factors or of three products.
    fn products(&self, x: u128, y: u128, z: u128) -> u128 {
        Self::combine(&self.s, [x, y, z])
    }
    /// `theta*x + theta^2*y + theta^3*z`, for the values being squared.
    fn square_roots(&self, x: u128, y: u128, z: u128) -> u128 {
        Self::combine(&self.theta, [x, y, z])
    }
    /// `theta^2*x + theta^4*y + theta^6*z`, for the claimed squares.
    fn squares(&self, x: u128, y: u128, z: u128) -> u128 {
        let squared = self.theta.map(|weight| gf2_128_mul(weight, weight));
        Self::combine(&squared, [x, y, z])
    }
}

fn check_coin_digest(context: &[u8; 32], id: u16, coin: &[u8; 32]) -> [u8; 32] {
    cshake256_framed_32(
        b"QSAG.DKG.CHECK.COIN_COMMIT.V1",
        &[context, &id.to_be_bytes(), coin],
    )
}
fn check_tag_digest(context: &[u8; 32], id: u16, tags: &[u128; 2], salt: &[u8; 32]) -> [u8; 32] {
    cshake256_framed_32(
        b"QSAG.DKG.CHECK.TAG_COMMIT.V1",
        &[
            context,
            &id.to_be_bytes(),
            &tags[0].to_le_bytes(),
            &tags[1].to_le_bytes(),
            salt,
        ],
    )
}

/// Broadcast first: binds this party's check coin before any coin is opened.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParallelSeededDkgCheckCommit {
    pub party_id: u16,
    pub context: [u8; 32],
    pub digest: [u8; 32],
}
/// Broadcast second, only after every [`ParallelSeededDkgCheckCommit`] is frozen.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParallelSeededDkgCheckCoin {
    pub party_id: u16,
    pub context: [u8; 32],
    pub coin: [u8; 32],
}
/// Broadcast third: this party's additive shares of every masked opening. `rho` holds one
/// entry per output triple and then one per power tuple, `sigma` one per output triple.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParallelSeededDkgCheckShares {
    pub party_id: u16,
    pub context: [u8; 32],
    pub rho: Vec<u128>,
    pub sigma: Vec<u128>,
    /// The masked combination of the square check.
    pub square: u128,
    pub masked: u128,
}
/// Broadcast fourth: binds this party's MAC tags before any tag is opened.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParallelSeededDkgCheckTagCommit {
    pub party_id: u16,
    pub context: [u8; 32],
    pub digest: [u8; 32],
}
/// Broadcast fifth, only after every [`ParallelSeededDkgCheckTagCommit`] is frozen.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParallelSeededDkgCheckTagOpen {
    pub party_id: u16,
    pub context: [u8; 32],
    pub tags: [u128; 2],
    pub salt: [u8; 32],
}

/// One custodian's DKG result before the active consistency check. The share and preprocessing
/// are released only by [`Self::activate`]. Every method must see the same authenticated
/// broadcast, in roster order, at every party. Any error is final for this ceremony.
pub struct ParallelSeededDkgUnverifiedOutput {
    output: Option<ParallelSeededDkgOutput>,
    roster: Vec<u16>,
    party_id: u16,
    context: [u8; 32],
    layout: CheckLayout,
    alpha: [u128; 2],
    values: SecretVec<u128>,
    macs: [SecretVec<u128>; 2],
    coin: [u8; 32],
    salt: [u8; 32],
    step: u8,
    coin_commits: Vec<ParallelSeededDkgCheckCommit>,
    joint_coin: [u8; 32],
    own_shares_digest: [u8; 32],
    tags: [u128; 2],
    tag_commits: Vec<ParallelSeededDkgCheckTagCommit>,
}
impl Drop for ParallelSeededDkgUnverifiedOutput {
    fn drop(&mut self) {
        ct_zeroize_u128s(&mut self.alpha);
        ct_zeroize_u128s(&mut self.tags);
        ct_zeroize_bytes(&mut self.coin);
        ct_zeroize_bytes(&mut self.salt);
    }
}
impl ParallelSeededDkgUnverifiedOutput {
    const FAILED: u8 = u8::MAX;

    fn fail<T>(&mut self, error: ParallelSeededError) -> Result<T, ParallelSeededError> {
        self.step = Self::FAILED;
        self.output = None;
        Err(error)
    }
    /// A broadcast is acceptable only if it has one entry per roster member, in roster order,
    /// bound to this ceremony's check context.
    fn roster_matches(&self, entries: impl ExactSizeIterator<Item = (u16, [u8; 32])>) -> bool {
        entries.len() == self.roster.len()
            && entries
                .zip(&self.roster)
                .all(|((id, context), expected)| id == *expected && context == self.context)
    }
    fn challenge_frames(&self) -> [[u8; 8]; 2] {
        [
            (self.layout.power_count as u64).to_be_bytes(),
            (self.layout.output_triples as u64).to_be_bytes(),
        ]
    }
    fn relation_challenges(&self) -> Vec<u128> {
        let [powers, triples] = self.challenge_frames();
        xof_field_elements(
            b"QSAG.DKG.CHECK.SACRIFICE_T.V1",
            &[&self.context, &self.joint_coin, &powers, &triples],
            self.layout.challenge_count(),
        )
    }
    fn fold_weights(&self) -> Vec<u128> {
        let [powers, triples] = self.challenge_frames();
        xof_field_elements(
            b"QSAG.DKG.CHECK.FOLD_WEIGHTS.V1",
            &[&self.context, &self.joint_coin, &powers, &triples],
            self.layout.output_value_count(),
        )
    }
    fn shares_digest(shares: &ParallelSeededDkgCheckShares) -> [u8; 32] {
        let mut bytes = Vec::with_capacity((shares.rho.len() + shares.sigma.len() + 2) * 16);
        for value in shares
            .rho
            .iter()
            .chain(&shares.sigma)
            .chain([&shares.square, &shares.masked])
        {
            bytes.extend_from_slice(&value.to_le_bytes());
        }
        cshake256_framed_32(
            b"QSAG.DKG.CHECK.SHARES.V1",
            &[
                &shares.context,
                &shares.party_id.to_be_bytes(),
                &(shares.rho.len() as u64).to_be_bytes(),
                &(shares.sigma.len() as u64).to_be_bytes(),
                &bytes,
            ],
        )
    }

    /// Step 1: this party's check-coin commitment.
    pub fn check_commitment(&self) -> ParallelSeededDkgCheckCommit {
        ParallelSeededDkgCheckCommit {
            party_id: self.party_id,
            context: self.context,
            digest: check_coin_digest(&self.context, self.party_id, &self.coin),
        }
    }
    /// Step 2: freeze every party's coin commitment, then reveal this party's coin.
    pub fn reveal_check_coin(
        &mut self,
        commits: &[ParallelSeededDkgCheckCommit],
    ) -> Result<ParallelSeededDkgCheckCoin, ParallelSeededError> {
        if self.step != 0
            || !self.roster_matches(commits.iter().map(|c| (c.party_id, c.context)))
            || !commits.contains(&self.check_commitment())
        {
            return self.fail(ParallelSeededError::InvalidThresholdParameters);
        }
        self.coin_commits = commits.to_vec();
        self.step = 1;
        Ok(ParallelSeededDkgCheckCoin {
            party_id: self.party_id,
            context: self.context,
            coin: self.coin,
        })
    }
    /// Step 3: verify every coin opening, derive the challenges, and return this party's
    /// shares of the masked openings.
    pub fn masked_shares(
        &mut self,
        coins: &[ParallelSeededDkgCheckCoin],
    ) -> Result<ParallelSeededDkgCheckShares, ParallelSeededError> {
        if self.step != 1 || !self.roster_matches(coins.iter().map(|c| (c.party_id, c.context))) {
            return self.fail(ParallelSeededError::InvalidThresholdParameters);
        }
        let mismatch = coins.iter().zip(&self.coin_commits).find(|(coin, commit)| {
            !ct_eq_bytes(
                &check_coin_digest(&self.context, coin.party_id, &coin.coin),
                &commit.digest,
            )
        });
        if let Some(party_id) = mismatch.map(|(coin, _)| coin.party_id) {
            return self.fail(ParallelSeededError::CommitmentMismatch { party_id });
        }
        let mut opened = Vec::with_capacity(coins.len() * 32);
        for coin in coins {
            opened.extend_from_slice(&coin.coin);
        }
        self.joint_coin =
            cshake256_framed_32(b"QSAG.DKG.CHECK.JOINT_COIN.V1", &[&self.context, &opened]);
        let challenges = self.relation_challenges();
        let weights = self.fold_weights();
        let values = &self.values.0;
        let layout = self.layout;
        let triples = layout.output_triples;
        let mut rho = Vec::with_capacity(triples + layout.power_count);
        let mut sigma = Vec::with_capacity(triples);
        for (index, &t) in challenges[..triples].iter().enumerate() {
            let sacrifice = triples + index;
            rho.push(
                gf2_128_mul(t, values[layout.triple(index, 0)])
                    ^ values[layout.triple(sacrifice, 0)],
            );
            sigma.push(values[layout.triple(index, 1)] ^ values[layout.triple(sacrifice, 1)]);
        }
        let mut square = values[layout.square_mask(0)];
        for (index, challenge) in challenges[triples..].as_chunks::<2>().0.iter().enumerate() {
            let powers = &values[layout.power(index, 0)..layout.power(index, 7)];
            let s = PowerChallenge::new(challenge);
            rho.push(
                s.products(powers[1], powers[3], powers[5]) ^ values[layout.sacrifice(index, 0)],
            );
            square ^= s.square_roots(powers[0], powers[1], powers[2]);
        }
        let masked = weights
            .iter()
            .zip(values)
            .fold(values[layout.mask_index()], |acc, (&weight, &value)| {
                acc ^ gf2_128_mul(weight, value)
            });
        let shares = ParallelSeededDkgCheckShares {
            party_id: self.party_id,
            context: self.context,
            rho,
            sigma,
            square,
            masked,
        };
        self.own_shares_digest = Self::shares_digest(&shares);
        self.step = 2;
        Ok(shares)
    }
    /// Step 4: reconstruct the masked openings from every party's shares, compute this party's
    /// MAC tag on both lanes, and commit to it.
    pub fn tag_commitment(
        &mut self,
        shares: &[ParallelSeededDkgCheckShares],
    ) -> Result<ParallelSeededDkgCheckTagCommit, ParallelSeededError> {
        let layout = self.layout;
        let triples = layout.output_triples;
        if self.step != 2
            || !self.roster_matches(shares.iter().map(|s| (s.party_id, s.context)))
            || shares
                .iter()
                .any(|s| s.rho.len() != triples + layout.power_count || s.sigma.len() != triples)
            || !shares.iter().any(|s| {
                s.party_id == self.party_id
                    && ct_eq_bytes(&Self::shares_digest(s), &self.own_shares_digest)
            })
        {
            return self.fail(ParallelSeededError::InvalidThresholdParameters);
        }
        let mut rho = vec![0u128; triples + layout.power_count];
        let mut sigma = vec![0u128; triples];
        let (mut square, mut masked) = (0u128, 0u128);
        let mut transcript = Vec::with_capacity(shares.len() * 32);
        for share in shares {
            for (acc, value) in rho.iter_mut().zip(&share.rho) {
                *acc ^= value;
            }
            for (acc, value) in sigma.iter_mut().zip(&share.sigma) {
                *acc ^= value;
            }
            square ^= share.square;
            masked ^= share.masked;
            transcript.extend_from_slice(&Self::shares_digest(share));
        }
        let challenges = self.relation_challenges();
        let weights = self.fold_weights();
        // The MAC weights depend on every broadcast share, so they are fixed only after the
        // opened values are.
        let mac_weights = xof_field_elements(
            b"QSAG.DKG.CHECK.MAC_WEIGHTS.V1",
            &[&self.context, &self.joint_coin, &transcript],
            layout.mac_weight_count(),
        );
        let (triple_weights, rest) = mac_weights.split_at(3 * triples);
        let (power_weights, tail_weights) = rest.split_at(2 * layout.power_count);
        let mut tags = SecretBuffer([0u128; 2]);
        for (lane, tag) in tags.iter_mut().enumerate() {
            let (alpha, mac) = (self.alpha[lane], &self.macs[lane].0);
            for (index, weights) in triple_weights.as_chunks::<3>().0.iter().enumerate() {
                let sacrifice = triples + index;
                let (x, y, c) = (
                    mac[layout.triple(index, 0)],
                    mac[layout.triple(index, 1)],
                    mac[layout.triple(index, 2)],
                );
                let (u, v, w) = (
                    mac[layout.triple(sacrifice, 0)],
                    mac[layout.triple(sacrifice, 1)],
                    mac[layout.triple(sacrifice, 2)],
                );
                let (t, rho, sigma) = (challenges[index], rho[index], sigma[index]);
                let rho_tag = gf2_128_mul(t, x) ^ u ^ gf2_128_mul(alpha, rho);
                let sigma_tag = y ^ v ^ gf2_128_mul(alpha, sigma);
                // MAC share of `t*c + w + sigma*u + rho*v + rho*sigma`, which must open to zero.
                let zero_tag = gf2_128_mul(t, c)
                    ^ w
                    ^ gf2_128_mul(sigma, u)
                    ^ gf2_128_mul(rho, v)
                    ^ gf2_128_mul(alpha, gf2_128_mul(rho, sigma));
                *tag ^= gf2_128_mul(weights[0], rho_tag)
                    ^ gf2_128_mul(weights[1], sigma_tag)
                    ^ gf2_128_mul(weights[2], zero_tag);
            }
            // MAC shares of the square check's opened combination and of its squared image.
            let mut square_tag = mac[layout.square_mask(0)] ^ gf2_128_mul(alpha, square);
            let mut squared_tag =
                mac[layout.square_mask(1)] ^ gf2_128_mul(alpha, gf2_128_mul(square, square));
            for (index, (challenge, weights)) in challenges[triples..]
                .as_chunks::<2>()
                .0
                .iter()
                .zip(power_weights.as_chunks::<2>().0)
                .enumerate()
            {
                let powers = &mac[layout.power(index, 0)..layout.power(index, 7)];
                let s = PowerChallenge::new(challenge);
                let rho = rho[triples + index];
                let rho_tag = s.products(powers[1], powers[3], powers[5])
                    ^ mac[layout.sacrifice(index, 0)]
                    ^ gf2_128_mul(alpha, rho);
                // MAC share of `s*a^3 + s^2*a^5 + s^3*a^7 + u*a + rho*a`, which must open to zero.
                let zero_tag = s.products(powers[2], powers[4], powers[6])
                    ^ mac[layout.sacrifice(index, 1)]
                    ^ gf2_128_mul(rho, powers[0]);
                *tag ^= gf2_128_mul(weights[0], rho_tag) ^ gf2_128_mul(weights[1], zero_tag);
                square_tag ^= s.square_roots(powers[0], powers[1], powers[2]);
                squared_tag ^= s.squares(powers[1], powers[3], powers[5]);
            }
            let masked_tag = weights.iter().zip(mac).fold(
                mac[layout.mask_index()] ^ gf2_128_mul(alpha, masked),
                |acc, (&weight, &share)| acc ^ gf2_128_mul(weight, share),
            );
            *tag ^= gf2_128_mul(tail_weights[0], square_tag)
                ^ gf2_128_mul(tail_weights[1], squared_tag)
                ^ gf2_128_mul(tail_weights[2], masked_tag);
        }
        self.tags = *tags;
        self.step = 3;
        Ok(ParallelSeededDkgCheckTagCommit {
            party_id: self.party_id,
            context: self.context,
            digest: check_tag_digest(&self.context, self.party_id, &self.tags, &self.salt),
        })
    }
    /// Step 5: freeze every party's tag commitment, then open this party's tags.
    pub fn open_tags(
        &mut self,
        commits: &[ParallelSeededDkgCheckTagCommit],
    ) -> Result<ParallelSeededDkgCheckTagOpen, ParallelSeededError> {
        let own = check_tag_digest(&self.context, self.party_id, &self.tags, &self.salt);
        if self.step != 3
            || !self.roster_matches(commits.iter().map(|c| (c.party_id, c.context)))
            || !commits
                .iter()
                .any(|c| c.party_id == self.party_id && ct_eq_bytes(&c.digest, &own))
        {
            return self.fail(ParallelSeededError::InvalidThresholdParameters);
        }
        self.tag_commits = commits.to_vec();
        self.step = 4;
        Ok(ParallelSeededDkgCheckTagOpen {
            party_id: self.party_id,
            context: self.context,
            tags: self.tags,
            salt: self.salt,
        })
    }
    /// Verify every tag opening against its commitment and require the tags to cancel on both
    /// MAC lanes. Only then is the key share released.
    pub fn activate(
        mut self,
        openings: &[ParallelSeededDkgCheckTagOpen],
    ) -> Result<ParallelSeededDkgOutput, ParallelSeededError> {
        if self.step != 4 || !self.roster_matches(openings.iter().map(|o| (o.party_id, o.context)))
        {
            return self.fail(ParallelSeededError::InvalidThresholdParameters);
        }
        let mismatch = openings
            .iter()
            .zip(&self.tag_commits)
            .find(|(open, commit)| {
                !ct_eq_bytes(
                    &check_tag_digest(&self.context, open.party_id, &open.tags, &open.salt),
                    &commit.digest,
                )
            });
        if let Some(party_id) = mismatch.map(|(open, _)| open.party_id) {
            return self.fail(ParallelSeededError::CommitmentMismatch { party_id });
        }
        let sum = openings.iter().fold([0u128; 2], |acc, open| {
            [acc[0] ^ open.tags[0], acc[1] ^ open.tags[1]]
        });
        if !(qsag_accel::ct::ct_eq_u128(sum[0], 0) & qsag_accel::ct::ct_eq_u128(sum[1], 0)) {
            return self.fail(ParallelSeededError::BdozMacCheckFailed);
        }
        self.output.take().ok_or(ParallelSeededError::Poisoned)
    }
}

/// Finalize only one custodian. Commitments must already be frozen. Private
/// packages contain exactly the incoming lower-ID pair seeds. All cross terms,
/// including both MAC lanes, flow through pairwise oblivious products; alpha and
/// global seeds are never formed. Any error consumes and erases local state.
///
/// The result is unverified: run the consistency check on it and call
/// [`ParallelSeededDkgUnverifiedOutput::activate`] to obtain the key share.
pub fn finalize_parallel_seeded_dkg_party<T: ParallelSeededDkgProducts>(
    state: ParallelSeededDkgRound1State,
    openings: &[ParallelSeededDkgRound2Open],
    packages: Vec<ParallelSeededDkgSharePackage>,
    backend: &mut T,
) -> Result<ParallelSeededDkgUnverifiedOutput, ParallelSeededError> {
    finalize_dkg(state, openings, packages, backend, None)
}

pub(super) fn finalize_dkg<T: ParallelSeededDkgProducts>(
    state: ParallelSeededDkgRound1State,
    openings: &[ParallelSeededDkgRound2Open],
    packages: Vec<ParallelSeededDkgSharePackage>,
    backend: &mut T,
    previous: Option<ParallelSeededPartyShare>,
) -> Result<ParallelSeededDkgUnverifiedOutput, ParallelSeededError> {
    let layout = CheckLayout::new(state.config.power_count, state.config.beaver_count)
        .ok_or(ParallelSeededError::InvalidThresholdParameters)?;
    let frozen = state.frozen_context()?;
    let commits = state
        .commits
        .as_ref()
        .ok_or(ParallelSeededError::InvalidThresholdParameters)?;
    if !state.packages_sent
        || backend.party_id() != state.party_id
        || openings.len() != commits.len()
    {
        return Err(ParallelSeededError::InvalidThresholdParameters);
    }
    let mut coin = [0u8; 32];
    for (open, commit) in openings.iter().zip(commits) {
        if open.party_id != commit.party_id
            || open.context != state.context
            || !ct_eq_bytes(
                &coin_digest(&state.context, open.party_id, &open.coin),
                &commit.digest,
            )
        {
            return Err(ParallelSeededError::CommitmentMismatch {
                party_id: commit.party_id,
            });
        }
        for (acc, value) in coin.iter_mut().zip(open.coin) {
            *acc ^= value;
        }
    }
    let key_seed = previous.as_ref().map_or_else(
        || cshake256_framed_32(b"QSAG.DKG.PUBLIC_SEED.V1", &[&frozen, &coin]),
        |share| share.key_seed,
    );
    let mut share = ParallelSeededPartyShare {
        party_id: state.party_id,
        params: state.config.params,
        key_seed,
        committee: state.config.roster.clone(),
        sk_seed_lanes: [0; 2],
        sk_seed_macs: [[0; 2]; 2],
        sk_prf_lanes: [0; 2],
        sk_prf_macs: [[0; 2]; 2],
        bdoz_alpha_share: [0; 2],
        local_salt_seed: cshake256_framed_32(b"QSAG.DKG.SALT.V1", &[&state.entropy, &frozen]),
        // Exact capacities: growth would free seed and share copies unerased.
        pairwise_zero_seeds: Vec::with_capacity(state.config.roster.len() - 1),
        beaver_pool: Vec::with_capacity(state.config.power_count),
        beaver_cursor: 0,
        epoch_uses: vec![0; 1usize << state.config.params.tree_height],
        poisoned: false,
        pending_openings: Vec::new(),
        #[cfg(test)]
        power_fault: false,
    };
    let incoming = state
        .config
        .roster
        .iter()
        .filter(|&&id| id < state.party_id)
        .count();
    if packages.len() != incoming {
        return Err(ParallelSeededError::InvalidThresholdParameters);
    }
    for &peer in &state.config.roster {
        if peer == state.party_id {
            continue;
        }
        let seed = SecretBytes::new(if peer > state.party_id {
            state.pair_seed(peer, &frozen)
        } else {
            let mut found = packages.iter().filter(|p| p.sender == peer);
            let p = found
                .next()
                .ok_or(ParallelSeededError::InvalidThresholdParameters)?;
            if found.next().is_some() || p.recipient != state.party_id || p.context != frozen {
                return Err(ParallelSeededError::InvalidThresholdParameters);
            }
            p.seed
        });
        share.pairwise_zero_seeds.push((peer, *seed));
    }
    // A refill must prove continuity with the already authenticated key, not
    // authenticate a replacement key selected by a malicious party. Preserve
    // the original four MACs; they participate in the masked share commitment.
    let previous_key_macs = previous.as_ref().map(|share| {
        SecretBuffer([
            share.sk_seed_macs[0],
            share.sk_seed_macs[1],
            share.sk_prf_macs[0],
            share.sk_prf_macs[1],
        ])
    });
    let private = if let Some(mut previous) = previous {
        share.epoch_uses = core::mem::take(&mut previous.epoch_uses);
        SecretBuffer(vec![
            previous.sk_seed_lanes[0],
            previous.sk_seed_lanes[1],
            previous.sk_prf_lanes[0],
            previous.sk_prf_lanes[1],
            previous.bdoz_alpha_share[0],
            previous.bdoz_alpha_share[1],
        ])
    } else {
        state.sample(b"KEYS", 6)
    };
    share.sk_seed_lanes.copy_from_slice(&private.0[..2]);
    share.sk_prf_lanes.copy_from_slice(&private.0[2..4]);
    share.bdoz_alpha_share.copy_from_slice(&private.0[4..6]);
    let mut products = Products {
        backend,
        roster: &state.config.roster,
        context: cshake256_framed_32(b"QSAG.DKG.CORRELATIONS.V1", &[&frozen, &key_seed]),
        sequence: 0,
    };
    let powers = state.config.power_count;
    let a = state.sample(b"POWER_MASKS", powers);
    let square = |values: &[u128]| {
        SecretBuffer(
            values
                .iter()
                .map(|&x| gf2_128_mul(x, x))
                .collect::<Vec<u128>>(),
        )
    };
    let (a2, sacrifice) = (square(&a), state.sample(b"POWER_SACRIFICE", powers));
    let a4 = square(&a2);
    // Every product of a power tuple has the factor `a`: `a^3 = a^2*a`, `a^5 = a^4*a`,
    // `a^7 = a^6*a`, and the sacrificial `u*a`. The first three share one set of OTs.
    let mut factors = SecretVec::<u128>::with_capacity(3 * powers);
    for ((&a2, &a4), &u) in a2.iter().zip(a4.iter()).zip(sacrifice.iter()) {
        factors.extend_from_slice(&[a2, a4, u]);
    }
    #[cfg_attr(not(test), expect(unused_mut))]
    let mut first = products.multiply(3, &factors, &a)?;
    #[cfg(test)]
    for &(index, delta) in &state.product_faults {
        first[index] ^= delta;
    }
    let a3 = SecretBuffer(first.iter().step_by(3).copied().collect::<Vec<u128>>());
    let a6 = square(&a3);
    let a7 = products.multiply(1, &a6, &a)?;
    // Output triples first, then one sacrificial triple for each.
    let u = state.sample(b"BEAVER_U", layout.total_triples());
    let v = state.sample(b"BEAVER_V", layout.total_triples());
    let uv = if u.is_empty() {
        SecretBuffer(Vec::new())
    } else {
        products.multiply(1, &u, &v)?
    };
    let masks = state.sample(b"CHECK_MASKS", 2);
    let mut values = SecretVec::<u128>::with_capacity(layout.value_count());
    values.extend_from_slice(&private[..4]);
    for (index, products) in first.as_chunks::<3>().0.iter().enumerate() {
        values.extend_from_slice(&[
            a[index],
            a2[index],
            a3[index],
            a4[index],
            products[1],
            a6[index],
            a7[index],
        ]);
    }
    for ((&u, &v), &uv) in u.iter().zip(v.iter()).zip(uv.iter()) {
        values.extend_from_slice(&[u, v, uv]);
    }
    for (&u, products) in sacrifice.iter().zip(first.as_chunks::<3>().0) {
        values.extend_from_slice(&[u, products[2]]);
    }
    values.extend_from_slice(&[masks[0], gf2_128_mul(masks[0], masks[0]), masks[1]]);
    if values.len() != layout.value_count() {
        return Err(ParallelSeededError::InvalidThresholdParameters);
    }
    #[cfg(test)]
    for &(index, delta) in &state.value_faults {
        values[index] ^= delta;
    }
    let mut macs = Vec::new();
    for (lane, alpha) in share.bdoz_alpha_share.into_iter().enumerate() {
        let start = if previous_key_macs.is_some() { 4 } else { 0 };
        let mut authenticated = products.authenticate(alpha, &values[start..])?;
        if let Some(previous) = &previous_key_macs {
            let mut combined = SecretVec::<u128>::with_capacity(values.len());
            combined.extend(previous.iter().map(|mac| mac[lane]));
            combined.append(&mut authenticated.0);
            macs.push(combined);
        } else {
            macs.push(authenticated);
        }
    }
    let wire = |i: usize| AuthWire128 {
        val_sh: values.0[i],
        mac: [macs[0].0[i], macs[1].0[i]],
    };
    share.sk_seed_macs = [wire(0).mac, wire(1).mac];
    share.sk_prf_macs = [wire(2).mac, wire(3).mac];
    for index in 0..state.config.power_count {
        share.beaver_pool.push(AuthenticatedPowerShare {
            powers: core::array::from_fn(|j| wire(4 + index * 7 + j)),
        });
    }
    let start = 4 + state.config.power_count * 7;
    let beaver_triples = (0..state.config.beaver_count)
        .map(|i| ParallelSeededDkgBeaverShare {
            values: core::array::from_fn(|j| values.0[start + i * 3 + j]),
            macs: core::array::from_fn(|j| wire(start + i * 3 + j).mac),
        })
        .collect();
    let context = cshake256_framed_32(
        b"QSAG.DKG.CHECK.CONTEXT.V1",
        &[
            &frozen,
            &key_seed,
            &(layout.power_count as u64).to_be_bytes(),
            &(layout.output_triples as u64).to_be_bytes(),
        ],
    );
    let id = state.party_id.to_be_bytes();
    let coin = cshake256_framed_32(b"QSAG.DKG.CHECK.COIN.V1", &[&state.entropy, &context, &id]);
    let salt = cshake256_framed_32(
        b"QSAG.DKG.CHECK.TAG_SALT.V1",
        &[&state.entropy, &context, &id],
    );
    let alpha = share.bdoz_alpha_share;
    let mac_lane_1 = macs
        .pop()
        .ok_or(ParallelSeededError::InvalidThresholdParameters)?;
    let mac_lane_0 = macs
        .pop()
        .ok_or(ParallelSeededError::InvalidThresholdParameters)?;
    Ok(ParallelSeededDkgUnverifiedOutput {
        output: Some(ParallelSeededDkgOutput {
            pk_seed_bytes: key_seed,
            share,
            beaver_triples,
        }),
        roster: state.config.roster.clone(),
        party_id: state.party_id,
        context,
        layout,
        alpha,
        values,
        macs: [mac_lane_0, mac_lane_1],
        coin,
        salt,
        step: 0,
        coin_commits: Vec::new(),
        joint_coin: [0; 32],
        own_shares_digest: [0; 32],
        tags: [0; 2],
        tag_commits: Vec::new(),
    })
}

/// Ideal OT for tests: pads come from a public hash, so it checks the adapter's algebra and
/// message flow and nothing about OT security.
#[cfg(test)]
pub(crate) mod ideal_ot {
    extern crate std;
    use super::*;
    use std::collections::BTreeMap;
    use std::sync::{Arc, Condvar, Mutex};

    type Key = (u16, u16, [u8; 32], u8);
    type Messages = BTreeMap<Key, Vec<u128>>;
    /// Which of a party's word messages to alter, counted from zero, and how.
    pub(crate) type Tamper = (usize, fn(&mut [u128]));
    #[derive(Clone, Default)]
    pub(crate) struct Mailbox(Arc<(Mutex<Messages>, Condvar)>);
    impl Mailbox {
        fn put(&self, key: Key, words: Vec<u128>) {
            let fresh = self.0.0.lock().unwrap().insert(key, words).is_none();
            assert!(fresh, "a context was used twice");
            self.0.1.notify_all();
        }
        fn take(&self, key: Key) -> Vec<u128> {
            let mut map = self.0.0.lock().unwrap();
            loop {
                if let Some(words) = map.remove(&key) {
                    return words;
                }
                let (guard, timeout) = self
                    .0
                    .1
                    .wait_timeout(map, std::time::Duration::from_secs(60))
                    .unwrap();
                assert!(!timeout.timed_out(), "no message for {key:?}");
                map = guard;
            }
        }
        pub(crate) fn is_empty(&self) -> bool {
            self.0.0.lock().unwrap().is_empty()
        }
    }

    pub(crate) struct IdealOt {
        pub(crate) id: u16,
        pub(crate) mailbox: Mailbox,
        pub(crate) tamper: Option<Tamper>,
        pub(crate) sends: usize,
    }
    impl IdealOt {
        pub(crate) fn new(id: u16, mailbox: &Mailbox) -> Self {
            Self {
                id,
                mailbox: mailbox.clone(),
                tamper: None,
                sends: 0,
            }
        }
    }
    fn pads(
        sender: u16,
        receiver: u16,
        context: &[u8; 32],
        count: usize,
    ) -> Vec<([u8; 48], [u8; 48])> {
        let mut raw = vec![0u8; count * 96];
        cshake256_framed_xof(
            b"QSAG.TEST.IDEAL.OT",
            &[&sender.to_be_bytes(), &receiver.to_be_bytes(), context],
            &mut raw,
        );
        raw.as_chunks::<96>()
            .0
            .iter()
            .map(|pair| {
                let (zero, one) = pair.split_at(48);
                (zero.try_into().unwrap(), one.try_into().unwrap())
            })
            .collect()
    }
    impl ParallelSeededDkgOt for IdealOt {
        fn random_ots(
            &mut self,
            context: [u8; 32],
            peers: &[ParallelSeededDkgOtPeer<'_>],
        ) -> Result<Vec<ParallelSeededDkgOtPads>, ParallelSeededError> {
            Ok(peers
                .iter()
                .map(|session| ParallelSeededDkgOtPads {
                    sent: pads(self.id, session.peer, &context, session.send_words * 128),
                    received: pads(session.peer, self.id, &context, session.choices.len() * 128)
                        .iter()
                        .enumerate()
                        .map(|(i, pair)| {
                            if (session.choices[i / 128] >> (i % 128)) & 1 == 1 {
                                pair.1
                            } else {
                                pair.0
                            }
                        })
                        .collect(),
                })
                .collect())
        }
        fn send_words(
            &mut self,
            peer: u16,
            context: [u8; 32],
            mut words: Vec<u128>,
        ) -> Result<(), ParallelSeededError> {
            if let Some((at, alter)) = self.tamper
                && at == self.sends
            {
                alter(&mut words);
            }
            self.sends += 1;
            self.mailbox.put((self.id, peer, context, 1), words);
            Ok(())
        }
        fn receive_words(
            &mut self,
            peer: u16,
            context: [u8; 32],
            count: usize,
        ) -> Result<Vec<u128>, ParallelSeededError> {
            let words = self.mailbox.take((peer, self.id, context, 1));
            assert_eq!(words.len(), count);
            Ok(words)
        }
        fn send(
            &mut self,
            peer: u16,
            context: [u8; 32],
            alternatives: &[[u128; 2]],
        ) -> Result<(), ParallelSeededError> {
            self.mailbox.put(
                (self.id, peer, context, 0),
                alternatives.as_flattened().to_vec(),
            );
            Ok(())
        }
        fn receive(
            &mut self,
            peer: u16,
            context: [u8; 32],
            choices: &[u128],
        ) -> Result<SecretVec<u128>, ParallelSeededError> {
            let alternatives = self.mailbox.take((peer, self.id, context, 0));
            assert_eq!(alternatives.len(), choices.len() * 256);
            Ok(SecretBuffer(
                alternatives
                    .as_chunks::<2>()
                    .0
                    .iter()
                    .enumerate()
                    .map(|(i, pair)| pair[((choices[i / 128] >> (i % 128)) & 1) as usize])
                    .collect(),
            ))
        }
    }
}

#[cfg(test)]
mod gilboa_tests {
    extern crate std;
    use super::ideal_ot::{IdealOt, Mailbox};
    use super::*;
    use qsag_accel::gf2_128::gf2_128_mul_const;

    fn party(id: u16, mailbox: &Mailbox) -> ParallelSeededGilboaProducts<IdealOt> {
        ParallelSeededGilboaProducts::new(id, [id as u8 + 40; 32], IdealOt::new(id, mailbox))
    }

    fn operands(len: usize, salt: u128) -> Vec<u128> {
        const EDGES: [u128; 6] = [0, 1, 2, 1 << 127, u128::MAX, 0x87];
        (0..len)
            .map(|i| {
                if i < EDGES.len() && salt.is_multiple_of(2) {
                    EDGES[i]
                } else {
                    (i as u128 + salt).wrapping_mul(0x9e37_79b9_7f4a_7c15_f39c_c060_5ced_c835)
                        ^ (salt << 64)
                }
            })
            .collect()
    }

    /// The chosen-message path against the bitwise field reference, at every length around
    /// the OT batch and with operands on the reduction edges.
    #[test]
    fn gilboa_shares_sum_to_the_field_product_at_every_batch_tail() {
        for len in [1usize, 2, 5, 31, 32, 33, 63, 64, 65, 97] {
            let mailbox = Mailbox::default();
            let (mut sender, mut receiver, mut outsider) =
                (party(3, &mailbox), party(9, &mailbox), party(11, &mailbox));
            let (x, y) = (operands(len, 6), operands(len, 7));
            let context = [len as u8; 32];
            let sent = sender.product_shares(context, 3, 9, &x).unwrap();
            let received = receiver.product_shares(context, 3, 9, &y).unwrap();
            assert!(
                outsider
                    .product_shares(context, 3, 9, &[])
                    .unwrap()
                    .is_empty()
            );
            assert_eq!((sent.len(), received.len()), (len, len));
            for i in 0..len {
                assert_eq!(
                    sent[i] ^ received[i],
                    gf2_128_mul_const(x[i], y[i]),
                    "length {len} element {i}"
                );
            }
            assert!(mailbox.is_empty(), "every batch was sent and received");
        }
    }

    /// Three parties, each with its own operands: the shares of every party must sum to the
    /// off-diagonal part of `(sum x) * (sum y)`.
    fn cross_terms(
        roster: [u16; 3],
        run: impl Fn(&mut ParallelSeededGilboaProducts<IdealOt>, usize) -> Vec<u128> + Sync,
    ) -> Vec<u128> {
        let mailbox = Mailbox::default();
        let run = &run;
        let shares: Vec<Vec<u128>> = std::thread::scope(|scope| {
            let handles: Vec<_> = roster
                .iter()
                .enumerate()
                .map(|(index, &id)| {
                    let mut party = party(id, &mailbox);
                    scope.spawn(move || run(&mut party, index))
                })
                .collect();
            handles.into_iter().map(|h| h.join().unwrap()).collect()
        });
        assert!(mailbox.is_empty(), "every message was received");
        (0..shares[0].len())
            .map(|i| shares.iter().fold(0, |sum, share| sum ^ share[i]))
            .collect()
    }

    #[test]
    fn cross_products_sum_to_the_off_diagonal_products_at_every_width_and_flight_tail() {
        let roster = [2u16, 5, 7];
        for width in 1..=3usize {
            let tails = [
                GILBOA_FLIGHT_WORDS - 1,
                GILBOA_FLIGHT_WORDS,
                GILBOA_FLIGHT_WORDS + 1,
            ];
            // The flight boundary does not depend on the width; cross it at the widest only.
            for len in [1usize, 3]
                .into_iter()
                .chain(tails.into_iter().filter(|_| width == 3))
            {
                let x: Vec<_> = (0..3).map(|p| operands(len * width, 2 * p + 20)).collect();
                let y: Vec<_> = (0..3).map(|p| operands(len, 2 * p + 31)).collect();
                let context = [(width * 16 + len % 13) as u8; 32];
                let total = cross_terms(roster, |party, index| {
                    party
                        .cross_products(context, &roster, width, &x[index], &y[index])
                        .unwrap()
                });
                for (i, &share) in total.iter().enumerate() {
                    let mut expected = 0;
                    for (s, x) in x.iter().enumerate() {
                        for (_, y) in y.iter().enumerate().filter(|&(r, _)| r != s) {
                            expected ^= gf2_128_mul_const(x[i], y[i / width]);
                        }
                    }
                    assert_eq!(share, expected, "width {width} length {len} element {i}");
                }
            }
        }
    }

    #[test]
    fn keyed_products_sum_to_the_off_diagonal_mac_terms_at_every_block_tail() {
        let roster = [0u16, 1, 4];
        let keys = [
            0x87u128,
            u128::MAX,
            0x0123_4567_89ab_cdef_0f1e_2d3c_4b5a_6978,
        ];
        for len in [
            1usize,
            2,
            511,
            512,
            KEYED_BLOCK - 1,
            KEYED_BLOCK,
            KEYED_BLOCK + 3,
        ] {
            let values: Vec<_> = (0..3).map(|p| operands(len, 2 * p + 8)).collect();
            let context = [len as u8 ^ 0x5a; 32];
            let total = cross_terms(roster, |party, index| {
                party
                    .keyed_products(context, &roster, keys[index], &values[index])
                    .unwrap()
            });
            for (i, &share) in total.iter().enumerate() {
                let mut expected = 0;
                for (k, &key) in keys.iter().enumerate() {
                    for (_, values) in values.iter().enumerate().filter(|&(v, _)| v != k) {
                        expected ^= gf2_128_mul_const(key, values[i]);
                    }
                }
                assert_eq!(share, expected, "length {len} element {i}");
            }
        }
    }

    /// The eight-lane stream against the byte-oriented cSHAKE256 of the same input, and the
    /// row fold against field multiplication by powers of `z`.
    #[test]
    fn seed_streams_match_scalar_cshake_and_rows_fold_by_powers_of_z() {
        let seeds: Vec<[u8; 48]> = (0..11u8)
            .map(|i| core::array::from_fn(|j| i.wrapping_mul(29) ^ (j as u8).wrapping_mul(7)))
            .collect();
        let context = [0xc3; 32];
        for count in [1usize, 8, 9, 17, 600] {
            let mut rows = vec![0u128; seeds.len() * count];
            for (seeds, rows) in seeds.chunks(8).zip(rows.chunks_mut(8 * count)) {
                let refs: Vec<&[u8; 48]> = seeds.iter().collect();
                expand_seed_group(&refs, &context, count, rows);
            }
            for (seed, row) in seeds.iter().zip(rows.chunks(count)) {
                let mut xof =
                    qsag_core::sponge::keccak::Cshake256Xof::new(b"QSAG.DKG.KEYED.PRG.V1");
                xof.absorb(seed);
                xof.absorb(&context);
                let mut raw = vec![0u8; count * 16];
                xof.squeeze(&mut raw);
                let expected: Vec<u128> = raw
                    .as_chunks::<16>()
                    .0
                    .iter()
                    .map(|b| u128::from_le_bytes(*b))
                    .collect();
                assert_eq!(row, expected, "count {count}");
            }
        }
        let rows = operands(128 * 5, 3);
        let folded = fold_rows(&rows, 5);
        // Sixteen unit folds of eight rows each recombine to the same sum.
        let units: Vec<_> = rows.chunks(8 * 5).map(|unit| fold_rows(unit, 5)).collect();
        let mut recombined = [7u128; 5];
        add_unit_folds(&mut recombined, &units, 1);
        for j in 0..5 {
            // z^i is the field element with only bit i set.
            let expected = (0..128).fold(0, |sum, i| {
                sum ^ gf2_128_mul_const(rows[i * 5 + j], 1u128 << i)
            });
            assert_eq!((folded[j], recombined[j]), (expected, expected ^ 7));
        }
    }

    #[test]
    fn gilboa_refuses_degenerate_roles() {
        let mailbox = Mailbox::default();
        let mut party = party(1, &mailbox);
        let invalid = Err(ParallelSeededError::InvalidThresholdParameters);
        assert_eq!(party.product_shares([0; 32], 1, 1, &[5]), invalid);
        // A bystander holds no operand for a pair it is not part of.
        assert_eq!(party.product_shares([0; 32], 2, 3, &[5]), invalid);
        // More operands per OT than a pad covers, a foreign roster, mismatched lengths.
        assert_eq!(
            party.cross_products([0; 32], &[1, 2], 4, &[0; 4], &[0]),
            invalid
        );
        assert_eq!(
            party.cross_products([0; 32], &[2, 3], 1, &[0], &[0]),
            invalid
        );
        assert_eq!(
            party.cross_products([0; 32], &[1, 2], 2, &[0; 3], &[0]),
            invalid
        );
        assert_eq!(party.keyed_products([0; 32], &[2, 3], 1, &[0]), invalid);
        for roster in [&[1, 1][..], &[2, 1][..], &[1, 2, 2][..], &[][..]] {
            assert_eq!(party.cross_products([0; 32], roster, 1, &[0], &[0]), invalid);
            assert_eq!(party.keyed_products([0; 32], roster, 1, &[0]), invalid);
        }
        assert!(mailbox.is_empty());
    }
}
