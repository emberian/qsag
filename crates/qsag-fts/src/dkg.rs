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
//! 2. **Sacrifice.** Each output Beaver triple, and each of the six products that define a power
//!    tuple (`a^2 = a*a`, `a^3 = a*a^2`, `a^4 = a^2*a^2`, `a^5 = a*a^4`, `a^6 = a^3*a^3`,
//!    `a^7 = a^3*a^4`), is checked against its own sacrificial triple `(u, v, w)` under a
//!    coin-derived challenge `t`: parties open `rho = t*x + u` and `sigma = y + v`, and the shared
//!    value `t*c + w + sigma*u + rho*v + rho*sigma` must be zero.
//! 3. **Share commitment.** Every remaining output value is folded with coin-derived weights
//!    into one opening masked by a sacrificial authenticated random value.
//! 4. **MAC check.** All opened values, and the claimed zeros, are verified in one batched check
//!    on both MAC lanes; each party commits to its MAC tag before any tag is opened.
//!
//! A relation that is false on the authenticated values, or a MAC share that is not the global
//! key times the value, survives with probability about `2^-127` over the joint coin. Any failure
//! discards the ceremony; nothing from it may be reused.
//!
//! Not covered: the check does not identify the cheater, and it is not a simulation proof for
//! the OT backend. A malicious OT sender can still stake the ceremony on a guess of `k` bits of
//! a peer's operand, succeeding with probability `2^-k` and otherwise aborting it.
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
    fn sample(&self, label: &[u8], count: usize) -> SecretValues {
        SecretValues(xof_field_elements(
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
}

/// Binary OT backend for the Gilboa adapter. `receive` returns one field element
/// per bit, least significant bit first, for each packed 128-bit choice word.
/// Sending both alternatives on a private channel does NOT implement this trait.
/// Implementations must hide choices from the sender and unchosen messages from
/// the receiver, authenticate peers, and reject repeated contexts.
pub trait ParallelSeededDkgOt {
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
    ) -> Result<Vec<u128>, ParallelSeededError>;
}

/// GF(2^128) Gilboa multiplication using 128 binary OTs per field product.
/// Background: <https://tlsnotary.org/docs/mpc/mac/>.
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
        let mut shares = SecretValues(Vec::with_capacity(operand.len()));
        // Bound temporary OT storage independently of the preprocessing pool.
        for (batch, inputs) in operand.chunks(32).enumerate() {
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
                let mut raw = vec![0u8; inputs.len() * 128 * 16];
                cshake256_framed_xof(b"QSAG.DKG.OT.PADS.V1", &[&self.entropy, &context], &mut raw);
                let mut alternatives = Vec::with_capacity(inputs.len() * 128);
                for (&x, pads) in inputs.iter().zip(raw.as_chunks::<{ 128 * 16 }>().0.iter()) {
                    let powers: [u128; 128] = core::array::from_fn(|bit| 1u128 << bit);
                    let mut basis = [0u128; 128];
                    // OT needs every product separately. The scale kernel retains
                    // all 128 outputs; a single mul_acc_batch dot product would
                    // XOR them together and destroy the alternatives.
                    qsag_asm::bitslice::gf2_128_scale_xor(&mut basis, &powers, x);
                    let mut share = 0;
                    for (pad, &term) in pads.as_chunks::<16>().0.iter().zip(&basis) {
                        let r = u128::from_le_bytes(*pad);
                        share ^= r;
                        alternatives.push([r, r ^ term]);
                    }
                    ct_zeroize_u128s(&mut basis);
                    shares.0.push(share);
                }
                ct_zeroize_bytes(&mut raw);
                let result = self.ot.send(receiver, context, &alternatives);
                for pair in &mut alternatives {
                    ct_zeroize_u128s(pair);
                }
                result?;
            } else {
                let selected = SecretValues(self.ot.receive(sender, context, inputs)?);
                if selected.0.len() != inputs.len() * 128 {
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
}

struct Products<'a, T> {
    backend: &'a mut T,
    roster: &'a [u16],
    context: [u8; 32],
    sequence: u64,
}
impl<T: ParallelSeededDkgProducts> Products<'_, T> {
    fn multiply(&mut self, x: &[u128], y: &[u128]) -> Result<SecretValues, ParallelSeededError> {
        if x.len() != y.len() {
            return Err(ParallelSeededError::InvalidThresholdParameters);
        }
        let id = self.backend.party_id();
        let mut result = SecretValues(x.iter().zip(y).map(|(&a, &b)| gf2_128_mul(a, b)).collect());
        for &sender in self.roster {
            for &receiver in self.roster {
                if sender == receiver {
                    continue;
                }
                let context = cshake256_framed_32(
                    b"QSAG.DKG.PRODUCT.V1",
                    &[
                        &self.context,
                        &self.sequence.to_be_bytes(),
                        &sender.to_be_bytes(),
                        &receiver.to_be_bytes(),
                        &(x.len() as u64).to_be_bytes(),
                    ],
                );
                let operand = if id == sender {
                    x
                } else if id == receiver {
                    y
                } else {
                    &[]
                };
                let part = SecretValues(
                    self.backend
                        .product_shares(context, sender, receiver, operand)?,
                );
                if part.0.len() != operand.len() {
                    return Err(ParallelSeededError::BdozMacCheckFailed);
                }
                for (sum, contribution) in result.0.iter_mut().zip(&part.0) {
                    *sum ^= contribution;
                }
            }
        }
        self.sequence += 1;
        Ok(result)
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
    values: [u128; 3],
    macs: [[u128; 2]; 3],
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

/// The six products that define a power tuple `(a, a^2, ..., a^7)`, as indices
/// `(x, y, c)` into the tuple with `tuple[c] = tuple[x] * tuple[y]`.
const POWER_RELATIONS: [(usize, usize, usize); 6] = [
    (0, 0, 1),
    (0, 1, 2),
    (1, 1, 3),
    (0, 3, 4),
    (2, 2, 5),
    (2, 3, 6),
];

/// One product `values[c] = values[x] * values[y]` and the sacrificial triple that checks it.
struct CheckRelation {
    x: usize,
    y: usize,
    c: usize,
    u: usize,
    v: usize,
    w: usize,
}

/// Public index layout of the authenticated value vector: four key lanes, the power tuples,
/// the output triples, one sacrificial triple per checked relation, and one mask value.
#[derive(Clone, Copy)]
struct CheckLayout {
    power_count: usize,
    output_triples: usize,
    triple_base: usize,
}
impl CheckLayout {
    fn new(power_count: usize, output_triples: usize) -> Option<Self> {
        let relations = power_count.checked_mul(6)?.checked_add(output_triples)?;
        let triple_base = power_count.checked_mul(7)?.checked_add(4)?;
        // The whole value vector, including the trailing mask, must be addressable.
        relations
            .checked_add(output_triples)?
            .checked_mul(3)?
            .checked_add(triple_base)?
            .checked_add(1)?;
        Some(Self {
            power_count,
            output_triples,
            triple_base,
        })
    }
    fn relation_count(&self) -> usize {
        self.output_triples + 6 * self.power_count
    }
    fn total_triples(&self) -> usize {
        self.output_triples + self.relation_count()
    }
    fn triple(&self, index: usize, part: usize) -> usize {
        self.triple_base + 3 * index + part
    }
    /// Values handed to the caller after activation; all of them enter the masked opening.
    fn output_value_count(&self) -> usize {
        self.triple(self.output_triples, 0)
    }
    fn mask_index(&self) -> usize {
        self.triple(self.total_triples(), 0)
    }
    fn value_count(&self) -> usize {
        self.mask_index() + 1
    }
    fn relation(&self, index: usize) -> CheckRelation {
        let sacrifice = self.output_triples + index;
        let (u, v, w) = (
            self.triple(sacrifice, 0),
            self.triple(sacrifice, 1),
            self.triple(sacrifice, 2),
        );
        if index < self.output_triples {
            return CheckRelation {
                x: self.triple(index, 0),
                y: self.triple(index, 1),
                c: self.triple(index, 2),
                u,
                v,
                w,
            };
        }
        let power = index - self.output_triples;
        let base = 4 + (power / 6) * 7;
        let (x, y, c) = POWER_RELATIONS[power % 6];
        CheckRelation {
            x: base + x,
            y: base + y,
            c: base + c,
            u,
            v,
            w,
        }
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
/// Broadcast third: this party's additive shares of every masked opening.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParallelSeededDkgCheckShares {
    pub party_id: u16,
    pub context: [u8; 32],
    pub rho: Vec<u128>,
    pub sigma: Vec<u128>,
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
    values: SecretValues,
    macs: [SecretValues; 2],
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
            self.layout.relation_count(),
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
        let mut bytes = Vec::with_capacity((shares.rho.len() + shares.sigma.len() + 1) * 16);
        for value in shares
            .rho
            .iter()
            .chain(&shares.sigma)
            .chain(core::iter::once(&shares.masked))
        {
            bytes.extend_from_slice(&value.to_le_bytes());
        }
        cshake256_framed_32(
            b"QSAG.DKG.CHECK.SHARES.V1",
            &[
                &shares.context,
                &shares.party_id.to_be_bytes(),
                &(shares.rho.len() as u64).to_be_bytes(),
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
        let mut rho = Vec::with_capacity(challenges.len());
        let mut sigma = Vec::with_capacity(challenges.len());
        for (index, &t) in challenges.iter().enumerate() {
            let r = self.layout.relation(index);
            rho.push(gf2_128_mul(t, values[r.x]) ^ values[r.u]);
            sigma.push(values[r.y] ^ values[r.v]);
        }
        let masked = weights.iter().zip(values).fold(
            values[self.layout.mask_index()],
            |acc, (&weight, &value)| acc ^ gf2_128_mul(weight, value),
        );
        let shares = ParallelSeededDkgCheckShares {
            party_id: self.party_id,
            context: self.context,
            rho,
            sigma,
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
        let relations = self.layout.relation_count();
        if self.step != 2
            || !self.roster_matches(shares.iter().map(|s| (s.party_id, s.context)))
            || shares
                .iter()
                .any(|s| s.rho.len() != relations || s.sigma.len() != relations)
            || !shares.iter().any(|s| {
                s.party_id == self.party_id
                    && ct_eq_bytes(&Self::shares_digest(s), &self.own_shares_digest)
            })
        {
            return self.fail(ParallelSeededError::InvalidThresholdParameters);
        }
        let mut rho = vec![0u128; relations];
        let mut sigma = vec![0u128; relations];
        let mut masked = 0u128;
        let mut transcript = Vec::with_capacity(shares.len() * 32);
        for share in shares {
            for (acc, value) in rho.iter_mut().zip(&share.rho) {
                *acc ^= value;
            }
            for (acc, value) in sigma.iter_mut().zip(&share.sigma) {
                *acc ^= value;
            }
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
            3 * relations + 1,
        );
        let mut tags = [0u128; 2];
        for (lane, tag) in tags.iter_mut().enumerate() {
            let (alpha, mac) = (self.alpha[lane], &self.macs[lane].0);
            for index in 0..relations {
                let r = self.layout.relation(index);
                let (t, rho, sigma) = (challenges[index], rho[index], sigma[index]);
                let rho_tag = gf2_128_mul(t, mac[r.x]) ^ mac[r.u] ^ gf2_128_mul(alpha, rho);
                let sigma_tag = mac[r.y] ^ mac[r.v] ^ gf2_128_mul(alpha, sigma);
                // MAC share of `t*c + w + sigma*u + rho*v + rho*sigma`, which must open to zero.
                let zero_tag = gf2_128_mul(t, mac[r.c])
                    ^ mac[r.w]
                    ^ gf2_128_mul(sigma, mac[r.u])
                    ^ gf2_128_mul(rho, mac[r.v])
                    ^ gf2_128_mul(alpha, gf2_128_mul(rho, sigma));
                *tag ^= gf2_128_mul(mac_weights[3 * index], rho_tag)
                    ^ gf2_128_mul(mac_weights[3 * index + 1], sigma_tag)
                    ^ gf2_128_mul(mac_weights[3 * index + 2], zero_tag);
            }
            let masked_tag = weights.iter().zip(mac).fold(
                mac[self.layout.mask_index()] ^ gf2_128_mul(alpha, masked),
                |acc, (&weight, &share)| acc ^ gf2_128_mul(weight, share),
            );
            *tag ^= gf2_128_mul(mac_weights[3 * relations], masked_tag);
        }
        self.tags = tags;
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
    let key_seed = cshake256_framed_32(b"QSAG.DKG.PUBLIC_SEED.V1", &[&frozen, &coin]);
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
        pairwise_zero_seeds: Vec::new(),
        beaver_pool: Vec::new(),
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
        let seed = if peer > state.party_id {
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
        };
        share.pairwise_zero_seeds.push((peer, seed));
    }
    let private = state.sample(b"KEYS", 6);
    share.sk_seed_lanes.copy_from_slice(&private.0[..2]);
    share.sk_prf_lanes.copy_from_slice(&private.0[2..4]);
    share.bdoz_alpha_share.copy_from_slice(&private.0[4..6]);
    let mut products = Products {
        backend,
        roster: &state.config.roster,
        context: cshake256_framed_32(b"QSAG.DKG.CORRELATIONS.V1", &[&frozen, &key_seed]),
        sequence: 0,
    };
    let a = state.sample(b"POWER_MASKS", state.config.power_count);
    let a2 = SecretValues(a.0.iter().map(|&x| gf2_128_mul(x, x)).collect());
    let a3 = products.multiply(&a.0, &a2.0)?;
    let a4 = SecretValues(a2.0.iter().map(|&x| gf2_128_mul(x, x)).collect());
    let a5 = products.multiply(&a.0, &a4.0)?;
    let a6 = SecretValues(a3.0.iter().map(|&x| gf2_128_mul(x, x)).collect());
    let a7 = products.multiply(&a3.0, &a4.0)?;
    // Output triples first, then one sacrificial triple per checked relation.
    let u = state.sample(b"BEAVER_U", layout.total_triples());
    let v = state.sample(b"BEAVER_V", layout.total_triples());
    let uv = products.multiply(&u.0, &v.0)?;
    let mask = state.sample(b"CHECK_MASK", 1);
    let mut values = SecretValues(private.0[..4].to_vec());
    for (index, _) in a.0.iter().enumerate() {
        for power in [&a, &a2, &a3, &a4, &a5, &a6, &a7] {
            values.0.push(power.0[index]);
        }
    }
    for ((&u, &v), &uv) in u.0.iter().zip(&v.0).zip(&uv.0) {
        values.0.extend_from_slice(&[u, v, uv]);
    }
    values.0.push(mask.0[0]);
    if values.0.len() != layout.value_count() {
        return Err(ParallelSeededError::InvalidThresholdParameters);
    }
    let mut macs = Vec::new();
    for alpha in share.bdoz_alpha_share {
        let keys = SecretValues(vec![alpha; values.0.len()]);
        macs.push(products.multiply(&keys.0, &values.0)?);
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

#[cfg(test)]
mod gilboa_tests {
    extern crate std;
    use super::*;
    use qsag_accel::gf2_128::gf2_128_mul_const;
    use std::{cell::RefCell, collections::BTreeMap, rc::Rc};

    type Mailbox = Rc<RefCell<BTreeMap<(u16, u16, [u8; 32]), Vec<[u128; 2]>>>>;

    /// Ideal 1-of-2 OT inside one thread: the sender deposits its pairs and the receiver
    /// takes exactly the chosen element of each. Checks the adapter's algebra only.
    struct IdealOt {
        id: u16,
        mailbox: Mailbox,
    }
    impl ParallelSeededDkgOt for IdealOt {
        fn send(
            &mut self,
            peer: u16,
            context: [u8; 32],
            alternatives: &[[u128; 2]],
        ) -> Result<(), ParallelSeededError> {
            let fresh = self
                .mailbox
                .borrow_mut()
                .insert((self.id, peer, context), alternatives.to_vec())
                .is_none();
            assert!(fresh, "an OT context was used twice");
            Ok(())
        }
        fn receive(
            &mut self,
            peer: u16,
            context: [u8; 32],
            choices: &[u128],
        ) -> Result<Vec<u128>, ParallelSeededError> {
            let alternatives = self
                .mailbox
                .borrow_mut()
                .remove(&(peer, self.id, context))
                .ok_or(ParallelSeededError::InvalidThresholdParameters)?;
            assert_eq!(alternatives.len(), choices.len() * 128);
            Ok(alternatives
                .iter()
                .enumerate()
                .map(|(i, pair)| pair[((choices[i / 128] >> (i % 128)) & 1) as usize])
                .collect())
        }
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

    /// The scale kernel behind the 128 alternatives against the bitwise field reference, at
    /// every length around the 32-operand OT batch and with operands on the reduction edges.
    #[test]
    fn gilboa_shares_sum_to_the_field_product_at_every_batch_tail() {
        for len in [1usize, 2, 5, 31, 32, 33, 63, 64, 65, 97] {
            let mailbox = Mailbox::default();
            let party = |id: u16| {
                ParallelSeededGilboaProducts::new(
                    id,
                    [id as u8 + 40; 32],
                    IdealOt {
                        id,
                        mailbox: mailbox.clone(),
                    },
                )
            };
            let (mut sender, mut receiver, mut outsider) = (party(3), party(9), party(11));
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
            assert!(
                mailbox.borrow().is_empty(),
                "every batch was sent and received"
            );
        }
    }

    #[test]
    fn gilboa_refuses_degenerate_roles() {
        let mailbox = Mailbox::default();
        let mut party = ParallelSeededGilboaProducts::new(
            1,
            [1; 32],
            IdealOt {
                id: 1,
                mailbox: mailbox.clone(),
            },
        );
        let invalid = Err(ParallelSeededError::InvalidThresholdParameters);
        assert_eq!(party.product_shares([0; 32], 1, 1, &[5]), invalid);
        // A bystander holds no operand for a pair it is not part of.
        assert_eq!(party.product_shares([0; 32], 2, 3, &[5]), invalid);
        assert!(mailbox.borrow().is_empty());
    }
}
