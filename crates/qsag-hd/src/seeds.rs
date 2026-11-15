//! Dealerless replicated subset-seed ceremony.
//!
//! # Model
//!
//! A committee of `n` custodians with threshold `t` (any `t` custodians hold every
//! seed between them). The adversary statically and maliciously corrupts at most
//! `t - 1` custodians and [`CommitteeConfig::new`] enforces `n >= 2t - 1`, so the
//! corrupt custodians are a strict minority. Custodians are connected by
//! authenticated confidential pairwise channels and an authenticated consistent
//! broadcast channel; neither is implemented here. Security is with abort: a
//! corrupt custodian can stop a ceremony, never bias or learn its result.
//!
//! For every subset `A` of `n - t + 1` custodians there is one 32-byte seed `k_A`
//! known to exactly the members of `A`. Every such subset contains an honest
//! custodian, and the complement of the corrupt set is a subset whose seed no
//! corrupt custodian holds. Each member commits to a private contribution for
//! each of its subsets by broadcast, delivers the openings privately only after
//! the complete commitment set is frozen, and the seed is a hash of all the
//! contributions and the frozen commitment transcript. A final broadcast
//! key-confirmation makes every holder check that the other holders derived the
//! same seed. No party ever samples a seed on behalf of others.
//!
//! All later sharings (MAC keys, multiplication masks, opening masks, hardened
//! tweaks, inventory child seeds) are pseudorandom functions of these seeds, so
//! they are consistent by construction and need no further private messages.

use crate::erase::{SecretBytes, ct_zeroize_bytes};
use alloc::vec::Vec;

use qsag_accel::ct::{RedactedSecret, ct_eq_bytes};
use qsag_accel::keccak::{Shake256, cshake256_framed_32, finalize_cshake256, init_cshake256};

use crate::inventory::{HdError, RekeyFault};

/// Largest supported committee. Subset counts grow as `binomial(n, t - 1)`.
pub const MAX_CUSTODIANS: usize = 256;
/// Largest number of subset seeds `binomial(n, t - 1)` a committee may need.
/// Every custodian stores, hashes and broadcasts state linear in this count, so
/// a committee beyond it is rejected at construction instead of exhausting
/// memory inside a ceremony. The ceiling bounds resource use only: the work per
/// rekey is still linear in the subset count.
pub const MAX_SUBSET_SEEDS: usize = 1 << 16;

/// Whether `binomial(n, k) <= limit`, without overflow for any `n <= MAX_CUSTODIANS`.
fn binomial_at_most(n: usize, k: usize, limit: usize) -> bool {
    let k = k.min(n - k);
    let mut count = 1u128;
    for i in 1..=k {
        // `count` is `binomial(n - k + i, i)` after each step, an exact division.
        count = count * (n - k + i) as u128 / i as u128;
        if count > limit as u128 {
            return false;
        }
    }
    true
}
/// Public set of committee positions, with a canonical 32-byte big-endian codec.
/// Ordering is numerical, so subset vectors can be searched by binary search.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct CustodianSet(pub [u64; 4]);

impl CustodianSet {
    pub fn contains(self, position: usize) -> bool {
        position < MAX_CUSTODIANS && (self.0[position / 64] >> (position % 64)) & 1 != 0
    }
    pub fn insert(&mut self, position: usize) {
        assert!(position < MAX_CUSTODIANS);
        self.0[position / 64] |= 1u64 << (position % 64);
    }
    pub fn to_be_bytes(self) -> [u8; 32] {
        let mut bytes = [0; 32];
        for (dst, word) in bytes
            .as_chunks_mut::<8>()
            .0
            .iter_mut()
            .zip(self.0.iter().rev())
        {
            dst.copy_from_slice(&word.to_be_bytes());
        }
        bytes
    }
    #[cfg(test)]
    pub(crate) fn trailing_zeros(self) -> u32 {
        self.0
            .iter()
            .enumerate()
            .find(|(_, w)| **w != 0)
            .map_or(256, |(i, w)| i as u32 * 64 + w.trailing_zeros())
    }
}
#[cfg(test)]
impl From<u16> for CustodianSet {
    fn from(value: u16) -> Self {
        Self([u64::from(value), 0, 0, 0])
    }
}
impl Ord for CustodianSet {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.0.iter().rev().cmp(other.0.iter().rev())
    }
}
impl PartialOrd for CustodianSet {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// Field modulus of the linear module; evaluation points are nonzero residues.
const POINT_MODULUS: u32 = 8_380_417;

/// Public committee description: threshold, custodian identifiers in strictly
/// increasing order with their distinct nonzero evaluation points, and a label
/// separating independent ceremonies of the same committee.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CommitteeConfig {
    threshold: u16,
    members: Vec<(u16, u32)>,
    label: [u8; 32],
}

impl CommitteeConfig {
    /// Rejects every committee outside the proven model with
    /// [`HdError::UnsupportedCommittee`]: `t = 0`, `n < 2t - 1`, more than
    /// [`MAX_CUSTODIANS`] members, more than [`MAX_SUBSET_SEEDS`] subset seeds,
    /// unordered or duplicate identifiers, and zero, duplicate or non-canonical
    /// evaluation points.
    pub fn new(threshold: u16, members: &[(u16, u32)], label: [u8; 32]) -> Result<Self, HdError> {
        let n = members.len();
        let t = usize::from(threshold);
        if t == 0
            || n > MAX_CUSTODIANS
            || n < 2 * t - 1
            || !binomial_at_most(n, t - 1, MAX_SUBSET_SEEDS)
        {
            return Err(HdError::UnsupportedCommittee);
        }
        for (i, &(id, x)) in members.iter().enumerate() {
            if x == 0
                || x >= POINT_MODULUS
                || members[..i]
                    .iter()
                    .any(|&(prior_id, prior_x)| prior_id >= id || prior_x == x)
            {
                return Err(HdError::UnsupportedCommittee);
            }
        }
        Ok(Self {
            threshold,
            members: members.to_vec(),
            label,
        })
    }

    pub const fn threshold(&self) -> u16 {
        self.threshold
    }

    pub fn members(&self) -> &[(u16, u32)] {
        &self.members
    }

    /// Largest number of corrupt custodians covered by the security argument.
    pub const fn max_corruptions(&self) -> usize {
        self.threshold as usize - 1
    }

    pub fn digest(&self) -> [u8; 32] {
        let mut bytes = Vec::with_capacity(2 + self.members.len() * 6);
        bytes.extend_from_slice(&self.threshold.to_be_bytes());
        for &(id, x) in &self.members {
            bytes.extend_from_slice(&id.to_be_bytes());
            bytes.extend_from_slice(&x.to_be_bytes());
        }
        cshake256_framed_32(b"QSAG.HD.SEEDS.CONFIG.V2", &[&self.label, &bytes])
    }

    pub(crate) fn position(&self, party_id: u16) -> Option<usize> {
        self.members.iter().position(|&(id, _)| id == party_id)
    }

    /// Every subset of `n - t + 1` member positions as an ascending bit mask list.
    pub fn subsets(&self) -> Vec<CustodianSet> {
        // Generate only the required combinations, in colexicographic order.
        // Replicated PRSS still needs C(n,t-1) seeds; widening the representation
        // does not change that protocol's communication cost.
        let n = self.members.len();
        let size = n + 1 - usize::from(self.threshold);
        let mut positions: Vec<_> = (0..size).collect();
        let mut subsets = Vec::new();
        loop {
            let mut subset = CustodianSet::default();
            for &p in &positions {
                subset.insert(p);
            }
            subsets.push(subset);
            let Some(i) = (0..size)
                .find(|&i| positions[i] + 1 < if i + 1 == size { n } else { positions[i + 1] })
            else {
                break;
            };
            positions[i] += 1;
            for (j, p) in positions[..i].iter_mut().enumerate() {
                *p = j;
            }
        }
        subsets
    }

    pub(crate) fn subsets_of(&self, position: usize) -> Vec<CustodianSet> {
        self.subsets()
            .into_iter()
            .filter(|mask| mask.contains(position))
            .collect()
    }
}

/// Whether `entries` names exactly the members of `subsets` that contain
/// `position`, in the same ascending order. `subsets` is the committee's full
/// list, generated once by the caller for all positions.
pub(crate) fn lists_subsets_of<T>(
    subsets: &[CustodianSet],
    position: usize,
    entries: &[T],
    subset_of: impl Fn(&T) -> CustodianSet,
) -> bool {
    let mut expected = subsets.iter().filter(|subset| subset.contains(position));
    entries
        .iter()
        .all(|entry| expected.next() == Some(&subset_of(entry)))
        && expected.next().is_none()
}

/// Round 1 broadcast: one hiding commitment for each subset the sender belongs to.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SeedContributionCommit {
    pub party_id: u16,
    pub digests: Vec<(CustodianSet, [u8; 32])>,
}

/// One private opening: the contribution to subset `subset` and its commitment salt.
pub struct SeedOpening {
    pub subset: CustodianSet,
    pub contribution: [u8; 32],
    pub salt: [u8; 32],
}

impl Drop for SeedOpening {
    fn drop(&mut self) {
        ct_zeroize_bytes(&mut self.contribution);
        ct_zeroize_bytes(&mut self.salt);
    }
}

/// Round 2 private delivery over the authenticated confidential channel
/// `from -> to`. No `Clone` or `Debug`; the openings are erased on drop.
pub struct SeedPrivateDelivery {
    pub from: u16,
    pub to: u16,
    pub openings: Vec<SeedOpening>,
}

/// Round 3 broadcast: a one-way confirmation tag for each held subset seed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SeedConfirmation {
    pub party_id: u16,
    pub tags: Vec<(CustodianSet, [u8; 32])>,
}

fn commit_contribution(
    config: &[u8; 32],
    party_id: u16,
    subset: CustodianSet,
    contribution: &[u8; 32],
    salt: &[u8; 32],
) -> [u8; 32] {
    cshake256_framed_32(
        b"QSAG.HD.SEEDS.COMMIT.V2",
        &[
            config,
            &party_id.to_be_bytes(),
            &subset.to_be_bytes(),
            contribution,
            salt,
        ],
    )
}

fn abort<T>(fault: RekeyFault) -> Result<T, HdError> {
    Err(HdError::RekeyAborted(fault))
}

pub struct SeedCeremonyRound1 {
    config: CommitteeConfig,
    position: usize,
    contributions: Vec<SeedOpening>,
}

pub struct SeedCeremonyRound2 {
    config: CommitteeConfig,
    position: usize,
    contributions: Vec<SeedOpening>,
    commits: Vec<SeedContributionCommit>,
    transcript: [u8; 32],
}

pub struct SeedCeremonyRound3 {
    seeds: CustodianSeeds,
    own: SeedConfirmation,
}

impl SeedCeremonyRound1 {
    /// `private_entropy` must be fresh secret CSPRNG output of this custodian.
    pub fn begin(
        config: &CommitteeConfig,
        party_id: u16,
        mut private_entropy: [u8; 32],
    ) -> Result<(Self, SeedContributionCommit), HdError> {
        let entropy = RedactedSecret::new(private_entropy);
        ct_zeroize_bytes(&mut private_entropy);
        let position = config
            .position(party_id)
            .ok_or(HdError::InvalidThresholdParameters)?;
        let digest = config.digest();
        let contributions: Vec<SeedOpening> = config
            .subsets_of(position)
            .into_iter()
            .map(|subset| SeedOpening {
                subset,
                contribution: cshake256_framed_32(
                    b"QSAG.HD.SEEDS.CONTRIBUTION.V2",
                    &[entropy.expose(), &digest, &subset.to_be_bytes()],
                ),
                salt: cshake256_framed_32(
                    b"QSAG.HD.SEEDS.SALT.V2",
                    &[entropy.expose(), &digest, &subset.to_be_bytes()],
                ),
            })
            .collect();
        let commit = SeedContributionCommit {
            party_id,
            digests: contributions
                .iter()
                .map(|c| {
                    (
                        c.subset,
                        commit_contribution(&digest, party_id, c.subset, &c.contribution, &c.salt),
                    )
                })
                .collect(),
        };
        Ok((
            Self {
                config: config.clone(),
                position,
                contributions,
            },
            commit,
        ))
    }

    /// Freezes the complete broadcast commitment set, then releases the private
    /// openings. Nothing private leaves this custodian before the freeze.
    pub fn freeze(
        self,
        commits: &[SeedContributionCommit],
    ) -> Result<(SeedCeremonyRound2, Vec<SeedPrivateDelivery>), HdError> {
        let members = self.config.members();
        if commits.len() != members.len() {
            return abort(RekeyFault::MalformedMessage);
        }
        let mut transcript = Vec::new();
        let subsets = self.config.subsets();
        for (position, (commit, &(id, _))) in commits.iter().zip(members).enumerate() {
            if commit.party_id != id
                || !lists_subsets_of(&subsets, position, &commit.digests, |entry| entry.0)
            {
                return abort(RekeyFault::MalformedMessage);
            }
            transcript.extend_from_slice(&id.to_be_bytes());
            for (subset, digest) in &commit.digests {
                transcript.extend_from_slice(&subset.to_be_bytes());
                transcript.extend_from_slice(digest);
            }
        }
        let own_id = members[self.position].0;
        let digest = self.config.digest();
        if self
            .contributions
            .iter()
            .zip(&commits[self.position].digests)
            .any(|(c, entry)| {
                commit_contribution(&digest, own_id, c.subset, &c.contribution, &c.salt) != entry.1
            })
        {
            return abort(RekeyFault::CommitmentMismatch);
        }
        let transcript =
            cshake256_framed_32(b"QSAG.HD.SEEDS.TRANSCRIPT.V2", &[&digest, &transcript]);
        let deliveries = members
            .iter()
            .enumerate()
            .filter(|&(position, _)| position != self.position)
            .map(|(position, &(to, _))| SeedPrivateDelivery {
                from: own_id,
                to,
                openings: self
                    .contributions
                    .iter()
                    .filter(|c| c.subset.contains(position))
                    .map(|c| SeedOpening {
                        subset: c.subset,
                        contribution: c.contribution,
                        salt: c.salt,
                    })
                    .collect(),
            })
            .collect();
        Ok((
            SeedCeremonyRound2 {
                config: self.config,
                position: self.position,
                contributions: self.contributions,
                commits: commits.to_vec(),
                transcript,
            },
            deliveries,
        ))
    }
}

impl SeedCeremonyRound2 {
    /// Checks every received opening against the frozen commitments and derives
    /// the subset seeds. `deliveries` holds exactly one delivery from every other
    /// custodian, addressed to this custodian.
    pub fn receive(
        self,
        deliveries: Vec<SeedPrivateDelivery>,
    ) -> Result<(SeedCeremonyRound3, SeedConfirmation), HdError> {
        let members = self.config.members();
        let own_id = members[self.position].0;
        if deliveries.len() + 1 != members.len() {
            return abort(RekeyFault::MalformedMessage);
        }
        // One delivery from every other custodian, addressed to this one, with
        // its openings in ascending subset order (so each subset occurs once).
        let mut inbox: Vec<Option<&SeedPrivateDelivery>> = alloc::vec![None; members.len()];
        for delivery in &deliveries {
            let slot = match self.config.position(delivery.from) {
                Some(from) if from != self.position && delivery.to == own_id => &mut inbox[from],
                _ => return abort(RekeyFault::MalformedMessage),
            };
            if slot.is_some()
                || delivery
                    .openings
                    .windows(2)
                    .any(|pair| pair[0].subset >= pair[1].subset)
            {
                return abort(RekeyFault::MalformedMessage);
            }
            *slot = Some(delivery);
        }
        let digest = self.config.digest();
        let mut seeds = Vec::with_capacity(self.contributions.len());
        for own in &self.contributions {
            let mut frames: Vec<RedactedSecret<32>> = Vec::with_capacity(members.len());
            for (position, &(id, _)) in members.iter().enumerate() {
                if !own.subset.contains(position) {
                    continue;
                }
                if position == self.position {
                    frames.push(RedactedSecret::new(own.contribution));
                    continue;
                }
                let malformed = HdError::RekeyAborted(RekeyFault::MalformedMessage);
                let delivery = inbox[position].ok_or(malformed)?;
                let opening = delivery
                    .openings
                    .binary_search_by_key(&own.subset, |opening| opening.subset)
                    .map(|index| &delivery.openings[index])
                    .map_err(|_| malformed)?;
                let digests = &self.commits[position].digests;
                let committed = digests
                    .binary_search_by_key(&own.subset, |entry| entry.0)
                    .map(|index| &digests[index])
                    .map_err(|_| malformed)?;
                let actual = commit_contribution(
                    &digest,
                    id,
                    own.subset,
                    &opening.contribution,
                    &opening.salt,
                );
                if !ct_eq_bytes(&actual, &committed.1) {
                    return abort(RekeyFault::CommitmentMismatch);
                }
                frames.push(RedactedSecret::new(opening.contribution));
            }
            let mut joined = SecretBytes(Vec::with_capacity(frames.len() * 32));
            for frame in &mut frames {
                joined.0.extend_from_slice(frame.expose());
                ct_zeroize_bytes(frame.expose_mut());
            }
            let seed = cshake256_framed_32(
                b"QSAG.HD.SEEDS.KEY.V2",
                &[&self.transcript, &own.subset.to_be_bytes(), &joined.0],
            );
            ct_zeroize_bytes(&mut joined.0);
            seeds.push((own.subset, RedactedSecret::new(seed)));
        }
        let seeds = CustodianSeeds {
            ceremony: cshake256_framed_32(b"QSAG.HD.SEEDS.CEREMONY.V2", &[&self.transcript]),
            config: self.config,
            position: self.position,
            seeds,
        };
        let own = seeds.confirmation();
        Ok((
            SeedCeremonyRound3 {
                seeds,
                own: own.clone(),
            },
            own,
        ))
    }
}

impl SeedCeremonyRound3 {
    /// Releases usable custody only when every holder of every subset this
    /// custodian belongs to broadcast the identical confirmation tag.
    pub fn confirm(self, confirmations: &[SeedConfirmation]) -> Result<CustodianSeeds, HdError> {
        let members = self.seeds.config.members();
        if confirmations.len() != members.len() {
            return abort(RekeyFault::MalformedMessage);
        }
        let subsets = self.seeds.config.subsets();
        for (position, (confirmation, &(id, _))) in confirmations.iter().zip(members).enumerate() {
            if confirmation.party_id != id
                || !lists_subsets_of(&subsets, position, &confirmation.tags, |entry| entry.0)
            {
                return abort(RekeyFault::MalformedMessage);
            }
            for (subset, tag) in &confirmation.tags {
                if let Ok(index) = self.own.tags.binary_search_by_key(subset, |entry| entry.0)
                    && !ct_eq_bytes(&self.own.tags[index].1, tag)
                {
                    return abort(RekeyFault::SeedConfirmationMismatch);
                }
            }
        }
        Ok(self.seeds)
    }
}

/// One custodian's replicated seed custody. No `Clone` or `Debug`; erased on drop.
pub struct CustodianSeeds {
    config: CommitteeConfig,
    position: usize,
    ceremony: [u8; 32],
    seeds: Vec<(CustodianSet, RedactedSecret<32>)>,
}

impl Drop for CustodianSeeds {
    fn drop(&mut self) {
        for (_, seed) in &mut self.seeds {
            ct_zeroize_bytes(seed.expose_mut());
        }
    }
}

impl CustodianSeeds {
    pub fn config(&self) -> &CommitteeConfig {
        &self.config
    }

    pub fn party_id(&self) -> u16 {
        self.config.members[self.position].0
    }

    pub(crate) fn position(&self) -> usize {
        self.position
    }

    /// Public digest of the frozen ceremony transcript; identical at every custodian.
    pub fn ceremony_digest(&self) -> [u8; 32] {
        self.ceremony
    }

    pub(crate) fn held_subsets(&self) -> impl Iterator<Item = CustodianSet> + '_ {
        self.seeds.iter().map(|entry| entry.0)
    }

    fn confirmation(&self) -> SeedConfirmation {
        SeedConfirmation {
            party_id: self.party_id(),
            tags: self
                .seeds
                .iter()
                .map(|(subset, seed)| {
                    (
                        *subset,
                        cshake256_framed_32(
                            b"QSAG.HD.SEEDS.CONFIRM.V2",
                            &[seed.expose(), &self.ceremony, &subset.to_be_bytes()],
                        ),
                    )
                })
                .collect(),
        }
    }

    /// Domain-separated 32-byte PRF output under the seed of `subset`.
    pub(crate) fn prf32(
        &self,
        subset: CustodianSet,
        domain: &[u8],
        context: &[&[u8]],
    ) -> Option<[u8; 32]> {
        let seed = &self.seeds[self
            .seeds
            .binary_search_by_key(&subset, |entry| entry.0)
            .ok()?]
        .1;
        let mut frames: Vec<&[u8]> = Vec::with_capacity(context.len() + 3);
        let subset_bytes = subset.to_be_bytes();
        frames.push(seed.expose());
        frames.push(&self.ceremony);
        frames.push(&subset_bytes);
        frames.extend_from_slice(context);
        Some(cshake256_framed_32(domain, &frames))
    }

    /// Streaming PRF output under the seed of `subset`.
    pub(crate) fn prf_stream(
        &self,
        subset: CustodianSet,
        domain: &[u8],
        context: &[&[u8]],
    ) -> Option<Shake256> {
        let mut key = self.prf32(subset, domain, context)?;
        let mut sponge = init_cshake256(b"", b"QSAG.HD.SEEDS.STREAM.V2");
        sponge.absorb(&key);
        ct_zeroize_bytes(&mut key);
        finalize_cshake256(&mut sponge, true);
        Some(sponge)
    }

    /// Key shared with the custodian at `other` and with no coalition of at most
    /// `t - 1` custodians that excludes both: it hashes every subset seed held by
    /// both, and one of those subsets avoids any such coalition when `t >= 2`.
    /// Returns `None` for `t = 1`, where every custodian holds every seed.
    pub(crate) fn pairwise_key(&self, other: usize, domain: &[u8]) -> Option<[u8; 32]> {
        if self.config.threshold < 2 || other == self.position {
            return None;
        }
        let low = (self.position.min(other) as u16).to_be_bytes();
        let high = (self.position.max(other) as u16).to_be_bytes();
        let mut joined = SecretBytes(Vec::with_capacity(self.seeds.len() * 32));
        for (subset, seed) in &self.seeds {
            if subset.contains(other) {
                joined.0.extend_from_slice(seed.expose());
            }
        }
        let key = cshake256_framed_32(domain, &[&joined.0, &self.ceremony, &low, &high]);
        ct_zeroize_bytes(&mut joined.0);
        Some(key)
    }

    /// Test-only construction from explicit seeds, used to couple two worlds
    /// that differ in exactly one subset seed.
    #[cfg(test)]
    pub(crate) fn from_explicit_seeds(
        config: &CommitteeConfig,
        party_id: u16,
        ceremony: [u8; 32],
        seed_of: impl Fn(CustodianSet) -> [u8; 32],
    ) -> Self {
        let position = config.position(party_id).unwrap();
        Self {
            config: config.clone(),
            position,
            ceremony,
            seeds: config
                .subsets_of(position)
                .into_iter()
                .map(|subset| (subset, RedactedSecret::new(seed_of(subset))))
                .collect(),
        }
    }
}

/// Runs the ceremony among in-process custodians, routing only the messages a
/// network would carry. Shared by the unit tests of every module.
#[cfg(test)]
pub(crate) fn run_seed_ceremony(config: &CommitteeConfig, entropy_tag: u8) -> Vec<CustodianSeeds> {
    let mut commits = Vec::new();
    let mut states = Vec::new();
    for (position, &(id, _)) in config.members().iter().enumerate() {
        let (state, commit) = SeedCeremonyRound1::begin(
            config,
            id,
            [entropy_tag ^ (position as u8).wrapping_add(1); 32],
        )
        .unwrap();
        states.push(state);
        commits.push(commit);
    }
    let mut inboxes: Vec<Vec<SeedPrivateDelivery>> =
        config.members().iter().map(|_| Vec::new()).collect();
    let mut second = Vec::new();
    for state in states {
        let (state, deliveries) = state.freeze(&commits).unwrap();
        for delivery in deliveries {
            let to = config.position(delivery.to).unwrap();
            inboxes[to].push(delivery);
        }
        second.push(state);
    }
    let mut third = Vec::new();
    let mut confirmations = Vec::new();
    for (state, inbox) in second.into_iter().zip(inboxes) {
        let (state, confirmation) = state.receive(inbox).unwrap();
        third.push(state);
        confirmations.push(confirmation);
    }
    third
        .into_iter()
        .map(|state| state.confirm(&confirmations).unwrap())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn config(t: u16, n: u16) -> CommitteeConfig {
        let members: Vec<_> = (0..n).map(|i| (i + 10, u32::from(i) + 1)).collect();
        CommitteeConfig::new(t, &members, [7; 32]).unwrap()
    }

    #[test]
    fn committee_positions_span_all_four_words() {
        for n in [8, 17, 64, 65, 128, 129, 255, 256] {
            let cfg = config(2, n);
            let subsets = cfg.subsets();
            assert_eq!(subsets.len(), usize::from(n));
            assert!(subsets.windows(2).all(|w| w[0] < w[1]));
            for position in 0..usize::from(n) {
                assert_eq!(
                    subsets.iter().filter(|s| s.contains(position)).count(),
                    usize::from(n - 1)
                );
            }
        }
        let cfg = config(1, 256);
        assert_eq!(cfg.subsets(), [CustodianSet([u64::MAX; 4])]);
        let seeds = run_seed_ceremony(&cfg, 0x40);
        let set = cfg.subsets()[0];
        let expected = seeds[0].prf32(set, b"wide-committee", &[]);
        assert!(
            seeds
                .iter()
                .all(|s| s.prf32(set, b"wide-committee", &[]) == expected)
        );
    }

    #[test]
    fn unsupported_committees_are_rejected() {
        let members =
            |n: u16| -> Vec<(u16, u32)> { (0..n).map(|i| (i, u32::from(i) + 1)).collect() };
        for (t, n) in [(0, 3), (2, 2), (3, 4), (4, 6), (2, 257)] {
            assert_eq!(
                CommitteeConfig::new(t, &members(n), [0; 32]),
                Err(HdError::UnsupportedCommittee),
                "({t},{n})"
            );
        }
        for (t, n) in [(1, 1), (2, 3), (2, 5), (3, 5), (4, 7), (2, 256)] {
            assert!(CommitteeConfig::new(t, &members(n), [0; 32]).is_ok());
        }
        for bad in [
            [(0, 1), (0, 2), (2, 3)],
            [(0, 1), (1, 1), (2, 3)],
            [(0, 0), (1, 2), (2, 3)],
            [(0, POINT_MODULUS), (1, 2), (2, 3)],
            [(1, 1), (0, 2), (2, 3)],
        ] {
            assert_eq!(
                CommitteeConfig::new(2, &bad, [0; 32]),
                Err(HdError::UnsupportedCommittee)
            );
        }
    }

    #[test]
    fn oversized_subset_families_are_rejected_before_enumeration() {
        let members =
            |n: u16| -> Vec<(u16, u32)> { (0..n).map(|i| (i, u32::from(i) + 1)).collect() };
        // binomial(256, 2) = 32,640 is within the ceiling; binomial(256, 3) and
        // binomial(255, 127) are not, and must fail without being enumerated.
        assert_eq!(config(3, 256).subsets().len(), 32_640);
        for (t, n) in [(4, 256), (128, 255), (20, 40), (9, 20)] {
            assert_eq!(
                CommitteeConfig::new(t, &members(n), [0; 32]),
                Err(HdError::UnsupportedCommittee),
                "({t},{n})"
            );
        }
        // binomial(19, 7) = 50,388 and binomial(20, 7) = 77,520 straddle the ceiling.
        assert!(CommitteeConfig::new(8, &members(19), [0; 32]).is_ok());
        assert_eq!(
            CommitteeConfig::new(8, &members(20), [0; 32]),
            Err(HdError::UnsupportedCommittee)
        );
        assert!(binomial_at_most(18, 8, 43_758));
        assert!(!binomial_at_most(18, 8, 43_757));
        assert!(binomial_at_most(18, 10, 43_758));
        assert!(binomial_at_most(256, 0, 1));
        assert!(binomial_at_most(256, 256, 1));
        assert!(!binomial_at_most(256, 128, usize::MAX));
    }

    #[test]
    fn ceremony_spans_a_committee_wider_than_one_mask_word() {
        let cfg = config(2, 65);
        let seeds = run_seed_ceremony(&cfg, 0x52);
        for subset in cfg.subsets() {
            let held: Vec<_> = seeds
                .iter()
                .filter_map(|s| s.prf32(subset, b"wide", &[]))
                .collect();
            assert_eq!(held.len(), 64);
            assert!(held.windows(2).all(|w| w[0] == w[1]));
        }
        for (a, b) in [(0, 64), (63, 64), (1, 2)] {
            let key = seeds[a].pairwise_key(b, b"wide-pair").unwrap();
            assert_eq!(seeds[b].pairwise_key(a, b"wide-pair"), Some(key));
            assert_ne!(seeds[a].pairwise_key((b + 1) % 65, b"wide-pair"), Some(key));
        }
    }

    #[test]
    fn unordered_duplicate_or_misrouted_deliveries_abort() {
        let config = config(2, 4);
        let run = |tamper: &dyn Fn(&mut Vec<SeedPrivateDelivery>)| {
            let mut commits = Vec::new();
            let mut states = Vec::new();
            for (position, &(id, _)) in config.members().iter().enumerate() {
                let (state, commit) =
                    SeedCeremonyRound1::begin(&config, id, [position as u8 + 3; 32]).unwrap();
                states.push(state);
                commits.push(commit);
            }
            let mut inbox = Vec::new();
            let mut receiver = None;
            for (position, state) in states.into_iter().enumerate() {
                let (state, deliveries) = state.freeze(&commits).unwrap();
                inbox.extend(deliveries.into_iter().filter(|d| d.to == 10));
                if position == 0 {
                    receiver = Some(state);
                }
            }
            tamper(&mut inbox);
            receiver.unwrap().receive(inbox).err()
        };
        let malformed = Some(HdError::RekeyAborted(RekeyFault::MalformedMessage));
        assert_eq!(run(&|_| {}), None);
        // Two custodians of a (2,4) committee share two subsets.
        assert_eq!(run(&|inbox| inbox[0].openings.reverse()), malformed);
        assert_eq!(
            run(&|inbox| {
                let first = &inbox[0].openings[0];
                let copy = SeedOpening {
                    subset: first.subset,
                    contribution: first.contribution,
                    salt: first.salt,
                };
                inbox[0].openings.insert(0, copy);
            }),
            malformed
        );
        assert_eq!(run(&|inbox| inbox[1].from = inbox[0].from), malformed);
        assert_eq!(run(&|inbox| inbox[1].from = 10), malformed);
        assert_eq!(run(&|inbox| inbox[1].from = 99), malformed);
        assert_eq!(run(&|inbox| inbox[1].to = 11), malformed);
        assert_eq!(run(&|inbox| drop(inbox[2].openings.pop())), malformed);
    }

    #[test]
    fn holders_agree_and_every_coalition_misses_a_seed() {
        for (t, n) in [(2u16, 3u16), (2, 5), (3, 5)] {
            let config = config(t, n);
            let seeds = run_seed_ceremony(&config, 0x40);
            for subset in config.subsets() {
                let held: Vec<_> = seeds
                    .iter()
                    .filter_map(|s| s.prf32(subset, b"test", &[]))
                    .collect();
                assert_eq!(held.len(), usize::from(n - t + 1));
                assert!(held.windows(2).all(|w| w[0] == w[1]));
            }
            // Every coalition of t-1 custodians lacks the seed of its complement.
            for coalition in (0u16..1 << n).filter(|m| m.count_ones() == u32::from(t) - 1) {
                let complement = !coalition & ((1 << n) - 1);
                for (position, custodian) in seeds.iter().enumerate() {
                    assert_eq!(
                        custodian.prf32(complement.into(), b"test", &[]).is_some(),
                        coalition >> position & 1 == 0
                    );
                }
            }
            // Independent ceremonies give unrelated seeds.
            let other = run_seed_ceremony(&config, 0x41);
            let subset = config.subsets()[0];
            let holder = subset.trailing_zeros() as usize;
            assert_ne!(
                seeds[holder].prf32(subset, b"test", &[]),
                other[holder].prf32(subset, b"test", &[])
            );
        }
    }

    #[test]
    fn equivocated_or_substituted_contribution_aborts() {
        let config = config(2, 3);
        let mut commits = Vec::new();
        let mut states = Vec::new();
        for (position, &(id, _)) in config.members().iter().enumerate() {
            let (state, commit) =
                SeedCeremonyRound1::begin(&config, id, [position as u8 + 1; 32]).unwrap();
            states.push(state);
            commits.push(commit);
        }
        // A commitment set missing a member or carrying a foreign subset is rejected.
        let mut short = commits.clone();
        short.pop();
        let (probe, _) = SeedCeremonyRound1::begin(&config, 10, [1; 32]).unwrap();
        assert_eq!(
            probe.freeze(&short).err(),
            Some(HdError::RekeyAborted(RekeyFault::MalformedMessage))
        );
        let mut inboxes: Vec<Vec<SeedPrivateDelivery>> = (0..3).map(|_| Vec::new()).collect();
        let mut second = Vec::new();
        for state in states {
            let (state, deliveries) = state.freeze(&commits).unwrap();
            for delivery in deliveries {
                let to = config.position(delivery.to).unwrap();
                inboxes[to].push(delivery);
            }
            second.push(state);
        }
        // Custodian 0 sends custodian 1 a contribution that differs from its commitment.
        let tampered = inboxes[1].iter_mut().find(|d| d.from == 10).unwrap();
        tampered.openings[0].contribution[0] ^= 1;
        let mut second = second.into_iter();
        let mut inboxes = inboxes.into_iter();
        let honest = second.next().unwrap().receive(inboxes.next().unwrap());
        assert!(honest.is_ok());
        assert_eq!(
            second
                .next()
                .unwrap()
                .receive(inboxes.next().unwrap())
                .err(),
            Some(HdError::RekeyAborted(RekeyFault::CommitmentMismatch))
        );
    }

    #[test]
    fn mismatched_confirmation_blocks_activation() {
        let config = config(2, 3);
        let mut commits = Vec::new();
        let mut states = Vec::new();
        for (position, &(id, _)) in config.members().iter().enumerate() {
            let (state, commit) =
                SeedCeremonyRound1::begin(&config, id, [position as u8 + 9; 32]).unwrap();
            states.push(state);
            commits.push(commit);
        }
        let mut inboxes: Vec<Vec<SeedPrivateDelivery>> = (0..3).map(|_| Vec::new()).collect();
        let mut second = Vec::new();
        for state in states {
            let (state, deliveries) = state.freeze(&commits).unwrap();
            for delivery in deliveries {
                let to = config.position(delivery.to).unwrap();
                inboxes[to].push(delivery);
            }
            second.push(state);
        }
        let mut third = Vec::new();
        let mut confirmations = Vec::new();
        for (state, inbox) in second.into_iter().zip(inboxes) {
            let (state, confirmation) = state.receive(inbox).unwrap();
            third.push(state);
            confirmations.push(confirmation);
        }
        // Custodian 2 confirms a different seed for a subset it shares with custodian 0.
        let shared = confirmations[0].tags[0].0;
        assert!(shared.contains(2) || shared.contains(1));
        let liar = if shared.contains(1) { 1 } else { 2 };
        let entry = confirmations[liar]
            .tags
            .iter_mut()
            .find(|entry| entry.0 == shared)
            .unwrap();
        entry.1[0] ^= 1;
        let mut third = third.into_iter();
        assert_eq!(
            third.next().unwrap().confirm(&confirmations).err(),
            Some(HdError::RekeyAborted(RekeyFault::SeedConfirmationMismatch))
        );
    }
}
