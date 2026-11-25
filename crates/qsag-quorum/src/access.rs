//! Constructively checked asymmetric quorum systems and authenticated durable releases.
//! Quorums here are explicit sufficient sets, not unclosed Stellar local slices.
//! Safety holds for *wise* observers: actual faults must lie in both observers'
//! downward-closed fail-prone families. Availability is checked independently.
use crate::quorum_jorts::QuorumConfig;
use alloc::{
    collections::{BTreeMap, BTreeSet},
    vec::Vec,
};
pub use qsag_core::access::{AccessError, MonotoneSpanProgram};
pub use qsag_core::reshare::reshare_rank_guard;
use qsag_core::{
    belt_latch::{BeltLatch, BeltLatchError, BeltLatchRecord, DurableWal, derive_echo_mac_key},
    wipe::{SecretBuffer, ct_eq_bytes32},
};

pub type PartySet = BTreeSet<u16>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PersonalQuorumSlice {
    pub observer: u16,
    /// Minimal sufficient quorums; supersets are implicitly accepted.
    pub quorums: Vec<PartySet>,
    /// Maximal possible faulty sets; subsets are implicitly covered.
    pub fail_prone: Vec<PartySet>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum QuorumPolicyError {
    InvalidConfiguration,
    Unavailable {
        observer: u16,
        faults: PartySet,
    },
    Intersection {
        left: u16,
        right: u16,
        first: PartySet,
        second: PartySet,
        faults: PartySet,
    },
    B3 {
        left: u16,
        right: u16,
    },
    InvalidCertificate,
    Latch(BeltLatchError),
}
impl From<BeltLatchError> for QuorumPolicyError {
    fn from(e: BeltLatchError) -> Self {
        Self::Latch(e)
    }
}

/// Validated, immutable policy. Mutation requires constructing and verifying a new policy.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AsymmetricQuorumSystem {
    participants: PartySet,
    personal: Vec<PersonalQuorumSlice>,
}
impl AsymmetricQuorumSystem {
    pub fn new(
        participants: PartySet,
        personal: Vec<PersonalQuorumSlice>,
    ) -> Result<Self, QuorumPolicyError> {
        let s = Self {
            participants,
            personal,
        };
        s.validate_shape()?;
        s.verify_b3()?;
        s.verify_quorum_intersection()?;
        for p in &s.personal {
            for f in &p.fail_prone {
                if !p.quorums.iter().any(|q| q.is_disjoint(f)) {
                    return Err(QuorumPolicyError::Unavailable {
                        observer: p.observer,
                        faults: f.clone(),
                    });
                }
            }
        }
        Ok(s)
    }
    /// Canonical complement construction from fail-prone families, checked against B^3.
    pub fn from_fail_prone(
        participants: PartySet,
        families: BTreeMap<u16, Vec<PartySet>>,
    ) -> Result<Self, QuorumPolicyError> {
        let personal = families
            .into_iter()
            .map(|(observer, fail_prone)| PersonalQuorumSlice {
                observer,
                quorums: fail_prone
                    .iter()
                    .map(|f| participants.difference(f).copied().collect())
                    .collect(),
                fail_prone,
            })
            .collect();
        Self::new(participants, personal)
    }
    fn validate_shape(&self) -> Result<(), QuorumPolicyError> {
        let observers: PartySet = self.personal.iter().map(|p| p.observer).collect();
        if self.participants.is_empty()
            || observers != self.participants
            || observers.len() != self.personal.len()
            || self.personal.iter().any(|p| {
                p.quorums.is_empty()
                    || p.fail_prone.is_empty()
                    || p.quorums
                        .iter()
                        .any(|q| q.is_empty() || !q.is_subset(&self.participants))
                    || p.fail_prone
                        .iter()
                        .any(|f| !f.is_subset(&self.participants))
            })
        {
            return Err(QuorumPolicyError::InvalidConfiguration);
        }
        Ok(())
    }
    pub fn participants(&self) -> &PartySet {
        &self.participants
    }
    pub fn personal_slices(&self) -> &[PersonalQuorumSlice] {
        &self.personal
    }
    pub fn accepts(&self, observer: u16, signers: &PartySet) -> bool {
        signers.is_subset(&self.participants)
            && self
                .personal
                .iter()
                .find(|p| p.observer == observer)
                .is_some_and(|p| p.quorums.iter().any(|q| q.is_subset(signers)))
    }
    /// Common downward-closure maximal sets are intersections `Fi intersect Fj`.
    /// Checking those suffices for every common possible fault subset.
    pub fn verify_quorum_intersection(&self) -> Result<(), QuorumPolicyError> {
        for a in &self.personal {
            for b in &self.personal {
                for fa in &a.fail_prone {
                    for fb in &b.fail_prone {
                        let faults: PartySet = fa.intersection(fb).copied().collect();
                        for q in &a.quorums {
                            for r in &b.quorums {
                                if !q.intersection(r).any(|p| !faults.contains(p)) {
                                    return Err(QuorumPolicyError::Intersection {
                                        left: a.observer,
                                        right: b.observer,
                                        first: q.clone(),
                                        second: r.clone(),
                                        faults,
                                    });
                                }
                            }
                        }
                    }
                }
            }
        }
        Ok(())
    }
    /// Cachin–Tackmann B^3: no Fi, Fj and common possible Fij cover the universe.
    pub fn verify_b3(&self) -> Result<(), QuorumPolicyError> {
        for a in &self.personal {
            for b in &self.personal {
                for fi in &a.fail_prone {
                    for fj in &b.fail_prone {
                        for ga in &a.fail_prone {
                            for gb in &b.fail_prone {
                                if self.participants.iter().all(|p| {
                                    fi.contains(p)
                                        || fj.contains(p)
                                        || (ga.contains(p) && gb.contains(p))
                                }) {
                                    return Err(QuorumPolicyError::B3 {
                                        left: a.observer,
                                        right: b.observer,
                                    });
                                }
                            }
                        }
                    }
                }
            }
        }
        Ok(())
    }
    /// Digest of the whole validated policy under `key_epoch_context`: a `QPOL0001`
    /// frame over the same injective encoding that keys the latch acknowledgements.
    pub fn policy_digest(&self, key_epoch_context: &[u8; 32]) -> [u8; 32] {
        let mut framed = b"QPOL0001".to_vec();
        framed.extend_from_slice(&self.context(key_epoch_context));
        qsag_core::sponge::keccak::shake256_32(&framed)
    }
    fn context(&self, key_epoch_context: &[u8; 32]) -> Vec<u8> {
        let mut bytes = key_epoch_context.to_vec();
        fn put_set(out: &mut Vec<u8>, set: &PartySet) {
            out.extend_from_slice(&(set.len() as u64).to_be_bytes());
            for p in set {
                out.extend_from_slice(&p.to_be_bytes());
            }
        }
        put_set(&mut bytes, &self.participants);
        bytes.extend_from_slice(&(self.personal.len() as u64).to_be_bytes());
        for p in &self.personal {
            bytes.extend_from_slice(&p.observer.to_be_bytes());
            for sets in [&p.quorums, &p.fail_prone] {
                bytes.extend_from_slice(&(sets.len() as u64).to_be_bytes());
                for set in sets {
                    put_set(&mut bytes, set);
                }
            }
        }
        bytes
    }
}

/// Verify cross-configuration intersection for an explicitly supplied overlap fault model.
/// This is a transition check, not a substitute for finalizing a constitutional handoff.
pub fn verify_handoff_safety(
    old: &AsymmetricQuorumSystem,
    new: &AsymmetricQuorumSystem,
    faults: &[PartySet],
) -> Result<(), QuorumPolicyError> {
    if faults.is_empty() {
        return Err(QuorumPolicyError::InvalidConfiguration);
    }
    for a in &old.personal {
        for b in &new.personal {
            for q in &a.quorums {
                for r in &b.quorums {
                    for f in faults {
                        if !q.intersection(r).any(|p| !f.contains(p)) {
                            return Err(QuorumPolicyError::Intersection {
                                left: a.observer,
                                right: b.observer,
                                first: q.clone(),
                                second: r.clone(),
                                faults: f.clone(),
                            });
                        }
                    }
                }
            }
        }
    }
    Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ThresholdNode {
    Leaf(u16),
    Weighted {
        threshold: u64,
        children: Vec<(u64, ThresholdNode)>,
    },
}
impl ThresholdNode {
    fn satisfied(&self, active: &PartySet) -> bool {
        match self {
            Self::Leaf(p) => active.contains(p),
            Self::Weighted {
                threshold,
                children,
            } => {
                *threshold > 0
                    && children
                        .iter()
                        .filter(|(_, c)| c.satisfied(active))
                        .map(|(w, _)| u128::from(*w))
                        .sum::<u128>()
                        >= u128::from(*threshold)
            }
        }
    }
    fn parties(&self, out: &mut PartySet) {
        match self {
            Self::Leaf(p) => {
                out.insert(*p);
            }
            Self::Weighted { children, .. } => {
                for (_, c) in children {
                    c.parties(out);
                }
            }
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum QuorumTopology {
    Symmetric(QuorumConfig),
    Weighted {
        weights: BTreeMap<u16, u64>,
        threshold: u64,
    },
    ThresholdTree(ThresholdNode),
    PersonalSlices(AsymmetricQuorumSystem),
}
impl From<QuorumConfig> for QuorumTopology {
    fn from(c: QuorumConfig) -> Self {
        Self::Symmetric(c)
    }
}
impl QuorumTopology {
    /// Compile custody access only. Latch safety must separately pass ABQS validation.
    /// Exhaustive compilation is explicitly limited to 16 parties; larger policies can
    /// supply a compact binary MSP directly. `observer` selects a personal access policy.
    pub fn to_span_program(&self, observer: u16) -> Result<MonotoneSpanProgram, AccessError> {
        let mut parties = PartySet::new();
        match self {
            Self::Symmetric(c) => parties.extend((0..c.parties()).map(|p| p as u16)),
            Self::Weighted { weights, .. } => parties.extend(weights.keys().copied()),
            Self::ThresholdTree(t) => t.parties(&mut parties),
            Self::PersonalSlices(s) => {
                let p = s
                    .personal
                    .iter()
                    .find(|p| p.observer == observer)
                    .ok_or(AccessError::Unauthorized)?;
                return MonotoneSpanProgram::from_authorized_sets(&p.quorums);
            }
        }
        if parties.len() > 16 {
            return Err(AccessError::PolicyTooLarge);
        }
        let ids: Vec<_> = parties.into_iter().collect();
        let mut minimal: Vec<PartySet> = Vec::new();
        for mask in 1usize..(1usize << ids.len()) {
            let active: PartySet = ids
                .iter()
                .enumerate()
                .filter_map(|(i, &p)| (mask & (1 << i) != 0).then_some(p))
                .collect();
            if minimal.iter().any(|s| s.is_subset(&active)) {
                continue;
            }
            let yes = match self {
                Self::Symmetric(c) => active.len() >= c.threshold(),
                Self::Weighted { weights, threshold } => {
                    *threshold > 0
                        && active.iter().map(|p| u128::from(weights[p])).sum::<u128>()
                            >= u128::from(*threshold)
                }
                Self::ThresholdTree(t) => t.satisfied(&active),
                Self::PersonalSlices(_) => false,
            };
            if yes {
                minimal.push(active);
            }
        }
        MonotoneSpanProgram::from_authorized_sets(&minimal)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PersonalLatchAck {
    pub from: u16,
    pub to: u16,
    pub epoch: u64,
    pub binding: [u8; 32],
    pub tag: [u8; 32],
}
impl PersonalLatchAck {
    pub const WIRE_BYTES: usize = 2 + 2 + 8 + 32 + 32;

    pub fn to_bytes(&self) -> [u8; Self::WIRE_BYTES] {
        let mut out = [0u8; Self::WIRE_BYTES];
        out[0..2].copy_from_slice(&self.from.to_be_bytes());
        out[2..4].copy_from_slice(&self.to.to_be_bytes());
        out[4..12].copy_from_slice(&self.epoch.to_be_bytes());
        out[12..44].copy_from_slice(&self.binding);
        out[44..76].copy_from_slice(&self.tag);
        out
    }

    pub fn from_bytes(raw: &[u8]) -> Option<Self> {
        if raw.len() != Self::WIRE_BYTES {
            return None;
        }
        Some(Self {
            from: u16::from_be_bytes([raw[0], raw[1]]),
            to: u16::from_be_bytes([raw[2], raw[3]]),
            epoch: u64::from_be_bytes(raw[4..12].try_into().ok()?),
            binding: raw[12..44].try_into().ok()?,
            tag: raw[44..76].try_into().ok()?,
        })
    }
}
/// Receiver-specific authenticated release certificate. It is not a public signature.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PersonalLatchCertificate {
    pub acks: Vec<PersonalLatchAck>,
}
/// Unforgeable through the safe API; issued only after durable binding, authenticated
/// quorum intersection checks and the WAL's external release authorization.
pub struct PersonalReleasePermit {
    party: u16,
    record: BeltLatchRecord,
    signers: PartySet,
}
impl PersonalReleasePermit {
    pub fn party(&self) -> u16 {
        self.party
    }
    pub fn record(&self) -> &BeltLatchRecord {
        &self.record
    }
    pub fn signers(&self) -> &PartySet {
        &self.signers
    }
}

/// Personal quorum counterpart of the fixed three-party BeltLatch echo gate.
/// Pair keys must be independently authenticated secrets shared only by each pair.
/// `key_epoch_context` binds the enrolled key and finalized constitutional epoch;
/// changing policy on a live key additionally requires a safe, finalized handoff.
pub struct PersonalBeltLatch<W: DurableWal> {
    party: u16,
    system: AsymmetricQuorumSystem,
    latch: BeltLatch<W>,
    keys: BTreeMap<u16, SecretBuffer<[u8; 32]>>,
    context: [u8; 32],
}
impl<W: DurableWal> PersonalBeltLatch<W> {
    pub fn new(
        party: u16,
        system: AsymmetricQuorumSystem,
        latch: BeltLatch<W>,
        key_epoch_context: [u8; 32],
        pair_keys: BTreeMap<u16, SecretBuffer<[u8; 32]>>,
    ) -> Result<Self, QuorumPolicyError> {
        if !system.participants.contains(&party)
            || system.participants.iter().any(|p| *p > 255)
            || pair_keys.keys().copied().collect::<PartySet>() != system.participants
        {
            return Err(QuorumPolicyError::InvalidConfiguration);
        }
        let context_bytes = system.context(&key_epoch_context);
        let keys = pair_keys
            .into_iter()
            .map(|(p, k)| {
                (
                    p,
                    SecretBuffer(derive_echo_mac_key(
                        &context_bytes,
                        usize::from(party),
                        usize::from(p),
                        &[&k.0],
                    )),
                )
            })
            .collect();
        Ok(Self {
            party,
            system,
            latch,
            keys,
            context: key_epoch_context,
        })
    }
    /// Persist before producing an acknowledgement. Retries must exactly match.
    pub fn acknowledge(
        &mut self,
        record: &BeltLatchRecord,
        receiver: u16,
    ) -> Result<PersonalLatchAck, QuorumPolicyError> {
        let key = self
            .keys
            .get(&receiver)
            .ok_or(QuorumPolicyError::InvalidCertificate)?;
        self.latch.bind(
            record.epoch,
            &record.msg_digest,
            &record.retry_salt,
            &record.target_sum_digits,
        )?;
        let binding = record.binding();
        let tag = qsag_verified::custodian_ack_tag(
            &key.0,
            &self.context,
            record.epoch,
            &binding,
            self.party as u8,
        );
        Ok(PersonalLatchAck {
            from: self.party,
            to: receiver,
            epoch: record.epoch,
            binding,
            tag,
        })
    }
    pub fn authorize(
        &mut self,
        record: &BeltLatchRecord,
        cert: &PersonalLatchCertificate,
    ) -> Result<PersonalReleasePermit, QuorumPolicyError> {
        let binding = record.binding();
        let mut signers = PartySet::new();
        for a in &cert.acks {
            let key = self
                .keys
                .get(&a.from)
                .ok_or(QuorumPolicyError::InvalidCertificate)?;
            let expected = qsag_verified::custodian_ack_tag(
                &key.0,
                &self.context,
                a.epoch,
                &a.binding,
                a.from as u8,
            );
            if a.to != self.party
                || a.epoch != record.epoch
                || a.binding != binding
                || !ct_eq_bytes32(&a.tag, &expected)
                || !signers.insert(a.from)
            {
                return Err(QuorumPolicyError::InvalidCertificate);
            }
        }
        if !self.system.accepts(self.party, &signers) {
            return Err(QuorumPolicyError::InvalidCertificate);
        }
        self.latch.bind(
            record.epoch,
            &record.msg_digest,
            &record.retry_salt,
            &record.target_sum_digits,
        )?;
        if self.latch.is_wal_poisoned() {
            return Err(QuorumPolicyError::Latch(BeltLatchError::WalPoisoned));
        }
        self.latch
            .wal()
            .authorize_open(record)
            .map_err(|e| QuorumPolicyError::Latch(BeltLatchError::Wal(e)))?;
        Ok(PersonalReleasePermit {
            party: self.party,
            record: record.clone(),
            signers,
        })
    }
    pub fn party(&self) -> u16 {
        self.party
    }
    pub fn system(&self) -> &AsymmetricQuorumSystem {
        &self.system
    }
    pub fn key_epoch_context(&self) -> &[u8; 32] {
        &self.context
    }
    pub(crate) fn derive_wire_link_key(
        &self,
        session_id: &[u8; 32],
        peer: u16,
    ) -> Option<[u8; 32]> {
        let key = self.keys.get(&peer)?;
        let low = self.party.min(peer).to_be_bytes();
        let high = self.party.max(peer).to_be_bytes();
        Some(crate::hash::mac32(
            &key.0,
            b"personal-release/wire-link",
            &[&self.context, session_id, &low, &high],
        ))
    }
    pub fn into_latch(self) -> BeltLatch<W> {
        self.latch
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;
    use qsag_core::belt_latch::MemoryWal;
    fn system() -> AsymmetricQuorumSystem {
        let roster = PartySet::from([0, 1, 2, 3]);
        let fs: Vec<_> = roster.iter().map(|&p| PartySet::from([p])).collect();
        AsymmetricQuorumSystem::from_fail_prone(
            roster.clone(),
            roster.iter().map(|&p| (p, fs.clone())).collect(),
        )
        .unwrap()
    }
    #[test]
    fn b3_intersection_availability_and_handoff() {
        let s = system();
        assert!(s.accepts(0, &PartySet::from([0, 1, 2])));
        assert!(!s.accepts(0, &PartySet::from([0, 1])));
        let mut bad = s.personal.clone();
        bad[0].quorums = vec![PartySet::from([0, 1])];
        assert!(matches!(
            AsymmetricQuorumSystem::new(s.participants.clone(), bad),
            Err(QuorumPolicyError::Intersection { .. })
        ));
        let three = PartySet::from([0, 1, 2]);
        assert!(
            AsymmetricQuorumSystem::from_fail_prone(
                three.clone(),
                three
                    .iter()
                    .map(|&p| (
                        p,
                        vec![
                            PartySet::from([0]),
                            PartySet::from([1]),
                            PartySet::from([2])
                        ]
                    ))
                    .collect()
            )
            .is_err()
        );
        let mut unavailable = s.personal.clone();
        unavailable[0].quorums = vec![s.participants.clone()];
        assert!(matches!(
            AsymmetricQuorumSystem::new(s.participants.clone(), unavailable),
            Err(QuorumPolicyError::Unavailable { observer: 0, .. })
        ));
        // Cross-observer safety uses COMMON possible faults, not their union.
        // The extra quorums {0,1} and {1,2} intersect at 1: possibly faulty to
        // observer 0, but not to observer 1. Their common fault model is empty.
        let asymmetric = AsymmetricQuorumSystem::new(
            PartySet::from([0, 1, 2]),
            vec![
                PersonalQuorumSlice {
                    observer: 0,
                    quorums: vec![PartySet::from([0, 2]), PartySet::from([0, 1])],
                    fail_prone: vec![PartySet::from([1])],
                },
                PersonalQuorumSlice {
                    observer: 1,
                    quorums: vec![PartySet::from([0, 1]), PartySet::from([1, 2])],
                    fail_prone: vec![PartySet::from([2])],
                },
                PersonalQuorumSlice {
                    observer: 2,
                    quorums: vec![PartySet::from([0, 1, 2])],
                    fail_prone: vec![PartySet::new()],
                },
            ],
        )
        .unwrap();
        assert!(asymmetric.accepts(0, &PartySet::from([0, 1])));
        assert!(asymmetric.accepts(1, &PartySet::from([1, 2])));
        assert!(verify_handoff_safety(&s, &s, &[PartySet::from([0])]).is_ok());
        assert!(verify_handoff_safety(&s, &s, &[PartySet::from([0, 1, 2])]).is_err());
    }
    #[test]
    fn authenticated_certificate_gates_durable_release_and_replay() {
        let s = system();
        let mut nodes: Vec<_> = (0..4)
            .map(|p| {
                let keys = (0..4)
                    .map(|q| (q, SecretBuffer([10 + p.min(q) * 4 + p.max(q); 32])))
                    .map(|(q, k)| (u16::from(q), k))
                    .collect();
                PersonalBeltLatch::new(
                    u16::from(p),
                    s.clone(),
                    BeltLatch::recover(MemoryWal::new(), 4).unwrap(),
                    [9; 32],
                    keys,
                )
                .unwrap()
            })
            .collect();
        let record = BeltLatchRecord {
            epoch: 0,
            msg_digest: [1; 32],
            retry_salt: [2; 32],
            target_sum_digits: vec![1; 128],
        };
        let acks = nodes[..3]
            .iter_mut()
            .map(|n| n.acknowledge(&record, 3).unwrap())
            .collect();
        let cert = PersonalLatchCertificate { acks };
        assert_eq!(
            nodes[3].authorize(&record, &cert).unwrap().signers().len(),
            3
        );
        let mut bad = cert.clone();
        bad.acks[0].tag[0] ^= 1;
        assert!(nodes[3].authorize(&record, &bad).is_err());
        let mut duplicate = cert.clone();
        duplicate.acks[2] = duplicate.acks[1].clone();
        assert!(nodes[3].authorize(&record, &duplicate).is_err());
        let mut other = record.clone();
        other.msg_digest[0] ^= 1;
        assert!(nodes[0].acknowledge(&other, 3).is_err());
        let old = nodes.pop().unwrap().into_latch().into_wal();
        let mut recovered = BeltLatch::recover(old, 4).unwrap();
        assert!(
            recovered
                .bind(
                    other.epoch,
                    &other.msg_digest,
                    &other.retry_salt,
                    &other.target_sum_digits
                )
                .is_err()
        );
    }
    #[test]
    fn personal_certificate_and_msp_input_compose() {
        use crate::party_node::PersonalMspInput;
        use qsag_core::field::goldilocks::Goldilocks as F;
        let s = system();
        let m = QuorumTopology::PersonalSlices(s.clone())
            .to_span_program(0)
            .unwrap();
        let secret = [F::from_u64_reduced(73); 4];
        let masks = vec![[F::from_u64_reduced(99); 4]; m.num_cols() - 1];
        let rows = m.share(&secret, &masks).unwrap();
        let mut nodes: Vec<_> = (0u8..4)
            .map(|p| {
                let keys = (0u8..4)
                    .map(|q| {
                        (
                            u16::from(q),
                            SecretBuffer([10 + p.min(q) * 4 + p.max(q); 32]),
                        )
                    })
                    .collect();
                PersonalBeltLatch::new(
                    u16::from(p),
                    s.clone(),
                    BeltLatch::recover(MemoryWal::new(), 4).unwrap(),
                    [9; 32],
                    keys,
                )
                .unwrap()
            })
            .collect();
        let record = BeltLatchRecord {
            epoch: 0,
            msg_digest: [1; 32],
            retry_salt: [2; 32],
            target_sum_digits: vec![1; 128],
        };
        let mut sum = [F::ZERO; 4];
        for p in 0u16..3 {
            let acks = nodes[..3]
                .iter_mut()
                .map(|n| n.acknowledge(&record, p).unwrap())
                .collect();
            let local = m
                .row_owners()
                .iter()
                .zip(rows.iter())
                .filter_map(|(&owner, &row)| (owner == p).then_some(row))
                .collect();
            let input = PersonalMspInput::new(p, m.clone(), SecretBuffer(local)).unwrap();
            let additive = input
                .release(
                    &mut nodes[usize::from(p)],
                    &record,
                    &PersonalLatchCertificate { acks },
                )
                .unwrap();
            for k in 0..4 {
                sum[k] += additive[k];
            }
        }
        assert_eq!(sum, secret);
    }

    #[test]
    fn weighted_and_hierarchical_compilation() {
        let m = QuorumTopology::Weighted {
            weights: BTreeMap::from([(0, 2), (1, 1), (2, 1)]),
            threshold: 3,
        }
        .to_span_program(0)
        .unwrap();
        assert!(
            m.solve_reconstruction_weights(&PartySet::from([0, 1]))
                .is_some()
        );
        assert!(
            m.solve_reconstruction_weights(&PartySet::from([1, 2]))
                .is_none()
        );
        let tree = ThresholdNode::Weighted {
            threshold: 2,
            children: vec![
                (1, ThresholdNode::Leaf(0)),
                (
                    1,
                    ThresholdNode::Weighted {
                        threshold: 1,
                        children: vec![(1, ThresholdNode::Leaf(1)), (1, ThresholdNode::Leaf(2))],
                    },
                ),
            ],
        };
        let m = QuorumTopology::ThresholdTree(tree)
            .to_span_program(0)
            .unwrap();
        assert!(
            m.solve_reconstruction_weights(&PartySet::from([0, 2]))
                .is_some()
        );
        assert!(
            m.solve_reconstruction_weights(&PartySet::from([1, 2]))
                .is_none()
        );
    }
}
