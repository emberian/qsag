//! Range allocation for a single 3-of-5 Shamir tree. A vote burns through
//! the exclusive upper bound before its tag leaves the voter. A second WAL
//! binds each opened leaf to one message. Lease voters may then go offline.
//! Both WALs must be unique to the key, deployment, fault model and party,
//! and provisioned outside the same rollback threat as the signing process.

#![forbid(unsafe_code)]
use super::*;
use qsag_core::belt_latch::MAX_EPOCH_JUMP;

/// Public evidence of two different messages under one key and leaf. The
/// signatures identify the key; identifying an individual voter takes a
/// transferable attestation from that voter.
pub fn verify_leaf_equivocation(
    pk: &QuorumPublicKey,
    messages: [&[u8]; 2],
    signatures: [&QuorumJortsSig; 2],
) -> bool {
    let leaf = signatures[0].leaf;
    leaf == signatures[1].leaf
        && message_hash(pk, leaf, messages[0]) != message_hash(pk, leaf, messages[1])
        && (0..2).all(|i| quorum_jorts_verify(pk, messages[i], signatures[i]))
}

/// Advance large gaps through the existing WAL's bounded, crash-safe burns.
/// The terminal bind always persists the actual vote or signing record.
fn burn_gap<W: DurableWal>(
    latch: &mut BeltLatch<W>,
    target: u64,
    intent: &Node,
) -> Result<(), QuorumError> {
    while target.saturating_sub(latch.next_epoch()) > MAX_EPOCH_JUMP {
        let next = latch.next_epoch() + MAX_EPOCH_JUMP;
        latch.bind(next, intent, &[0; 32], &[])?;
    }
    Ok(())
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum LeaseVoters {
    /// All voters enforce their durable non-equivocation locks.
    NonEquivocating,
    /// Up to two voters can equivocate. Acquisition needs four responses.
    Byzantine,
}

impl LeaseVoters {
    fn required(self) -> usize {
        match self {
            Self::NonEquivocating => 3,
            Self::Byzantine => 4,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EpochLease {
    pub lo: u64,
    pub hi: u64,
    /// Sorted, distinct zero-based Shamir party ids.
    pub members: [u8; 3],
}

/// Receiver-specific MACs. A vote is locally verifiable by a custodian.
/// Transferable public blame requires a separate signature from the voter.
#[derive(Clone, Debug)]
pub struct HandoffVote {
    pub from: u8,
    pub tags: [Node; 5],
}

pub struct EpochLeaseCertificate {
    pub lease: EpochLease,
    pub votes: Vec<HandoffVote>,
}

/// One party's single share of every leaf. The same layout is used across leases.
pub struct CommitteeHandoffJorts<W: DurableWal> {
    deployment: Node,
    model: LeaseVoters,
    tree: Arc<QuorumTree>,
    material: ShamirPartyMaterial,
    lease_lock: BeltLatch<W>,
    leaf_lock: BeltLatch<W>,
}

impl<W: DurableWal> CommitteeHandoffJorts<W> {
    pub fn new(
        deployment: Node,
        model: LeaseVoters,
        cfg: QuorumConfig,
        tree: Arc<QuorumTree>,
        material: ShamirPartyMaterial,
        lease_wal: W,
        leaf_wal: W,
    ) -> Result<Self, QuorumError> {
        let h = usize::from(tree.public_key().height);
        if cfg.threshold() != 3
            || cfg.parties() != 5
            || material.party >= 5
            || material.mac_keys.len() != 5
            || !(1..=10).contains(&h)
            || material.leaves.len() != 1usize << h
            || material.leaves.iter().any(|l| l.len() != LEAF_SHARE_NODES)
        {
            return Err(QuorumError::InvalidConfig(
                "handoff requires a full 3-of-5 Shamir tree",
            ));
        }
        Ok(Self {
            deployment,
            model,
            tree,
            material,
            lease_lock: BeltLatch::recover(lease_wal, h)?,
            leaf_lock: BeltLatch::recover(leaf_wal, h)?,
        })
    }

    pub fn high_water_mark(&self) -> u64 {
        self.lease_lock.next_epoch()
    }

    fn binding(&self, l: &EpochLease) -> Result<Node, QuorumError> {
        if l.lo >= l.hi
            || l.hi > self.material.leaves.len() as u64
            || l.members[2] >= 5
            || l.members.windows(2).any(|w| w[0] >= w[1])
        {
            return Err(QuorumError::InvalidConfig(
                "invalid lease range or committee",
            ));
        }
        let pk = self.tree.public_key();
        Ok(h32(
            b"QSAG.JORTS.HANDOFF/v1",
            &[
                &self.deployment,
                &pk.root,
                &pk.pk_seed,
                &[pk.height, self.model.required() as u8],
                &l.lo.to_be_bytes(),
                &l.hi.to_be_bytes(),
                &l.members,
            ],
        ))
    }

    fn lock(&mut self, l: &EpochLease, binding: &Node) -> Result<(), QuorumError> {
        let last = l.hi - 1;
        let retry = self
            .lease_lock
            .in_flight()
            .is_some_and(|r| r.epoch <= last && &r.msg_digest == binding);
        if !retry && l.lo < self.high_water_mark() {
            return Err(QuorumError::Latch(BeltLatchError::EpochConsumed));
        }
        burn_gap(&mut self.lease_lock, last, binding)?;
        self.lease_lock.bind(last, binding, &[0; 32], &[])?;
        Ok(())
    }

    fn vote(&self, domain: &[u8], binding: &Node) -> HandoffVote {
        let from = self.material.party as u8;
        HandoffVote {
            from,
            tags: core::array::from_fn(|to| {
                mac32(
                    &self.material.mac_keys[to],
                    domain,
                    &[binding, &[from, to as u8]],
                )
            }),
        }
    }

    pub fn vote_lease(&mut self, l: &EpochLease) -> Result<HandoffVote, QuorumError> {
        let binding = self.binding(l)?;
        self.lock(l, &binding)?;
        Ok(self.vote(b"QSAG.JORTS.LEASE.VOTE/v1", &binding))
    }

    fn verify_votes(
        &self,
        domain: &[u8],
        binding: &Node,
        votes: &[HandoffVote],
        allowed: &[u8],
        required: usize,
    ) -> Result<(), QuorumError> {
        let mut seen = [false; 5];
        for vote in votes {
            let p = usize::from(vote.from);
            if !allowed.contains(&vote.from) || seen[p] {
                return Err(QuorumError::BadOpeningSet);
            }
            let me = self.material.party;
            if !mac32_verify(
                &self.material.mac_keys[p],
                domain,
                &[binding, &[vote.from, me as u8]],
                &vote.tags[me],
            ) {
                return Err(QuorumError::EchoMacInvalid { party: p });
            }
            seen[p] = true;
        }
        if votes.len() < required {
            return Err(QuorumError::CertificateTooSmall {
                valid: votes.len(),
                required,
            });
        }
        Ok(())
    }

    fn prepare(
        &mut self,
        cert: &EpochLeaseCertificate,
        leaf: u64,
        msg: &[u8],
    ) -> Result<(LeafRecord, Node), QuorumError> {
        let l = &cert.lease;
        let binding = self.binding(l)?;
        if !l.members.contains(&(self.material.party as u8)) || !(l.lo..l.hi).contains(&leaf) {
            return Err(QuorumError::PermitMismatch);
        }
        self.verify_votes(
            b"QSAG.JORTS.LEASE.VOTE/v1",
            &binding,
            &cert.votes,
            &[0, 1, 2, 3, 4],
            self.model.required(),
        )?;
        self.lock(l, &binding)?;
        let record = LeafRecord::derive(self.tree.public_key(), leaf, msg)
            .ok_or(QuorumError::GrindFailed)?;
        let intent = h32(
            b"QSAG.JORTS.LEASE.INTENT/v1",
            &[&binding, &record.binding()],
        );
        burn_gap(&mut self.leaf_lock, leaf, &intent)?;
        self.leaf_lock
            .bind(leaf, &intent, &record.salt(), &record.digits)?;
        Ok((record, intent))
    }

    pub fn acknowledge(
        &mut self,
        cert: &EpochLeaseCertificate,
        leaf: u64,
        msg: &[u8],
    ) -> Result<HandoffVote, QuorumError> {
        let (_, intent) = self.prepare(cert, leaf, msg)?;
        Ok(self.vote(b"QSAG.JORTS.LEASE.ECHO/v1", &intent))
    }

    /// A durable adapter can authenticate the pending leaf's external release
    /// reservation against this exact WAL record before calling open.
    pub fn pending_leaf(&self) -> Option<&BeltLatchRecord> {
        self.leaf_lock.in_flight()
    }

    pub fn open(
        &mut self,
        cert: &EpochLeaseCertificate,
        leaf: u64,
        msg: &[u8],
        echoes: &[HandoffVote],
    ) -> Result<ShareOpening, QuorumError> {
        let (record, intent) = self.prepare(cert, leaf, msg)?;
        self.verify_votes(
            b"QSAG.JORTS.LEASE.ECHO/v1",
            &intent,
            echoes,
            &cert.lease.members,
            3,
        )?;
        let bound = self.pending_leaf().ok_or(QuorumError::PermitMismatch)?;
        self.leaf_lock
            .wal()
            .authorize_open(bound)
            .map_err(BeltLatchError::Wal)?;
        Ok(select_shares(
            self.material.party,
            &record,
            &self.material.leaves[leaf as usize],
        ))
    }
}

#[cfg(feature = "std")]
impl CommitteeHandoffJorts<qsag_core::belt_latch::FsBeltWal> {
    /// Install a one-attempt authorization. The WAL compares both epoch and binding
    /// with the current leaf record when consuming the permit during `open`.
    pub fn install_ceremony_permit(
        &mut self,
        journal: &qsag_core::ceremony_journal::FsCeremonyJournal,
        permit: qsag_core::ceremony_journal::CeremonyReleasePermit,
    ) -> std::io::Result<()> {
        self.leaf_lock.wal_mut().authorize_release(journal, permit)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(all(feature = "std", unix))]
    #[test]
    fn anchored_filesystem_handoff_requires_a_single_use_release_permit() {
        use qsag_core::belt_latch::FsBeltWal;
        use qsag_core::ceremony_journal::{CeremonyReservation, FsCeremonyJournal};
        let cfg = QuorumConfig::new(3, 5, 1).unwrap();
        let keys = stage_bft_shamir(cfg, 1, &[38; 32]).unwrap();
        let key_id = keys.tree.public_key().root;
        let dir = std::env::temp_dir().join(std::format!(
            "qsag-handoff-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir(&dir).unwrap();
        let anchor = |name: &str, party: u8| {
            alloc::boxed::Box::new(
                crate::FsDirectoryMonotoneAnchor::create_new(
                    dir.join(std::format!("{name}-anchor-{party}")),
                    [party + 9; 32],
                )
                .unwrap(),
            )
        };
        let mut nodes: Vec<_> = keys
            .parties
            .into_iter()
            .take(3)
            .enumerate()
            .map(|(i, k)| {
                let wal = |name: &str| {
                    FsBeltWal::provision_genesis_anchored(
                        dir.join(std::format!("{name}-{i}")),
                        [i as u8 + 13; 32],
                        anchor(name, i as u8),
                    )
                    .unwrap()
                };
                CommitteeHandoffJorts::new(
                    [8; 32],
                    LeaseVoters::NonEquivocating,
                    cfg,
                    keys.tree.clone(),
                    k,
                    wal("lease"),
                    wal("leaf"),
                )
                .unwrap()
            })
            .collect();
        let lease = EpochLease {
            lo: 0,
            hi: 2,
            members: [0, 1, 2],
        };
        let cert = EpochLeaseCertificate {
            lease,
            votes: nodes
                .iter_mut()
                .map(|p| p.vote_lease(&lease).unwrap())
                .collect(),
        };
        let echoes: Vec<_> = nodes
            .iter_mut()
            .map(|p| p.acknowledge(&cert, 0, b"settle").unwrap())
            .collect();
        let mut shares = Vec::new();
        for (i, node) in nodes.iter_mut().enumerate() {
            assert!(node.open(&cert, 0, b"settle", &echoes).is_err());
            let mut journal = FsCeremonyJournal::create_new_anchored(
                dir.join(std::format!("journal-{i}")),
                key_id,
                [i as u8 + 24; 32],
                anchor("permit", i as u8),
            )
            .unwrap();
            let rec = node.pending_leaf().unwrap();
            let permit = journal
                .persist_epoch_before_release(
                    rec.epoch,
                    CeremonyReservation {
                        ceremony_id: [3; 32],
                        key_id,
                        epoch_or_codeword: rec.binding(),
                        seed_burn_cursor: 1,
                        hedge_generation: 1,
                    },
                )
                .unwrap();
            node.install_ceremony_permit(&journal, permit).unwrap();
            shares.push(node.open(&cert, 0, b"settle", &echoes).unwrap());
            assert!(node.open(&cert, 0, b"settle", &echoes).is_err());
        }
        let record = LeafRecord::derive(keys.tree.public_key(), 0, b"settle").unwrap();
        let sig = combine_shamir(&cfg, &keys.tree, &record, &shares).unwrap();
        assert!(quorum_jorts_verify(keys.tree.public_key(), b"settle", &sig));
        drop(nodes);
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn crossing_ranges_and_stale_leases_fail_after_recovery() {
        let cfg = QuorumConfig::new(3, 5, 1).unwrap();
        let keys = stage_bft_shamir(cfg, 3, &[11; 32]).unwrap();
        let tree = keys.tree;
        let mut nodes: Vec<_> = keys
            .parties
            .into_iter()
            .map(|k| {
                CommitteeHandoffJorts::new(
                    [4; 32],
                    LeaseVoters::NonEquivocating,
                    cfg,
                    tree.clone(),
                    k,
                    MemoryWal::new(),
                    MemoryWal::new(),
                )
                .unwrap()
            })
            .collect();
        let old = EpochLease {
            lo: 0,
            hi: 4,
            members: [0, 1, 2],
        };
        let old = EpochLeaseCertificate {
            lease: old,
            votes: (0..3).map(|i| nodes[i].vote_lease(&old).unwrap()).collect(),
        };
        let mut node = nodes.remove(2);
        node.acknowledge(&old, 0, b"m").unwrap();
        let mut recovered = CommitteeHandoffJorts::new(
            node.deployment,
            node.model,
            cfg,
            tree,
            node.material,
            node.lease_lock.into_wal(),
            node.leaf_lock.into_wal(),
        )
        .unwrap();
        assert_eq!(recovered.high_water_mark(), 4);
        assert!(
            recovered
                .vote_lease(&EpochLease {
                    lo: 3,
                    hi: 6,
                    members: [2, 3, 4]
                })
                .is_err()
        );
        recovered
            .vote_lease(&EpochLease {
                lo: 4,
                hi: 7,
                members: [2, 3, 4],
            })
            .unwrap();
        assert!(recovered.acknowledge(&old, 2, b"m").is_err());
    }

    #[test]
    fn same_leaf_evidence_verifies_only_for_a_conflicting_signed_pair() {
        let cfg = QuorumConfig::new(3, 5, 1).unwrap();
        let mut a = BftShamirJorts::stage(cfg, 1, &[7; 32]).unwrap();
        let mut b = BftShamirJorts::stage(cfg, 1, &[7; 32]).unwrap();
        let x = a.sign(&[0, 1, 2, 3], b"x").unwrap();
        let y = b.sign(&[0, 1, 2, 3], b"y").unwrap();
        assert!(verify_leaf_equivocation(
            a.public_key(),
            [b"x", b"y"],
            [&x, &y]
        ));
        assert!(!verify_leaf_equivocation(
            a.public_key(),
            [b"x", b"y"],
            [&x, &x]
        ));
        assert!(!verify_leaf_equivocation(
            a.public_key(),
            [b"x", b"x"],
            [&x, &x]
        ));
    }

    #[test]
    fn handoff_burn_and_message_refusals_preserve_qs_b_signature() {
        let cfg = QuorumConfig::new(3, 5, 1).unwrap();
        let seed = [7; 32];
        for model in [LeaseVoters::NonEquivocating, LeaseVoters::Byzantine] {
            let keys = stage_bft_shamir(cfg, 2, &seed).unwrap();
            let tree = keys.tree;
            let mut nodes: Vec<_> = keys
                .parties
                .into_iter()
                .map(|k| {
                    CommitteeHandoffJorts::new(
                        [8; 32],
                        model,
                        cfg,
                        tree.clone(),
                        k,
                        MemoryWal::new(),
                        MemoryWal::new(),
                    )
                    .unwrap()
                })
                .collect();
            let mut reference = BftShamirJorts::stage(cfg, 2, &seed).unwrap();
            for (epoch, members) in [
                (0, [0, 1, 2]),
                (1, [2, 3, 4]),
                (2, [0, 2, 4]),
                (3, [1, 2, 3]),
            ] {
                let l = EpochLease {
                    lo: epoch,
                    hi: epoch + 1,
                    members,
                };
                let mut cert = EpochLeaseCertificate {
                    lease: l,
                    votes: (0..model.required())
                        .map(|p| nodes[p].vote_lease(&l).unwrap())
                        .collect(),
                };
                let last = cert.votes.pop().unwrap();
                assert!(
                    nodes[members[0] as usize]
                        .acknowledge(&cert, epoch, b"m")
                        .is_err()
                );
                cert.votes.push(last);
                let echoes: Vec<_> = members
                    .iter()
                    .map(|p| nodes[*p as usize].acknowledge(&cert, epoch, b"m").unwrap())
                    .collect();
                let first = &mut nodes[members[0] as usize];
                assert!(first.open(&cert, epoch, b"m", &echoes[..2]).is_err());
                assert!(first.open(&cert, epoch, b"other", &echoes).is_err());
                let shares: Vec<_> = members
                    .iter()
                    .map(|p| {
                        nodes[*p as usize]
                            .open(&cert, epoch, b"m", &echoes)
                            .unwrap()
                    })
                    .collect();
                let record = LeafRecord::derive(tree.public_key(), epoch, b"m").unwrap();
                assert_eq!(
                    combine_shamir(&cfg, &tree, &record, &shares).unwrap(),
                    reference
                        .sign_at(&[0, 1, 2, 3], &[0, 1, 2], epoch, b"m")
                        .unwrap()
                );
                assert!(
                    nodes[0]
                        .vote_lease(&EpochLease {
                            lo: 0,
                            hi: epoch + 1,
                            members: [0, 1, 4]
                        })
                        .is_err()
                );
            }
        }
    }
}
