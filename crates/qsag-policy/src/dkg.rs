use super::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PolicyGuardSeedCommitMsg {
    pub sender: u16,
    pub recipient: u16,
    pub setup_digest: [u8; 32],
    pub commitment: [u8; 32],
}

/// Send only over the private authenticated channel to `recipient`, never broadcast.
#[derive(Clone)]
pub struct PolicyGuardSeedOpenMsg {
    pub sender: u16,
    pub recipient: u16,
    pub setup_digest: [u8; 32],
    pub seed: [u8; 32],
}

impl Drop for PolicyGuardSeedOpenMsg {
    fn drop(&mut self) {
        wipe(&mut self.seed);
    }
}

pub struct PolicyGuardDkgRound1 {
    pub(crate) guard: PolicySignerGuardShare,
    ids: Vec<u16>,
    digest: [u8; 32],
    seeds: Vec<PolicyGuardSeedOpenMsg>,
}

pub struct PolicyGuardDkgRound2 {
    first: PolicyGuardDkgRound1,
    peer_commits: Vec<PolicyGuardSeedCommitMsg>,
}

pub(crate) fn policy_seed_commit(o: &PolicyGuardSeedOpenMsg) -> [u8; 32] {
    cshake256_framed_32(
        b"QSAG.POLICY.DKG.SEED_COMMIT.V1",
        &[
            &o.setup_digest,
            &o.sender.to_be_bytes(),
            &o.recipient.to_be_bytes(),
            &o.seed,
        ],
    )
}

impl PolicyGuardDkgRound1 {
    /// Each participant supplies independent private CSPRNG entropy and a fresh setup ID.
    /// No participant provides any other participant's entropy or guard secrets.
    pub fn new(
        party_id: u16,
        party_ids: &[u16],
        setup_id: [u8; 32],
        entropy: [u8; 32],
    ) -> Result<(Self, Vec<PolicyGuardSeedCommitMsg>), PolicyViolation> {
        Self::new_with_capacity(party_id, party_ids, setup_id, entropy, BDOZ_PREPROC_SLOTS)
    }

    /// Provision a caller-sized pool. The capacity is committed into the ceremony transcript.
    pub fn new_with_capacity(
        party_id: u16,
        party_ids: &[u16],
        setup_id: [u8; 32],
        mut entropy: [u8; 32],
        preprocessing_slots: usize,
    ) -> Result<(Self, Vec<PolicyGuardSeedCommitMsg>), PolicyViolation> {
        if preprocessing_slots == 0 || preprocessing_slots > MAX_POLICY_CAPACITY {
            wipe(&mut entropy);
            return Err(PolicyViolation::BarrierPreprocExhausted);
        }
        let mut ids = party_ids.to_vec();
        ids.sort_unstable();
        if ids.len() < 2 || !ids.contains(&party_id) || ids.windows(2).any(|w| w[0] == w[1]) {
            wipe(&mut entropy);
            return Err(PolicyViolation::IntentBindingMismatch);
        }
        let digest = cshake256_framed_32(
            b"QSAG.POLICY.DKG.V1",
            &[
                &setup_id,
                &policy_ids_bytes(&ids),
                &(preprocessing_slots as u64).to_be_bytes(),
            ],
        );
        let mut local = cshake256_framed_32(
            b"QSAG.POLICY.DKG.LOCAL.V1",
            &[&entropy, &digest, &party_id.to_be_bytes()],
        );
        wipe(&mut entropy);
        let mut guard = PolicySignerGuardShare {
            party_id,
            enrolled_party_id: party_id,
            active_phase: None,
            poisoned: false,
            bdoz_alpha_share: policy_pair(&secret_digest(b"QSAG.POLICY.DKG.ALPHA.V1", &[&local])),
            window_authority: None,
            durable_key_id: cshake256_framed_32(b"QSAG.POLICY.DURABLE_KEY.V2", &[&local]),
            durable_generation: Cell::new(0),
            verified_velocity: None,
            velocity_generation: 0,
            local_salt_seed: local,
            pairwise_zero_seeds: Vec::with_capacity(ids.len() - 1),
            preproc_r: Vec::with_capacity(preprocessing_slots),
            preproc_outgoing_macs: Vec::with_capacity(ids.len() - 1),
            preproc_incoming_keys: Vec::with_capacity(ids.len() - 1),
            consumed_peer_slots: Vec::new(),
            next_slot: Cell::new(0),
            current_window_id: 0,
            accumulated_window_spend: 0,
            replay_capacity: MAX_BURNED_INTENT_NONCES,
            burned_intent_nonces: Vec::new(),
            min_nonce_watermark: None,
            burned_sessions: Vec::new(),
            min_session_watermark: None,
            require_authenticated_initiator: true,
        };
        wipe(&mut local);
        for slot in 0..preprocessing_slots {
            guard.preproc_r.push(policy_pair(&secret_digest(
                b"QSAG.POLICY.DKG.R.V1",
                &[&guard.local_salt_seed, &(slot as u64).to_be_bytes()],
            )));
        }
        let mut seeds = Vec::with_capacity(ids.len() - 1);
        let mut commits = Vec::new();
        for &peer in &ids {
            if peer == party_id {
                continue;
            }
            let o = PolicyGuardSeedOpenMsg {
                sender: party_id,
                recipient: peer,
                setup_digest: digest,
                seed: cshake256_framed_32(
                    b"QSAG.POLICY.DKG.SEED.V1",
                    &[&guard.local_salt_seed, &peer.to_be_bytes()],
                ),
            };
            commits.push(PolicyGuardSeedCommitMsg {
                sender: party_id,
                recipient: peer,
                setup_digest: digest,
                commitment: policy_seed_commit(&o),
            });
            seeds.push(o);
        }
        Ok((
            Self {
                guard,
                ids,
                digest,
                seeds,
            },
            commits,
        ))
    }

    /// Accept exactly one authenticated directed commitment from every other participant.
    pub fn round2_open_seeds(
        self,
        peer_commits: &[PolicyGuardSeedCommitMsg],
    ) -> Result<(PolicyGuardDkgRound2, Vec<PolicyGuardSeedOpenMsg>), PolicyViolation> {
        let peers: Vec<_> = self
            .ids
            .iter()
            .copied()
            .filter(|p| *p != self.guard.party_id)
            .collect();
        let mut commits = peer_commits.to_vec();
        commits.sort_by_key(|c| c.sender);
        if commits.len() != peers.len() {
            return Err(PolicyViolation::IntentBindingMismatch);
        }
        for (c, peer) in commits.iter().zip(peers) {
            if c.sender != peer
                || c.recipient != self.guard.party_id
                || !ct_eq_bytes(&c.setup_digest, &self.digest)
            {
                return Err(PolicyViolation::IntentBindingMismatch);
            }
        }
        let opens = self.seeds.clone();
        Ok((
            PolicyGuardDkgRound2 {
                first: self,
                peer_commits: commits,
            },
            opens,
        ))
    }
}

pub(crate) fn policy_ot_pad_stream(
    seed: &[u8; 32],
    domain: &[u8; 32],
    sender: u16,
    receiver: u16,
    start: usize,
) -> qsag_accel::keccak::Shake256 {
    let mut pads = qsag_accel::keccak::init_cshake256(b"", b"QSAG.POLICY.DKG.OT_PAD_STREAM.V2");
    pads.absorb(seed);
    pads.absorb(domain);
    pads.absorb(&sender.to_be_bytes());
    pads.absorb(&receiver.to_be_bytes());
    pads.absorb(&(start as u64).to_be_bytes());
    qsag_accel::keccak::finalize_cshake256(&mut pads, true);
    pads
}

/// Complete pairwise preprocessing without any shared master secret or dealer.
/// OT authenticates each private r bit under the peer's private per-`(peer, slot)` alpha.
/// XOR of the 128 selected values is M; XOR of the sender pads is K, hence M = K + alpha_{peer,slot} * r.
/// The two lanes use separate transfers. Seed openings are private to their endpoints.
/// On every error the owned partial guard and seed material are erased by Drop.
pub fn finalize_distributed_policy_guard<O: PolicyAuthenticatedOt>(
    mut state: PolicyGuardDkgRound2,
    peer_openings: &[PolicyGuardSeedOpenMsg],
    ot: &mut O,
) -> Result<PolicySignerGuardShare, PolicyViolation> {
    let mut opens: Vec<_> = peer_openings.iter().collect();
    opens.sort_by_key(|o| o.sender);
    if opens.len() != state.peer_commits.len() {
        return Err(PolicyViolation::IntentBindingMismatch);
    }
    for (c, o) in state.peer_commits.iter().zip(&opens) {
        if c.sender != o.sender
            || c.recipient != o.recipient
            || !ct_eq_bytes(&c.setup_digest, &o.setup_digest)
            || !ct_eq_bytes(&c.commitment, &policy_seed_commit(o))
        {
            return Err(PolicyViolation::BarrierCommitmentMismatch { party_id: c.sender });
        }
    }
    for o in opens {
        let g = &mut state.first.guard;
        let local = state
            .first
            .seeds
            .iter()
            .find(|s| s.recipient == o.sender)
            .ok_or(PolicyViolation::IntentBindingMismatch)?;
        let (lo_seed, hi_seed) = if g.party_id < o.sender {
            (&local.seed, &o.seed)
        } else {
            (&o.seed, &local.seed)
        };
        let domain = cshake256_framed_32(
            b"QSAG.POLICY.DKG.PAIR.V1",
            &[
                &state.first.digest,
                &g.party_id.min(o.sender).to_be_bytes(),
                &g.party_id.max(o.sender).to_be_bytes(),
            ],
        );
        g.pairwise_zero_seeds.push((
            o.sender,
            cshake256_framed_32(b"QSAG.POLICY.DKG.ZERO.V1", &[&domain, lo_seed, hi_seed]),
        ));
        g.consumed_peer_slots
            .push((o.sender, alloc::vec![0u64; g.preproc_r.len().div_ceil(64)]));
        let mut keys = SecretVec::with_capacity(g.preproc_r.len());
        let mut macs = SecretVec::with_capacity(g.preproc_r.len());
        // Bound scratch buffers independently of the caller's durable pool capacity.
        for start in (0..g.preproc_r.len()).step_by(256) {
            let end = (start + 256).min(g.preproc_r.len());
            let domain = if g.preproc_r.len() <= 256 {
                domain
            } else {
                cshake256_framed_32(
                    b"QSAG.POLICY.DKG.POOL_BATCH.V1",
                    &[
                        &domain,
                        &(start as u64).to_be_bytes(),
                        &(g.preproc_r.len() as u64).to_be_bytes(),
                    ],
                )
            };
            // One private, domain-separated stream per peer and pool batch. The
            // cursor gives distinct pads for every (slot, lane, bit).
            let mut pads =
                policy_ot_pad_stream(&g.local_salt_seed, &domain, g.party_id, o.sender, start);
            let mut alternatives = SecretVec::with_capacity((end - start) * 256);
            let mut choices = SecretVec::with_capacity((end - start) * 256);
            for slot in start..end {
                let slot_alpha = g.incoming_slot_alpha(o.sender, slot);
                let mut key = SecretBuffer([0u128; 2]);
                for (lane, key_lane) in key.iter_mut().enumerate() {
                    for bit in 0..128 {
                        let mut raw = SecretBuffer([0u8; 16]);
                        pads.squeeze(&mut raw[..]);
                        let pad = SecretBuffer(u128::from_le_bytes(*raw));
                        alternatives.push_wiping([
                            *pad,
                            *pad ^ gf2_128_mul(slot_alpha[lane], 1u128 << bit),
                        ]);
                        choices.push_wiping(((g.preproc_r[slot][lane] >> bit) & 1) != 0);
                        *key_lane ^= *pad;
                    }
                }
                keys.push_wiping(*key);
            }
            let selected = SecretVec::new(ot.exchange(
                g.party_id,
                o.sender,
                domain,
                &alternatives,
                &choices,
            )?);
            if selected.len() != (end - start) * 256 {
                return Err(PolicyViolation::BarrierBdozMacFailed);
            }
            for chunk in selected.as_chunks::<256>().0 {
                macs.push_wiping([
                    chunk[..128].iter().fold(0, |a, b| a ^ b),
                    chunk[128..].iter().fold(0, |a, b| a ^ b),
                ]);
            }
        }
        g.preproc_outgoing_macs.push((o.sender, macs.into_inner()));
        g.preproc_incoming_keys.push((o.sender, keys.into_inner()));
    }
    Ok(state.first.guard)
}
