use super::*;

/// Public network envelopes require authenticated sender identities and reliable broadcast.
/// In particular, a caller must not accept an envelope merely because its ID is in the quorum.
/// The session ID must be fresh; durable slot storage is required across process restarts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PartyPolicyDeltaCommitMsg {
    pub party_id: u16,
    pub slot: usize,
    pub session_id: [u8; 32],
    pub initiator_party: u16,
    pub window_id: u64,
    pub quorum_ids: Vec<u16>,
    pub policy_digest: [u8; 32],
    pub intent_digest: [u8; 32],
    pub commitment: [u8; 32],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PartyPolicyDeltaOpenMsg {
    pub party_id: u16,
    pub salt_i: [u8; 32],
    pub delta_i: [u128; 2],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PartyPolicySigmaCommitMsg {
    pub party_id: u16,
    pub transcript_digest: [u8; 32],
    pub commitment: [u8; 32],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PartyPolicySigmaOpenMsg {
    pub party_id: u16,
    pub sigma_salt_i: [u8; 32],
    pub sigma_i: [u128; 2],
}

// No Clone or public constructors for any phase state.
pub(crate) struct PartyPolicyContext {
    intent: TransactionIntent,
    velocity_window_cap: u128,
    cumulative_epoch_spent: u128,
    own: PartyPolicyDeltaCommitMsg,
    peer_slots: Vec<(u16, usize)>,
    guard_binding: [u8; 32],
    pub(crate) salt: [u8; 32],
    pub(crate) delta: [u128; 2],
    folded: [u128; 2],
    pub(crate) sigma: [u128; 2],
    pub(crate) sigma_salt: [u8; 32],
}

impl Drop for PartyPolicyContext {
    fn drop(&mut self) {
        wipe(&mut self.guard_binding);
        wipe(&mut self.salt);
        wipe(&mut self.sigma_salt);
        wipe(&mut self.delta);
        wipe(&mut self.folded);
        wipe(&mut self.sigma);
    }
}

/// Owns the pending opening. A session that cannot continue (a peer went silent or the
/// transport failed) is ended with `abort`, which retires its slots and frees the guard for
/// the next session. Merely dropping a state leaves its guard latched: the next session
/// start on that guard is treated as an overlap and poisons it.
#[must_use]
pub struct PartyPolicyRound1State {
    context: PartyPolicyContext,
}
/// All delta commitments are frozen; verify every opening before producing sigma.
#[must_use]
pub struct PartyPolicyRound2State {
    pub(crate) context: PartyPolicyContext,
    commits: Vec<PartyPolicyDeltaCommitMsg>,
}
/// Sigma is committed but remains private until the complete commitment vector is frozen.
#[must_use]
pub struct PartyPolicyRound3State {
    pub(crate) context: PartyPolicyContext,
    pub(crate) own_sigma: PartyPolicySigmaCommitMsg,
}
/// Only this state can verify sigma openings and mint the per-party capability.
#[must_use]
pub struct PartyPolicyFinalizeState {
    context: PartyPolicyContext,
    commits: Vec<PartyPolicySigmaCommitMsg>,
}

pub(crate) fn policy_ids_bytes(ids: &[u16]) -> Vec<u8> {
    ids.iter().flat_map(|id| id.to_be_bytes()).collect()
}

pub(crate) fn policy_pair_bytes(pair: &[u128; 2]) -> [u8; 32] {
    let mut bytes = [0; 32];
    bytes[..16].copy_from_slice(&pair[0].to_le_bytes());
    bytes[16..].copy_from_slice(&pair[1].to_le_bytes());
    bytes
}

pub(crate) fn policy_pair(bytes: &[u8; 32]) -> [u128; 2] {
    [
        u128::from_le_bytes(core::array::from_fn(|i| bytes[i])),
        u128::from_le_bytes(core::array::from_fn(|i| bytes[16 + i])),
    ]
}

/// A digest derived from guard secrets, erased when it leaves scope.
pub(crate) fn secret_digest(domain: &[u8], fields: &[&[u8]]) -> SecretBytes<32> {
    SecretBuffer(cshake256_framed_32(domain, fields))
}

pub(crate) fn delta_commitment(
    c: &PartyPolicyDeltaCommitMsg,
    salt: &[u8; 32],
    delta: &[u128; 2],
) -> [u8; 32] {
    cshake256_framed_32(
        b"QSAG.POLICY.DELTA_COMMIT.V2",
        &[
            &c.session_id,
            &c.party_id.to_be_bytes(),
            &c.initiator_party.to_be_bytes(),
            &c.window_id.to_be_bytes(),
            &policy_ids_bytes(&c.quorum_ids),
            &c.intent_digest,
            salt,
            &policy_pair_bytes(delta),
            &c.policy_digest,
            &(c.slot as u64).to_be_bytes(),
        ],
    )
}

pub(crate) fn sigma_commitment(
    c: &PartyPolicySigmaCommitMsg,
    salt: &[u8; 32],
    sigma: &[u128; 2],
) -> [u8; 32] {
    cshake256_framed_32(
        b"QSAG.POLICY.SIGMA_COMMIT.V1",
        &[
            &c.transcript_digest,
            &c.party_id.to_be_bytes(),
            salt,
            &policy_pair_bytes(sigma),
        ],
    )
}

/// The values one guard derives in barrier round 1: the folded policy wire, that wire
/// masked with the guard's preprocessed `r` of the session slot, and the salt of the
/// delta commitment.
pub(crate) struct MaskedWire {
    pub(crate) folded: [u128; 2],
    pub(crate) delta: [u128; 2],
    pub(crate) salt: [u8; 32],
}

/// The values one guard derives in barrier round 3: its sigma commitment message, its
/// sigma share and the salt of the commitment.
pub(crate) type CommittedSigma = (
    PartyPolicySigmaCommitMsg,
    SecretBuffer<[u128; 2]>,
    SecretBytes<32>,
);

// The round derivations of the committed barrier. The per-party phase states and the
// in-process barrier both call these and nothing else, so one session produces the same
// commitments, transcript digest and sigma shares on either path.
impl PolicySignerGuardShare {
    /// Round 1 for the session `own` describes.
    pub(crate) fn masked_policy_wire<B: AcceleratorBackend>(
        &self,
        own: &PartyPolicyDeltaCommitMsg,
        intent_nonce: &[u8; 32],
        accel: &B,
    ) -> Result<MaskedWire, PolicyViolation> {
        let r = SecretBuffer(
            *self
                .preproc_r
                .get(own.slot)
                .ok_or(PolicyViolation::BarrierPreprocExhausted)?,
        );
        let x = compute_folded_policy_wire(
            &own.policy_digest,
            &own.intent_digest,
            &own.session_id,
            own.initiator_party,
            own.window_id,
            intent_nonce,
            accel,
        )?;
        let salt = cshake256_framed_32(
            b"QSAG.POLICY.DELTA_SALT.V1",
            &[
                &self.local_salt_seed,
                &own.session_id,
                &(own.slot as u64).to_be_bytes(),
            ],
        );
        Ok(MaskedWire {
            folded: [x.0, x.1],
            delta: [r[0] ^ x.0, r[1] ^ x.1],
            salt,
        })
    }

    /// Round 3 for the session `own` describes: check every delta opening against its
    /// frozen commitment, bind the verified openings into the transcript digest, and
    /// derive this guard's sigma share with its commitment. `commits` and `opens` are
    /// sorted by party and cover `own.quorum_ids`.
    pub(crate) fn committed_sigma(
        &self,
        own: &PartyPolicyDeltaCommitMsg,
        folded: &[u128; 2],
        commits: &[PartyPolicyDeltaCommitMsg],
        opens: &[PartyPolicyDeltaOpenMsg],
    ) -> Result<CommittedSigma, PolicyViolation> {
        if opens.len() != commits.len() {
            return Err(PolicyViolation::IntentBindingMismatch);
        }
        let mut transcript = Vec::new();
        for (c, o) in commits.iter().zip(opens) {
            if c.party_id != o.party_id
                || !ct_eq_bytes(&c.commitment, &delta_commitment(c, &o.salt_i, &o.delta_i))
            {
                return Err(PolicyViolation::BarrierCommitmentMismatch {
                    party_id: c.party_id,
                });
            }
            transcript.extend_from_slice(&c.party_id.to_be_bytes());
            transcript.extend_from_slice(&(c.slot as u64).to_be_bytes());
            transcript.extend_from_slice(&c.commitment);
            transcript.extend_from_slice(&o.salt_i);
            transcript.extend_from_slice(&policy_pair_bytes(&o.delta_i));
        }
        let q_digest = cshake256_framed_32(
            b"QSAG.POLICY.QUORUM_SET.V2",
            &[&policy_ids_bytes(&own.quorum_ids)],
        );
        let digest = cshake256_framed_32(
            b"QSAG.POLICY.VERIFIED_DELTAS.V2",
            &[
                &own.session_id,
                &own.initiator_party.to_be_bytes(),
                &own.window_id.to_be_bytes(),
                &own.policy_digest,
                &own.intent_digest,
                &q_digest,
                &transcript,
            ],
        );
        let mut sigma = self.pairwise_zero_share(&own.quorum_ids, &own.session_id, &q_digest);
        for (c, o) in commits.iter().zip(opens) {
            if c.party_id == own.party_id {
                continue;
            }
            let m = SecretBuffer(self.outgoing_mac(c.party_id, own.slot)?);
            let k = SecretBuffer(self.incoming_key(c.party_id, c.slot)?);
            let peer_alpha = self.incoming_slot_alpha(c.party_id, c.slot);
            let chi = policy_pair(&cshake256_framed_32(
                b"QSAG.POLICY.PAIR_WEIGHT.V3",
                &[
                    &digest,
                    &own.party_id.min(c.party_id).to_be_bytes(),
                    &own.party_id.max(c.party_id).to_be_bytes(),
                ],
            ));
            for lane in 0..2 {
                sigma[lane] ^= gf2_128_mul(
                    chi[lane],
                    m[lane]
                        ^ k[lane]
                        ^ gf2_128_mul(peer_alpha[lane], folded[lane] ^ o.delta_i[lane]),
                );
            }
        }
        let salt = secret_digest(
            b"QSAG.POLICY.SIGMA_SALT.V1",
            &[
                &self.local_salt_seed,
                &digest,
                &(own.slot as u64).to_be_bytes(),
            ],
        );
        let mut msg = PartyPolicySigmaCommitMsg {
            party_id: own.party_id,
            transcript_digest: digest,
            commitment: [0; 32],
        };
        msg.commitment = sigma_commitment(&msg, &salt, &sigma);
        Ok((msg, sigma, salt))
    }
}

/// Round 4 verification: every sigma opening against its frozen commitment, then the
/// zero-sum release decision of the extracted single-use guard, bound to the transcript
/// digest the commitments froze. `commits` and `opens` are sorted by party.
pub(crate) fn release_committed_sigmas(
    session_id: &[u8; 32],
    round_id: u64,
    commits: &[PartyPolicySigmaCommitMsg],
    opens: &[PartyPolicySigmaOpenMsg],
) -> Result<qsag_verified::OpeningReleasePermit, PolicyViolation> {
    if opens.len() != commits.len() {
        return Err(PolicyViolation::IntentBindingMismatch);
    }
    let mut sigma_openings = Vec::with_capacity(opens.len());
    for (c, o) in commits.iter().zip(opens) {
        let recomputed = sigma_commitment(c, &o.sigma_salt_i, &o.sigma_i);
        if c.party_id != o.party_id || !ct_eq_bytes(&c.commitment, &recomputed) {
            return Err(PolicyViolation::BarrierCommitmentMismatch {
                party_id: c.party_id,
            });
        }
        sigma_openings.push((c.commitment, recomputed, o.sigma_i));
    }
    let binding = commits
        .first()
        .map(|c| c.transcript_digest)
        .ok_or(PolicyViolation::IntentBindingMismatch)?;
    release_sigma_round(session_id, round_id, &binding, &sigma_openings)
}

impl PolicySignerGuardShare {
    fn phase_binding(&self, slot: usize) -> [u8; 32] {
        cshake256_framed_32(
            b"QSAG.POLICY.GUARD_BINDING.V1",
            &[
                &self.local_salt_seed,
                &self.enrolled_party_id.to_be_bytes(),
                &(slot as u64).to_be_bytes(),
            ],
        )
    }

    fn check_phase(&mut self, c: &PartyPolicyContext, phase: u8) -> Result<(), PolicyViolation> {
        if self.poisoned {
            return Err(PolicyViolation::GuardPoisoned);
        }
        if self.party_id != self.enrolled_party_id
            || self.party_id != c.own.party_id
            || self.active_phase != Some((c.own.slot, phase))
            || !ct_eq_bytes(&self.phase_binding(c.own.slot), &c.guard_binding)
        {
            self.poison();
            return Err(PolicyViolation::IntentBindingMismatch);
        }
        Ok(())
    }

    fn round1_commit_intent_inner(
        &mut self,
        policy: &TransactionPolicy,
        intent: &TransactionIntent,
        session_id: [u8; 32],
        current_timestamp: u64,
        cumulative_epoch_spent: u128,
        force_authenticated_initiator: bool,
    ) -> Result<(PartyPolicyRound1State, PartyPolicyDeltaCommitMsg), PolicyViolation> {
        if self.poisoned {
            return Err(PolicyViolation::GuardPoisoned);
        }
        if self.active_phase.is_some() || self.party_id != self.enrolled_party_id {
            self.poison();
            return Err(PolicyViolation::IntentBindingMismatch);
        }
        policy.evaluate(intent)?;
        if current_timestamp != intent.timestamp_secs {
            return Err(PolicyViolation::TimestampOutsideWindow);
        }
        if cumulative_epoch_spent != intent.rolling_window_spent {
            return Err(PolicyViolation::VelocityCapOverflowOrExceeded);
        }
        self.verify_initiator_authentication(policy, intent, force_authenticated_initiator)?;
        self.check_window_nonce_and_projected_spend(
            policy.velocity_window_cap,
            intent,
            &session_id,
            cumulative_epoch_spent,
        )?;
        let mut ids = intent.approver_parties.clone();
        ids.sort_unstable();
        if ids.len() < 2
            || ids != intent.quorum_ids
            || !ids.contains(&self.party_id)
            || session_id != intent.session_id
        {
            return Err(PolicyViolation::IntentBindingMismatch);
        }
        if !self.has_global_velocity_intersection(policy, &ids) {
            return Err(PolicyViolation::MissingHardwareGuardian);
        }
        let slot = self.next_slot.get();
        if slot >= self.preproc_r.len() {
            return Err(PolicyViolation::BarrierPreprocExhausted);
        }
        for &peer in &ids {
            if peer != self.party_id {
                self.outgoing_mac(peer, slot)?;
                if !self.pairwise_zero_seeds.iter().any(|(id, _)| *id == peer) {
                    return Err(PolicyViolation::BarrierBdozMacFailed);
                }
            }
        }
        self.next_slot.set(slot + 1);
        self.active_phase = Some((slot, 1));
        let mut own = PartyPolicyDeltaCommitMsg {
            party_id: self.party_id,
            slot,
            session_id,
            initiator_party: intent.initiator_party,
            window_id: intent.window_id,
            quorum_ids: ids,
            policy_digest: policy.canonical_digest(),
            intent_digest: intent.canonical_digest(),
            commitment: [0; 32],
        };
        let MaskedWire {
            folded,
            delta,
            salt,
        } = match self.masked_policy_wire(
            &own,
            &intent.nonce,
            &qsag_accel::CpuReferenceBackend::new(),
        ) {
            Ok(v) => v,
            Err(err) => {
                self.abort_session_slot(slot, &[]);
                return Err(err);
            }
        };
        own.commitment = delta_commitment(&own, &salt, &delta);
        let context = PartyPolicyContext {
            intent: intent.clone(),
            velocity_window_cap: policy.velocity_window_cap,
            cumulative_epoch_spent,
            own: own.clone(),
            peer_slots: Vec::new(),
            guard_binding: self.phase_binding(slot),
            salt,
            delta,
            folded,
            sigma: [0; 2],
            sigma_salt: [0; 32],
        };
        Ok((PartyPolicyRound1State { context }, own))
    }

    /// Clock and epoch spend must come from local authoritative state, never from the requester.
    pub fn round1_commit_intent(
        &mut self,
        policy: &TransactionPolicy,
        intent: &TransactionIntent,
        session_id: [u8; 32],
        current_timestamp: u64,
        cumulative_epoch_spent: u128,
    ) -> Result<(PartyPolicyRound1State, PartyPolicyDeltaCommitMsg), PolicyViolation> {
        self.round1_commit_intent_inner(
            policy,
            intent,
            session_id,
            current_timestamp,
            cumulative_epoch_spent,
            false,
        )
    }

    /// Commit to `intent` while mandating cryptographic authentication of `intent.initiator_party`.
    pub fn round1_commit_intent_authenticated(
        &mut self,
        policy: &TransactionPolicy,
        intent: &TransactionIntent,
        session_id: [u8; 32],
        current_timestamp: u64,
        cumulative_epoch_spent: u128,
    ) -> Result<(PartyPolicyRound1State, PartyPolicyDeltaCommitMsg), PolicyViolation> {
        self.round1_commit_intent_inner(
            policy,
            intent,
            session_id,
            current_timestamp,
            cumulative_epoch_spent,
            true,
        )
    }
}

impl PolicySignerGuardShare {
    /// End the session that `context` owns in `phase` without releasing anything: its own
    /// slot and every peer slot it was shown are retired, the ledger is untouched. A state
    /// presented to a guard that does not own it poisons that guard, as in every phase.
    fn abandon_session(
        &mut self,
        context: &PartyPolicyContext,
        phase: u8,
    ) -> Result<(), PolicyViolation> {
        self.check_phase(context, phase)?;
        self.abort_session_slot(context.own.slot, &context.peer_slots);
        Ok(())
    }
}

macro_rules! policy_phase_abort {
    ($($state:ty => $phase:literal),* $(,)?) => {$(
        impl $state {
            /// Abandon this session on `guard`, retiring its preprocessing slots. The guard
            /// keeps its keys and ledger and can start another session. Persist a checkpoint
            /// afterwards so the retired slots stay retired across a restart.
            pub fn abort(self, guard: &mut PolicySignerGuardShare) -> Result<(), PolicyViolation> {
                guard.abandon_session(&self.context, $phase)
            }
        }
    )*};
}
policy_phase_abort!(
    PartyPolicyRound1State => 1,
    PartyPolicyRound2State => 2,
    PartyPolicyRound3State => 3,
    PartyPolicyFinalizeState => 4,
);

/// Abort ONLY the active session slot (and any opened peer slots) on peer/network protocol errors,
/// preserving the honest party's persistent guard key material and durable spend/nonce ledger.
pub(crate) fn policy_phase_result<T>(
    guard: &mut PolicySignerGuardShare,
    slot: usize,
    peer_slots: &[(u16, usize)],
    result: Result<T, PolicyViolation>,
) -> Result<T, PolicyViolation> {
    if result.is_err() {
        guard.abort_session_slot(slot, peer_slots);
    }
    result
}

impl PartyPolicyRound1State {
    /// Freeze the entire delta commitment vector before releasing this party's opening.
    pub fn round2_open_delta_and_commit_sigma(
        self,
        guard: &mut PolicySignerGuardShare,
        all_r1_commits: &[PartyPolicyDeltaCommitMsg],
    ) -> Result<(PartyPolicyRound2State, PartyPolicyDeltaOpenMsg), PolicyViolation> {
        self.round2_open_delta(guard, all_r1_commits)
    }

    pub fn round2_open_delta(
        mut self,
        guard: &mut PolicySignerGuardShare,
        all_r1_commits: &[PartyPolicyDeltaCommitMsg],
    ) -> Result<(PartyPolicyRound2State, PartyPolicyDeltaOpenMsg), PolicyViolation> {
        guard.check_phase(&self.context, 1)?;
        let own_slot = self.context.own.slot;
        // Peer slots this guard accepted as bound to the session. They are retired with the
        // own slot even when a later commitment is rejected: the peer latched each of them
        // for this session and can never present it again.
        let mut peer_slots = Vec::with_capacity(all_r1_commits.len().saturating_sub(1));
        let result = (|| {
            let own = &self.context.own;
            let mut commits = all_r1_commits.to_vec();
            commits.sort_by_key(|c| c.party_id);
            if commits.len() != own.quorum_ids.len() {
                return Err(PolicyViolation::IntentBindingMismatch);
            }
            for (c, id) in commits.iter().zip(&own.quorum_ids) {
                if c.party_id != *id
                    || c.session_id != own.session_id
                    || c.initiator_party != own.initiator_party
                    || c.window_id != own.window_id
                    || c.quorum_ids != own.quorum_ids
                    || c.policy_digest != own.policy_digest
                    || c.intent_digest != own.intent_digest
                    || (c.party_id == own.party_id && c != own)
                {
                    return Err(PolicyViolation::IntentBindingMismatch);
                }
                if c.party_id != own.party_id {
                    guard.incoming_key(c.party_id, c.slot)?;
                    peer_slots.push((c.party_id, c.slot));
                }
            }
            let msg = PartyPolicyDeltaOpenMsg {
                party_id: own.party_id,
                salt_i: self.context.salt,
                delta_i: self.context.delta,
            };
            self.context.peer_slots = peer_slots.clone();
            guard.active_phase = Some((own.slot, 2));
            Ok((
                PartyPolicyRound2State {
                    context: self.context,
                    commits,
                },
                msg,
            ))
        })();
        policy_phase_result(guard, own_slot, &peer_slots, result)
    }
}

impl PartyPolicyRound2State {
    pub fn round3_commit_sigma(
        mut self,
        guard: &mut PolicySignerGuardShare,
        openings: &[PartyPolicyDeltaOpenMsg],
    ) -> Result<(PartyPolicyRound3State, PartyPolicySigmaCommitMsg), PolicyViolation> {
        guard.check_phase(&self.context, 2)?;
        let own_slot = self.context.own.slot;
        let peer_slots = self.context.peer_slots.clone();
        let result = (|| {
            let mut opens = openings.to_vec();
            opens.sort_by_key(|o| o.party_id);
            let (msg, sigma, salt) = guard.committed_sigma(
                &self.context.own,
                &self.context.folded,
                &self.commits,
                &opens,
            )?;
            guard.active_phase = Some((own_slot, 3));
            self.context.sigma = *sigma;
            self.context.sigma_salt = *salt;
            Ok((
                PartyPolicyRound3State {
                    context: self.context,
                    own_sigma: msg.clone(),
                },
                msg,
            ))
        })();
        policy_phase_result(guard, own_slot, &peer_slots, result)
    }
}

impl PartyPolicyRound3State {
    pub fn round4_open_sigma(
        self,
        guard: &mut PolicySignerGuardShare,
        commitments: &[PartyPolicySigmaCommitMsg],
    ) -> Result<(PartyPolicyFinalizeState, PartyPolicySigmaOpenMsg), PolicyViolation> {
        guard.check_phase(&self.context, 3)?;
        let own_slot = self.context.own.slot;
        let peer_slots = self.context.peer_slots.clone();
        let result = (|| {
            let mut commits = commitments.to_vec();
            commits.sort_by_key(|c| c.party_id);
            if commits.len() != self.context.own.quorum_ids.len() {
                return Err(PolicyViolation::IntentBindingMismatch);
            }
            for (c, id) in commits.iter().zip(&self.context.own.quorum_ids) {
                if c.party_id != *id
                    || c.transcript_digest != self.own_sigma.transcript_digest
                    || (c.party_id == self.own_sigma.party_id && c != &self.own_sigma)
                {
                    return Err(PolicyViolation::IntentBindingMismatch);
                }
            }
            let msg = PartyPolicySigmaOpenMsg {
                party_id: self.own_sigma.party_id,
                sigma_salt_i: self.context.sigma_salt,
                sigma_i: self.context.sigma,
            };
            guard.active_phase = Some((self.context.own.slot, 4));
            Ok((
                PartyPolicyFinalizeState {
                    context: self.context,
                    commits,
                },
                msg,
            ))
        })();
        policy_phase_result(guard, own_slot, &peer_slots, result)
    }
}

impl PartyPolicyFinalizeState {
    pub fn finalize(
        self,
        guard: &mut PolicySignerGuardShare,
        openings: &[PartyPolicySigmaOpenMsg],
    ) -> Result<AuthorizedSignReleaseToken, PolicyViolation> {
        guard.check_phase(&self.context, 4)?;
        let own_slot = self.context.own.slot;
        let peer_slots = self.context.peer_slots.clone();
        let result = (|| {
            let mut opens = openings.to_vec();
            opens.sort_by_key(|o| o.party_id);
            let permit = release_committed_sigmas(
                &self.context.own.session_id,
                own_slot as u64,
                &self.commits,
                &opens,
            )?;
            let projected_spend = guard.check_window_nonce_and_projected_spend(
                self.context.velocity_window_cap,
                &self.context.intent,
                &self.context.own.session_id,
                self.context.cumulative_epoch_spent,
            )?;
            guard.record_approved_intent(
                self.context.velocity_window_cap,
                projected_spend,
                self.context.intent.nonce,
                self.context.own.session_id,
            )?;
            guard.abort_session_slot(own_slot, &peer_slots);
            AuthorizedSignReleaseToken::mint(
                permit,
                self.context.own.session_id,
                self.context.own.policy_digest,
                self.context.own.intent_digest,
                self.context.intent.clone(),
            )
        })();
        policy_phase_result(guard, own_slot, &peer_slots, result)
    }
}
