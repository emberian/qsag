use super::*;

/// What one in-process barrier evaluation is asked to approve.
pub(crate) struct BarrierRequest<'a> {
    policy: &'a TransactionPolicy,
    /// One intent per guard, in guard order.
    per_party_intents: &'a [TransactionIntent],
    session_id: [u8; 32],
    current_timestamp: u64,
    force_authenticated_initiator: bool,
    #[cfg(test)]
    injected_delta_fault: Option<(usize, (u128, u128))>,
}

/// Evaluate `policy` across `quorum_guards` where each signer $i$ independently evaluates its own
/// local `per_party_intents[i]` inside the **commit-then-open Eurocrypt-2011 pairwise BDOZ**
/// barrier (`0` central MAC key reconstruction, private pairwise zero-shares!). The rounds
/// are those of the per-party phase states, run by [`barrier_rounds_in_process`].
///
/// Recording the approval is all-or-nothing across `shared_ledger` and every guard. Each
/// guard's spend is first decided without mutation; only when all of them and the shared
/// ledger accept is anything advanced, and those commits cannot fail. On a refusal:
/// * by a guard: that guard is poisoned (its own verified guard contradicts the spend it
///   projected a moment ago), the shared ledger and every other guard keep their spend,
///   generation and replay sets unchanged;
/// * by the shared ledger: the ledger is disabled (`LedgerPersistenceFailed` until it is
///   recovered from its checkpoint) with its accounting unchanged, and no guard advances.
///
/// Either way the session's own and peer slots are retired, since its openings exist.
pub(crate) fn evaluate_per_party_intents_barrier_inner<B: AcceleratorBackend>(
    request: BarrierRequest<'_>,
    quorum_guards: &mut [PolicySignerGuardShare],
    shared_ledger: Option<&mut SharedWindowSpendLedger>,
    accel: &B,
) -> Result<AuthorizedSignReleaseToken, PolicyViolation> {
    let BarrierRequest {
        policy,
        per_party_intents,
        session_id,
        current_timestamp,
        force_authenticated_initiator,
        #[cfg(test)]
        injected_delta_fault,
    } = request;
    let m = quorum_guards.len();
    if m < 2 || per_party_intents.len() != m {
        return Err(PolicyViolation::EmptySignerBarrierSet);
    }

    let mut quorum_ids: Vec<u16> = quorum_guards.iter().map(|g| g.party_id).collect();
    quorum_ids.sort_unstable();
    if quorum_ids.windows(2).any(|w| w[0] == w[1]) {
        return Err(PolicyViolation::DuplicateApproverInQuorum);
    }
    let mut projected_spends = Vec::with_capacity(m);
    for (guard, intent) in quorum_guards.iter().zip(per_party_intents) {
        policy.evaluate(intent)?;
        if current_timestamp < policy.valid_not_before_secs
            || current_timestamp > policy.valid_not_after_secs
            || current_timestamp != intent.timestamp_secs
        {
            return Err(PolicyViolation::TimestampOutsideWindow);
        }
        if guard.poisoned {
            return Err(PolicyViolation::GuardPoisoned);
        }
        if guard.active_phase.is_some() || guard.party_id != guard.enrolled_party_id {
            return Err(PolicyViolation::BarrierBdozMacFailed);
        }
        let mut approvers = intent.approver_parties.clone();
        approvers.sort_unstable();
        if approvers != quorum_ids
            || intent.quorum_ids != quorum_ids
            || intent.session_id != session_id
        {
            return Err(PolicyViolation::IntentBindingMismatch);
        }
        if shared_ledger.is_none() && !guard.has_global_velocity_intersection(policy, &quorum_ids) {
            return Err(PolicyViolation::MissingHardwareGuardian);
        }
        guard.verify_initiator_authentication(policy, intent, force_authenticated_initiator)?;
        let external_floor = if let Some(ledger) = shared_ledger.as_deref() {
            let _ = ledger.check_projected_spend(policy, intent, &session_id)?;
            ledger
                .accumulated_window_spend()
                .max(intent.rolling_window_spent)
        } else {
            intent.rolling_window_spent
        };
        let projected = guard.check_window_nonce_and_projected_spend(
            policy.velocity_window_cap,
            intent,
            &session_id,
            external_floor,
        )?;
        projected_spends.push(projected);
    }
    let policy_digest = policy.canonical_digest();

    // Verify all guards have an available preprocessing slot before advancing any slot latch.
    for g in quorum_guards.iter() {
        let slot = g.next_slot.get();
        if slot >= g.preproc_r.len() {
            return Err(PolicyViolation::BarrierPreprocExhausted);
        }
        for &peer in &quorum_ids {
            if peer != g.party_id {
                g.outgoing_mac(peer, slot)?;
            }
        }
    }

    // Latch one preprocessing slot per guard. From here every exit retires these slots.
    let sessions: Vec<PartyPolicyDeltaCommitMsg> = quorum_guards
        .iter()
        .zip(per_party_intents)
        .map(|(g, intent)| {
            let slot = g.next_slot.get();
            g.next_slot.set(slot + 1);
            PartyPolicyDeltaCommitMsg {
                party_id: g.party_id,
                slot,
                session_id,
                initiator_party: intent.initiator_party,
                window_id: intent.window_id,
                quorum_ids: quorum_ids.clone(),
                policy_digest,
                intent_digest: intent.canonical_digest(),
                commitment: [0; 32],
            }
        })
        .collect();
    let online_res = barrier_rounds_in_process(
        &sessions,
        quorum_guards,
        per_party_intents,
        #[cfg(test)]
        injected_delta_fault,
        accel,
    );

    let peer_slots_of = |party_id: u16| -> Vec<(u16, usize)> {
        sessions
            .iter()
            .filter(|peer| peer.party_id != party_id)
            .map(|peer| (peer.party_id, peer.slot))
            .collect()
    };
    let abort_all = |quorum_guards: &mut [PolicySignerGuardShare]| {
        for (g_abort, own) in quorum_guards.iter_mut().zip(&sessions) {
            g_abort.abort_session_slot(own.slot, &peer_slots_of(g_abort.party_id));
        }
    };
    let (permit, _sigma_commits) = match online_res {
        Ok(rounds) => rounds,
        Err(err) => {
            abort_all(quorum_guards);
            return Err(err);
        }
    };

    // Decide every guard's spend without changing any guard or the shared ledger.
    let global_projected = projected_spends.iter().copied().max().unwrap_or(0);
    let mut prepared = Vec::with_capacity(m);
    let mut refusal = None;
    for (idx, g) in quorum_guards.iter().enumerate() {
        let recorded_spend = if shared_ledger.is_some() {
            projected_spends[idx].max(global_projected)
        } else {
            projected_spends[idx]
        };
        match g.prepare_approved_intent(
            policy.velocity_window_cap,
            recorded_spend,
            per_party_intents[idx].nonce,
            session_id,
        ) {
            Ok(spend) => prepared.push(spend),
            Err(err) => {
                refusal = Some((idx, err));
                break;
            }
        }
    }
    if let Some((idx, err)) = refusal {
        // The guard refused a spend the barrier approved: nothing is released or recorded.
        abort_all(quorum_guards);
        quorum_guards[idx].poison();
        return Err(err);
    }
    // The shared ledger's record is atomic and is the last step that can refuse.
    if let Some(ledger) = shared_ledger
        && let Err(err) =
            ledger.record_approved_intent(global_projected, per_party_intents[0].nonce, session_id)
    {
        ledger.failed = true;
        abort_all(quorum_guards);
        return Err(err);
    }
    // Advance accumulated window spend, burn the intent nonces and session ID, retire slots.
    for ((g, spend), own) in quorum_guards.iter_mut().zip(prepared).zip(&sessions) {
        g.commit_approved_intent(spend);
        g.abort_session_slot(own.slot, &peer_slots_of(g.party_id));
    }

    AuthorizedSignReleaseToken::mint(
        permit,
        session_id,
        policy_digest,
        sessions[0].intent_digest,
        per_party_intents[0].clone(),
    )
}

/// The four barrier rounds for guards that share one process, after the caller latched
/// the slot named in each guard's entry of `sessions` (commitment still unset). Every
/// value is derived by the functions the per-party phase states use (`masked_policy_wire`,
/// `delta_commitment`, `committed_sigma`, `release_committed_sigmas`); only the message
/// passing is elided. Returns the release permit of the sigma opening and the frozen
/// sigma commitments, sorted by party.
pub(crate) fn barrier_rounds_in_process<B: AcceleratorBackend>(
    sessions: &[PartyPolicyDeltaCommitMsg],
    quorum_guards: &[PolicySignerGuardShare],
    per_party_intents: &[TransactionIntent],
    #[cfg(test)] injected_delta_fault: Option<(usize, (u128, u128))>,
    accel: &B,
) -> Result<
    (
        qsag_verified::OpeningReleasePermit,
        Vec<PartyPolicySigmaCommitMsg>,
    ),
    PolicyViolation,
> {
    let m = sessions.len();

    // Round 1: every guard commits to its masked wire.
    let mut own_commits: Vec<PartyPolicyDeltaCommitMsg> = Vec::with_capacity(m);
    let mut folded = Vec::with_capacity(m);
    let mut delta_opens = Vec::with_capacity(m);
    for ((g, intent), session) in quorum_guards.iter().zip(per_party_intents).zip(sessions) {
        let mut own = session.clone();
        let MaskedWire {
            folded: folded_x,
            delta,
            salt,
        } = g.masked_policy_wire(&own, &intent.nonce, accel)?;
        #[cfg(test)]
        let delta = match injected_delta_fault {
            Some((fault_index, fault)) if fault_index == own_commits.len() => {
                [delta[0] ^ fault.0, delta[1] ^ fault.1]
            }
            _ => delta,
        };
        own.commitment = delta_commitment(&own, &salt, &delta);
        delta_opens.push(PartyPolicyDeltaOpenMsg {
            party_id: g.party_id,
            salt_i: salt,
            delta_i: delta,
        });
        folded.push(folded_x);
        own_commits.push(own);
    }

    // Rounds 2 and 3: with the whole delta commitment vector frozen, every guard checks
    // the openings and commits to its sigma share. No sigma is opened before all exist.
    let mut delta_commits = own_commits.clone();
    delta_commits.sort_by_key(|c| c.party_id);
    delta_opens.sort_by_key(|o| o.party_id);
    let mut sigma_commits = Vec::with_capacity(m);
    /// Party, sigma commitment salt and sigma lanes.
    type SigmaOpening = (u16, [u8; 32], [u128; 2]);
    let mut deferred_openings: SecretVec<SigmaOpening> = SecretVec::with_capacity(m);
    for ((g, own), folded_x) in quorum_guards.iter().zip(&own_commits).zip(&folded) {
        let (msg, sigma, salt) = g.committed_sigma(own, folded_x, &delta_commits, &delta_opens)?;
        sigma_commits.push(msg);
        deferred_openings.push_wiping((g.party_id, *salt, *sigma));
    }
    sigma_commits.sort_by_key(|c| c.party_id);

    // Round 4. Guards that evaluated different intents froze different transcripts.
    let (first_delta, first_sigma) = delta_commits
        .first()
        .zip(sigma_commits.first())
        .ok_or(PolicyViolation::EmptySignerBarrierSet)?;
    let mut one_transcript = true;
    for (d, c) in delta_commits.iter().zip(&sigma_commits) {
        one_transcript &= ct_eq_bytes(&d.intent_digest, &first_delta.intent_digest);
        one_transcript &= ct_eq_bytes(&c.transcript_digest, &first_sigma.transcript_digest);
    }
    if !one_transcript {
        return Err(PolicyViolation::BarrierBdozMacFailed);
    }
    let mut sigma_opens: Vec<PartyPolicySigmaOpenMsg> = deferred_openings
        .iter()
        .map(|(party_id, salt, sigma)| PartyPolicySigmaOpenMsg {
            party_id: *party_id,
            sigma_salt_i: *salt,
            sigma_i: *sigma,
        })
        .collect();
    sigma_opens.sort_by_key(|o| o.party_id);
    let permit = release_committed_sigmas(
        &first_delta.session_id,
        first_delta.slot as u64,
        &sigma_commits,
        &sigma_opens,
    )?;
    Ok((permit, sigma_commits))
}

/// Evaluate `policy` across `guards`; peer/session MAC or commitment faults abort ONLY the
/// consumed session slot on each guard without wiping persistent guard keys or spend ledgers.
pub fn evaluate_per_party_intents_barrier<B: AcceleratorBackend>(
    policy: &TransactionPolicy,
    intents: &[TransactionIntent],
    session_id: [u8; 32],
    current_timestamp: u64,
    guards: &mut [PolicySignerGuardShare],
    #[cfg(test)] fault: Option<(usize, (u128, u128))>,
    accel: &B,
) -> Result<AuthorizedSignReleaseToken, PolicyViolation> {
    evaluate_per_party_intents_barrier_inner(
        BarrierRequest {
            policy,
            per_party_intents: intents,
            session_id,
            current_timestamp,
            force_authenticated_initiator: false,
            #[cfg(test)]
            injected_delta_fault: fault,
        },
        guards,
        None,
        accel,
    )
}

/// Evaluate `policy` on `intent` across `quorum_guards` inside a **commit-then-open** pairwise
/// 2-lane BDOZ GF($2^{128}$) MAC barrier (`AcceleratorBackend::bdoz_gf2_128_batch_dot`), returning
/// an unforgeable [`AuthorizedSignReleaseToken`] iff every signer approves and all MACs verify!
pub fn evaluate_policy_committed_barrier<B: AcceleratorBackend>(
    policy: &TransactionPolicy,
    intent: &TransactionIntent,
    session_id: [u8; 32],
    current_timestamp: u64,
    quorum_guards: &mut [PolicySignerGuardShare],
    accel: &B,
) -> Result<AuthorizedSignReleaseToken, PolicyViolation> {
    if quorum_guards.len() < 2 {
        return Err(PolicyViolation::EmptySignerBarrierSet);
    }
    let intents: Vec<TransactionIntent> =
        (0..quorum_guards.len()).map(|_| intent.clone()).collect();
    evaluate_per_party_intents_barrier(
        policy,
        &intents,
        session_id,
        current_timestamp,
        quorum_guards,
        #[cfg(test)]
        None,
        accel,
    )
}

/// Evaluate `policy` on `intent` across `quorum_guards` using a committee-wide
/// [`SharedWindowSpendLedger`] so non-intersecting quorums in guardian-less multi-quorum setups
/// enforce cumulative window velocity caps without quorum-switching bypass.
/// `persist` must atomically persist the shared and participating guard checkpoints, and
/// fence the shared generation in independent monotonic storage before returning success.
/// Hold exclusive ownership of that storage across recovery and this call. Never provision
/// another ledger for an existing policy: recover the checkpoint instead. Persistence errors
/// disable the live ledger and withhold the token; already consumed slots remain spent.
#[allow(clippy::too_many_arguments)]
pub fn evaluate_policy_committed_barrier_with_ledger<B: AcceleratorBackend>(
    policy: &TransactionPolicy,
    intent: &TransactionIntent,
    session_id: [u8; 32],
    current_timestamp: u64,
    quorum_guards: &mut [PolicySignerGuardShare],
    shared_ledger: &mut SharedWindowSpendLedger,
    persist: impl FnOnce(
        &SharedWindowSpendLedger,
        &[PolicySignerGuardShare],
    ) -> Result<(), PolicyViolation>,
    accel: &B,
) -> Result<AuthorizedSignReleaseToken, PolicyViolation> {
    if quorum_guards.len() < 2 {
        return Err(PolicyViolation::EmptySignerBarrierSet);
    }
    let intents: Vec<TransactionIntent> =
        (0..quorum_guards.len()).map(|_| intent.clone()).collect();
    let token = evaluate_per_party_intents_barrier_inner(
        BarrierRequest {
            policy,
            per_party_intents: &intents,
            session_id,
            current_timestamp,
            force_authenticated_initiator: false,
            #[cfg(test)]
            injected_delta_fault: None,
        },
        quorum_guards,
        Some(&mut *shared_ledger),
        accel,
    )?;
    // No token escapes until the common ledger and participating guard snapshots are durable.
    // Keep the handle disabled across errors and unwinding; recovery requires its checkpoint.
    shared_ledger.failed = true;
    persist(shared_ledger, quorum_guards)?;
    shared_ledger.failed = false;
    Ok(token)
}

/// Evaluate `policy` on `intent` across `quorum_guards` while mandating pairwise cryptographic
/// authentication of `intent.initiator_party` (`InitiatorPeerMac`) from the initiator guard share.
pub fn evaluate_policy_committed_barrier_authenticated<B: AcceleratorBackend>(
    policy: &TransactionPolicy,
    intent: &TransactionIntent,
    session_id: [u8; 32],
    current_timestamp: u64,
    quorum_guards: &mut [PolicySignerGuardShare],
    accel: &B,
) -> Result<AuthorizedSignReleaseToken, PolicyViolation> {
    if quorum_guards.len() < 2 {
        return Err(PolicyViolation::EmptySignerBarrierSet);
    }
    let intents: Vec<TransactionIntent> =
        (0..quorum_guards.len()).map(|_| intent.clone()).collect();
    evaluate_per_party_intents_barrier_inner(
        BarrierRequest {
            policy,
            per_party_intents: &intents,
            session_id,
            current_timestamp,
            force_authenticated_initiator: true,
            #[cfg(test)]
            injected_delta_fault: None,
        },
        quorum_guards,
        None,
        accel,
    )
}

/// Adapter for a mutually authenticated, malicious-secure, bidirectional 1-of-2 OT channel.
/// Each call sends one pair per choice and receives exactly the chosen peer values.
/// Implementations must bind both authenticated endpoint IDs, the domain and vector length,
/// reject replay, and hide sender alternatives and receiver choices. An ordinary channel
/// cannot implement this contract. Base OT and its security parameters belong to the provider.
/// One call covers both directions with `peer`. The trait does not say in which order: each
/// implementation fixes one, and both endpoints must agree on it or a blocking transport
/// deadlocks.
pub trait PolicyAuthenticatedOt {
    fn exchange(
        &mut self,
        local_party: u16,
        peer: u16,
        domain: [u8; 32],
        alternatives: &[[u128; 2]],
        choices: &[bool],
    ) -> Result<Vec<u128>, PolicyViolation>;
}

/// Production adapter using the interactive KOS check and committed Ring-LWE base OT.
/// The two directions run one after the other, never concurrently: for every chunk of at
/// most 65,536 choices the party with the lower ID sends its pairs and then receives, and
/// the party with the higher ID receives and then sends. The opposite orders at the two
/// endpoints are what keeps blocking sends from crossing on a synchronous transport.
impl<W: crate::ot::AuthenticatedOtWire> PolicyAuthenticatedOt
    for crate::ot::CommittedCorrelatedOt<W>
{
    fn exchange(
        &mut self,
        local_party: u16,
        peer: u16,
        domain: [u8; 32],
        alternatives: &[[u128; 2]],
        choices: &[bool],
    ) -> Result<Vec<u128>, PolicyViolation> {
        if local_party != self.party_id() || alternatives.len() != choices.len() {
            return Err(PolicyViolation::IntentBindingMismatch);
        }
        let failed = |_| PolicyViolation::BarrierBdozMacFailed;
        let mut result = SecretVec::with_capacity(choices.len());
        for (index, (pairs, bits)) in alternatives
            .chunks(65_536)
            .zip(choices.chunks(65_536))
            .enumerate()
        {
            let context = cshake256_framed_32(
                b"QSAG.POLICY.OT.CHUNK.V1",
                &[
                    &domain,
                    &(index as u64).to_be_bytes(),
                    &(choices.len() as u64).to_be_bytes(),
                ],
            );
            let values = if local_party < peer {
                self.send_values(peer, context, pairs).map_err(failed)?;
                self.receive_values(peer, context, bits).map_err(failed)?
            } else {
                let values = self.receive_values(peer, context, bits).map_err(failed)?;
                self.send_values(peer, context, pairs).map_err(failed)?;
                values
            };
            let values = SecretVec::new(values);
            result.extend_wiping(&values);
        }
        Ok(result.into_inner())
    }
}
