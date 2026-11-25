#[test]
fn shared_verified_guard_survives_rotation_and_checkpoint() {
    let (policy, _) = phase_fixture(&[1, 2]);
    let mut ledger = SharedWindowSpendLedger::new(&policy, 0)
        .with_window_authority([42; 32], [43; 32])
        .unwrap();
    ledger.record_approved_intent(7, [1; 32], [2; 32]).unwrap();
    ledger.record_approved_intent(11, [3; 32], [4; 32]).unwrap();
    assert_eq!(ledger.verified_velocity.as_ref().unwrap().last_nonce(), 2);
    let auth = WindowAdvanceAuthorization::new(&[43; 32], &[42; 32], 0, 1);
    ledger.advance_velocity_window(&auth).unwrap();
    let guard = ledger.verified_velocity.as_ref().unwrap();
    assert_eq!(guard.window_id(), 1);
    assert_eq!(guard.spent_units(), 0);
    assert_eq!(guard.last_nonce(), 2);
    ledger.record_approved_intent(5, [5; 32], [6; 32]).unwrap();
    assert_eq!(ledger.verified_velocity.as_ref().unwrap().last_nonce(), 4);
    let bytes = ledger.export_durable_checkpoint(&[7; 32]);
    let mut restored = SharedWindowSpendLedger::new(&policy, 0)
        .with_window_authority([42; 32], [43; 32])
        .unwrap();
    restored
        .restore_from_durable_checkpoint(&bytes, &[7; 32], 4)
        .unwrap();
    restored
        .record_approved_intent(9, [8; 32], [9; 32])
        .unwrap();
    let guard = restored.verified_velocity.as_ref().unwrap();
    assert_eq!(guard.spent_units(), 9);
    assert_eq!(guard.last_nonce(), 5);
    assert!(!restored.is_nonce_burned(&[1; 32]));
    assert!(!restored.is_session_burned(&[2; 32]));
}

pub(super) fn raw_test_guards(entropy: [u8; 32], ids: &[u16]) -> Vec<PolicySignerGuardShare> {
    let mut guards: Vec<_> = super::trusted_dealer_setup_for_testing(entropy, ids)
        .into_iter()
        .map(|g| g.with_window_authority([42; 32], [43; 32]).unwrap())
        .collect();
    for guard in &mut guards {
        guard.set_require_authenticated_initiator(false);
    }
    guards
}
#[test]
fn window_authority_is_required_and_bound_to_checkpoint() {
    let mut bare = super::trusted_dealer_setup_for_testing([9; 32], &[1, 2]).remove(0);
    let auth = WindowAdvanceAuthorization::new(&[43; 32], &[42; 32], 0, 1);
    assert!(bare.advance_velocity_window(&auth).is_err());
    let guard = bare.with_window_authority([42; 32], [43; 32]).unwrap();
    let snapshot = guard.export_durable_checkpoint(&[7; 32], 1);
    let mut other = super::trusted_dealer_setup_for_testing([9; 32], &[1, 2])
        .remove(0)
        .with_window_authority([41; 32], [43; 32])
        .unwrap();
    assert!(
        other
            .restore_from_durable_checkpoint(&snapshot, &[7; 32], 1)
            .is_err()
    );
    assert!(guard.with_window_authority([41; 32], [43; 32]).is_err());
}

#[test]
fn window_authorization_rejects_forgery_replay_and_wrong_policy() {
    let mut guards = raw_test_guards([9; 32], &[1, 2]);
    let guard = &mut guards[0];
    guard.accumulated_window_spend = 99;
    for auth in [
        WindowAdvanceAuthorization::new(&[44; 32], &[42; 32], 0, 1),
        WindowAdvanceAuthorization::new(&[43; 32], &[41; 32], 0, 1),
        WindowAdvanceAuthorization::new(&[43; 32], &[42; 32], 1, 2),
        WindowAdvanceAuthorization::new(&[43; 32], &[42; 32], 0, 0),
    ] {
        assert!(guard.advance_velocity_window(&auth).is_err());
        assert_eq!(guard.current_window_id(), 0);
        assert_eq!(guard.accumulated_window_spend(), 99);
    }
    let valid = WindowAdvanceAuthorization::new(&[43; 32], &[42; 32], 0, 1);
    guard.advance_velocity_window(&valid).unwrap();
    assert_eq!(guard.accumulated_window_spend(), 0);
    assert!(guard.advance_velocity_window(&valid).is_err());
}

#[test]
fn signer_verified_guard_survives_approvals_rotation_and_checkpoint() {
    use PolicyViolation::VelocityCapOverflowOrExceeded as OverCap;
    let mut guards = raw_test_guards([9; 32], &[1, 2]);
    let guard = &mut guards[0];
    assert!(guard.verified_velocity.is_none());
    guard
        .record_approved_intent(50, 7, [1; 32], [2; 32])
        .unwrap();
    guard
        .record_approved_intent(50, 30, [3; 32], [4; 32])
        .unwrap();
    let v = guard.verified_velocity.as_ref().unwrap();
    assert_eq!(
        (v.cap_units(), v.spent_units(), v.last_nonce()),
        (50, 30, 2)
    );
    // Over the pinned cap: refused, nothing recorded or burned.
    assert_eq!(
        guard.record_approved_intent(50, 51, [5; 32], [6; 32]),
        Err(OverCap)
    );
    assert_eq!(guard.accumulated_window_spend(), 30);
    assert!(!guard.is_nonce_burned(&[5; 32]));
    // A cap below what is already spent cannot be pinned; the old guard stays.
    assert_eq!(
        guard.record_approved_intent(20, 30, [5; 32], [6; 32]),
        Err(OverCap)
    );
    assert_eq!(guard.verified_velocity.as_ref().unwrap().cap_units(), 50);
    // Rotation keeps the guard and its request nonce and resets the spend.
    guard
        .advance_velocity_window(&WindowAdvanceAuthorization::new(&[43; 32], &[42; 32], 0, 1))
        .unwrap();
    let v = guard.verified_velocity.as_ref().unwrap();
    assert_eq!((v.window_id(), v.spent_units(), v.last_nonce()), (1, 0, 2));
    guard
        .record_approved_intent(50, 9, [7; 32], [8; 32])
        .unwrap();
    // A freshly provisioned guard recovers the verified state from the checkpoint.
    let bytes = guard.export_durable_checkpoint(&[7; 32], 5);
    let mut fresh = raw_test_guards([9; 32], &[1, 2]);
    fresh[0]
        .restore_from_durable_checkpoint(&bytes, &[7; 32], 5)
        .unwrap();
    let v = fresh[0].verified_velocity.as_ref().unwrap();
    assert_eq!(
        (
            v.window_id(),
            v.cap_units(),
            v.spent_units(),
            v.last_nonce()
        ),
        (1, 50, 9, 3)
    );
    assert_eq!(
        fresh[0].record_approved_intent(50, 51, [9; 32], [10; 32]),
        Err(OverCap)
    );
    fresh[0]
        .record_approved_intent(50, 50, [9; 32], [10; 32])
        .unwrap();
    assert_eq!(fresh[0].verified_velocity.as_ref().unwrap().last_nonce(), 4);
}

#[test]
fn provisioned_guards_require_initiator_authentication_and_cannot_be_downgraded() {
    let accel = CpuReferenceBackend::new();
    let (policy, intent) = phase_fixture(&[1, 4]);
    let provision = || -> Vec<PolicySignerGuardShare> {
        super::trusted_dealer_setup_for_testing([8; 32], &[1, 4])
            .into_iter()
            .map(|g| g.with_window_authority([42; 32], [43; 32]).unwrap())
            .collect()
    };
    let mut guards = provision();
    assert!(guards.iter().all(|g| g.require_authenticated_initiator));

    // The intent carries no initiator MAC. The entry points that do not force
    // authentication refuse it all the same.
    assert_eq!(
        evaluate_policy_committed_barrier(
            &policy,
            &intent,
            intent.session_id,
            intent.timestamp_secs,
            &mut guards,
            &accel,
        )
        .unwrap_err(),
        PolicyViolation::UnauthenticatedInitiator
    );
    assert_eq!(
        guards[0]
            .round1_commit_intent(
                &policy,
                &intent,
                intent.session_id,
                intent.timestamp_secs,
                intent.rolling_window_spent,
            )
            .err(),
        Some(PolicyViolation::UnauthenticatedInitiator)
    );

    // A checkpoint of the same guard with the requirement waived is a rollback; one
    // with the requirement set restores.
    let waived = raw_test_guards([8; 32], &[1, 4]);
    assert!(!waived[0].require_authenticated_initiator);
    let downgrade = waived[0].export_durable_checkpoint(&[7; 32], 1);
    assert!(matches!(
        guards[0].restore_from_durable_checkpoint(&downgrade, &[7; 32], 1),
        Err(PolicyGuardError::Rollback)
    ));
    assert!(guards[0].require_authenticated_initiator);
    let twin = provision();
    let same = twin[0].export_durable_checkpoint(&[7; 32], 1);
    guards[0]
        .restore_from_durable_checkpoint(&same, &[7; 32], 1)
        .unwrap();
    assert!(guards[0].require_authenticated_initiator);
}

#[test]
fn quorum_tier_order_is_validated_before_any_tier_is_selected() {
    let (mut policy, intent) = phase_fixture(&[1, 4]);
    let tier = |max_amount_units, min_approvers, require_hardware_guardian| QuorumTierRule {
        max_amount_units,
        min_approvers,
        require_hardware_guardian,
    };
    // The intent (amount 10, approvers {1, 4}, guardian 4) satisfies the first tier of
    // every list below, so each refusal comes from the order check alone.
    let mut verdict = |tiers: Vec<QuorumTierRule>| {
        policy.quorum_tiers = tiers;
        (policy.validate_quorum_tiers(), policy.evaluate(&intent))
    };
    let refused = (
        Err(PolicyViolation::InvalidQuorumTierOrder),
        Err(PolicyViolation::InvalidQuorumTierOrder),
    );

    assert_eq!(
        verdict(vec![
            tier(50, 2, false),
            tier(100, 2, false),
            tier(1_000, 3, true)
        ]),
        (Ok(()), Ok(()))
    );
    // A later tier whose bound an earlier tier already covers is unreachable.
    assert_eq!(
        verdict(vec![tier(100, 2, false), tier(100, 3, true)]),
        refused
    );
    assert_eq!(
        verdict(vec![tier(100, 2, false), tier(50, 3, true)]),
        refused
    );
    assert_eq!(
        verdict(vec![
            tier(50, 2, false),
            tier(1_000, 2, false),
            tier(100, 3, true)
        ]),
        refused
    );
    // A larger amount selecting a weaker quorum than a smaller one.
    assert_eq!(
        verdict(vec![tier(50, 2, false), tier(100, 1, false)]),
        refused
    );
    assert_eq!(
        verdict(vec![tier(50, 2, true), tier(100, 2, false)]),
        refused
    );
    assert_eq!(
        verdict(vec![
            tier(50, 2, true),
            tier(100, 3, true),
            tier(1_000, 3, false)
        ]),
        refused
    );
    // No tier: in order, and no amount is covered.
    assert_eq!(
        verdict(Vec::new()),
        (Ok(()), Err(PolicyViolation::NoMatchingQuorumTier))
    );
}

#[test]
fn in_process_barrier_and_party_phases_derive_identical_rounds() {
    let (policy, intent) = phase_fixture(&[1, 4]);
    // The dealer is deterministic: both guard sets hold the same secrets.
    let mut phase_guards = raw_test_guards([0x5A; 32], &[1, 4]);
    let batch_guards = raw_test_guards([0x5A; 32], &[1, 4]);

    let (states, delta_commits) = start_phases(&mut phase_guards, &policy, &intent);
    let (states, delta_opens): (Vec<_>, Vec<_>) = states
        .into_iter()
        .zip(&mut phase_guards)
        .map(|(s, g)| s.round2_open_delta(g, &delta_commits).unwrap())
        .unzip();
    let (_states, sigma_commits): (Vec<_>, Vec<_>) = states
        .into_iter()
        .zip(&mut phase_guards)
        .map(|(s, g)| s.round3_commit_sigma(g, &delta_opens).unwrap())
        .unzip();

    // The same session on the in-process path: same slots, commitments not yet set.
    let sessions: Vec<PartyPolicyDeltaCommitMsg> = delta_commits
        .iter()
        .map(|c| PartyPolicyDeltaCommitMsg {
            commitment: [0; 32],
            ..c.clone()
        })
        .collect();
    for g in &batch_guards {
        g.next_slot.set(1);
    }
    let (_permit, batch_sigma_commits) = barrier_rounds_in_process(
        &sessions,
        &batch_guards,
        &[intent.clone(), intent.clone()],
        None,
        &CpuReferenceBackend::new(),
    )
    .unwrap();
    // A sigma commitment covers the transcript digest (every delta commitment, salt
    // and opening), the sigma share and its salt.
    assert_eq!(batch_sigma_commits, sigma_commits);
}
#[test]
fn replay_capacity_exceeds_legacy_limit_and_is_durable() {
    let mut guards = raw_test_guards([9; 32], &[1, 2]);
    let guard = &mut guards[0];
    guard.set_replay_capacity(600).unwrap();
    for i in 0u64..600 {
        let mut nonce = [0; 32];
        nonce[..8].copy_from_slice(&i.to_be_bytes());
        guard
            .record_approved_intent(u128::MAX, i as u128, nonce, nonce)
            .unwrap();
    }
    let snapshot = guard.export_durable_checkpoint(&[7; 32], 600);
    let mut restored = raw_test_guards([9; 32], &[1, 2]);
    restored[0]
        .restore_from_durable_checkpoint(&snapshot, &[7; 32], 600)
        .unwrap();
    assert_eq!(restored[0].replay_capacity, 600);
    assert_eq!(
        restored[0].export_durable_checkpoint(&[7; 32], 600),
        snapshot
    );
    assert_eq!(
        restored[0].record_approved_intent(u128::MAX, 601, [255; 32], [255; 32]),
        Err(PolicyViolation::ReplayWindowExhausted)
    );
    assert!(restored[0].set_replay_capacity(599).is_err());
    restored[0].set_replay_capacity(601).unwrap();
    restored[0]
        .record_approved_intent(u128::MAX, 601, [255; 32], [255; 32])
        .unwrap();
}

#[test]
fn bounded_replay_window_retains_random_nonces_until_authenticated_rotation() {
    let mut guards = raw_test_guards([9; 32], &[1, 2]);
    let guard = &mut guards[0];
    guard.set_replay_capacity(256).unwrap();
    let nonces: Vec<_> = (0u32..256)
        .map(|i| cshake256_framed_32(b"nonce test", &[&i.to_be_bytes()]))
        .collect();
    for (i, nonce) in nonces.iter().enumerate() {
        assert!(!guard.is_nonce_burned(nonce));
        guard
            .record_approved_intent(u128::MAX, i as u128, *nonce, *nonce)
            .unwrap();
    }
    for nonce in &nonces {
        assert!(guard.is_nonce_burned(nonce));
    }
    assert_eq!(
        guard.record_approved_intent(u128::MAX, 256, [0; 32], [0; 32]),
        Err(PolicyViolation::ReplayWindowExhausted)
    );
    let checkpoint = guard.export_durable_checkpoint(&[7; 32], 256);
    guard
        .restore_from_durable_checkpoint(&checkpoint, &[7; 32], 256)
        .unwrap();
    guard
        .advance_velocity_window(&WindowAdvanceAuthorization::new(&[43; 32], &[42; 32], 0, 1))
        .unwrap();
    assert!(!guard.is_nonce_burned(&[0; 32]));
    guard
        .record_approved_intent(u128::MAX, 1, [0; 32], [0; 32])
        .unwrap();
}

use alloc::format;
use alloc::vec;
use qsag_accel::CpuReferenceBackend;
use qsag_addr::KeyIdentityKind;

use super::*;

pub(super) fn phase_fixture(ids: &[u16]) -> (TransactionPolicy, TransactionIntent) {
    let recipient = QsagAddress::from_pubkey_cshake256(
        "qsp",
        WitnessSuiteTag::MlDsa65,
        KeyIdentityKind::SingleOrThreshold,
        b"phase-recipient",
    )
    .unwrap();
    let policy = TransactionPolicy {
        chain_id: 1,
        pinned_suite: WitnessSuiteTag::MlDsa65,
        recipient_allowlist: vec![recipient.commitment_256],
        max_single_tx_amount: 100,
        velocity_window_cap: 200,
        valid_not_before_secs: 1,
        valid_not_after_secs: 100,
        forbid_initiator_self_approval: true,
        hardware_guardian_party: Some(*ids.last().unwrap()),
        quorum_tiers: vec![QuorumTierRule {
            max_amount_units: 100,
            min_approvers: 2,
            require_hardware_guardian: true,
        }],
    };
    let intent = TransactionIntent {
        chain_id: 1,
        suite: WitnessSuiteTag::MlDsa65,
        recipient,
        amount_units: 10,
        rolling_window_spent: 20,
        window_id: 0,
        nonce: [7; 32],
        timestamp_secs: 50,
        initiator_party: 0,
        initiator_macs: Vec::new(),
        approver_parties: ids.to_vec(),
        payload_digest: [1; 32],
        guard_authority_pk: [0; 32],
        rolling_window_accumulator: [0; 32],
        signing_key_id: [2; 32],
        policy_revision: 1,
        message_digest: cshake256_framed_32(b"QSAG.POLICY.MSG.V1", &[b"message"]),
        signing_context_digest: cshake256_framed_32(b"QSAG.POLICY.CTX.V1", &[b"context"]),
        session_id: [3; 32],
        quorum_ids: ids.to_vec(),
    };
    (policy, intent)
}

fn start_phases(
    guards: &mut [PolicySignerGuardShare],
    policy: &TransactionPolicy,
    intent: &TransactionIntent,
) -> (Vec<PartyPolicyRound1State>, Vec<PartyPolicyDeltaCommitMsg>) {
    guards
        .iter_mut()
        .map(|g| {
            g.round1_commit_intent(
                policy,
                intent,
                intent.session_id,
                intent.timestamp_secs,
                intent.rolling_window_spent,
            )
            .unwrap()
        })
        .unzip()
}

fn delta_phases(
    guards: &mut [PolicySignerGuardShare],
    policy: &TransactionPolicy,
    intent: &TransactionIntent,
) -> (Vec<PartyPolicyRound2State>, Vec<PartyPolicyDeltaOpenMsg>) {
    let (states, commits) = start_phases(guards, policy, intent);
    states
        .into_iter()
        .zip(guards)
        .map(|(s, g)| s.round2_open_delta_and_commit_sigma(g, &commits).unwrap())
        .unzip()
}

fn sigma_phases(
    guards: &mut [PolicySignerGuardShare],
    policy: &TransactionPolicy,
    intent: &TransactionIntent,
) -> (Vec<PartyPolicyRound3State>, Vec<PartyPolicySigmaCommitMsg>) {
    let (states, opens) = delta_phases(guards, policy, intent);
    states
        .into_iter()
        .zip(guards)
        .map(|(s, g)| s.round3_commit_sigma(g, &opens).unwrap())
        .unzip()
}

fn assert_erased(g: &PolicySignerGuardShare) {
    assert!(g.poisoned);
    assert_eq!(g.bdoz_alpha_share, [0; 2]);
    assert_eq!(g.local_salt_seed, [0; 32]);
    assert!(g.preproc_r.iter().all(|r| *r == [0; 2]));
    assert!(g.pairwise_zero_seeds.iter().all(|(_, s)| *s == [0; 32]));
    assert!(
        g.preproc_outgoing_macs
            .iter()
            .chain(&g.preproc_incoming_keys)
            .all(|(_, values)| values.iter().all(|v| *v == [0; 2]))
    );
}

fn assert_slot_aborted_not_bricked(g: &PolicySignerGuardShare, slot: usize) {
    assert!(!g.poisoned);
    assert_eq!(g.active_phase, None);
    assert_ne!(g.bdoz_alpha_share, [0; 2]);
    assert_ne!(g.local_salt_seed, [0; 32]);
    assert_eq!(g.preproc_r[slot], [0; 2]);
    assert!(
        g.preproc_outgoing_macs
            .iter()
            .all(|(_, values)| values[slot] == [0; 2])
    );
    if slot + 1 < BDOZ_PREPROC_SLOTS {
        assert_ne!(g.preproc_r[slot + 1], [0; 2]);
    }
}

fn run_phases(
    guards: &mut [PolicySignerGuardShare],
    policy: &TransactionPolicy,
    intent: &TransactionIntent,
) {
    let (states, mut commits) = sigma_phases(guards, policy, intent);
    // Arrival ordering has no effect on canonical transcript ordering.
    commits.reverse();
    let (states, mut opens): (Vec<_>, Vec<_>) = states
        .into_iter()
        .zip(guards.iter_mut())
        .map(|(s, g)| s.round4_open_sigma(g, &commits).unwrap())
        .unzip();
    opens.reverse();
    for (s, g) in states.into_iter().zip(guards) {
        let token = s.finalize(g, &opens).unwrap();
        assert_eq!(token.intent_digest(), &intent.canonical_digest());
        assert!(token.matches_signing(
            &intent.signing_key_id,
            &intent.to_canonical_signing_bytes(&policy.canonical_digest()),
            b"context",
            &intent.quorum_ids
        ));
        assert_eq!(g.active_phase, None);
    }
}

#[test]
fn party_phases_release_once_and_advance_slots() {
    let (policy, intent) = phase_fixture(&[1, 2, 4]);
    let mut guards = raw_test_guards([11; 32], &[1, 2, 4]);
    run_phases(&mut guards, &policy, &intent);
    assert!(guards.iter().all(|g| g.accumulated_window_spend() == 30));
    let mut next = intent.clone();
    next.session_id = [4; 32];
    next.nonce = [8; 32];
    next.rolling_window_spent = 30;
    run_phases(&mut guards, &policy, &next);
    assert!(guards.iter().all(|g| g.next_slot.get() == 2));
    assert!(guards.iter().all(|g| g.accumulated_window_spend() == 40));
}

#[test]
fn party_phases_reject_clock_spend_and_guardian_spoofing() {
    let (policy, intent) = phase_fixture(&[1, 4]);
    let mut guards = raw_test_guards([12; 32], &[1, 4]);
    assert!(matches!(
        guards[0].round1_commit_intent(&policy, &intent, intent.session_id, 51, 20),
        Err(PolicyViolation::TimestampOutsideWindow)
    ));
    assert!(matches!(
        guards[0].round1_commit_intent(&policy, &intent, intent.session_id, 50, 19),
        Err(PolicyViolation::VelocityCapOverflowOrExceeded)
    ));
    assert_eq!(guards[0].next_slot.get(), 0);
    guards[0].party_id = 4;
    assert!(
        guards[0]
            .round1_commit_intent(&policy, &intent, intent.session_id, 50, 20)
            .is_err()
    );
    assert_erased(&guards[0]);
    let mut guards = raw_test_guards([12; 32], &[1, 4]);
    let (mut states, mut commits) = start_phases(&mut guards, &policy, &intent);
    let honest_commits = commits.clone();
    commits[1] = commits[0].clone();
    commits[1].party_id = 4;
    let (state, _) = states
        .remove(0)
        .round2_open_delta(&mut guards[0], &commits)
        .unwrap();
    let (_, guardian_open) = states
        .remove(0)
        .round2_open_delta(&mut guards[1], &honest_commits)
        .unwrap();
    let own_open = PartyPolicyDeltaOpenMsg {
        party_id: 1,
        salt_i: state.context.salt,
        delta_i: state.context.delta,
    };
    assert!(
        state
            .round3_commit_sigma(&mut guards[0], &[own_open, guardian_open])
            .is_err()
    );
    assert_slot_aborted_not_bricked(&guards[0], 0);
}

#[test]
fn party_phases_reject_even_quorum_conflicting_intents() {
    let (policy, intent) = phase_fixture(&[1, 2, 3, 4]);
    let mut guards = raw_test_guards([13; 32], &[1, 2, 3, 4]);
    let mut states = Vec::new();
    let mut commits = Vec::new();
    for (i, g) in guards.iter_mut().enumerate() {
        let mut local = intent.clone();
        if i % 2 == 1 {
            local.amount_units += 1;
        }
        let (s, c) = g
            .round1_commit_intent(&policy, &local, local.session_id, 50, 20)
            .unwrap();
        states.push(s);
        commits.push(c);
    }
    for (s, g) in states.into_iter().zip(&mut guards) {
        assert!(s.round2_open_delta(g, &commits).is_err());
        assert_slot_aborted_not_bricked(g, 0);
    }
}

#[test]
fn party_phases_reject_overlap_wrong_guard_and_equivocation() {
    let (policy, intent) = phase_fixture(&[1, 4]);
    let mut guards = raw_test_guards([14; 32], &[1, 4]);
    let (mut states, commits) = start_phases(&mut guards, &policy, &intent);
    assert!(
        states
            .remove(0)
            .round2_open_delta(&mut guards[1], &commits)
            .is_err()
    );
    assert_erased(&guards[1]);
    assert!(
        guards[0]
            .round1_commit_intent(&policy, &intent, intent.session_id, 50, 20)
            .is_err()
    );
    assert_erased(&guards[0]);
    let mut guards = raw_test_guards([14; 32], &[1, 4]);
    let (mut states, mut commits) = start_phases(&mut guards, &policy, &intent);
    commits[0].commitment[0] ^= 1;
    assert!(
        states
            .remove(0)
            .round2_open_delta(&mut guards[0], &commits)
            .is_err()
    );
    assert_slot_aborted_not_bricked(&guards[0], 0);
    let mut guards = raw_test_guards([14; 32], &[1, 4]);
    let (mut states, mut opens) = delta_phases(&mut guards, &policy, &intent);
    opens[1].delta_i[0] ^= 1;
    assert!(
        states
            .remove(0)
            .round3_commit_sigma(&mut guards[0], &opens)
            .is_err()
    );
    assert_slot_aborted_not_bricked(&guards[0], 0);
    let mut guards = raw_test_guards([14; 32], &[1, 4]);
    let (mut states, mut commits) = start_phases(&mut guards, &policy, &intent);
    commits.pop();
    assert!(
        states
            .remove(0)
            .round2_open_delta(&mut guards[0], &commits)
            .is_err()
    );
    assert_slot_aborted_not_bricked(&guards[0], 0);
}

#[test]
fn abandoned_session_is_aborted_in_any_phase_without_bricking_the_guard() {
    let (policy, intent) = phase_fixture(&[1, 2, 4]);
    let mut guards = raw_test_guards([15; 32], &[1, 2, 4]);
    let mut session = 0u8;
    let mut next_intent = |spent: u128| {
        session += 1;
        let mut next = intent.clone();
        next.session_id = [0x40 + session; 32];
        next.nonce = [0x80 + session; 32];
        next.rolling_window_spent = spent;
        next
    };
    // Phase 1: a peer never answers the commitments.
    let attempt = next_intent(20);
    let (states, _) = start_phases(&mut guards, &policy, &attempt);
    for (state, guard) in states.into_iter().zip(&mut guards) {
        state.abort(guard).unwrap();
        assert_slot_aborted_not_bricked(guard, 0);
    }
    // Phase 2: deltas are open; the peer slots that were named are retired with ours.
    let attempt = next_intent(20);
    let (states, _) = delta_phases(&mut guards, &policy, &attempt);
    for (state, guard) in states.into_iter().zip(&mut guards) {
        state.abort(guard).unwrap();
        assert_slot_aborted_not_bricked(guard, 1);
    }
    for guard in &guards {
        for (peer, _) in &guard.pairwise_zero_seeds {
            assert!(!guard.is_peer_slot_consumed(*peer, 0));
            assert!(guard.is_peer_slot_consumed(*peer, 1));
            assert!(guard.incoming_key(*peer, 1).is_err());
        }
    }
    // Phase 3 and phase 4: sigma is committed, then opened.
    let attempt = next_intent(20);
    let (states, commits) = sigma_phases(&mut guards, &policy, &attempt);
    let (finals, _): (Vec<_>, Vec<_>) = states
        .into_iter()
        .zip(guards.iter_mut())
        .map(|(s, g)| s.round4_open_sigma(g, &commits).unwrap())
        .unzip();
    for (state, guard) in finals.into_iter().zip(&mut guards) {
        state.abort(guard).unwrap();
        assert_slot_aborted_not_bricked(guard, 2);
    }
    let attempt = next_intent(20);
    let (states, _) = sigma_phases(&mut guards, &policy, &attempt);
    for (state, guard) in states.into_iter().zip(&mut guards) {
        state.abort(guard).unwrap();
        assert_slot_aborted_not_bricked(guard, 3);
    }
    // Nothing was spent or burned, and the guards complete a later session.
    assert!(guards.iter().all(|g| g.accumulated_window_spend() == 0));
    assert!(guards.iter().all(|g| !g.is_session_burned(&[0x41; 32])));
    run_phases(&mut guards, &policy, &next_intent(20));
    assert!(guards.iter().all(|g| g.next_slot.get() == 5));
    assert!(guards.iter().all(|g| g.accumulated_window_spend() == 30));
    // A state handed to the wrong guard still poisons that guard.
    let attempt = next_intent(30);
    let (mut states, _) = start_phases(&mut guards, &policy, &attempt);
    assert!(states.remove(0).abort(&mut guards[1]).is_err());
    assert_erased(&guards[1]);
}

#[test]
fn slot_capacity_boundaries_fail_closed_and_capacity_is_transcript_bound() {
    for capacity in [1usize, 63, 64, 65, 255, 256, 257] {
        let mut guards = raw_test_guards([0x71; 32], &[1, 2]);
        let guard = &mut guards[0];
        // Bookkeeping only: the preprocessing values themselves are not exercised.
        guard.preproc_r.resize(capacity, [1; 2]);
        for (_, words) in &mut guard.consumed_peer_slots {
            *words = vec![0; capacity.div_ceil(64)];
        }
        for (_, values) in guard
            .preproc_outgoing_macs
            .iter_mut()
            .chain(&mut guard.preproc_incoming_keys)
        {
            values.resize(capacity, [1; 2]);
        }
        let last = capacity - 1;
        assert!(!guard.is_peer_slot_consumed(2, last));
        assert!(guard.incoming_key(2, last).is_ok());
        for beyond in [
            capacity,
            capacity + 1,
            capacity.next_multiple_of(64),
            usize::MAX,
        ] {
            assert!(guard.is_peer_slot_consumed(2, beyond));
            assert_eq!(
                guard.incoming_key(2, beyond),
                Err(PolicyViolation::BarrierPreprocExhausted)
            );
            assert_eq!(
                guard.outgoing_mac(2, beyond),
                Err(PolicyViolation::BarrierPreprocExhausted)
            );
            // Retiring an out-of-range slot neither panics nor marks a real one.
            guard.retire_peer_slot(2, beyond);
        }
        assert!(
            guard
                .consumed_peer_slots
                .iter()
                .all(|(_, words)| words.iter().all(|w| *w == 0))
        );
        guard.retire_peer_slot(2, last);
        assert!(guard.is_peer_slot_consumed(2, last));
        assert_eq!(
            guard.incoming_key(2, last),
            Err(PolicyViolation::IntentBindingMismatch)
        );
        let marked: u32 = guard.consumed_peer_slots[0]
            .1
            .iter()
            .map(|w| w.count_ones())
            .sum();
        assert_eq!(marked, 1);
        if last > 0 {
            assert!(!guard.is_peer_slot_consumed(2, last - 1));
        }
        // An unknown peer has no usable slot at all.
        assert!(guard.is_peer_slot_consumed(9, 0));
        // The local cursor stops exactly at capacity.
        guard.next_slot.set(capacity);
        let (policy, intent) = phase_fixture(&[1, 2]);
        assert_eq!(
            guard
                .round1_commit_intent(&policy, &intent, intent.session_id, 50, 20)
                .err(),
            Some(PolicyViolation::BarrierPreprocExhausted)
        );
        assert!(!guard.is_poisoned());
    }
    for capacity in [0, MAX_POLICY_CAPACITY + 1] {
        assert_eq!(
            PolicyGuardDkgRound1::new_with_capacity(1, &[1, 2], [9; 32], [1; 32], capacity).err(),
            Some(PolicyViolation::BarrierPreprocExhausted)
        );
    }
    // Two parties that disagree on the pool size cannot complete the ceremony.
    let (small, small_commits) =
        PolicyGuardDkgRound1::new_with_capacity(1, &[1, 2], [9; 32], [1; 32], 64).unwrap();
    let (_, large_commits) =
        PolicyGuardDkgRound1::new_with_capacity(2, &[1, 2], [9; 32], [2; 32], 65).unwrap();
    assert_ne!(small_commits[0].setup_digest, large_commits[0].setup_digest);
    assert_eq!(
        small.round2_open_seeds(&large_commits).err(),
        Some(PolicyViolation::IntentBindingMismatch)
    );
}

#[test]
fn party_phases_reject_stale_openings_and_sigma_commit_equivocation() {
    let (policy, intent) = phase_fixture(&[1, 4]);
    let mut previous = raw_test_guards([19; 32], &[1, 4]);
    let (_, stale_opens) = delta_phases(&mut previous, &policy, &intent);
    let mut next_intent = intent.clone();
    next_intent.session_id = [22; 32];
    next_intent.nonce = [23; 32];
    let mut guards = raw_test_guards([19; 32], &[1, 4]);
    let (mut states, _) = delta_phases(&mut guards, &policy, &next_intent);
    assert!(
        states
            .remove(0)
            .round3_commit_sigma(&mut guards[0], &stale_opens)
            .is_err()
    );
    assert_slot_aborted_not_bricked(&guards[0], 0);
    for mode in 0..3 {
        let mut guards = raw_test_guards([19; 32], &[1, 4]);
        let (mut states, mut commits) = sigma_phases(&mut guards, &policy, &intent);
        match mode {
            0 => {
                commits.pop();
            }
            1 => {
                commits[0].commitment[0] ^= 1;
            }
            _ => {
                commits[1].transcript_digest[0] ^= 1;
            }
        }
        assert!(
            states
                .remove(0)
                .round4_open_sigma(&mut guards[0], &commits)
                .is_err()
        );
        assert_slot_aborted_not_bricked(&guards[0], 0);
    }
    let mut guards = raw_test_guards([19; 32], &[1, 4]);
    let (mut states, commits) = start_phases(&mut guards, &policy, &intent);
    // A corrupted local phase latch must fail closed, even with an otherwise valid transcript.
    guards[0].active_phase = Some((0, 3));
    assert!(
        states
            .remove(0)
            .round2_open_delta(&mut guards[0], &commits)
            .is_err()
    );
    assert_erased(&guards[0]);
}

#[test]
fn party_phases_reject_sigma_opening_and_nonzero_sum() {
    let (policy, intent) = phase_fixture(&[1, 4]);
    for coherent in [false, true] {
        let mut guards = raw_test_guards([15; 32], &[1, 4]);
        let (mut states, mut commits) = sigma_phases(&mut guards, &policy, &intent);
        if coherent {
            states[1].context.sigma[0] ^= 1;
            commits[1].commitment = sigma_commitment(
                &commits[1],
                &states[1].context.sigma_salt,
                &states[1].context.sigma,
            );
            states[1].own_sigma = commits[1].clone();
        }
        let (mut finals, mut opens): (Vec<_>, Vec<_>) = states
            .into_iter()
            .zip(&mut guards)
            .map(|(s, g)| s.round4_open_sigma(g, &commits).unwrap())
            .unzip();
        if !coherent {
            opens[1].sigma_i[0] ^= 1;
        }
        let result = finals.remove(0).finalize(&mut guards[0], &opens);
        if coherent {
            assert!(matches!(result, Err(PolicyViolation::BarrierBdozMacFailed)));
        } else {
            assert!(matches!(
                result,
                Err(PolicyViolation::BarrierCommitmentMismatch { .. })
            ));
        }
        assert_slot_aborted_not_bricked(&guards[0], 0);
    }
}

// Ideal OT functionality for algebra tests only; production uses a secure OT provider.
#[derive(Default)]
struct IdealPolicyOt {
    peers: Vec<(u16, [u128; 2], [u8; 32])>,
    slot_cursors: Vec<(u16, u16, usize)>,
}
impl Drop for IdealPolicyOt {
    fn drop(&mut self) {
        for (_, alpha, seed) in &mut self.peers {
            wipe(alpha);
            wipe(seed);
        }
    }
}
impl PolicyAuthenticatedOt for IdealPolicyOt {
    fn exchange(
        &mut self,
        local_party: u16,
        peer: u16,
        domain: [u8; 32],
        alternatives: &[[u128; 2]],
        choices: &[bool],
    ) -> Result<Vec<u128>, PolicyViolation> {
        assert!(alternatives.len().is_multiple_of(256));
        assert_eq!(choices.len(), alternatives.len());
        let (_, local_alpha, _) = self
            .peers
            .iter()
            .find(|(id, _, _)| *id == local_party)
            .unwrap();
        let (_, alpha, seed) = self.peers.iter().find(|(id, _, _)| *id == peer).unwrap();
        let cursor = match self
            .slot_cursors
            .iter()
            .position(|(a, b, _)| *a == local_party && *b == peer)
        {
            Some(index) => index,
            None => {
                self.slot_cursors.push((local_party, peer, 0));
                self.slot_cursors.len() - 1
            }
        };
        let start = self.slot_cursors[cursor].2;
        self.slot_cursors[cursor].2 += alternatives.len() / 256;
        let mut pads = policy_ot_pad_stream(seed, &domain, peer, local_party, start);
        let mut selected = Vec::new();
        for (i, choice) in choices.iter().enumerate() {
            let slot = start + i / 256;
            let lane = i % 256 / 128;
            let bit = i % 128;
            let local_slot_alpha = derive_peer_slot_alpha(local_alpha, peer, slot);
            let peer_slot_alpha = derive_peer_slot_alpha(alpha, local_party, slot);
            assert_eq!(
                alternatives[i][0] ^ alternatives[i][1],
                gf2_128_mul(local_slot_alpha[lane], 1u128 << bit)
            );
            let mut raw = SecretBuffer([0u8; 16]);
            pads.squeeze(&mut raw[..]);
            let pad = u128::from_le_bytes(*raw);
            selected.push(
                pad ^ if *choice {
                    gf2_128_mul(peer_slot_alpha[lane], 1u128 << bit)
                } else {
                    0
                },
            );
        }
        Ok(selected)
    }
}

#[test]
fn distributed_setup_and_all_party_phases() {
    let all_ids = [0, 1, 2, 4];
    let mut first = Vec::new();
    let mut commits = Vec::new();
    let mut ot = IdealPolicyOt::default();
    for id in all_ids {
        let (state, messages) =
            PolicyGuardDkgRound1::new_with_capacity(id, &all_ids, [20; 32], [id as u8; 32], 300)
                .unwrap();
        ot.peers.push((
            id,
            state.guard.bdoz_alpha_share,
            state.guard.local_salt_seed,
        ));
        first.push(state);
        commits.extend(messages);
    }
    let mut second = Vec::new();
    let mut opens = Vec::new();
    for (state, id) in first.into_iter().zip(all_ids) {
        let incoming: Vec<_> = commits
            .iter()
            .filter(|c| c.recipient == id)
            .cloned()
            .collect();
        let (state, messages) = state.round2_open_seeds(&incoming).unwrap();
        second.push(state);
        opens.extend(messages);
    }
    let mut guards = Vec::new();
    for (state, id) in second.into_iter().zip(all_ids) {
        let incoming: Vec<_> = opens
            .iter()
            .filter(|o| o.recipient == id)
            .cloned()
            .collect();
        guards.push(finalize_distributed_policy_guard(state, &incoming, &mut ot).unwrap());
    }
    for g in &guards {
        for peer in &guards {
            if g.party_id == peer.party_id {
                continue;
            }
            for slot in 0..300 {
                let m = g.outgoing_mac(peer.party_id, slot).unwrap();
                let k = peer.incoming_key(g.party_id, slot).unwrap();
                let peer_alpha = peer.incoming_slot_alpha(g.party_id, slot);
                for lane in 0..2 {
                    assert_eq!(
                        m[lane],
                        k[lane] ^ gf2_128_mul(peer_alpha[lane], g.preproc_r[slot][lane])
                    );
                }
            }
        }
    }
    let (policy, mut intent) = phase_fixture(&[1, 2, 4]);
    // Production DKG guards mandate cryptographic initiator authentication!
    assert!(matches!(
        guards[1].round1_commit_intent(
            &policy,
            &intent,
            intent.session_id,
            intent.timestamp_secs,
            intent.rolling_window_spent,
        ),
        Err(PolicyViolation::UnauthenticatedInitiator)
    ));
    guards[0]
        .authenticate_initiated_intent(&policy, &mut intent)
        .unwrap();
    run_phases(&mut guards[1..], &policy, &intent);
}

#[test]
fn distributed_setup_rejects_seed_equivocation_and_sender_spoofing() {
    for spoof in [false, true] {
        let (a, ca) = PolicyGuardDkgRound1::new(1, &[1, 4], [21; 32], [1; 32]).unwrap();
        let (b, mut cb) = PolicyGuardDkgRound1::new(4, &[1, 4], [21; 32], [4; 32]).unwrap();
        if spoof {
            cb[0].sender = 1;
            assert!(a.round2_open_seeds(&cb).is_err());
        } else {
            let (a, _) = a.round2_open_seeds(&cb).unwrap();
            let (_, mut ob) = b.round2_open_seeds(&ca).unwrap();
            ob[0].seed[0] ^= 1;
            let mut ot = IdealPolicyOt::default();
            assert!(matches!(
                finalize_distributed_policy_guard(a, &ob, &mut ot),
                Err(PolicyViolation::BarrierCommitmentMismatch { party_id: 4 })
            ));
        }
    }
}

#[test]
fn test_policy_allowlist_velocity_quorum_tiers_anti_self_approval_and_bdoz_soundness() {
    let accel = CpuReferenceBackend::new();
    let allowed_dest = QsagAddress::from_pubkey_cshake256(
        "qsp",
        WitnessSuiteTag::MlDsa65,
        KeyIdentityKind::SingleOrThreshold,
        b"TREASURY_COLD_PK_1",
    )
    .unwrap();
    let unallowed_dest = QsagAddress::from_pubkey_cshake256(
        "qsp",
        WitnessSuiteTag::MlDsa65,
        KeyIdentityKind::SingleOrThreshold,
        b"ATTACKER_DRAIN_PK",
    )
    .unwrap();

    let policy = TransactionPolicy {
        chain_id: 1,
        pinned_suite: WitnessSuiteTag::MlDsa65,
        recipient_allowlist: vec![allowed_dest.commitment_256],
        max_single_tx_amount: 500_000,
        velocity_window_cap: 1_000_000,
        valid_not_before_secs: 1_700_000_000,
        valid_not_after_secs: 1_800_000_000,
        forbid_initiator_self_approval: true,
        hardware_guardian_party: Some(4),
        quorum_tiers: vec![
            QuorumTierRule {
                max_amount_units: 10_000,
                min_approvers: 2,
                require_hardware_guardian: false,
            },
            QuorumTierRule {
                max_amount_units: 500_000,
                min_approvers: 3,
                require_hardware_guardian: true,
            },
        ],
    };

    // Provision a 4-party committee `[1, 2, 3, 4]` and test subset quorum `[1, 2, 4]`!
    let all_guards = raw_test_guards([0x77u8; 32], &[1, 2, 3, 4]);
    assert!(format!("{:?}", all_guards[0]).contains("<REDACTED>"));
    let mut guards = raw_test_guards([0x77u8; 32], &[1, 2, 4]);

    let good_intent = TransactionIntent {
        chain_id: 1,
        suite: WitnessSuiteTag::MlDsa65,
        recipient: allowed_dest,
        amount_units: 250_000,
        rolling_window_spent: 600_000,
        window_id: 0,
        nonce: [0x55; 32],
        timestamp_secs: 1_750_000_000,
        initiator_party: 0,
        initiator_macs: Vec::new(),
        approver_parties: vec![1, 2, 4],
        payload_digest: [0xAB; 32],
        guard_authority_pk: [0; 32],
        rolling_window_accumulator: [0; 32],
        signing_key_id: [0; 32],
        policy_revision: 1,
        message_digest: cshake256_framed_32(b"QSAG.POLICY.MSG.V1", &[b"approved"]),
        signing_context_digest: cshake256_framed_32(b"QSAG.POLICY.CTX.V1", &[b"context"]),
        session_id: [0x12; 32],
        quorum_ids: vec![1, 2, 4],
    };

    let token = evaluate_policy_committed_barrier(
        &policy,
        &good_intent,
        [0x12; 32],
        good_intent.timestamp_secs,
        &mut guards,
        &accel,
    )
    .unwrap();
    assert!(
        guards
            .iter()
            .all(|g| g.accumulated_window_spend() == 850_000)
    );
    assert_eq!(token.intent_digest(), &good_intent.canonical_digest());
    assert!(!token.matches_signing(&[0; 32], b"approved", b"context", &[4, 1, 2]));
    assert!(token.matches_signing(
        &[0; 32],
        &good_intent.to_canonical_signing_bytes(&policy.canonical_digest()),
        b"context",
        &[4, 1, 2]
    ));
    for index in 0..4 {
        let mut changed = good_intent.clone();
        match index {
            0 => changed.amount_units += 1,
            1 => changed.recipient.commitment_256[0] ^= 1,
            2 => changed.guard_authority_pk[0] ^= 1,
            _ => changed.rolling_window_accumulator[0] ^= 1,
        }
        assert!(!token.matches_signing(
            &[0; 32],
            &changed.to_canonical_signing_bytes(&policy.canonical_digest()),
            b"context",
            &[1, 2, 4]
        ));
    }
    assert!(!token.matches_signing_for_policy(
        &[0; 32],
        &good_intent.to_canonical_signing_bytes(&policy.canonical_digest()),
        b"context",
        &[1, 2, 4],
        &[99; 32],
        &[0; 32]
    ));
    assert!(!token.matches_signing(&[0; 32], b"other", b"context", &[1, 2, 4]));
    assert!(!token.matches_signing(&[0; 32], b"approved", b"other", &[1, 2, 4]));
    assert!(!token.matches_signing(&[0; 32], b"approved", b"context", &[1, 2, 3]));

    // Each split token is bound to one quorum member, in ascending party order. A
    // custodian handed a peer's token (or the unsplit one) cannot spend it, and a
    // per-party token never fans out again.
    let msg = good_intent.to_canonical_signing_bytes(&policy.canonical_digest());
    assert_eq!(token.party_id(), None);
    for party in [1, 2, 4] {
        assert!(!token.matches_signing_party(party, &[0; 32], &msg, b"context", &[1, 2, 4]));
    }
    let party_tokens = token.into_quorum_party_tokens();
    assert_eq!(
        party_tokens
            .iter()
            .map(|t| t.party_id())
            .collect::<Vec<_>>(),
        [Some(1), Some(2), Some(4)]
    );
    for child in party_tokens {
        let owner = child.party_id().unwrap();
        for party in [0, 1, 2, 3, 4] {
            assert_eq!(
                child.matches_signing_party(party, &[0; 32], &msg, b"context", &[1, 2, 4]),
                party == owner
            );
        }
        assert!(!child.matches_signing_party(owner, &[0; 32], b"other", b"context", &[1, 2, 4]));
        let again = child.into_quorum_party_tokens();
        assert_eq!(again.len(), 1);
        assert_eq!(again[0].party_id(), Some(owner));
        assert!(again[0].matches_signing(&[0; 32], &msg, b"context", &[4, 1, 2]));
    }
    let mut colluding = raw_test_guards([0x44; 32], &[1, 2]);
    assert_eq!(
        evaluate_policy_committed_barrier(
            &policy,
            &good_intent,
            [0x12; 32],
            good_intent.timestamp_secs,
            &mut colluding,
            &accel
        )
        .unwrap_err(),
        PolicyViolation::IntentBindingMismatch
    );
    let mut even = raw_test_guards([0x45; 32], &[1, 2, 3, 4]);
    let mut even_intent = good_intent.clone();
    even_intent.approver_parties = vec![1, 2, 3, 4];
    even_intent.quorum_ids = vec![1, 2, 3, 4];
    let mut conflicting = vec![even_intent; 4];
    conflicting[1].amount_units -= 1;
    assert_eq!(
        evaluate_per_party_intents_barrier(
            &policy,
            &conflicting,
            [0x12; 32],
            good_intent.timestamp_secs,
            &mut even,
            None,
            &accel
        )
        .unwrap_err(),
        PolicyViolation::BarrierBdozMacFailed
    );
    for g in &even {
        assert_slot_aborted_not_bricked(g, 0);
    }

    // Negative BDOZ Soundness Test A: 1-bit wire fault (`delta_0 ^= 1`) MUST be caught (`1 - 2^-128`)!
    let mut fault_guards = raw_test_guards([0x77; 32], &[1, 2, 4]);
    let intents3 = vec![
        good_intent.clone(),
        good_intent.clone(),
        good_intent.clone(),
    ];
    assert_eq!(
        evaluate_per_party_intents_barrier(
            &policy,
            &intents3,
            [0x12; 32],
            good_intent.timestamp_secs,
            &mut fault_guards,
            Some((0, (1u128, 0u128))),
            &accel,
        )
        .unwrap_err(),
        PolicyViolation::BarrierBdozMacFailed
    );
    for g in &fault_guards {
        assert_slot_aborted_not_bricked(g, 0);
    }

    let mut guards = raw_test_guards([0x77; 32], &[1, 2, 4]);
    // Negative BDOZ Soundness Test B: Insider signer 2 approves a DIFFERENT valid amount (`200_000`
    // vs `250_000`) -> pairwise BDOZ catches intent equivocation (`1 - 2^-256`)!
    let mut equiv_intents = vec![
        good_intent.clone(),
        good_intent.clone(),
        good_intent.clone(),
    ];
    equiv_intents[2].amount_units = 200_000;
    assert_eq!(
        evaluate_per_party_intents_barrier(
            &policy,
            &equiv_intents,
            [0x12; 32],
            good_intent.timestamp_secs,
            &mut guards,
            None,
            &accel,
        )
        .unwrap_err(),
        PolicyViolation::BarrierBdozMacFailed
    );

    let mut guards = raw_test_guards([0x77; 32], &[1, 2, 4]);
    // 1. Unallowlisted recipient -> refused!
    let mut bad_dest = good_intent.clone();
    bad_dest.recipient = unallowed_dest;
    bad_dest.session_id = [0x13; 32];
    assert_eq!(
        evaluate_policy_committed_barrier(
            &policy,
            &bad_dest,
            [0x13; 32],
            bad_dest.timestamp_secs,
            &mut guards,
            &accel
        )
        .unwrap_err(),
        PolicyViolation::RecipientNotAllowlisted
    );

    // 2. Velocity cap exceeded (`600_000 + 450_000 > 1_000_000`) -> refused!
    let mut bad_vel = good_intent.clone();
    bad_vel.amount_units = 450_000;
    bad_vel.session_id = [0x14; 32];
    assert_eq!(
        evaluate_policy_committed_barrier(
            &policy,
            &bad_vel,
            [0x14; 32],
            bad_vel.timestamp_secs,
            &mut guards,
            &accel
        )
        .unwrap_err(),
        PolicyViolation::VelocityCapOverflowOrExceeded
    );

    // 3. Initiator self-approval (`initiator == 1` inside `[1, 2, 4]`) -> refused!
    let mut self_app = good_intent.clone();
    self_app.initiator_party = 1;
    self_app.session_id = [0x15; 32];
    assert_eq!(
        evaluate_policy_committed_barrier(
            &policy,
            &self_app,
            [0x15; 32],
            self_app.timestamp_secs,
            &mut guards,
            &accel
        )
        .unwrap_err(),
        PolicyViolation::InitiatorSelfApprovalForbidden
    );

    // 4. Tier 2 missing hardware guardian (`party 4`) -> refused!
    let mut no_hw = good_intent;
    no_hw.approver_parties = vec![1, 2, 3];
    no_hw.session_id = [0x16; 32];
    assert_eq!(
        evaluate_policy_committed_barrier(
            &policy,
            &no_hw,
            [0x16; 32],
            no_hw.timestamp_secs,
            &mut guards,
            &accel
        )
        .unwrap_err(),
        PolicyViolation::MissingHardwareGuardian
    );
}

#[cfg(test)]
mod quorum_ledger;
