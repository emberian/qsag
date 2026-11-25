use super::*;
use qsag_verified::StatefulVelocityGuard;

#[test]
fn durable_checkpoint_restart_tamper_and_rollback() {
    let (mut policy, mut intent) = phase_fixture(&[1, 2, 4]);
    policy.max_single_tx_amount = 100;
    policy.velocity_window_cap = 100;
    intent.amount_units = 60;
    intent.rolling_window_spent = 0;
    let key = [0x91; 32];
    let mut guards = raw_test_guards([0x61; 32], &[1, 2, 4]);
    let old = guards[0].export_durable_checkpoint(&key, 1);
    run_phases(&mut guards, &policy, &intent);
    let snapshots: Vec<_> = guards
        .iter()
        .map(|g| g.export_durable_checkpoint(&key, 2))
        .collect();
    let mut restarted = raw_test_guards([0x61; 32], &[1, 2, 4]);
    for (g, bytes) in restarted.iter_mut().zip(&snapshots) {
        assert_eq!(g.restore_from_durable_checkpoint(bytes, &key, 2), Ok(2));
        assert_eq!(g.export_durable_checkpoint(&key, 2), *bytes);
        assert_eq!(g.accumulated_window_spend(), 60);
        assert!(g.is_nonce_burned(&intent.nonce));
        assert!(g.is_session_burned(&intent.session_id));
    }
    intent.nonce = [0xA2; 32];
    intent.session_id = [0xB2; 32];
    for g in &mut restarted {
        assert_eq!(
            g.round1_commit_intent(
                &policy,
                &intent,
                intent.session_id,
                intent.timestamp_secs,
                0
            )
            .err(),
            Some(PolicyViolation::VelocityCapOverflowOrExceeded)
        );
    }
    let g = &mut restarted[0];
    assert_eq!(
        g.restore_from_durable_checkpoint(&old, &key, 0),
        Err(PolicyGuardError::Rollback)
    );
    assert_eq!(
        g.restore_from_durable_checkpoint(&snapshots[0], &key, 3),
        Err(PolicyGuardError::Rollback)
    );
    assert_eq!(
        g.restore_from_durable_checkpoint(&snapshots[1], &key, 0),
        Err(PolicyGuardError::WrongGuard)
    );
    for i in 0..snapshots[0].len() {
        let mut corrupt = snapshots[0].clone();
        corrupt[i] ^= 1;
        assert_eq!(
            g.restore_from_durable_checkpoint(&corrupt, &key, 0),
            Err(PolicyGuardError::AuthenticationFailed)
        );
    }
    assert_eq!(g.export_durable_checkpoint(&key, 2), snapshots[0]);
    let mut fresh = raw_test_guards([0x61; 32], &[1, 2, 4]);
    assert_eq!(
        fresh[0].restore_from_durable_checkpoint(&old, &key, 2),
        Err(PolicyGuardError::Rollback)
    );
    // A freshly authenticated higher generation still cannot erase live spend.
    let regressing = fresh[0].export_durable_checkpoint(&key, 5);
    assert_eq!(
        g.restore_from_durable_checkpoint(&regressing, &key, 0),
        Err(PolicyGuardError::Rollback)
    );
}

#[test]
fn stateful_guard_enforces_accumulated_spend_cap_and_nonce_replay_even_when_caller_lies() {
    let accel = CpuReferenceBackend::new();
    let (mut policy, base_intent) = phase_fixture(&[1, 2, 4]);
    policy.max_single_tx_amount = 100;
    policy.velocity_window_cap = 100;

    // Path A: 4-round per-party phase state machine (`cap = 100`, two `60` intents).
    let mut guards = raw_test_guards([0x61; 32], &[1, 2, 4]);
    let mut tx1 = base_intent.clone();
    tx1.amount_units = 60;
    tx1.rolling_window_spent = 0;
    tx1.nonce = [0xA1; 32];
    tx1.session_id = [0xB1; 32];
    run_phases(&mut guards, &policy, &tx1);
    assert!(guards.iter().all(|g| g.accumulated_window_spend() == 60));
    assert!(guards.iter().all(|g| g.is_nonce_burned(&[0xA1; 32])));

    // Second `60` intent where caller dishonestly passes `rolling_window_spent = 0` and
    // `cumulative_epoch_spent = 0`: MUST be rejected by internal `accumulated_window_spend`!
    let mut tx2_over_cap = tx1.clone();
    tx2_over_cap.nonce = [0xA2; 32];
    tx2_over_cap.session_id = [0xB2; 32];
    tx2_over_cap.rolling_window_spent = 0;
    for g in &mut guards {
        assert_eq!(
            g.round1_commit_intent(
                &policy,
                &tx2_over_cap,
                tx2_over_cap.session_id,
                tx2_over_cap.timestamp_secs,
                0,
            )
            .err(),
            Some(PolicyViolation::VelocityCapOverflowOrExceeded)
        );
    }

    // Replaying burned `nonce` (`[0xA1; 32]`) with small `amount_units = 10` and fresh session ID: MUST fail!
    let mut tx_replay_nonce = tx1.clone();
    tx_replay_nonce.amount_units = 10;
    tx_replay_nonce.session_id = [0xB3; 32];
    for g in &mut guards {
        assert_eq!(
            g.round1_commit_intent(
                &policy,
                &tx_replay_nonce,
                tx_replay_nonce.session_id,
                tx_replay_nonce.timestamp_secs,
                0,
            )
            .err(),
            Some(PolicyViolation::DuplicateIntentNonce)
        );
    }

    // Replaying burned `session_id` (`[0xB1; 32]`) with fresh `nonce`: MUST fail!
    let mut tx_replay_session = tx1.clone();
    tx_replay_session.amount_units = 10;
    tx_replay_session.nonce = [0xA4; 32];
    for g in &mut guards {
        assert_eq!(
            g.round1_commit_intent(
                &policy,
                &tx_replay_session,
                tx_replay_session.session_id,
                tx_replay_session.timestamp_secs,
                0,
            )
            .err(),
            Some(PolicyViolation::DuplicateIntentNonce)
        );
    }

    // Honest `40` intent (`60 + 40 == 100 <= 100`) succeeds, even if caller passes `rolling_window_spent = 0`!
    let mut tx3_fits = tx1.clone();
    tx3_fits.amount_units = 40;
    tx3_fits.nonce = [0xA5; 32];
    tx3_fits.session_id = [0xB5; 32];
    run_phases(&mut guards, &policy, &tx3_fits);
    assert!(guards.iter().all(|g| g.accumulated_window_spend() == 100));

    // Window mismatch rejected; advancing strictly to `window_id = 1` resets window spend while rejecting rollback!
    let mut tx_wrong_win = tx3_fits.clone();
    tx_wrong_win.window_id = 1;
    tx_wrong_win.nonce = [0xA6; 32];
    tx_wrong_win.session_id = [0xB6; 32];
    assert_eq!(
        guards[0]
            .round1_commit_intent(
                &policy,
                &tx_wrong_win,
                tx_wrong_win.session_id,
                tx_wrong_win.timestamp_secs,
                0,
            )
            .err(),
        Some(PolicyViolation::WindowIdMismatch)
    );
    for g in &mut guards {
        assert_eq!(
            g.advance_velocity_window(&WindowAdvanceAuthorization::new(&[43; 32], &[42; 32], 0, 0))
                .err(),
            Some(PolicyViolation::WindowIdMismatch)
        );
        g.advance_velocity_window(&WindowAdvanceAuthorization::new(&[43; 32], &[42; 32], 0, 1))
            .unwrap();
        assert_eq!(g.current_window_id(), 1);
        assert_eq!(g.accumulated_window_spend(), 0);
        assert_eq!(
            g.advance_velocity_window(&WindowAdvanceAuthorization::new(&[43; 32], &[42; 32], 0, 1))
                .err(),
            Some(PolicyViolation::WindowIdMismatch)
        );
    }
    run_phases(&mut guards, &policy, &tx_wrong_win);
    assert!(guards.iter().all(|g| g.accumulated_window_spend() == 40));

    // Path B: Direct `evaluate_policy_committed_barrier` (`cap = 100`, two `60` intents).
    let mut barrier_guards = raw_test_guards([0x62; 32], &[1, 2, 4]);
    evaluate_policy_committed_barrier(
        &policy,
        &tx1,
        tx1.session_id,
        tx1.timestamp_secs,
        &mut barrier_guards,
        &accel,
    )
    .unwrap();
    assert_eq!(
        evaluate_policy_committed_barrier(
            &policy,
            &tx2_over_cap,
            tx2_over_cap.session_id,
            tx2_over_cap.timestamp_secs,
            &mut barrier_guards,
            &accel,
        )
        .unwrap_err(),
        PolicyViolation::VelocityCapOverflowOrExceeded
    );
}

#[test]
fn peer_fault_aborts_only_session_slot_without_bricking_honest_guard_or_ledger() {
    let (policy, base_intent) = phase_fixture(&[1, 2, 4]);
    let mut guards = raw_test_guards([0x63; 32], &[1, 2, 4]);

    // 1. Complete an initial honest session (`accumulated_window_spend == 30`, slot 0 retired).
    run_phases(&mut guards, &policy, &base_intent);
    assert!(guards.iter().all(|g| g.accumulated_window_spend() == 30));
    assert!(guards.iter().all(|g| g.next_slot.get() == 1));

    // 2. Malicious peer `2` corrupts its Round-2 delta opening in session 2 (slot 1):
    //    Honest guards `1` and `4` MUST abort ONLY slot 1 without poisoning their keys or wiping `30` spend!
    let mut grief_intent = base_intent.clone();
    grief_intent.nonce = [0xC1; 32];
    grief_intent.session_id = [0xD1; 32];
    grief_intent.rolling_window_spent = 30;
    let (states, mut opens) = delta_phases(&mut guards, &policy, &grief_intent);
    opens[1].delta_i[0] ^= 0xDEAD_BEEF;
    for (st, g) in states.into_iter().zip(&mut guards) {
        assert!(matches!(
            st.round3_commit_sigma(g, &opens),
            Err(PolicyViolation::BarrierCommitmentMismatch { party_id: 2 })
        ));
        assert_slot_aborted_not_bricked(g, 1);
        for peer in [1u16, 2, 4] {
            if peer != g.party_id {
                assert!(
                    g.is_peer_slot_consumed(peer, 1),
                    "peer {peer} slot 1 must be retired on Round-3 abort"
                );
                assert!(
                    g.incoming_key(peer, 1).is_err(),
                    "peer {peer} slot 1 incoming BDOZ key must be wiped on Round-3 abort"
                );
            }
        }
        assert_eq!(g.accumulated_window_spend(), 30);
    }

    // 3. Malicious peer `2` next corrupts its Round-4 sigma opening in session 3 (slot 2):
    let mut grief_sigma = grief_intent.clone();
    grief_sigma.nonce = [0xC2; 32];
    grief_sigma.session_id = [0xD2; 32];
    let (states, commits) = sigma_phases(&mut guards, &policy, &grief_sigma);
    let (finals, mut sig_opens): (Vec<_>, Vec<_>) = states
        .into_iter()
        .zip(&mut guards)
        .map(|(s, g)| s.round4_open_sigma(g, &commits).unwrap())
        .unzip();
    sig_opens[1].sigma_i[1] ^= 1;
    for (fin, g) in finals.into_iter().zip(&mut guards) {
        assert!(matches!(
            fin.finalize(g, &sig_opens),
            Err(PolicyViolation::BarrierCommitmentMismatch { party_id: 2 })
        ));
        assert_slot_aborted_not_bricked(g, 2);
        assert_eq!(g.accumulated_window_spend(), 30);
    }

    // 4. Subsequent honest session on slot 3 succeeds cleanly and advances durable spend to `40`!
    let mut recovery_intent = grief_sigma;
    recovery_intent.nonce = [0xC3; 32];
    recovery_intent.session_id = [0xD3; 32];
    run_phases(&mut guards, &policy, &recovery_intent);
    assert!(guards.iter().all(|g| !g.is_poisoned()));
    assert!(guards.iter().all(|g| g.next_slot.get() == 4));
    assert!(guards.iter().all(|g| g.accumulated_window_spend() == 40));
}

#[test]
fn authenticated_initiator_prevents_self_approval_spoofing_and_transcript_equivocation() {
    let accel = CpuReferenceBackend::new();
    let all_ids = [10u16, 20, 30, 50];
    let approvers = [20u16, 30, 50];
    let (policy, mut intent) = phase_fixture(&approvers);
    intent.initiator_party = 10;

    let mut all_guards = raw_test_guards([0x88; 32], &all_ids);
    let guard_10 = all_guards.remove(0);
    // Remaining guards in `all_guards` are `[20, 30, 50]`.
    for g in &mut all_guards {
        g.set_require_authenticated_initiator(true);
    }

    // 1. Unauthenticated intent claiming `initiator_party = 10` is rejected!
    assert_eq!(
        evaluate_policy_committed_barrier_authenticated(
            &policy,
            &intent,
            intent.session_id,
            intent.timestamp_secs,
            &mut all_guards,
            &accel,
        )
        .unwrap_err(),
        PolicyViolation::UnauthenticatedInitiator
    );

    // 2. Insider approver `20` initiates a self-dealing request, tries to sign with `20`'s guard
    //    then rewrite `initiator_party = 10` to bypass `forbid_initiator_self_approval`: REJECTED!
    let mut forged = intent.clone();
    forged.initiator_party = 20;
    all_guards[0]
        .authenticate_initiated_intent(&policy, &mut forged)
        .unwrap();
    forged.initiator_party = 10;
    let forged_bytes = forged.to_canonical_signing_bytes(&policy.canonical_digest());
    forged.message_digest = cshake256_framed_32(b"QSAG.POLICY.MSG.V1", &[&forged_bytes]);
    assert_eq!(
        all_guards[1]
            .round1_commit_intent_authenticated(
                &policy,
                &forged,
                forged.session_id,
                forged.timestamp_secs,
                forged.rolling_window_spent,
            )
            .err(),
        Some(PolicyViolation::UnauthenticatedInitiator)
    );

    // 3. Genuine authentication by `guard_10` succeeds across all approvers `[20, 30, 50]`!
    let signed_bytes = guard_10
        .authenticate_initiated_intent(&policy, &mut intent)
        .unwrap();
    // Tampering with `amount_units` after `guard_10` authenticated invalidates the MAC!
    let mut tampered = intent.clone();
    tampered.amount_units += 1;
    assert_eq!(
        all_guards[0]
            .round1_commit_intent_authenticated(
                &policy,
                &tampered,
                tampered.session_id,
                tampered.timestamp_secs,
                tampered.rolling_window_spent,
            )
            .err(),
        Some(PolicyViolation::UnauthenticatedInitiator)
    );

    let token = evaluate_policy_committed_barrier_authenticated(
        &policy,
        &intent,
        intent.session_id,
        intent.timestamp_secs,
        &mut all_guards,
        &accel,
    )
    .unwrap();
    assert!(token.matches_signing(
        &intent.signing_key_id,
        &signed_bytes,
        b"context",
        &approvers,
    ));
}

#[test]
fn quorum_switching_cannot_bypass_cumulative_velocity_cap_across_subsets() {
    let accel = CpuReferenceBackend::new();
    let (mut policy, base_intent) = phase_fixture(&[1, 2, 3, 4]);
    policy.max_single_tx_amount = 100;
    policy.velocity_window_cap = 100;
    policy.hardware_guardian_party = None;
    policy.quorum_tiers = vec![QuorumTierRule {
        max_amount_units: 100,
        min_approvers: 2,
        require_hardware_guardian: false,
    }];

    let mut committee = raw_test_guards([0x71; 32], &[1, 2, 3, 4]);
    let mut q1_intent = base_intent.clone();
    q1_intent.amount_units = 60;
    q1_intent.rolling_window_spent = 0;
    q1_intent.nonce = [0xE1; 32];
    q1_intent.session_id = [0xF1; 32];
    q1_intent.approver_parties = vec![1, 2];
    q1_intent.quorum_ids = vec![1, 2];

    // 1. Disjoint 2-of-4 subset `{1, 2}` without a fixed accounting guardian or shared ledger
    //    is refused on both batch and 4-round APIs so disjoint quorums cannot double-spend!
    assert_eq!(
        evaluate_policy_committed_barrier(
            &policy,
            &q1_intent,
            q1_intent.session_id,
            q1_intent.timestamp_secs,
            &mut committee[0..2],
            &accel,
        )
        .unwrap_err(),
        PolicyViolation::MissingHardwareGuardian
    );
    assert_eq!(
        committee[0]
            .round1_commit_intent(
                &policy,
                &q1_intent,
                q1_intent.session_id,
                q1_intent.timestamp_secs,
                0,
            )
            .err(),
        Some(PolicyViolation::MissingHardwareGuardian)
    );
    assert!(committee.iter().all(|g| g.next_slot.get() == 0));

    // 2. With `SharedWindowSpendLedger`, `{1, 2}` approves `60`, and switching to disjoint
    //    quorum `{3, 4}` for a second `60` (even lying `rolling_window_spent = 0`) is rejected!
    let mut shared_ledger = SharedWindowSpendLedger::new(&policy, 0);
    let old_checkpoint = shared_ledger.export_durable_checkpoint(&[77; 32]);
    let mut saved = Vec::new();
    evaluate_policy_committed_barrier_with_ledger(
        &policy,
        &q1_intent,
        q1_intent.session_id,
        q1_intent.timestamp_secs,
        &mut committee[0..2],
        &mut shared_ledger,
        |ledger, _| {
            saved = ledger.export_durable_checkpoint(&[77; 32]);
            Ok(())
        },
        &accel,
    )
    .unwrap();
    assert_eq!(shared_ledger.accumulated_window_spend(), 60);

    let generation = shared_ledger.generation();
    assert_eq!(
        shared_ledger.restore_from_durable_checkpoint(&old_checkpoint, &[77; 32], 0),
        Err(PolicyGuardError::Rollback)
    );
    let mut recovered = SharedWindowSpendLedger::new(&policy, 0);
    assert_eq!(
        recovered.restore_from_durable_checkpoint(&old_checkpoint, &[77; 32], generation),
        Err(PolicyGuardError::Rollback)
    );
    let mut tampered = saved.clone();
    tampered[40] ^= 1;
    assert_eq!(
        recovered.restore_from_durable_checkpoint(&tampered, &[77; 32], generation),
        Err(PolicyGuardError::AuthenticationFailed)
    );
    recovered
        .restore_from_durable_checkpoint(&saved, &[77; 32], generation)
        .unwrap();
    assert_eq!(recovered.accumulated_window_spend(), 60);
    let verified = recovered.verified_velocity.as_ref().unwrap();
    assert_eq!(verified.spent_units(), 60);
    assert_eq!(verified.last_nonce(), generation);
    assert_eq!(verified.cap_units(), policy.velocity_window_cap);
    // Even a direct internal commit cannot bypass the retained verified cap.
    let mut over_cap = SharedWindowSpendLedger::new(&policy, 0);
    over_cap
        .restore_from_durable_checkpoint(&saved, &[77; 32], generation)
        .unwrap();
    assert_eq!(
        over_cap.record_approved_intent(policy.velocity_window_cap + 1, [0xA1; 32], [0xB1; 32]),
        Err(PolicyViolation::VelocityCapOverflowOrExceeded)
    );
    assert!(over_cap.failed);
    assert_eq!(
        over_cap.verified_velocity.as_ref().unwrap().spent_units(),
        60
    );
    assert!(recovered.is_nonce_burned(&q1_intent.nonce));
    shared_ledger = recovered;

    let mut q2_intent = q1_intent.clone();
    q2_intent.nonce = [0xE2; 32];
    q2_intent.session_id = [0xF2; 32];
    q2_intent.approver_parties = vec![3, 4];
    q2_intent.quorum_ids = vec![3, 4];
    assert_eq!(
        evaluate_policy_committed_barrier_with_ledger(
            &policy,
            &q2_intent,
            q2_intent.session_id,
            q2_intent.timestamp_secs,
            &mut committee[2..4],
            &mut shared_ledger,
            |_, _| Ok(()),
            &accel,
        )
        .unwrap_err(),
        PolicyViolation::VelocityCapOverflowOrExceeded
    );
    assert_eq!(committee[2].next_slot.get(), 0);
    assert_eq!(committee[3].next_slot.get(), 0);

    // A failed persistence callback withholds release and disables all later approvals.
    q2_intent.amount_units = 10;
    assert_eq!(
        evaluate_policy_committed_barrier_with_ledger(
            &policy,
            &q2_intent,
            q2_intent.session_id,
            q2_intent.timestamp_secs,
            &mut committee[2..4],
            &mut shared_ledger,
            |_, _| Err(PolicyViolation::LedgerPersistenceFailed),
            &accel
        )
        .unwrap_err(),
        PolicyViolation::LedgerPersistenceFailed
    );
    assert!(shared_ledger.failed);
    q2_intent.nonce = [0xE5; 32];
    q2_intent.session_id = [0xF5; 32];
    assert_eq!(
        evaluate_policy_committed_barrier_with_ledger(
            &policy,
            &q2_intent,
            q2_intent.session_id,
            q2_intent.timestamp_secs,
            &mut committee[2..4],
            &mut shared_ledger,
            |_, _| Ok(()),
            &accel
        )
        .unwrap_err(),
        PolicyViolation::LedgerPersistenceFailed
    );

    // 3. With a fixed accounting guardian `Some(4)`, switching `{1, 4}` (`60`) then `{2, 4}` (`60`)
    //    intersects at party `4` and rejects the second `60` even with dishonest `rolling_window_spent = 0`!
    let mut hw_policy = policy;
    hw_policy.hardware_guardian_party = Some(4);
    let mut hw_committee = raw_test_guards([0x72; 32], &[1, 2, 4]);
    let mut g1_intent = base_intent.clone();
    g1_intent.amount_units = 60;
    g1_intent.rolling_window_spent = 0;
    g1_intent.nonce = [0xE3; 32];
    g1_intent.session_id = [0xF3; 32];
    g1_intent.approver_parties = vec![1, 4];
    g1_intent.quorum_ids = vec![1, 4];
    let g4 = hw_committee.pop().unwrap();
    let g2 = hw_committee.pop().unwrap();
    let g1 = hw_committee.pop().unwrap();
    let mut pair_14 = vec![g1, g4];
    evaluate_policy_committed_barrier(
        &hw_policy,
        &g1_intent,
        g1_intent.session_id,
        g1_intent.timestamp_secs,
        &mut pair_14,
        &accel,
    )
    .unwrap();
    let g4_after = pair_14.pop().unwrap();
    let mut pair_24 = vec![g2, g4_after];
    let mut g2_intent = g1_intent;
    g2_intent.nonce = [0xE4; 32];
    g2_intent.session_id = [0xF4; 32];
    g2_intent.approver_parties = vec![2, 4];
    g2_intent.quorum_ids = vec![2, 4];
    assert_eq!(
        evaluate_policy_committed_barrier(
            &hw_policy,
            &g2_intent,
            g2_intent.session_id,
            g2_intent.timestamp_secs,
            &mut pair_24,
            &accel,
        )
        .unwrap_err(),
        PolicyViolation::VelocityCapOverflowOrExceeded
    );
}

#[test]
fn batch_barrier_enforces_authoritative_current_timestamp_before_consuming_slot() {
    let accel = CpuReferenceBackend::new();
    let (policy, intent) = phase_fixture(&[1, 2, 4]);
    let mut guards = raw_test_guards([0x73; 32], &[1, 2, 4]);

    // Expired wall-clock (`150 > valid_not_after_secs == 100`) and mismatched live clock (`51 != 50`)
    // both fail closed with `TimestampOutsideWindow` without consuming any preprocessing slot!
    for bad_now in [0u64, 51, 150] {
        assert_eq!(
            evaluate_policy_committed_barrier(
                &policy,
                &intent,
                intent.session_id,
                bad_now,
                &mut guards,
                &accel,
            )
            .unwrap_err(),
            PolicyViolation::TimestampOutsideWindow
        );
        assert!(
            guards
                .iter()
                .all(|g| g.next_slot.get() == 0 && !g.is_poisoned())
        );
    }

    // Exact authoritative clock (`50 == intent.timestamp_secs`) succeeds cleanly!
    evaluate_policy_committed_barrier(
        &policy,
        &intent,
        intent.session_id,
        intent.timestamp_secs,
        &mut guards,
        &accel,
    )
    .unwrap();
    assert!(guards.iter().all(|g| g.next_slot.get() == 1));
}

// ---- Regressions for the hostile-audit findings H-11, M-11, L-06 and L-07. ----

fn incoming_key_words(g: &PolicySignerGuardShare, peer: u16, slot: usize) -> [u128; 2] {
    g.preproc_incoming_keys
        .iter()
        .find(|(p, _)| *p == peer)
        .map(|(_, keys)| keys[slot])
        .unwrap()
}

fn assert_peer_slot_retired(g: &PolicySignerGuardShare, peer: u16, slot: usize) {
    assert!(
        g.is_peer_slot_consumed(peer, slot),
        "guard {} must retire slot {slot} of peer {peer}",
        g.party_id
    );
    assert_eq!(
        incoming_key_words(g, peer, slot),
        [0; 2],
        "guard {} must wipe its incoming key for slot {slot} of peer {peer}",
        g.party_id
    );
}

fn assert_peer_slot_live(g: &PolicySignerGuardShare, peer: u16, slot: usize) {
    assert!(!g.is_peer_slot_consumed(peer, slot));
    assert_ne!(incoming_key_words(g, peer, slot), [0; 2]);
}

/// H-11: every way a Round 3 delta opening vector can be refused retires each peer
/// slot of the session and wipes its incoming key, and the slot cannot be presented
/// to this guard again.
#[test]
fn round3_abort_retires_every_peer_slot_and_wipes_incoming_keys() {
    type Fault = fn(&mut Vec<PartyPolicyDeltaOpenMsg>);
    let faults: [Fault; 6] = [
        |opens| opens[1].delta_i[0] ^= 1,
        |opens| opens[1].salt_i[31] ^= 0x80,
        |opens| opens[1].party_id = 9,
        |opens| {
            opens.pop();
        },
        |opens| opens.clear(),
        |opens| opens[1] = opens[0].clone(),
    ];
    let ids = [1u16, 2, 4];
    for (case, fault) in faults.iter().enumerate() {
        let (policy, intent) = phase_fixture(&ids);
        let mut guards = raw_test_guards([0x90 + case as u8; 32], &ids);
        // Slot 0 is spent honestly; the faulted session runs on slot 1.
        run_phases(&mut guards, &policy, &intent);
        let mut faulted = intent.clone();
        faulted.nonce = [0xA1; 32];
        faulted.session_id = [0xA2; 32];
        faulted.rolling_window_spent = 30;
        let (states, mut opens) = delta_phases(&mut guards, &policy, &faulted);
        for g in &guards {
            for peer in ids.into_iter().filter(|p| *p != g.party_id) {
                assert_peer_slot_live(g, peer, 1);
            }
        }
        fault(&mut opens);
        for (state, g) in states.into_iter().zip(&mut guards) {
            assert!(state.round3_commit_sigma(g, &opens).is_err(), "case {case}");
            assert_slot_aborted_not_bricked(g, 1);
            for peer in ids.into_iter().filter(|p| *p != g.party_id) {
                assert_peer_slot_retired(g, peer, 1);
                assert_peer_slot_live(g, peer, 2);
            }
            assert_eq!(g.accumulated_window_spend(), 30);
        }

        // A peer that presents the retired slot again is refused in Round 2.
        let mut replay = faulted.clone();
        replay.nonce = [0xA3; 32];
        replay.session_id = [0xA4; 32];
        let (mut states, mut commits) = start_phases(&mut guards, &policy, &replay);
        assert!(commits.iter().all(|c| c.slot == 2));
        commits[1].slot = 1;
        assert_eq!(
            states
                .remove(0)
                .round2_open_delta(&mut guards[0], &commits)
                .err(),
            Some(PolicyViolation::IntentBindingMismatch),
            "case {case}"
        );
    }
}

/// H-11, same class in Round 2: a commitment vector rejected part-way retires the peer
/// slots the guard had already accepted as bound to the session, and no others.
#[test]
fn round2_rejection_retires_the_peer_slots_it_accepted() {
    let ids = [1u16, 2, 4];
    let (policy, intent) = phase_fixture(&ids);
    let mut guards = raw_test_guards([0x97; 32], &ids);
    let (mut states, mut commits) = start_phases(&mut guards, &policy, &intent);
    // Guard 1 accepts its own commitment and that of peer 2, then rejects peer 4.
    commits[2].intent_digest[0] ^= 1;
    assert_eq!(
        states
            .remove(0)
            .round2_open_delta(&mut guards[0], &commits)
            .err(),
        Some(PolicyViolation::IntentBindingMismatch)
    );
    assert_slot_aborted_not_bricked(&guards[0], 0);
    assert_peer_slot_retired(&guards[0], 2, 0);
    assert_peer_slot_live(&guards[0], 4, 0);
    assert_peer_slot_live(&guards[0], 2, 1);
}

fn open_quorum_policy(ids: &[u16]) -> (TransactionPolicy, TransactionIntent) {
    let (mut policy, intent) = phase_fixture(ids);
    policy.forbid_initiator_self_approval = false;
    policy.hardware_guardian_party = None;
    policy.quorum_tiers = vec![QuorumTierRule {
        max_amount_units: 100,
        min_approvers: 2,
        require_hardware_guardian: false,
    }];
    (policy, intent)
}

/// M-11: a list longer than the `u16` party-id space is refused before anything else
/// is looked at, and the longest admissible list is still evaluated.
#[test]
fn evaluate_bounds_the_approver_list_before_scanning_it() {
    let (policy, mut intent) = open_quorum_policy(&[1, 2]);
    intent.approver_parties = (1..=u16::MAX).collect();
    assert_eq!(intent.approver_parties.len(), 65_535);
    assert_eq!(policy.evaluate(&intent), Ok(()));

    // 65,536 distinct IDs: no duplicate exists, and a wrapping count would read 0.
    intent.approver_parties = (0..=u16::MAX).collect();
    assert_eq!(
        policy.evaluate(&intent),
        Err(PolicyViolation::ApproverCountOutOfRange)
    );
    intent.approver_parties = vec![7; 70_000];
    assert_eq!(
        policy.evaluate(&intent),
        Err(PolicyViolation::ApproverCountOutOfRange)
    );
    // The bound is checked before every other rule, including the cheap ones.
    intent.chain_id ^= 1;
    intent.amount_units = u128::MAX;
    assert_eq!(
        policy.evaluate(&intent),
        Err(PolicyViolation::ApproverCountOutOfRange)
    );
}

/// M-11: the bitset reports exactly what the quadratic scan it replaced reported, for
/// duplicates and self-approval at every position and across bitset word boundaries.
#[test]
fn evaluate_distinctness_matches_the_pairwise_scan() {
    fn pairwise(approvers: &[u16], initiator: u16, forbid: bool) -> Option<PolicyViolation> {
        for (i, &p_i) in approvers.iter().enumerate() {
            if forbid && p_i == initiator {
                return Some(PolicyViolation::InitiatorSelfApprovalForbidden);
            }
            if approvers[i + 1..].contains(&p_i) {
                return Some(PolicyViolation::DuplicateApproverInQuorum);
            }
        }
        None
    }
    fn observed(policy: &TransactionPolicy, intent: &TransactionIntent) -> Option<PolicyViolation> {
        match policy.evaluate(intent) {
            Err(
                err @ (PolicyViolation::InitiatorSelfApprovalForbidden
                | PolicyViolation::DuplicateApproverInQuorum),
            ) => Some(err),
            _ => None,
        }
    }
    let (mut policy, mut intent) = open_quorum_policy(&[1, 2]);
    intent.initiator_party = 64;

    let fixed: [&[u16]; 12] = [
        &[],
        &[5, 6],
        &[5, 6, 5],
        &[5, 64, 5],
        &[64, 5, 5],
        &[5, 5, 64],
        &[64, 64],
        &[63, 64, 127, 128, 0, u16::MAX],
        &[u16::MAX, 0, u16::MAX],
        &[0, 63, 0],
        &[1023, 1024, 1024],
        &[65_472, 65_535, 65_472],
    ];
    let mut cases: Vec<Vec<u16>> = fixed.iter().map(|c| c.to_vec()).collect();
    // Deterministic lists over a small ID range, so duplicates and the initiator recur.
    let mut state = 0x9E37_79B9_7F4A_7C15u64;
    let mut next = |bound: u64| {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        (state >> 33) % bound
    };
    for _ in 0..1_200 {
        let len = next(40) as usize;
        let spread = 1 + next(120);
        cases.push((0..len).map(|_| (next(spread) + 20) as u16).collect());
    }
    // Long lists: all distinct, a duplicate at the far ends, the initiator at the end.
    let long: Vec<u16> = (1_000..41_000).collect();
    cases.push(long.clone());
    let mut ends = long.clone();
    *ends.last_mut().unwrap() = ends[0];
    cases.push(ends);
    let mut with_initiator = long;
    with_initiator.push(64);
    cases.push(with_initiator);

    let mut seen = [0usize; 3];
    for forbid in [false, true] {
        policy.forbid_initiator_self_approval = forbid;
        for case in &cases {
            intent.approver_parties = case.clone();
            let expected = pairwise(case, intent.initiator_party, forbid);
            assert_eq!(observed(&policy, &intent), expected, "{forbid} {case:?}");
            seen[match expected {
                None => 0,
                Some(PolicyViolation::DuplicateApproverInQuorum) => 1,
                Some(_) => 2,
            }] += 1;
        }
    }
    assert!(seen.iter().all(|count| *count > 20), "{seen:?}");
}

fn quorum_intent(
    base: &TransactionIntent,
    ids: &[u16],
    tag: u8,
    amount: u128,
) -> TransactionIntent {
    let mut intent = base.clone();
    intent.amount_units = amount;
    intent.rolling_window_spent = 0;
    intent.nonce = [tag; 32];
    intent.session_id = [tag ^ 0xFF; 32];
    intent.approver_parties = ids.to_vec();
    intent.quorum_ids = ids.to_vec();
    intent
}

/// L-06: an uncapped velocity window is no exemption. A quorum that can be disjoint
/// from another one is refused without the shared ledger, and with it stays under the
/// committee-wide replay sets and cumulative spend.
#[test]
fn uncapped_velocity_window_keeps_disjoint_quorums_on_the_shared_ledger() {
    let accel = CpuReferenceBackend::new();
    let (mut policy, base) = open_quorum_policy(&[1, 2, 3, 4]);
    policy.velocity_window_cap = u128::MAX;
    let mut committee = raw_test_guards([0x73; 32], &[1, 2, 3, 4]);

    let first = quorum_intent(&base, &[1, 2], 0x11, 60);
    assert_eq!(
        evaluate_policy_committed_barrier(
            &policy,
            &first,
            first.session_id,
            first.timestamp_secs,
            &mut committee[0..2],
            &accel,
        )
        .unwrap_err(),
        PolicyViolation::MissingHardwareGuardian
    );
    assert_eq!(
        committee[0]
            .round1_commit_intent(&policy, &first, first.session_id, first.timestamp_secs, 0)
            .err(),
        Some(PolicyViolation::MissingHardwareGuardian)
    );
    assert!(committee.iter().all(|g| g.next_slot.get() == 0));

    let mut ledger = SharedWindowSpendLedger::new(&policy, 0);
    evaluate_policy_committed_barrier_with_ledger(
        &policy,
        &first,
        first.session_id,
        first.timestamp_secs,
        &mut committee[0..2],
        &mut ledger,
        |_, _| Ok(()),
        &accel,
    )
    .unwrap();
    // The disjoint quorum cannot reuse the nonce or the session the first one burned.
    let mut reused_nonce = quorum_intent(&base, &[3, 4], 0x12, 60);
    reused_nonce.nonce = first.nonce;
    let mut reused_session = quorum_intent(&base, &[3, 4], 0x13, 60);
    reused_session.session_id = first.session_id;
    for replay in [&reused_nonce, &reused_session] {
        assert_eq!(
            evaluate_policy_committed_barrier_with_ledger(
                &policy,
                replay,
                replay.session_id,
                replay.timestamp_secs,
                &mut committee[2..4],
                &mut ledger,
                |_, _| Ok(()),
                &accel,
            )
            .unwrap_err(),
            PolicyViolation::DuplicateIntentNonce
        );
    }
    let second = quorum_intent(&base, &[3, 4], 0x14, 60);
    evaluate_policy_committed_barrier_with_ledger(
        &policy,
        &second,
        second.session_id,
        second.timestamp_secs,
        &mut committee[2..4],
        &mut ledger,
        |_, _| Ok(()),
        &accel,
    )
    .unwrap();
    assert_eq!(ledger.accumulated_window_spend(), 120);
    assert_eq!(committee[3].accumulated_window_spend(), 120);

    // The structural exemptions are unchanged: the full committee needs no ledger.
    let mut full = raw_test_guards([0x74; 32], &[1, 2, 3, 4]);
    let all = quorum_intent(&base, &[1, 2, 3, 4], 0x15, 60);
    evaluate_policy_committed_barrier(
        &policy,
        &all,
        all.session_id,
        all.timestamp_secs,
        &mut full,
        &accel,
    )
    .unwrap();
}

/// Replace the retained verified guard by one in the same window, cap, spend and
/// nonce but pinned to another key: every pre-barrier check still passes and only the
/// verified transition of the record step refuses.
fn pin_verified_guard_elsewhere(g: &mut PolicySignerGuardShare, cap: u128) {
    let (foreign, generation) = rebuild_verified_velocity(
        g.current_window_id,
        cap,
        [0xEE; 32],
        g.velocity_generation,
        g.accumulated_window_spend,
    )
    .unwrap();
    assert_eq!(generation, g.velocity_generation);
    g.verified_velocity = Some(foreign);
}

/// What recording an approval advances on a guard.
fn recorded_state(g: &PolicySignerGuardShare) -> (u128, u64, Vec<[u8; 32]>, Vec<[u8; 32]>) {
    (
        g.accumulated_window_spend,
        g.velocity_generation,
        g.burned_intent_nonces.clone(),
        g.burned_sessions.clone(),
    )
}

/// L-07: when a guard refuses to record after the barrier opened, the shared ledger is
/// byte-for-byte what it was, no other guard has advanced, and the survivors still
/// agree with the ledger in a later session.
#[test]
fn guard_refusal_leaves_the_shared_ledger_and_the_other_guards_unadvanced() {
    let accel = CpuReferenceBackend::new();
    let (mut policy, base) = open_quorum_policy(&[1, 2, 3, 4]);
    policy.velocity_window_cap = 100;
    let mut committee = raw_test_guards([0x75; 32], &[1, 2, 3, 4]);
    let g4 = committee.pop().unwrap();
    let g3 = committee.pop().unwrap();
    let mut pair_12 = committee;
    let mut ledger = SharedWindowSpendLedger::new(&policy, 0);

    let honest = quorum_intent(&base, &[1, 2], 0x21, 10);
    evaluate_policy_committed_barrier_with_ledger(
        &policy,
        &honest,
        honest.session_id,
        honest.timestamp_secs,
        &mut pair_12,
        &mut ledger,
        |_, _| Ok(()),
        &accel,
    )
    .unwrap();

    // The second guard of the quorum refuses; the first one would already have advanced.
    pin_verified_guard_elsewhere(&mut pair_12[1], policy.velocity_window_cap);
    let ledger_before = ledger.export_durable_checkpoint(&[0x55; 32]);
    let ledger_generation = ledger.generation();
    let first_before = recorded_state(&pair_12[0]);
    let refused = quorum_intent(&base, &[1, 2], 0x22, 10);
    assert_eq!(
        evaluate_policy_committed_barrier_with_ledger(
            &policy,
            &refused,
            refused.session_id,
            refused.timestamp_secs,
            &mut pair_12,
            &mut ledger,
            |_, _| panic!("nothing to persist: no approval was recorded"),
            &accel,
        )
        .unwrap_err(),
        PolicyViolation::VelocityCapOverflowOrExceeded
    );
    assert_eq!(ledger.export_durable_checkpoint(&[0x55; 32]), ledger_before);
    assert_eq!(ledger.generation(), ledger_generation);
    assert_eq!(ledger.accumulated_window_spend(), 10);
    assert!(!ledger.failed);
    assert!(!ledger.is_nonce_burned(&refused.nonce));
    assert!(!ledger.is_session_burned(&refused.session_id));
    let verified = ledger.verified_velocity.as_ref().unwrap();
    assert_eq!((verified.spent_units(), verified.last_nonce()), (10, 1));

    let first = &pair_12[0];
    assert_eq!(recorded_state(first), first_before);
    assert!(!first.is_nonce_burned(&refused.nonce));
    assert!(!first.is_session_burned(&refused.session_id));
    let verified = first.verified_velocity.as_ref().unwrap();
    assert_eq!((verified.spent_units(), verified.last_nonce()), (10, 1));
    // The openings of the refused session exist, so its slots are spent on every guard.
    assert_slot_aborted_not_bricked(first, 1);
    assert_peer_slot_retired(first, 2, 1);
    assert_erased(&pair_12[1]);

    // Guard 1 and the ledger still agree: the same intent nonce completes with guard 3.
    let mut pair_13 = vec![pair_12.remove(0), g3];
    let mut retry = quorum_intent(&base, &[1, 3], 0x23, 10);
    retry.nonce = refused.nonce;
    evaluate_policy_committed_barrier_with_ledger(
        &policy,
        &retry,
        retry.session_id,
        retry.timestamp_secs,
        &mut pair_13,
        &mut ledger,
        |_, _| Ok(()),
        &accel,
    )
    .unwrap();
    assert_eq!(ledger.accumulated_window_spend(), 20);
    assert!(pair_13.iter().all(|g| g.accumulated_window_spend() == 20));
    assert_eq!(ledger.generation(), ledger_generation + 1);

    // A refusal by the shared ledger itself disables it without changing its
    // accounting, and advances no guard.
    let mut pair_34 = vec![pair_13.pop().unwrap(), g4];
    let before: Vec<_> = pair_34.iter().map(recorded_state).collect();
    ledger.verified_velocity = rebuild_verified_velocity(
        0,
        policy.velocity_window_cap,
        [0xEE; 32],
        ledger.generation,
        ledger.accumulated_window_spend,
    )
    .map(|(foreign, _)| foreign);
    let ledger_before = ledger.export_durable_checkpoint(&[0x55; 32]);
    let last = quorum_intent(&base, &[3, 4], 0x24, 10);
    assert_eq!(
        evaluate_policy_committed_barrier_with_ledger(
            &policy,
            &last,
            last.session_id,
            last.timestamp_secs,
            &mut pair_34,
            &mut ledger,
            |_, _| panic!("nothing to persist: no approval was recorded"),
            &accel,
        )
        .unwrap_err(),
        PolicyViolation::VelocityCapOverflowOrExceeded
    );
    assert!(ledger.failed);
    assert_eq!(ledger.export_durable_checkpoint(&[0x55; 32]), ledger_before);
    assert!(pair_34.iter().all(|g| !g.is_poisoned()));
    assert_eq!(
        pair_34.iter().map(recorded_state).collect::<Vec<_>>(),
        before
    );
}

/// L-07 without a shared ledger: a refusing guard leaves the guards before it unadvanced.
#[test]
fn guard_refusal_without_a_ledger_advances_no_guard() {
    let accel = CpuReferenceBackend::new();
    let (policy, base) = open_quorum_policy(&[1, 2]);
    let mut guards = raw_test_guards([0x76; 32], &[1, 2]);
    let honest = quorum_intent(&base, &[1, 2], 0x31, 10);
    evaluate_policy_committed_barrier(
        &policy,
        &honest,
        honest.session_id,
        honest.timestamp_secs,
        &mut guards,
        &accel,
    )
    .unwrap();
    pin_verified_guard_elsewhere(&mut guards[1], policy.velocity_window_cap);
    let first_before = recorded_state(&guards[0]);
    let refused = quorum_intent(&base, &[1, 2], 0x32, 10);
    assert_eq!(
        evaluate_policy_committed_barrier(
            &policy,
            &refused,
            refused.session_id,
            refused.timestamp_secs,
            &mut guards,
            &accel,
        )
        .unwrap_err(),
        PolicyViolation::VelocityCapOverflowOrExceeded
    );
    assert_eq!(recorded_state(&guards[0]), first_before);
    assert_eq!(first_before.0, 10);
    assert_slot_aborted_not_bricked(&guards[0], 1);
    assert_erased(&guards[1]);
}

/// L-07: a refused record leaves a guard's retained verified guard as it was, and the
/// replay used to decide a spend reproduces the retained guard exactly.
#[test]
fn refused_record_leaves_the_retained_verified_guard_untouched() {
    let mut guard = raw_test_guards([0x77; 32], &[1, 2]).remove(0);
    guard
        .record_approved_intent(50, 7, [1; 32], [2; 32])
        .unwrap();
    guard
        .record_approved_intent(50, 30, [3; 32], [4; 32])
        .unwrap();
    let observe = |v: &StatefulVelocityGuard| {
        (
            v.window_id(),
            v.spent_units(),
            v.cap_units(),
            v.policy_pin(),
            v.authority_pin(),
            v.last_nonce(),
        )
    };
    let retained = observe(guard.verified_velocity.as_ref().unwrap());
    assert_eq!((retained.1, retained.5), (30, 2));
    let replayed = replay_verified_velocity(guard.verified_velocity.as_ref().unwrap()).unwrap();
    assert_eq!(observe(&replayed), retained);

    let state = recorded_state(&guard);
    for (cap, spend, nonce) in [
        (50u128, 51u128, [5u8; 32]), // above the cap
        (50, 29, [5; 32]),           // below the recorded spend
        (50, 40, [3; 32]),           // burned nonce
        (20, 31, [5; 32]),           // a lower cap than the recorded spend
    ] {
        assert!(
            guard
                .record_approved_intent(cap, spend, nonce, [6; 32])
                .is_err()
        );
        assert_eq!(recorded_state(&guard), state);
        assert_eq!(observe(guard.verified_velocity.as_ref().unwrap()), retained);
    }
    guard
        .record_approved_intent(50, 50, [5; 32], [6; 32])
        .unwrap();
    let v = guard.verified_velocity.as_ref().unwrap();
    assert_eq!((v.spent_units(), v.last_nonce()), (50, 3));
}
