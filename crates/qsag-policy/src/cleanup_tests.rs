use super::*;
#[test]
fn cust06_staging_pool_isolates_unauthenticated_spam_and_enforces_self_mac() {
    let recipient = QsagAddress::from_pubkey_cshake256(
        "qsp",
        WitnessSuiteTag::MlDsa65,
        qsag_addr::KeyIdentityKind::SingleOrThreshold,
        b"cust06-recipient",
    )
    .unwrap();
    let policy = TransactionPolicy {
        chain_id: 1,
        pinned_suite: WitnessSuiteTag::MlDsa65,
        recipient_allowlist: alloc::vec![recipient.commitment_256],
        max_single_tx_amount: 100,
        velocity_window_cap: 10_000,
        valid_not_before_secs: 1,
        valid_not_after_secs: 1_000,
        forbid_initiator_self_approval: false,
        hardware_guardian_party: Some(2),
        quorum_tiers: alloc::vec![QuorumTierRule {
            max_amount_units: 100,
            min_approvers: 2,
            require_hardware_guardian: true,
        }],
    };
    let guards = trusted_dealer_setup_for_testing([0x77; 32], &[1, 2]);
    let mut pool = PendingIntentStagingPool::new(4);

    // 1. Unauthenticated spammer spoofing `initiator_party == 1` directly against guard 1
    //    (even when `forbid_initiator_self_approval == false`) is rejected with `UnauthenticatedInitiator`
    //    and consumes ZERO staging slots and ZERO committed replay slots!
    for i in 0..500u32 {
        let mut forged_nonce = [0u8; 32];
        forged_nonce[..4].copy_from_slice(&i.to_be_bytes());
        let forged_intent = TransactionIntent {
            chain_id: 1,
            suite: WitnessSuiteTag::MlDsa65,
            recipient: recipient.clone(),
            amount_units: 10,
            rolling_window_spent: 0,
            window_id: 0,
            nonce: forged_nonce,
            timestamp_secs: 10,
            initiator_party: 1,
            initiator_macs: Vec::new(),
            approver_parties: alloc::vec![1, 2],
            payload_digest: [0x11; 32],
            guard_authority_pk: [0x22; 32],
            rolling_window_accumulator: [0x33; 32],
            signing_key_id: [0x44; 32],
            policy_revision: 1,
            message_digest: [0; 32],
            signing_context_digest: [0x55; 32],
            session_id: forged_nonce,
            quorum_ids: alloc::vec![1, 2],
        };
        assert_eq!(
            pool.stage_authenticated_intent(&policy, &guards[0], &forged_intent, 10, 30),
            Err(PolicyViolation::UnauthenticatedInitiator)
        );
    }
    assert!(pool.is_empty());

    // 2. Authenticated pending proposals stage cleanly, expire after TTL without burning committed
    //    replay slots, and never evict committed replay nonces!
    for i in 0..4u8 {
        let mut valid_intent = TransactionIntent {
            chain_id: 1,
            suite: WitnessSuiteTag::MlDsa65,
            recipient: recipient.clone(),
            amount_units: 10,
            rolling_window_spent: 0,
            window_id: 0,
            nonce: [i + 1; 32],
            timestamp_secs: 10,
            initiator_party: 1,
            initiator_macs: Vec::new(),
            approver_parties: alloc::vec![1, 2],
            payload_digest: [0x11; 32],
            guard_authority_pk: [0x22; 32],
            rolling_window_accumulator: [0x33; 32],
            signing_key_id: [0x44; 32],
            policy_revision: 1,
            message_digest: [0; 32],
            signing_context_digest: [0x55; 32],
            session_id: [i + 0x81; 32],
            quorum_ids: alloc::vec![1, 2],
        };
        guards[0]
            .authenticate_initiated_intent(&policy, &mut valid_intent)
            .unwrap();
        pool.stage_authenticated_intent(&policy, &guards[0], &valid_intent, 10, 30)
            .unwrap();
        pool.complete_intent(&valid_intent.nonce, &valid_intent.session_id);
        pool.stage_authenticated_intent(&policy, &guards[1], &valid_intent, 10, 30)
            .unwrap();
    }
    assert_eq!(pool.len(), 4);
    // Advance past `10 + 30 = 40`: all 4 abandoned pending proposals expire without touching `guards[1]`.
    assert_eq!(pool.evict_expired(40), 4);
    assert!(pool.is_empty());
    assert!(!guards[1].is_nonce_burned(&[1; 32]));
}

#[test]
fn cust06_monotone_replay_floor_compacts_without_unburning_and_survives_checkpoint() {
    let mut guards = trusted_dealer_setup_for_testing([0x99; 32], &[1, 2]);
    let guard = &mut guards[0];

    // Fill all 256 slots with monotone nonces `1..=256`, plus keep a high random nonce `[0xFF; 32]`.
    for i in 1..=255u32 {
        let mut n = [0u8; 32];
        n[..4].copy_from_slice(&i.to_be_bytes());
        guard
            .record_approved_intent(100_000, i as u128, n, n)
            .unwrap();
    }
    guard
        .record_approved_intent(100_000, 256, [0xFF; 32], [0xFF; 32])
        .unwrap();

    // Compact monotone floor up to `200`: nonces `<= 200` remain permanently burned via floor,
    // nonces `201..=255` and `[0xFF; 32]` remain explicitly retained, and 200 slots are freed!
    let mut floor200 = [0u8; 32];
    floor200[..4].copy_from_slice(&200u32.to_be_bytes());
    guard
        .compact_monotone_replay_floor(floor200, floor200)
        .unwrap();

    // Regressing the floor is rejected.
    let mut floor199 = [0u8; 32];
    floor199[..4].copy_from_slice(&199u32.to_be_bytes());
    assert_eq!(
        guard.compact_monotone_replay_floor(floor199, floor199),
        Err(PolicyViolation::IntentBindingMismatch)
    );

    // Floored nonces (`1`, `200`) AND retained high nonces (`[0xFF; 32]`) CANNOT replay!
    let mut n1 = [0u8; 32];
    n1[..4].copy_from_slice(&1u32.to_be_bytes());
    assert!(guard.is_nonce_burned(&n1));
    assert!(guard.is_nonce_burned(&floor200));
    assert!(guard.is_nonce_burned(&[0xFF; 32]));
    assert_eq!(
        guard.record_approved_intent(100_000, 257, n1, n1),
        Err(PolicyViolation::DuplicateIntentNonce)
    );

    // Subsequent new intents (> 256 total in the same window!) succeed AND preserve `min_nonce_watermark`.
    for i in 256..=320u32 {
        let mut n = [0u8; 32];
        n[..4].copy_from_slice(&i.to_be_bytes());
        guard
            .record_approved_intent(100_000, (i + 10) as u128, n, n)
            .unwrap();
    }
    assert!(guard.is_nonce_burned(&n1));

    // Durable checkpoint export + restore preserves the monotone floor and blocks floored replays.
    let snap = guard.export_durable_checkpoint(&[0xAB; 32], 11);
    let mut fresh_guards = trusted_dealer_setup_for_testing([0x99; 32], &[1, 2]);
    fresh_guards[0]
        .restore_from_durable_checkpoint(&snap, &[0xAB; 32], 11)
        .unwrap();
    assert!(fresh_guards[0].is_nonce_burned(&n1));
    assert!(fresh_guards[0].is_nonce_burned(&floor200));
    assert!(fresh_guards[0].is_nonce_burned(&[0xFF; 32]));
}

#[test]
fn capability_binding_distinguishes_complete_intents() {
    let (policy, intent) = crate::tests::phase_fixture(&[1, 2]);
    let digest = |i: &TransactionIntent| {
        capability_request_digest(&CapabilityRequest::from_policy_intent(
            &policy,
            i,
            1,
            intent.timestamp_secs,
        ))
    };
    for field in 0..3 {
        let mut changed = intent.clone();
        match field {
            0 => changed.nonce[0] ^= 1,
            1 => changed.session_id[0] ^= 1,
            _ => changed.payload_digest[0] ^= 1,
        }
        assert_ne!(intent.canonical_digest(), changed.canonical_digest());
        assert_ne!(
            digest(&intent),
            digest(&changed),
            "intent field {field} omitted"
        );
    }
}

#[test]
fn policy_engine_integrates_macaroon_discharges_and_pq_biscuits_before_bdoz_barrier() {
    let accel = qsag_accel::CpuReferenceBackend::new();
    let (policy, mut intent) = crate::tests::phase_fixture(&[1, 2]);
    intent.session_id = [0x71; 32];
    intent.nonce = [0x72; 32];
    let policy_digest = policy.canonical_digest();
    let signing_bytes = intent.to_canonical_signing_bytes(&policy_digest);
    intent.message_digest = cshake256_framed_32(b"QSAG.POLICY.MSG.V1", &[&signing_bytes]);

    let mut guards = crate::tests::raw_test_guards([0x44; 32], &[1, 2]);
    let engine = PolicyEngine::new(&policy, 0b0001);

    // 1. Attenuated SpongeMacaroon with 3P discharge: narrower MaxAmount(1) refuses BEFORE
    // consuming any BDOZ preprocessing slot!
    let root_key = [0xA1; 32];
    let third_key = [0xB2; 32];
    let mut denied_mac = SpongeMacaroon::issue(&root_key, [0x01; 32], policy_digest);
    denied_mac
        .attenuate(Caveat::MaxAmount(intent.amount_units.saturating_sub(1)))
        .unwrap();
    let verifier = MacaroonVerifier::new(&root_key, [0x01; 32], policy_digest);
    assert_eq!(
        engine
            .authorize_committed_barrier(
                &intent,
                intent.session_id,
                intent.timestamp_secs,
                Some(&mut CapabilityGate::Macaroon {
                    verifier: &verifier,
                    token: &denied_mac,
                    discharges: &[],
                }),
                &mut guards,
                &accel,
            )
            .err(),
        Some(PolicyViolation::CapabilityDenied(CapabilityError::Denied))
    );
    assert_eq!(guards[0].next_slot.get(), 0);

    let mut ok_mac = SpongeMacaroon::issue(&root_key, [0x01; 32], policy_digest);
    ok_mac
        .attenuate(Caveat::Resource(intent.recipient.commitment_256))
        .unwrap();
    ok_mac.attenuate(Caveat::Actions(0b0011)).unwrap();
    ok_mac
        .attenuate(Caveat::MaxAmount(intent.amount_units))
        .unwrap();
    ok_mac.attenuate(Caveat::ThirdParty([0xCC; 32])).unwrap();
    let mut discharge = SpongeMacaroon::issue_discharge(&third_key, [0xCC; 32], policy_digest);
    ok_mac.bind_discharge(&mut discharge).unwrap();
    let discharges = [Discharge {
        token: &discharge,
        root_key: &third_key,
    }];
    let release = engine
        .authorize_committed_barrier(
            &intent,
            intent.session_id,
            intent.timestamp_secs,
            Some(&mut CapabilityGate::Macaroon {
                verifier: &verifier,
                token: &ok_mac,
                discharges: &discharges,
            }),
            &mut guards,
            &accel,
        )
        .unwrap();
    // Macaroons remain reusable bearer grants; the barrier, not the grant,
    // binds the complete intent and rejects repeated executions.
    assert_eq!(release.intent_digest(), &intent.canonical_digest());
    assert_eq!(
        engine
            .authorize_committed_barrier(
                &intent,
                intent.session_id,
                intent.timestamp_secs,
                Some(&mut CapabilityGate::Macaroon {
                    verifier: &verifier,
                    token: &ok_mac,
                    discharges: &discharges,
                }),
                &mut guards,
                &accel,
            )
            .err(),
        Some(PolicyViolation::DuplicateIntentNonce),
    );
    let party_tokens = release.into_quorum_party_tokens();
    assert_eq!(party_tokens.len(), 2);
    // The same macaroon authorizes a different intent: nothing in the engine treats
    // it as spent. What stops a second execution is the intent's own nonce above.
    let mut next_intent = intent.clone();
    next_intent.session_id = [0x73; 32];
    next_intent.nonce = [0x74; 32];
    let next_bytes = next_intent.to_canonical_signing_bytes(&policy_digest);
    next_intent.message_digest = cshake256_framed_32(b"QSAG.POLICY.MSG.V1", &[&next_bytes]);
    let next_release = engine
        .authorize_committed_barrier(
            &next_intent,
            next_intent.session_id,
            next_intent.timestamp_secs,
            Some(&mut CapabilityGate::Macaroon {
                verifier: &verifier,
                token: &ok_mac,
                discharges: &discharges,
            }),
            &mut guards,
            &accel,
        )
        .unwrap();
    assert_eq!(
        next_release.intent_digest(),
        &next_intent.canonical_digest()
    );
    drop(next_release);

    // 2. Ephemeral Compact1122 PqBiscuit 2-hop delegation chain + PoP seal gates BDOZ barrier!
    let dp = qsag_fts::FrontierDpTable::build(qsag_fts::FrontierFtsProfile::Compact1122);
    let mut auth = PqBiscuitAuthorityKey::keygen([0xD1; 32], [0xD2; 32], 1, &accel).unwrap();
    let auth_pk = *auth.public_key();
    let mut intent2 = intent.clone();
    intent2.session_id = [0x81; 32];
    intent2.nonce = [0x82; 32];
    intent2.rolling_window_spent = intent.amount_units;
    let sb2 = intent2.to_canonical_signing_bytes(&policy_digest);
    intent2.message_digest = cshake256_framed_32(b"QSAG.POLICY.MSG.V1", &[&sb2]);

    let (b0, s1) = auth
        .mint(
            &dp,
            [0x91; 32],
            policy_digest,
            &[Caveat::Resource(intent2.recipient.commitment_256)],
            [0x92; 32],
            &[0x93; 32],
            &accel,
        )
        .unwrap();
    let (b1, s2) = s1
        .attenuate(
            &b0,
            &dp,
            &[
                Caveat::Actions(0b0001),
                Caveat::MaxAmount(intent2.amount_units),
            ],
            [0x94; 32],
            &[0x95; 32],
            &accel,
        )
        .unwrap();
    let req2 =
        CapabilityRequest::from_policy_intent(&policy, &intent2, 0b0001, intent2.timestamp_secs);
    let b_sealed = s2.seal(&b1, &dp, Some(&req2), &[0x96; 32], &accel).unwrap();
    let release2 = engine
        .authorize_committed_barrier(
            &intent2,
            intent2.session_id,
            intent2.timestamp_secs,
            Some(&mut CapabilityGate::Biscuit {
                authority_pk: &auth_pk,
                dp: &dp,
                token: &b_sealed,
                domain: &mut MemorySealConsumptionStore::new(16),
            }),
            &mut guards,
            &accel,
        )
        .unwrap();
    assert_eq!(release2.quorum_ids(), &[1, 2]);
}
