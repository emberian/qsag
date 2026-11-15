//! Post-quantum addresses, a conjunctive hybrid identity, and a custody policy release gate
//! (`qsag-addr`, `qsag-policy`, `qsag-core`).
//!
//! ```bash
//! cargo run --release -p qsag-cli --example pq_address_and_policy
//! ```
//!
//! 1. Derives a Bech32m address for an SLH-DSA key, round-trips it, and shows that a legacy
//!    checksum and a single changed character are refused.
//! 2. Derives a hybrid classical + post-quantum identity; keys of the wrong length or encoding
//!    are refused before anything is hashed.
//! 3. Builds a custody policy, shows a refused transfer, then runs the four-round committed MAC
//!    barrier among three approvers and checks that each release token is bound to exactly the
//!    approved signing request.

#[allow(dead_code)]
#[path = "../src/dealerless_ceremony.rs"]
mod dealerless_ceremony;

use qsag_accel::keccak::cshake256_framed_32;
use qsag_addr::{
    AddrError, AddressVersion, HybridComponent, HybridPinnedEnvelope, HybridSuiteSpec,
    KeyIdentityKind, QsagAddress, WitnessSuiteTag,
};
use qsag_core::fips205::{Fips205Params, slh_keygen_from_seed};
use qsag_policy::{
    PolicyViolation, QuorumTierRule, SigningPayloadBinding, TransactionIntent, TransactionPolicy,
};

fn main() {
    println!("=== 1. Bech32m address of an SLH-DSA-SHAKE-128s key ===");
    let params = Fips205Params::SLH_DSA_SHAKE_128S;
    let (_sk, pk) =
        slh_keygen_from_seed(&params, b"example treasury key seed").expect("valid parameters");
    let treasury = QsagAddress::from_pubkey_cshake256(
        "qsp",
        WitnessSuiteTag::SlhDsa128s,
        KeyIdentityKind::SingleOrThreshold,
        &pk.to_bytes(),
    )
    .expect("valid human-readable part");
    let encoded = treasury
        .encode()
        .expect("address fits the Bech32m length bound");
    assert_eq!(
        QsagAddress::decode_for_hrp(&encoded, "qsp"),
        Ok(treasury.clone())
    );
    let mut corrupted = encoded.clone().into_bytes();
    let last = corrupted.len() - 1;
    corrupted[last] = if corrupted[last] == b'q' { b'p' } else { b'q' };
    assert!(QsagAddress::decode(core::str::from_utf8(&corrupted).unwrap()).is_err());
    assert_eq!(
        QsagAddress::decode("A12UEL5L"),
        Err(AddrError::LegacyBech32Rejected)
    );
    println!("  [ok] {encoded}");

    println!("\n=== 2. Hybrid secp256k1 + ML-DSA-44 identity ===");
    let spec =
        HybridSuiteSpec::for_suite(WitnessSuiteTag::HybridSecp256k1MlDsa44).expect("hybrid suite");
    let mut classical_pk = vec![0x5A; spec.classical.public_key_len()];
    classical_pk[0] = 0x02;
    let pq_pk = vec![0xA5; spec.pq.public_key_len()];
    spec.validate_public_keys(&classical_pk, &pq_pk)
        .expect("exact lengths and encodings");
    let id_commit = HybridPinnedEnvelope::compute_id_commit(
        &spec,
        &HybridPinnedEnvelope::hash_classical_pk(&spec, &classical_pk),
        &HybridPinnedEnvelope::hash_pq_pk(&spec, &pq_pk),
    );
    let hybrid = QsagAddress::from_pubkey_cshake256(
        "qsp",
        spec.suite_tag,
        KeyIdentityKind::HybridConjunctive,
        &id_commit,
    )
    .and_then(|a| a.encode())
    .expect("hybrid address");
    assert_eq!(
        spec.validate_public_keys(&classical_pk[..32], &pq_pk),
        Err(AddrError::HybridMalformedComponent(
            HybridComponent::ClassicalPublicKey
        ))
    );
    assert_eq!(
        spec.validate_public_keys(&classical_pk, &[0xA5; 1952]),
        Err(AddrError::HybridMalformedComponent(
            HybridComponent::PqPublicKey
        ))
    );
    assert_eq!(
        HybridSuiteSpec::for_suite(WitnessSuiteTag::SlhDsa128s).map(|_| ()),
        Err(AddrError::HybridUnsupportedSuite(0x0201))
    );
    // The same identity under the algebraic (Poseidon2) commitment is a different address.
    let algebraic = QsagAddress::from_pubkey_poseidon2(
        "qsp",
        spec.suite_tag,
        KeyIdentityKind::HybridConjunctive,
        &id_commit,
    )
    .expect("hybrid address");
    assert_eq!(algebraic.version, AddressVersion::V2Poseidon2);
    assert_ne!(algebraic.encode().expect("address"), hybrid);
    println!("  [ok] {hybrid}");

    println!("\n=== 3. Custody policy and signing release tokens ===");
    let policy = TransactionPolicy {
        chain_id: 1,
        pinned_suite: WitnessSuiteTag::SlhDsa128s,
        recipient_allowlist: vec![treasury.commitment_256],
        max_single_tx_amount: 1_000_000,
        velocity_window_cap: 5_000_000,
        valid_not_before_secs: 1_700_000_000,
        valid_not_after_secs: 1_800_000_000,
        forbid_initiator_self_approval: true,
        hardware_guardian_party: Some(50),
        quorum_tiers: vec![
            QuorumTierRule {
                max_amount_units: 10_000,
                min_approvers: 2,
                require_hardware_guardian: false,
            },
            QuorumTierRule {
                max_amount_units: 1_000_000,
                min_approvers: 3,
                require_hardware_guardian: true,
            },
        ],
    };
    let key_id = cshake256_framed_32(b"QSAG.POLICY.KEY.V1", &[&pk.to_bytes()]);
    let (payload, ctx, session, now) = (
        b"transfer 250000 units".as_slice(),
        b"custody:prod".as_slice(),
        [0x77; 32],
        1_750_000_000,
    );
    let request = |approvers: &[u16]| {
        TransactionIntent::builder(1, WitnessSuiteTag::SlhDsa128s, treasury.clone(), 250_000)
            .rolling_window(100_000, [0x33; 32])
            .timestamp_secs(now)
            .initiator_and_approvers(10, approvers)
            .bind_signing_payload(
                &SigningPayloadBinding {
                    key_id,
                    payload,
                    ctx,
                    session_id: session,
                    policy_revision: 1,
                    quorum: approvers,
                    authority_pk: [0x5A; 32],
                },
                &policy,
            )
    };
    // A 250,000-unit transfer needs the hardware guardian (party 50) among three approvers.
    assert_eq!(
        request(&[20, 30, 40]).err(),
        Some(PolicyViolation::MissingHardwareGuardian)
    );
    let quorum = [20u16, 30, 50];
    let (mut intent, _) = request(&quorum).expect("the policy approves this transfer");
    let all_guards =
        dealerless_ceremony::provision_distributed_policy_guards([0x99; 32], &[10, 20, 30, 40, 50])
            .expect("distributed policy guard ceremony");
    let signing_bytes = all_guards
        .iter()
        .find(|g| g.party_id == 10)
        .unwrap()
        .authenticate_initiated_intent(&policy, &mut intent)
        .expect("initiator authenticates intent");
    let mut guards: Vec<_> = all_guards
        .into_iter()
        .filter(|g| quorum.contains(&g.party_id))
        .collect();
    let (mut states, mut commits) = (Vec::new(), Vec::new());
    for guard in &mut guards {
        let (state, commit) = guard
            .round1_commit_intent(&policy, &intent, session, now, 100_000)
            .expect("each approver evaluates the policy itself");
        states.push(state);
        commits.push(commit);
    }
    let (mut states2, mut opens) = (Vec::new(), Vec::new());
    for (state, guard) in states.into_iter().zip(&mut guards) {
        let (state, open) = state.round2_open_delta(guard, &commits).expect("round 2");
        states2.push(state);
        opens.push(open);
    }
    let (mut states3, mut sigma_commits) = (Vec::new(), Vec::new());
    for (state, guard) in states2.into_iter().zip(&mut guards) {
        let (state, commit) = state.round3_commit_sigma(guard, &opens).expect("round 3");
        states3.push(state);
        sigma_commits.push(commit);
    }
    let (mut states4, mut sigma_opens) = (Vec::new(), Vec::new());
    for (state, guard) in states3.into_iter().zip(&mut guards) {
        let (state, open) = state
            .round4_open_sigma(guard, &sigma_commits)
            .expect("round 4");
        states4.push(state);
        sigma_opens.push(open);
    }
    for (state, guard) in states4.into_iter().zip(&mut guards) {
        let token = state
            .finalize(guard, &sigma_opens)
            .expect("MAC barrier passes");
        assert!(token.matches_signing(&key_id, &signing_bytes, ctx, &quorum));
        assert!(!token.matches_signing(&key_id, b"another request", ctx, &quorum));
        assert!(!token.matches_signing(&key_id, &signing_bytes, ctx, &[20, 30, 40]));
    }
    println!("  [ok] 3 release tokens minted, each bound to the approved request only");
}
