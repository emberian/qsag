use qsag_cred::blind_vc::{holder_prepare_blind_issuance, verify_blind_issuance_request};

#[test]
fn seed_opening_roundtrip_tampering_and_schema_substitution() {
    let attrs = [840, 1994, 3];
    let (mut request, _) =
        holder_prepare_blind_issuance(42, &attrs, [1; 32], 7, [2; 32], [3; 32]).unwrap();
    assert_eq!(request.opened_reps.len(), 438);
    assert!(verify_blind_issuance_request(&request, &attrs, 42));
    // The report's holder-chosen schema must not be accepted under issuer policy.
    assert!(!verify_blind_issuance_request(&request, &attrs, 43));
    request.schema_id = 43;
    assert!(!verify_blind_issuance_request(&request, &attrs, 43));
    request.schema_id = 42;
    request.opened_reps[0].gate_outs_e[0] ^= 1;
    assert!(!verify_blind_issuance_request(&request, &attrs, 42));
}
