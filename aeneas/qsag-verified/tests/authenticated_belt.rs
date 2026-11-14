use qsag_verified::{
    BeltAuthError, PantsGuardError, VerifiedBeltQuorumGuard, custodian_ack_tag, wal_receipt_tag,
};
const COMMIT: [u8; 32] = [9; 32];
const WAL: [u8; 32] = [8; 32];
const MSG: [u8; 32] = [7; 32];
fn keys() -> [[u8; 32]; 64] {
    let mut keys = [[0; 32]; 64];
    for (id, key) in keys.iter_mut().enumerate() {
        *key = [id as u8 + 1; 32];
    }
    keys
}
fn enrolled() -> VerifiedBeltQuorumGuard {
    match VerifiedBeltQuorumGuard::new_validated(3, 2, 1, 3, false, 10, 4, COMMIT, keys(), WAL) {
        Ok(g) => g,
        Err(e) => panic!("{e:?}"),
    }
}
fn bound() -> VerifiedBeltQuorumGuard {
    let receipt = [6; 32];
    let (g, result) = enrolled().propose_or_retry_epoch(
        10,
        MSG,
        receipt,
        wal_receipt_tag(&WAL, &COMMIT, 10, &MSG, &receipt),
    );
    assert_eq!(result, Ok(()));
    g
}
fn assert_count(g: &VerifiedBeltQuorumGuard) {
    assert_eq!(g.ack_count(), g.ack_bitmap().count_ones());
}
#[test]
fn duplicates_and_forgery_cannot_authorize() {
    let mut g = bound();
    for _ in 0..64 {
        let (next, result) = g.record_custodian_ack(
            10,
            MSG,
            0,
            custodian_ack_tag(&keys()[0], &COMMIT, 10, &MSG, 0),
        );
        assert_eq!(result, Ok(1));
        g = next;
        assert_count(&g);
    }
    let (next, result) = g.authorize_shares(10, MSG);
    assert_eq!(
        result.err(),
        Some(BeltAuthError::Core(PantsGuardError::InsufficientQuorumAcks))
    );
    g = next;
    for (id, tag) in [
        (1, [0; 32]),
        (1, custodian_ack_tag(&keys()[0], &COMMIT, 10, &MSG, 1)),
        (1, custodian_ack_tag(&keys()[1], &COMMIT, 11, &MSG, 1)),
        (1, custodian_ack_tag(&keys()[1], &[0; 32], 10, &MSG, 1)),
    ] {
        let (next, result) = g.record_custodian_ack(10, MSG, id, tag);
        assert_eq!(result, Err(BeltAuthError::InvalidCustodianTag));
        g = next;
        assert_count(&g);
        assert_eq!(g.ack_count(), 1);
    }
    for id in [3, 64, 255] {
        let (next, result) = g.record_custodian_ack(10, MSG, id, [0; 32]);
        assert_eq!(result, Err(BeltAuthError::CustodianOutOfRange));
        g = next;
        assert_count(&g);
    }
    for id in [1, 2] {
        let (next, result) = g.record_custodian_ack(
            10,
            MSG,
            id,
            custodian_ack_tag(&keys()[id as usize], &COMMIT, 10, &MSG, id),
        );
        assert_eq!(result, Ok(id as u32 + 1));
        g = next;
        assert_count(&g);
    }
    let (g, grant) = g.authorize_shares(10, MSG);
    assert_eq!(grant.unwrap().certified_acks, 3);
    assert_count(&g);
    let receipt = [6; 32];
    let (g, result) = g.propose_or_retry_epoch(
        11,
        MSG,
        receipt,
        wal_receipt_tag(&WAL, &COMMIT, 11, &MSG, &receipt),
    );
    assert_eq!(result, Ok(()));
    assert_count(&g);
    assert_eq!(g.ack_count(), 0);
}
#[test]
fn wal_receipt_is_bound_and_poison_sticky() {
    let receipt = [6; 32];
    let tag = wal_receipt_tag(&WAL, &COMMIT, 10, &MSG, &receipt);
    let (g, result) = enrolled().propose_or_retry_epoch(10, MSG, [5; 32], tag);
    assert_eq!(result, Err(BeltAuthError::InvalidWalReceipt));
    assert!(g.is_poisoned());
    assert_count(&g);
    let (g, result) = g.propose_or_retry_epoch(10, MSG, receipt, tag);
    assert_eq!(
        result,
        Err(BeltAuthError::Core(PantsGuardError::BeltGuardPoisoned))
    );
    assert_count(&g);
    assert!(
        VerifiedBeltQuorumGuard::new_validated(65, 1, 0, 65, false, 0, 0, COMMIT, keys(), WAL)
            .is_err()
    );
}
