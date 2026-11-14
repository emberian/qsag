use qsag_verified::tower::*;

fn valid_batch() -> (BdozCommittedBatchOpening2Lane, [BdozWireOpening2Lane; 1]) {
    let item = BdozWireOpening2Lane {
        opened_value: Gf256(3),
        chal_weight: Tower128(1),
        key_lanes: [Tower128(5), Tower128(7)],
    };
    let masked = Tower128(3 ^ 11);
    let macs = [
        tower128_add(Tower128(5 ^ 13), tower128_mul(Tower128(17), masked)),
        tower128_add(Tower128(7 ^ 19), tower128_mul(Tower128(23), masked)),
    ];
    let batch = BdozCommittedBatchOpening2Lane {
        session_id: [42; 32],
        round_id: 9,
        mask_value: Tower128(11),
        mask_key_lanes: [Tower128(13), Tower128(19)],
        peer_masked_mac_lanes: macs,
        open_nonce: [29; 32],
        tag_commitment: bdoz_commit_masked_tag(&[42; 32], 9, masked, macs, &[29; 32]),
    };
    (batch, [item])
}

fn guard() -> BdozOpeningGuard2Lane {
    BdozOpeningGuard2Lane::new([Tower128(17), Tower128(23)], [42; 32], 9)
}

#[test]
fn successful_opening_is_consumed() {
    let (batch, items) = valid_batch();
    let (spent, accepted) = guard().verify_once(&batch, &items);
    assert!(accepted && spent.is_consumed());
    let (spent, replay) = spent.verify_once(&batch, &items);
    assert!(!replay && spent.is_consumed());
}

#[test]
fn failed_or_wrong_context_attempt_cannot_retry() {
    for variant in 0..5 {
        let (valid, items) = valid_batch();
        let (mut bad, _) = valid_batch();
        match variant {
            0 => bad.session_id[0] ^= 1,
            1 => bad.round_id += 1,
            2 => bad.tag_commitment[0] ^= 1,
            3 => bad.peer_masked_mac_lanes[1].0 ^= 1,
            _ => {}
        }
        let slice = if variant == 4 { &[][..] } else { &items[..] };
        let (spent, accepted) = guard().verify_once(&bad, slice);
        assert!(!accepted && spent.is_consumed());
        let (spent, retried) = spent.verify_once(&valid, &items);
        assert!(!retried && spent.is_consumed());
    }
}
