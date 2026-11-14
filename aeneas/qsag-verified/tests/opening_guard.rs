use qsag_verified::ConsumingOpeningGuard2Lane;

const SESSION: [u8; 32] = [7; 32];
const BINDING: [u8; 32] = [9; 32];
const ROUND: u64 = 3;

fn folded(lanes: &[[u128; 2]]) -> ConsumingOpeningGuard2Lane {
    let mut guard = ConsumingOpeningGuard2Lane::new(SESSION, ROUND, BINDING, lanes.len() as u64);
    for (i, pair) in lanes.iter().enumerate() {
        let digest = [i as u8; 32];
        guard = guard.absorb_opening(&digest, &digest, *pair);
    }
    guard
}

const ZERO_SUM: [[u128; 2]; 3] = [[5, 1 << 127], [9, 3], [12, (1 << 127) | 3]];

#[test]
fn accepted_round_yields_one_permit_and_is_spent() {
    let (spent, permit) = folded(&ZERO_SUM).verify_once(&SESSION, ROUND, &BINDING);
    let permit = permit.expect("zero-sum committed round");
    assert_eq!(
        (permit.session_id(), permit.round_id(), permit.openings()),
        (SESSION, ROUND, 3)
    );
    assert!(spent.is_consumed());
    let (spent, replay) = spent.verify_once(&SESSION, ROUND, &BINDING);
    assert!(replay.is_none() && spent.is_consumed());
}

#[test]
fn every_rejection_spends_the_guard() {
    let wrong_session = folded(&ZERO_SUM).verify_once(&[8; 32], ROUND, &BINDING);
    let wrong_round = folded(&ZERO_SUM).verify_once(&SESSION, ROUND + 1, &BINDING);
    let wrong_binding = folded(&ZERO_SUM).verify_once(&SESSION, ROUND, &[0; 32]);
    let nonzero_lane0 = folded(&[[1, 0], [0, 0]]).verify_once(&SESSION, ROUND, &BINDING);
    let nonzero_lane1 = folded(&[[0, 2], [0, 0]]).verify_once(&SESSION, ROUND, &BINDING);
    let empty = folded(&[]).verify_once(&SESSION, ROUND, &BINDING);
    for (spent, permit) in [
        wrong_session,
        wrong_round,
        wrong_binding,
        nonzero_lane0,
        nonzero_lane1,
        empty,
    ] {
        assert!(permit.is_none() && spent.is_consumed());
        // A corrected request cannot reuse the spent guard.
        let (_, retry) = spent.verify_once(&SESSION, ROUND, &BINDING);
        assert!(retry.is_none());
    }
}

#[test]
fn commitment_mismatch_and_wrong_count_are_refused() {
    let guard = ConsumingOpeningGuard2Lane::new(SESSION, ROUND, BINDING, 2)
        .absorb_opening(&[1; 32], &[1; 32], [4, 4])
        .absorb_opening(&[2; 32], &[3; 32], [4, 4]);
    assert!(guard.verify_once(&SESSION, ROUND, &BINDING).1.is_none());

    let short = ConsumingOpeningGuard2Lane::new(SESSION, ROUND, BINDING, 2)
        .absorb_opening(&[1; 32], &[1; 32], [0, 0]);
    assert_eq!(short.absorbed(), 1);
    assert!(short.verify_once(&SESSION, ROUND, &BINDING).1.is_none());

    let long = ConsumingOpeningGuard2Lane::new(SESSION, ROUND, BINDING, 1)
        .absorb_opening(&[1; 32], &[1; 32], [6, 6])
        .absorb_opening(&[1; 32], &[1; 32], [6, 6]);
    assert!(long.verify_once(&SESSION, ROUND, &BINDING).1.is_none());
}

#[test]
fn spent_guard_ignores_later_openings() {
    let (spent, _) = folded(&[[1, 1]]).verify_once(&SESSION, ROUND, &BINDING);
    let spent = spent.absorb_opening(&[0; 32], &[0; 32], [1, 1]);
    assert!(spent.is_consumed() && spent.absorbed() == 1);
    assert!(spent.verify_once(&SESSION, ROUND, &BINDING).1.is_none());
}
