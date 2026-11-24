use super::*;

#[test]
fn private_rng_batched_refill_matches_scalar_stream_and_rekey() {
    fn scalar_stream(seed: &[u8; 32], counter: u64, blocks: usize) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(136 * blocks);
        for block in 0..blocks {
            let mut state = [0u64; 25];
            state[0] = u64::from_le_bytes(*b"QSAG.PRG");
            state[1] = u64::from_le_bytes(*b"NG.BLK\x01\x00");
            for i in 0..4 {
                state[2 + i] = u64::from_le_bytes(core::array::from_fn(|j| seed[8 * i + j]));
            }
            state[6] = counter.wrapping_add(block as u64);
            state[7] = 0x1f;
            state[16] = 0x8000_0000_0000_0000;
            keccak_f1600(&mut state);
            for word in &state[..17] {
                bytes.extend_from_slice(&word.to_le_bytes());
            }
        }
        bytes
    }
    for counter in [0, u64::MAX - 16] {
        for chunk in [1, 8, 26, 135, 136, 137, 543, 544, 545, 1088] {
            let mut rng = PartyPrivateRng::from_seed([0x93; 32], b"batch-stream-test");
            rng.counter = counter;
            let expected = scalar_stream(&rng.seed, counter, 12);
            let mut actual = vec![0; expected.len()];
            for part in actual.chunks_mut(chunk) {
                rng.fill_bytes(part);
            }
            assert_eq!(actual, expected);
        }
    }
    // A rekey must discard every prefetched block, even after a partial read.
    for consumed in [0, 1, 135, 136, 513, 544] {
        let mut rng = PartyPrivateRng::from_seed([0x93; 32], b"batch-stream-test");
        let old = scalar_stream(&rng.seed, 0, 8);
        let mut discard = vec![0; consumed];
        rng.fill_bytes(&mut discard);
        let mut seed = [0; 32];
        HedgedTranscriptRng::derive(
            &rng.seed,
            0,
            &old[consumed..consumed + 32],
            b"rekey",
            &mut seed,
        );
        rng.hedge_transcript(b"rekey");
        let mut actual = vec![0; 1088];
        rng.fill_bytes(&mut actual);
        assert_eq!(actual, scalar_stream(&seed, 0, 8));
    }
}

#[test]
fn zero_entropy_randomizers_bind_messages() {
    use crate::fips205::fips205_prf_msg;
    let key = [0x51; 32];
    let entropy = [0; 32];
    let a = fips205_prf_msg(32, &key, &entropy, b"message one");
    let b = fips205_prf_msg(32, &key, &entropy, b"message two");
    assert_ne!(a.as_slice(), b.as_slice());
}

#[test]
fn restored_rng_new_message_changes_masks() {
    let mut a = PartyPrivateRng::from_seed([19; 32], b"test");
    let mut b = PartyPrivateRng::from_seed([19; 32], b"test");
    a.hedge_transcript(b"session/message one");
    b.hedge_transcript(b"session/message two");
    assert_ne!(a.next_bytes32(), b.next_bytes32());
    let mut a = HedgedTranscriptRng::new([7; 32], 0);
    let mut b = HedgedTranscriptRng::new([7; 32], 0);
    let (mut x, mut y) = ([0; 32], [0; 32]);
    a.fill_bytes(&[0; 32], b"one", &mut x).unwrap();
    b.fill_bytes(&[0; 32], b"two", &mut y).unwrap();
    assert_ne!(x, y);
    let mut exhausted = HedgedTranscriptRng::new([7; 32], u64::MAX);
    assert!(exhausted.fill_bytes(&[], &[], &mut x).is_err());
}

#[test]
fn test_party_coin_commit_state_matches_helper_and_rejects_tamper() {
    let sid = [0x42u8; 32];
    let phase = b"UNIT_SEPARATED_COIN";
    let transcript = [0x99u8; 32];
    let mut rngs_helper = [
        PartyPrivateRng::from_seed([0x11; 32], b"coin_p0"),
        PartyPrivateRng::from_seed([0x22; 32], b"coin_p1"),
        PartyPrivateRng::from_seed([0x33; 32], b"coin_p2"),
    ];
    let mut rngs_sep = [
        PartyPrivateRng::from_seed([0x11; 32], b"coin_p0"),
        PartyPrivateRng::from_seed([0x22; 32], b"coin_p1"),
        PartyPrivateRng::from_seed([0x33; 32], b"coin_p2"),
    ];

    let expected = run_commit_and_open_coin(&sid, phase, &transcript, &mut rngs_helper)
        .expect("honest coin helper");

    let states: Vec<PartyCoinCommitState> = rngs_sep
        .iter_mut()
        .enumerate()
        .map(|(p, rng)| PartyCoinCommitState::commit(p, &sid, phase, &transcript, rng))
        .collect();
    let locked_commits: Vec<[u8; 32]> = states.iter().map(|s| s.commitment()).collect();
    let openings: Vec<[u8; 32]> = states
        .into_iter()
        .map(|s| s.open_share(&locked_commits).expect("valid locked commit"))
        .collect();
    let derived =
        verify_and_combine_coin_openings(&sid, phase, &transcript, &locked_commits, &openings)
            .expect("honest wire openings");
    assert_eq!(derived, expected);

    let mut bad_openings = openings.clone();
    bad_openings[1][0] ^= 0x01;
    assert!(matches!(
        verify_and_combine_coin_openings(&sid, phase, &transcript, &locked_commits, &bad_openings,),
        Err(PreprocessError::CoinCommitMismatch { party_id: 1 })
    ));
}
