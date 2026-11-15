//! The threshold ML-DSA-44 protocol through the default public API: three
//! custodians in three threads, no feature flags, standard verification.
use qsag_cred::{
    MlDsaLevel, MpcTransport, MpcTransportError, NonceBurnPersistence, RoundInbox, RoundInfo,
    ThresholdMlDsaDkgConfig, ThresholdMlDsaError, ThresholdSignSession, ml_dsa_keygen_from_seed,
    ml_dsa_sign_deterministic, ml_dsa_verify, threshold_mldsa_dkg_party,
    threshold_mldsa_shamir_expand_party, threshold_sign_mldsa_party,
};
use qsag_cred::{ThresholdMlDsaSignerShare, ThresholdVerificationPack};
use std::sync::{Arc, Barrier, Mutex};

type Row = Option<(Vec<Vec<u8>>, Vec<u8>)>;
struct Network {
    barrier: Barrier,
    rows: Mutex<Vec<Row>>,
}
struct Endpoint {
    me: usize,
    network: Arc<Network>,
}
impl MpcTransport for Endpoint {
    fn exchange(
        &mut self,
        _: RoundInfo,
        private: Vec<Vec<u8>>,
        broadcast: Vec<u8>,
    ) -> Result<RoundInbox, MpcTransportError> {
        self.network.rows.lock().unwrap()[self.me] = Some((private, broadcast));
        self.network.barrier.wait();
        let inbox = {
            let rows = self.network.rows.lock().unwrap();
            RoundInbox {
                private: rows
                    .iter()
                    .map(|row| row.as_ref().unwrap().0[self.me].clone())
                    .collect(),
                broadcast: rows
                    .iter()
                    .map(|row| row.as_ref().unwrap().1.clone())
                    .collect(),
            }
        };
        self.network.barrier.wait();
        Ok(inbox)
    }
}

fn run<S: Send, R: Send>(
    states: Vec<S>,
    f: impl Fn(usize, S, &mut Endpoint) -> R + Sync,
) -> Vec<R> {
    let parties = states.len();
    let network = Arc::new(Network {
        barrier: Barrier::new(parties),
        rows: Mutex::new(vec![None; parties]),
    });
    std::thread::scope(|scope| {
        let handles: Vec<_> = states
            .into_iter()
            .enumerate()
            .map(|(me, state)| {
                let mut endpoint = Endpoint {
                    me,
                    network: network.clone(),
                };
                let f = &f;
                scope.spawn(move || f(me, state, &mut endpoint))
            })
            .collect();
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    })
}

struct Burn(Vec<u64>);
impl NonceBurnPersistence for Burn {
    fn reserve(&mut self, _: u16, epoch: u64, _: &[u8; 32], _: u32) -> bool {
        let fresh = !self.0.contains(&epoch);
        self.0.push(epoch);
        fresh
    }
}

#[test]
fn default_build_generates_a_key_and_signs_without_a_dealer() {
    let config = ThresholdMlDsaDkgConfig {
        level: MlDsaLevel::MlDsa44,
        threshold: 2,
        party_ids: vec![7, 8, 9],
        session_id: [0x21; 32],
    };
    let mut shares: Vec<_> = run(vec![7u16, 8, 9], |me, id, net| {
        threshold_mldsa_dkg_party(&config, id, &[me as u8 + 1; 32], net)
    })
    .into_iter()
    .map(|share| share.expect("key generation is enabled by default"))
    .collect();
    let pk = shares[0].verification_pack().pk_bytes.clone();
    assert!(shares.iter().all(|s| s.verification_pack().pk_bytes == pk));

    // Two sessions on the same key: attempt epochs keep increasing.
    let mut burns: Vec<Burn> = (0..3).map(|_| Burn(Vec::new())).collect();
    for session in [1u8, 2] {
        let request = ThresholdSignSession {
            session_id: [session; 32],
            quorum: vec![7, 8, 9],
        };
        let states: Vec<_> = shares.iter_mut().zip(burns.iter_mut()).collect();
        let outputs = run(states, |me, (share, burn), net| {
            threshold_sign_mldsa_party(
                share,
                &request,
                b"integration",
                b"",
                &[session + me as u8; 32],
                burn,
                net,
            )
        });
        for output in outputs {
            let output = output.expect("signing is enabled by default");
            assert!(ml_dsa_verify(
                MlDsaLevel::MlDsa44,
                &pk,
                b"integration",
                b"",
                &output.signature
            ));
        }
    }
}

#[test]
fn two_custodians_cannot_run_the_three_party_rejection_test() {
    let config = ThresholdMlDsaDkgConfig {
        level: MlDsaLevel::MlDsa44,
        threshold: 2,
        party_ids: vec![1, 2, 3],
        session_id: [0x22; 32],
    };
    let mut shares: Vec<_> = run(vec![1u16, 2, 3], |me, id, net| {
        threshold_mldsa_dkg_party(&config, id, &[me as u8 + 40; 32], net)
    })
    .into_iter()
    .map(Result::unwrap)
    .collect();
    let request = ThresholdSignSession {
        session_id: [9; 32],
        quorum: vec![1, 2],
    };
    let network = Arc::new(Network {
        barrier: Barrier::new(1),
        rows: Mutex::new(vec![None; 1]),
    });
    let mut endpoint = Endpoint { me: 0, network };
    let error = threshold_sign_mldsa_party(
        &mut shares[0],
        &request,
        b"m",
        b"",
        &[0; 32],
        &mut Burn(Vec::new()),
        &mut endpoint,
    )
    .unwrap_err();
    assert_eq!(
        error,
        ThresholdMlDsaError::QuorumTooSmall { have: 2, need: 3 }
    );
}

#[test]
fn standard_fips204_remains_available() {
    for level in [
        MlDsaLevel::MlDsa44,
        MlDsaLevel::MlDsa65,
        MlDsaLevel::MlDsa87,
    ] {
        let (pk, sk) = ml_dsa_keygen_from_seed(level, &[3; 32]);
        let sig = ml_dsa_sign_deterministic(&sk, b"standard signing", b"").unwrap();
        assert!(ml_dsa_verify(level, &pk, b"standard signing", b"", &sig));
        assert!(!ml_dsa_verify(level, &pk, b"changed", b"", &sig));
    }
}

fn sign_with(
    shares: &mut [ThresholdMlDsaSignerShare],
    quorum: &[u16],
    session: u8,
) -> Vec<Result<Vec<u8>, ThresholdMlDsaError>> {
    let request = ThresholdSignSession {
        session_id: [session; 32],
        quorum: quorum.to_vec(),
    };
    let states: Vec<_> = shares
        .iter_mut()
        .filter(|share| quorum.contains(&share.party_id()))
        .map(|share| (share, Burn(Vec::new())))
        .collect();
    run(states, |me, (share, mut burn), net| {
        threshold_sign_mldsa_party(
            share,
            &request,
            b"eighteen custodians",
            b"",
            &[session ^ (me as u8 + 1); 32],
            &mut burn,
            net,
        )
        .map(|output| output.signature)
    })
}

/// The Shamir ceremony: the sampling committee generates the key, then every
/// custodian takes part in the expansion.
fn shamir_ceremony(config: &ThresholdMlDsaDkgConfig) -> Vec<ThresholdMlDsaSignerShare> {
    let committee = config.shamir_committee().unwrap();
    let sampled: Vec<_> = run(committee.party_ids.clone(), |me, id, net| {
        threshold_mldsa_dkg_party(&committee, id, &[me as u8 + 0x30; 32], net)
    })
    .into_iter()
    .map(|share| Some(share.expect("committee key generation")))
    .collect();
    let states: Vec<_> = config
        .party_ids
        .iter()
        .copied()
        .zip(sampled.into_iter().chain(std::iter::repeat_with(|| None)))
        .collect();
    run(states, |me, (id, share), net| {
        threshold_mldsa_shamir_expand_party(config, id, share, &[me as u8 + 0x50; 32], net)
    })
    .into_iter()
    .map(|share| share.expect("Shamir expansion"))
    .collect()
}

/// Eighteen custodians with privacy threshold three: the key is Shamir-shared, and
/// any five custodians sign a standard FIPS 204 signature.
#[test]
fn eighteen_custodians_hold_shamir_shares_and_any_five_sign() {
    let ids: Vec<u16> = (100..118).collect();
    let config = ThresholdMlDsaDkgConfig {
        level: MlDsaLevel::MlDsa44,
        threshold: 3,
        party_ids: ids.clone(),
        session_id: [0x44; 32],
    };
    // The replicated ceremony refuses the committee before any network round.
    assert!(matches!(
        config.validate(),
        Err(ThresholdMlDsaError::Mpc(_))
    ));
    assert_eq!(config.shamir_committee().unwrap().party_ids, ids[..5]);
    let mut shares = shamir_ceremony(&config);
    let pack = shares[0].verification_pack().clone();
    assert_eq!(pack.party_ids, ids);
    assert!(shares.iter().all(|s| s.is_shamir() && s.verification_pack() == &pack));
    assert_eq!(
        ThresholdVerificationPack::from_bytes(&pack.to_bytes()).unwrap(),
        pack
    );

    // Four custodians are below the 2t - 1 quorum.
    for result in sign_with(&mut shares, &[101, 107, 112, 117], 1) {
        assert_eq!(
            result,
            Err(ThresholdMlDsaError::QuorumTooSmall { have: 4, need: 5 })
        );
    }

    // Five custodians, four of them outside the sampling committee.
    let quorum = [103u16, 106, 109, 113, 117];
    let signatures = sign_with(&mut shares, &quorum, 2);
    for signature in &signatures {
        let signature = signature.as_ref().expect("threshold signing");
        assert!(ml_dsa_verify(
            MlDsaLevel::MlDsa44,
            &pack.pk_bytes,
            b"eighteen custodians",
            b"",
            signature
        ));
    }

    // A custodian that substitutes its share is caught before any mask is sampled:
    // every honest custodian aborts with the same verdict.
    let at = shares.iter().position(|s| s.party_id() == 109).unwrap();
    let mut bytes = shares[at].to_shamir_bytes().unwrap();
    let restored =
        ThresholdMlDsaSignerShare::from_shamir_bytes(&bytes, pack.clone(), 109).unwrap();
    assert_eq!(restored.to_shamir_bytes().unwrap(), bytes);
    bytes[18 + 3 * 700] ^= 1;
    shares[at] = ThresholdMlDsaSignerShare::from_shamir_bytes(&bytes, pack.clone(), 109).unwrap();
    for result in sign_with(&mut shares, &quorum, 3) {
        assert_eq!(result, Err(ThresholdMlDsaError::KeyShareInconsistent));
    }
}

/// The committee bound itself: sixty-four custodians, and three of them sign.
#[test]
fn sixty_four_custodians_enroll_and_three_sign() {
    let config = ThresholdMlDsaDkgConfig {
        level: MlDsaLevel::MlDsa44,
        threshold: 2,
        party_ids: (1..=64).collect(),
        session_id: [0x64; 32],
    };
    let mut shares = shamir_ceremony(&config);
    assert_eq!(shares.len(), 64);
    let pk = shares[0].verification_pack().pk_bytes.clone();
    for signature in sign_with(&mut shares, &[6, 41, 64], 4) {
        assert!(ml_dsa_verify(
            MlDsaLevel::MlDsa44,
            &pk,
            b"eighteen custodians",
            b"",
            &signature.expect("threshold signing")
        ));
    }
    // Sixty-five custodians, or a quorum above the session engine, are refused.
    let too_many = ThresholdMlDsaDkgConfig {
        party_ids: (1..=65).collect(),
        ..config.clone()
    };
    assert!(too_many.validate_shamir().is_err());
    let too_wide = ThresholdMlDsaDkgConfig {
        threshold: 9,
        ..config
    };
    assert!(matches!(
        too_wide.validate_shamir(),
        Err(ThresholdMlDsaError::Mpc(_))
    ));
}
