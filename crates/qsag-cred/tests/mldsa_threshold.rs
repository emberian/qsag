//! The threshold ML-DSA-44 protocol through the default public API: three
//! custodians in three threads, no feature flags, standard verification.
use qsag_cred::{
    MlDsaLevel, MpcTransport, MpcTransportError, NonceBurnPersistence, RoundInbox, RoundInfo,
    ThresholdMlDsaDkgConfig, ThresholdMlDsaError, ThresholdSignSession, ml_dsa_keygen_from_seed,
    ml_dsa_sign_deterministic, ml_dsa_verify, threshold_mldsa_dkg_party, threshold_sign_mldsa_party,
};
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
                private: rows.iter().map(|row| row.as_ref().unwrap().0[self.me].clone()).collect(),
                broadcast: rows.iter().map(|row| row.as_ref().unwrap().1.clone()).collect(),
            }
        };
        self.network.barrier.wait();
        Ok(inbox)
    }
}

fn run<S: Send, R: Send>(states: Vec<S>, f: impl Fn(usize, S, &mut Endpoint) -> R + Sync) -> Vec<R> {
    let parties = states.len();
    let network = Arc::new(Network { barrier: Barrier::new(parties), rows: Mutex::new(vec![None; parties]) });
    std::thread::scope(|scope| {
        let handles: Vec<_> = states
            .into_iter()
            .enumerate()
            .map(|(me, state)| {
                let mut endpoint = Endpoint { me, network: network.clone() };
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
        let request = ThresholdSignSession { session_id: [session; 32], quorum: vec![7, 8, 9] };
        let states: Vec<_> = shares.iter_mut().zip(burns.iter_mut()).collect();
        let outputs = run(states, |me, (share, burn), net| {
            threshold_sign_mldsa_party(share, &request, b"integration", b"", &[session + me as u8; 32], burn, net)
        });
        for output in outputs {
            let output = output.expect("signing is enabled by default");
            assert!(ml_dsa_verify(MlDsaLevel::MlDsa44, &pk, b"integration", b"", &output.signature));
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
    let request = ThresholdSignSession { session_id: [9; 32], quorum: vec![1, 2] };
    let network = Arc::new(Network { barrier: Barrier::new(1), rows: Mutex::new(vec![None; 1]) });
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
    assert_eq!(error, ThresholdMlDsaError::QuorumTooSmall { have: 2, need: 3 });
}

#[test]
fn standard_fips204_remains_available() {
    for level in [MlDsaLevel::MlDsa44, MlDsaLevel::MlDsa65, MlDsaLevel::MlDsa87] {
        let (pk, sk) = ml_dsa_keygen_from_seed(level, &[3; 32]);
        let sig = ml_dsa_sign_deterministic(&sk, b"standard signing", b"").unwrap();
        assert!(ml_dsa_verify(level, &pk, b"standard signing", b"", &sig));
        assert!(!ml_dsa_verify(level, &pk, b"changed", b"", &sig));
    }
}
