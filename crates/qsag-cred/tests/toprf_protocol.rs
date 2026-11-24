//! Threshold TOPRF public API from an external consumer.
use qsag_cred::voprf::{
    CounterStore, Error, SpdzConfig, SpdzPublic, SpdzServer, SpdzSession, spdz_blind, spdz_dkg,
};

#[derive(Default)]
struct Store(Option<u64>);
impl CounterStore for Store {
    fn high_water(&self) -> Result<Option<u64>, Error> {
        Ok(self.0)
    }
    fn reserve(&mut self, _: &[u8; 32], _: usize, counter: u64, _: usize) -> Result<(), Error> {
        if self.0.is_some_and(|prev| prev >= counter) {
            return Err(Error::Counter);
        }
        self.0 = Some(counter);
        Ok(())
    }
}

#[test]
fn restored_nonprefix_quorum_evaluates_once() {
    let mut servers = spdz_dkg(
        SpdzConfig::new(2, 3).unwrap(),
        [1; 32],
        &[[2; 32], [3; 32], [4; 32]],
    )
    .unwrap();
    let public = SpdzPublic::from_bytes(&servers[0].public().to_bytes()).unwrap();
    let mut last =
        SpdzServer::from_secret_bytes(&servers[2].to_secret_bytes(), &public, 2).unwrap();
    let mut members = [&mut servers[0], &mut last];
    let mut first_store = Store::default();
    let mut last_store = Store::default();
    let mut stores: [&mut dyn CounterStore; 2] = [&mut first_store, &mut last_store];
    let session = [5; 32];
    let entropy = [[7; 32], [8; 32]];
    let (round, grants) =
        SpdzSession::begin(&mut members, &mut stores, session, 1, 1, &entropy).unwrap();
    let input = b"threshold credential";
    let (client, request) = spdz_blind(&public, &[input], session, 1, &grants).unwrap();
    let result = client.finalize(&round.evaluate(&request).unwrap()).unwrap();
    assert_eq!(
        result.value_for(&public.public_key(), input),
        Some(result.values()[0])
    );
    assert!(matches!(
        SpdzSession::begin(&mut members, &mut stores, session, 1, 1, &entropy),
        Err(Error::Counter)
    ));
}
