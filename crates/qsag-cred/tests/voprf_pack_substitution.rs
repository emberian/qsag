use qsag_cred::voprf::{Config, CounterStore, Error, PublicKey, Server, Transport, blind, dkg};
use std::sync::{Arc, Barrier, Mutex};

type Rows = [Option<([u8; 32], [Vec<u8>; 5])>; 5];
struct Network {
    barrier: Barrier,
    rows: Mutex<Rows>,
}
struct Endpoint {
    party: usize,
    network: Arc<Network>,
}
impl Transport for Endpoint {
    fn exchange(&mut self, phase: [u8; 32], outgoing: [Vec<u8>; 5]) -> Result<[Vec<u8>; 5], Error> {
        self.network.rows.lock().unwrap()[self.party] = Some((phase, outgoing));
        self.network.barrier.wait();
        let result = {
            let mut rows = self.network.rows.lock().unwrap();
            assert!(rows.iter().all(|row| row.as_ref().unwrap().0 == phase));
            core::array::from_fn(|sender| {
                std::mem::take(&mut rows[sender].as_mut().unwrap().1[self.party])
            })
        };
        self.network.barrier.wait();
        Ok(result)
    }
    fn broadcast(&mut self, phase: [u8; 32], message: Vec<u8>) -> Result<[Vec<u8>; 5], Error> {
        self.exchange(phase, core::array::from_fn(|_| message.clone()))
    }
}

#[derive(Default)]
struct Store {
    last: Option<u64>,
}
impl CounterStore for Store {
    fn high_water(&self) -> Result<Option<u64>, Error> {
        Ok(self.last)
    }
    fn reserve(&mut self, _: &[u8; 32], _: usize, counter: u64, _: usize) -> Result<(), Error> {
        if self.last.is_some_and(|v| counter <= v) {
            return Err(Error::Counter);
        }
        self.last = Some(counter);
        Ok(())
    }
}

fn setup_cluster(session: [u8; 32], seed_tag: u8) -> (Vec<Server>, [Endpoint; 5]) {
    let net = Arc::new(Network {
        barrier: Barrier::new(5),
        rows: Mutex::new(core::array::from_fn(|_| None)),
    });
    let endpoints: [Endpoint; 5] = core::array::from_fn(|party| Endpoint {
        party,
        network: net.clone(),
    });
    let mut pairs = std::thread::scope(|scope| {
        let handles: Vec<_> = endpoints
            .into_iter()
            .enumerate()
            .map(|(party, mut ep)| {
                scope.spawn(move || {
                    let srv = dkg(
                        Config::new(2, 5).unwrap(),
                        party,
                        session,
                        [seed_tag.wrapping_add(party as u8); 32],
                        &mut ep,
                    )
                    .unwrap();
                    (srv, ep)
                })
            })
            .collect();
        handles
            .into_iter()
            .map(|h| h.join().unwrap())
            .collect::<Vec<_>>()
    });
    let arr: [(Server, Endpoint); 5] = std::array::from_fn(|_| pairs.remove(0));
    let (servers, eps): (Vec<_>, Vec<_>) = arr.into_iter().unzip();
    (servers, eps.try_into().ok().unwrap())
}

#[test]
fn exact_nonce_extraction_pack_substitution_is_rejected() {
    let (mut servers, mut endpoints) = setup_cluster([4; 32], 1);
    let pk: PublicKey = servers[0].public_key().clone();
    let (other_servers, _) = setup_cluster([8; 32], 41);
    let substituted_pk = other_servers[0].public_key().clone();
    assert_ne!(pk.commitment(), substituted_pk.commitment());

    // Request blinded under a substituted public key MUST be rejected before any round or counter step.
    let (_, bad_reqs) = blind(
        &substituted_pk,
        &[b"nonce extraction target"],
        [6; 32],
        0,
        [5; 32],
    )
    .unwrap();
    let mut stores: [Store; 5] = Default::default();
    for (party, req) in bad_reqs.into_iter().enumerate() {
        assert_eq!(
            servers[party].evaluate(req, &mut stores[party], &mut endpoints[party]),
            Err(Error::Context)
        );
    }

    // Honest requests under the pinned public key succeed and produce independent masked components.
    let (c1, reqs1) = blind(&pk, &[b"nonce extraction target"], [6; 32], 0, [5; 32]).unwrap();
    let outs1 = std::thread::scope(|scope| {
        let handles: Vec<_> = servers
            .iter_mut()
            .zip(&mut endpoints)
            .zip(&mut stores)
            .zip(reqs1)
            .map(|(((srv, ep), st), req)| scope.spawn(move || srv.evaluate(req, st, ep).unwrap()))
            .collect();
        handles
            .into_iter()
            .map(|h| Some(h.join().unwrap()))
            .collect::<Vec<_>>()
    });
    let (c2, reqs2) = blind(&pk, &[b"nonce extraction target"], [7; 32], 1, [9; 32]).unwrap();
    let outs2 = std::thread::scope(|scope| {
        let handles: Vec<_> = servers
            .iter_mut()
            .zip(&mut endpoints)
            .zip(&mut stores)
            .zip(reqs2)
            .map(|(((srv, ep), st), req)| scope.spawn(move || srv.evaluate(req, st, ep).unwrap()))
            .collect();
        handles
            .into_iter()
            .map(|h| Some(h.join().unwrap()))
            .collect::<Vec<_>>()
    });
    assert_ne!(
        outs1[0].as_ref().unwrap().components(),
        outs2[0].as_ref().unwrap().components()
    );
    let eval1 = c1.finalize(outs1.try_into().unwrap()).unwrap();
    let eval2 = c2.finalize(outs2.try_into().unwrap()).unwrap();
    assert_eq!(eval1.values(), eval2.values());
}
