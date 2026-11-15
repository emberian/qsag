use qsag_accel::{
    goldilocks::{GOLDILOCKS_PRIME, gl_add},
    keccak::{Shake256, cshake256_framed_32},
};
use qsag_cred::voprf::*;
use std::sync::{Arc, Barrier, Mutex};
use std::time::Instant;

type Rows = [Option<([u8; 32], [Vec<u8>; 5])>; 5];
struct Network {
    barrier: Barrier,
    rows: Mutex<Rows>,
    bytes: Mutex<usize>,
    rounds: Mutex<usize>,
}
struct Endpoint {
    party: usize,
    network: Arc<Network>,
    corrupt: bool,
    /// 0: add one to the first word; 1: invert every byte; 2: drop the last
    /// byte; 3: send nothing.
    mode: u8,
}
impl Transport for Endpoint {
    fn exchange(
        &mut self,
        phase: [u8; 32],
        mut outgoing: [Vec<u8>; 5],
    ) -> Result<[Vec<u8>; 5], Error> {
        if self.corrupt {
            for message in &mut outgoing {
                match self.mode {
                    0 if message.len() >= 8 => {
                        let v = u64::from_le_bytes(message[..8].try_into().unwrap());
                        message[..8].copy_from_slice(&v.wrapping_add(1).to_le_bytes());
                    }
                    1 => message.iter_mut().for_each(|b| *b = !*b),
                    2 => {
                        message.pop();
                    }
                    3 => message.clear(),
                    _ => {}
                }
            }
        }
        *self.network.bytes.lock().unwrap() += outgoing
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != self.party)
            .map(|(_, v)| v.len() + 32)
            .sum::<usize>();
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
        if self.party == 0 {
            *self.network.rounds.lock().unwrap() += 1;
        }
        Ok(result)
    }
    fn broadcast(&mut self, phase: [u8; 32], message: Vec<u8>) -> Result<[Vec<u8>; 5], Error> {
        {
            let corrupt = self.corrupt;
            self.corrupt = false;
            let out = self.exchange(phase, core::array::from_fn(|_| message.clone()));
            self.corrupt = corrupt;
            out
        }
    }
}
#[derive(Default)]
struct Store {
    last: Option<u64>,
    charged: usize,
}
impl CounterStore for Store {
    fn high_water(&self) -> Result<Option<u64>, Error> {
        Ok(self.last)
    }
    fn reserve(&mut self, _: &[u8; 32], _: usize, counter: u64, items: usize) -> Result<(), Error> {
        if self.last.is_some_and(|v| counter <= v) {
            return Err(Error::Counter);
        }
        if self.charged + items > 256 {
            return Err(Error::Quota);
        }
        self.last = Some(counter);
        self.charged += items;
        Ok(())
    }
}
fn network() -> (Arc<Network>, [Endpoint; 5]) {
    let n = Arc::new(Network {
        barrier: Barrier::new(5),
        rows: Mutex::new(core::array::from_fn(|_| None)),
        bytes: Mutex::new(0),
        rounds: Mutex::new(0),
    });
    (
        n.clone(),
        core::array::from_fn(|party| Endpoint {
            party,
            network: n.clone(),
            corrupt: false,
            mode: 0,
        }),
    )
}
fn setup() -> (Vec<Server>, [Endpoint; 5], Arc<Network>) {
    let (net, endpoints) = network();
    let mut result = std::thread::scope(|scope| {
        let handles: Vec<_> = endpoints
            .into_iter()
            .enumerate()
            .map(|(party, mut endpoint)| {
                scope.spawn(move || {
                    let server = dkg(
                        Config::new(2, 5).unwrap(),
                        party,
                        [91; 32],
                        [party as u8 + 1; 32],
                        &mut endpoint,
                    )
                    .unwrap();
                    (server, endpoint)
                })
            })
            .collect();
        handles
            .into_iter()
            .map(|h| h.join().unwrap())
            .collect::<Vec<_>>()
    });
    let endpoints: [(Server, Endpoint); 5] = std::array::from_fn(|_| result.remove(0));
    let (servers, channels): (Vec<_>, Vec<_>) = endpoints.into_iter().unzip();
    (servers, channels.try_into().ok().unwrap(), net)
}
fn evaluate<S: CounterStore + Send>(
    servers: &mut [Server],
    endpoints: &mut [Endpoint; 5],
    requests: [Request; 5],
    stores: &mut [S; 5],
) -> [Option<Output>; 5] {
    std::thread::scope(|scope| {
        let handles: Vec<_> = servers
            .iter_mut()
            .zip(endpoints)
            .zip(requests)
            .zip(stores)
            .map(|(((server, endpoint), request), store)| {
                scope.spawn(move || server.evaluate(request, store, endpoint).unwrap())
            })
            .collect();
        handles
            .into_iter()
            .map(|h| Some(h.join().unwrap()))
            .collect::<Vec<_>>()
            .try_into()
            .ok()
            .unwrap()
    })
}
fn fields(seed: &[u8; 32], domain: &[u8], context: &[u8]) -> [u64; 4] {
    let mut xof = Shake256::new();
    xof.absorb(&cshake256_framed_32(domain, &[seed, context]));
    xof.finalize(0x1f);
    std::array::from_fn(|_| {
        loop {
            let mut b = [0; 8];
            xof.squeeze(&mut b);
            let v = u64::from_le_bytes(b);
            if v < GOLDILOCKS_PRIME {
                break v;
            }
        }
    })
}
fn reference_key(public: &PublicKey) -> [u64; 4] {
    let mut key = [0; 4];
    for excluded in 0..5 {
        let mut joint = Vec::new();
        for dealer in 0..5 {
            if dealer != excluded {
                joint.extend_from_slice(&cshake256_framed_32(
                    b"QSAG.TOPRF.DKG.SEED.V1",
                    &[
                        &[dealer as u8 + 1; 32],
                        &[91; 32],
                        &[dealer as u8, excluded as u8, excluded as u8],
                    ],
                ));
            }
        }
        let seed = cshake256_framed_32(
            b"QSAG.TOPRF.DKG.JOINT.V1",
            &[&[91; 32], &[excluded as u8, excluded as u8], &joint],
        );
        let component = fields(&seed, b"QSAG.TOPRF.KEY.COMPONENT.V1", &public.commitment());
        for lane in 0..4 {
            key[lane] = gl_add(key[lane], component[lane]);
        }
    }
    key
}
#[test]
fn isolated_servers_correct_replays_faults_and_batch_costs() {
    for (t, n) in [(1, 1), (2, 3), (2, 4), (3, 7), (2, 6)] {
        assert_eq!(Config::new(t, n), Err(Error::UnsupportedThreshold));
    }
    let (mut servers, mut endpoints, net) = setup();
    let public = PublicKey::from_commitment(servers[0].public_key().commitment());
    assert!(servers.iter().all(|s| s.public_key() == &public));
    let key = reference_key(&public);
    let mut stores: [Store; 5] = std::array::from_fn(|_| Store::default());
    let (_, wrong_key) = blind(&public, &[b"binding"], [90; 32], 0, [89; 32]).unwrap();
    let mut encoded = wrong_key[0].to_wire();
    encoded[0] ^= 1;
    assert_eq!(
        servers[0].evaluate(
            Request::from_wire(&encoded).unwrap(),
            &mut stores[0],
            &mut endpoints[0]
        ),
        Err(Error::Context)
    );
    assert_eq!(stores[0].charged, 0);
    for (counter, batch) in [(0, 1), (1, 64)] {
        endpoints[1].corrupt = batch == 64;
        let input_storage: Vec<_> = (0..batch)
            .map(|i| format!("input-{i}").into_bytes())
            .collect();
        let inputs: Vec<_> = input_storage.iter().map(Vec::as_slice).collect();
        let (client, requests) = blind(&public, &inputs, [92; 32], counter, [93; 32]).unwrap();
        *net.bytes.lock().unwrap() = 0;
        *net.rounds.lock().unwrap() = 0;
        let start = Instant::now();
        let request_bytes: usize = requests.iter().map(|r| r.to_wire().len()).sum();
        let requests = requests.map(|r| Request::from_wire(&r.to_wire()).unwrap());
        let mut output = evaluate(&mut servers, &mut endpoints, requests, &mut stores);
        let mut output_bytes = 0;
        for (party, out) in output.iter_mut().enumerate() {
            let mut bytes = out.as_ref().unwrap().to_wire(party).unwrap();
            output_bytes += bytes.len();
            if party == 1 {
                // Corrupt one authenticated server's every serialized output component on the wire.
                for chunk in bytes[107..].as_chunks_mut::<8>().0 {
                    let v = u64::from_le_bytes(*chunk);
                    *chunk = gl_add(v, 1).to_le_bytes();
                }
            }
            *out = Some(Output::from_wire(&bytes, party).unwrap());
        }
        let impostor_inputs: Vec<&[u8]> = vec![b"a different input"; batch];
        let (impostor, _) = blind(&public, &impostor_inputs, [92; 32], counter, [93; 32]).unwrap();
        assert_eq!(
            impostor.finalize(output.clone()),
            Err(Error::InconsistentShares)
        );
        let evaluation = client.finalize(output).unwrap();
        assert_eq!(evaluation.faulty_servers, vec![1]);
        for (value, input) in evaluation.values().iter().zip(&inputs) {
            assert_eq!(*value, plaintext(&key, input));
        }
        assert_eq!(*net.rounds.lock().unwrap(), 92); // two input barriers + 30 * 3 multiplication depths
        eprintln!(
            "TOPRF batch={batch}: server_payload_and_phase_bytes={}, client_wire_bytes={}, logical_server_rounds={}, elapsed_us={}",
            net.bytes.lock().unwrap(),
            request_bytes + output_bytes,
            net.rounds.lock().unwrap(),
            start.elapsed().as_micros()
        );
        let (_, requests) = blind(&public, &inputs, [94; 32], counter, [95; 32]).unwrap();
        for (((server, endpoint), request), store) in servers
            .iter_mut()
            .zip(&mut endpoints)
            .zip(requests)
            .zip(&mut stores)
        {
            assert_eq!(
                server.evaluate(request, store, endpoint),
                Err(Error::Counter)
            );
        }
    }
    // An equivocating client is rejected before any key-dependent gate.
    let (_, mut requests) =
        blind(&public, &[b"inconsistent input"], [96; 32], 2, [97; 32]).unwrap();
    let mut encoded = requests[0].to_wire();
    let value = u64::from_le_bytes(encoded[235..243].try_into().unwrap());
    encoded[235..243].copy_from_slice(&gl_add(value, 1).to_le_bytes());
    requests[0] = Request::from_wire(&encoded).unwrap();
    std::thread::scope(|scope| {
        let handles: Vec<_> = servers
            .iter_mut()
            .zip(&mut endpoints)
            .zip(requests)
            .zip(&mut stores)
            .map(|(((server, endpoint), request), store)| {
                scope.spawn(move || server.evaluate(request, store, endpoint))
            })
            .collect();
        for handle in handles {
            assert_eq!(handle.join().unwrap(), Err(Error::InconsistentShares));
        }
    });
    assert!(
        stores
            .iter()
            .all(|store| store.last == Some(2) && store.charged == 66)
    );
}

/// Every single server, under every message fault, in both the plain-vector
/// (batch 1: layers of at most four gates in partial rounds) and the
/// vector-plus-digest regime (full rounds and batch 5), is corrected.
#[test]
fn any_single_malicious_server_is_corrected_in_every_layer() {
    let (mut servers, mut endpoints, _) = setup();
    let public = PublicKey::from_commitment(servers[0].public_key().commitment());
    let key = reference_key(&public);
    let mut stores: [Store; 5] = std::array::from_fn(|_| Store::default());
    let mut counter = 0;
    for bad in 0..5 {
        for mode in 0..4 {
            for batch in [1usize, 5] {
                if batch == 5 && mode % 2 == 1 {
                    continue;
                }
                for (party, endpoint) in endpoints.iter_mut().enumerate() {
                    endpoint.corrupt = party == bad;
                    endpoint.mode = mode;
                }
                let storage: Vec<_> = (0..batch)
                    .map(|i| format!("fault-{bad}-{mode}-{i}").into_bytes())
                    .collect();
                let inputs: Vec<_> = storage.iter().map(Vec::as_slice).collect();
                let (client, requests) =
                    blind(&public, &inputs, [70; 32], counter, [71 + bad as u8; 32]).unwrap();
                counter += 1;
                let outputs = evaluate(&mut servers, &mut endpoints, requests, &mut stores);
                let evaluation = client.finalize(outputs).unwrap();
                for (value, input) in evaluation.values().iter().zip(&inputs) {
                    assert_eq!(*value, plaintext(&key, input));
                }
            }
        }
    }
}

#[test]
fn blind_vc_uses_the_oprf_and_pins_schema() {
    use qsag_cred::blind_vc::*;
    let (mut servers, mut endpoints, _) = setup();
    let public = PublicKey::from_commitment(servers[0].public_key().commitment());
    let mut stores: [Store; 5] = std::array::from_fn(|_| Store::default());
    let (req, holder) = holder_prepare_blind_issuance(
        42,
        &[840, 1994, 3],
        public.commitment(),
        7,
        [22; 32],
        [23; 32],
    )
    .unwrap();
    assert!(verify_blind_issuance_request(&req, &[840, 1994, 3], 42));
    assert!(!verify_blind_issuance_request(&req, &[840, 1994, 3], 43));
    let input = issuance_input(&req);
    let (client, requests) = blind(&public, &[&input], [24; 32], 0, [25; 32]).unwrap();
    let receipt_key = IssuanceReceiptKey::new([93; 32]);
    let evaluation = client
        .finalize_for_issuance(
            evaluate(&mut servers, &mut endpoints, requests, &mut stores),
            &receipt_key,
        )
        .unwrap();
    let mut accumulator = IssuerCredentialAccumulator::new(public, 7);
    assert!(
        threshold_issue_blind_vc(
            &mut accumulator,
            &req,
            &[840, 1994, 3],
            &evaluation,
            &receipt_key,
            43
        )
        .is_err()
    );
    let cred = threshold_issue_blind_vc(
        &mut accumulator,
        &req,
        &[840, 1994, 3],
        &evaluation,
        &receipt_key,
        42,
    )
    .unwrap();

    // Tampering `cred.issuance_token` after issuance is rejected by `prove_selective_disclosure`!
    let mut bad_cred = cred.clone();
    bad_cred.issuance_token[0] ^= 0x01;
    assert_eq!(
        prove_selective_disclosure(
            &bad_cred,
            &holder,
            &accumulator
                .membership_witness(cred.accumulator_leaf_index)
                .unwrap(),
            &[0],
            PresentationRequest {
                verifier_scope: b"verifier",
                verifier_challenge: &[27; 32],
                mode: PresentationMode::UnlinkableFresh,
            },
            [26; 32],
        )
        .unwrap_err(),
        BlindVcError::CredentialBindingMismatch
    );

    let (issuer_mldsa_pk, issuer_mldsa_sk) =
        qsag_cred::ml_dsa_keygen_from_seed(qsag_cred::MlDsaLevel::MlDsa44, &[0x5A; 32]);
    let root_attestation = accumulator
        .attest_root_deterministic(
            qsag_cred::MlDsaLevel::MlDsa44,
            &issuer_mldsa_sk,
            issuer_mldsa_pk.clone(),
        )
        .unwrap();

    let presentation = prove_selective_disclosure(
        &cred,
        &holder,
        &accumulator
            .membership_witness(cred.accumulator_leaf_index)
            .unwrap(),
        &[0],
        PresentationRequest {
            verifier_scope: b"verifier",
            verifier_challenge: &[27; 32],
            mode: PresentationMode::UnlinkableFresh,
        },
        [26; 32],
    )
    .unwrap();
    assert!(verify_presentation(
        &presentation,
        &root_attestation,
        &issuer_mldsa_pk,
        &accumulator.oprf_key,
        b"verifier",
        &[27; 32],
        PresentationMode::UnlinkableFresh,
        42,
        3
    ));
    assert!(!verify_presentation(
        &presentation,
        &root_attestation,
        &issuer_mldsa_pk,
        &accumulator.oprf_key,
        b"verifier",
        &[27; 32],
        PresentationMode::UnlinkableFresh,
        43,
        3
    ));
    assert_eq!(presentation.pres_commit.len(), 6);
}

#[test]
fn counter_u64_max_and_unbounded_jump_rejected_without_bricking_servers() {
    let (mut servers, mut endpoints, _) = setup();
    let public = PublicKey::from_commitment(servers[0].public_key().commitment());
    let key = reference_key(&public);
    let mut stores: [Store; 5] = std::array::from_fn(|_| Store::default());

    // 1. Adversarial request with `counter = u64::MAX` MUST fail with `Err(Error::Counter)`
    //    and MUST NOT advance any server's counter store!
    for bad_counter in [u64::MAX, u64::MAX - 1, MAX_COUNTER_WINDOW] {
        let (_, bad_reqs) = blind(
            &public,
            &[b"dos-probe"],
            [0x31; 32],
            bad_counter,
            [0x32; 32],
        )
        .unwrap();
        for (((server, endpoint), req), store) in servers
            .iter_mut()
            .zip(&mut endpoints)
            .zip(bad_reqs)
            .zip(&mut stores)
        {
            assert_eq!(server.evaluate(req, store, endpoint), Err(Error::Counter));
            assert_eq!(store.last, None);
            assert_eq!(store.charged, 0);
        }
    }

    // 2. Normal evaluation at `counter = 0` immediately succeeds!
    let (client0, reqs0) = blind(&public, &[b"honest-0"], [0x33; 32], 0, [0x34; 32]).unwrap();
    let eval0 = client0
        .finalize(evaluate(&mut servers, &mut endpoints, reqs0, &mut stores))
        .unwrap();
    assert_eq!(eval0.values()[0], plaintext(&key, b"honest-0"));
    assert!(stores.iter().all(|s| s.last == Some(0) && s.charged == 1));

    // 3. Another `counter = u64::MAX` attempt after `counter = 0` is ALSO rejected without bricking!
    let (_, max_reqs) =
        blind(&public, &[b"dos-probe-2"], [0x35; 32], u64::MAX, [0x36; 32]).unwrap();
    for (((server, endpoint), req), store) in servers
        .iter_mut()
        .zip(&mut endpoints)
        .zip(max_reqs)
        .zip(&mut stores)
    {
        assert_eq!(server.evaluate(req, store, endpoint), Err(Error::Counter));
        assert_eq!(store.last, Some(0));
        assert_eq!(store.charged, 1);
    }

    // 4. Subsequent normal evaluation at `counter = 1` succeeds cleanly!
    let (client1, reqs1) = blind(&public, &[b"honest-1"], [0x37; 32], 1, [0x38; 32]).unwrap();
    let eval1 = client1
        .finalize(evaluate(&mut servers, &mut endpoints, reqs1, &mut stores))
        .unwrap();
    assert_eq!(eval1.values()[0], plaintext(&key, b"honest-1"));
    assert!(stores.iter().all(|s| s.last == Some(1) && s.charged == 2));
}

/// File-backed, identity-bound test store. Reservations are synced before the
/// evaluator can emit an output; reopening reads the persisted watermark.
struct DurableStore {
    path: std::path::PathBuf,
    key: [u8; 32],
    party: usize,
}
impl CounterStore for DurableStore {
    fn high_water(&self) -> Result<Option<u64>, Error> {
        match std::fs::read(&self.path) {
            Ok(bytes) => Ok(Some(u64::from_le_bytes(
                bytes.try_into().map_err(|_| Error::Counter)?,
            ))),
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(None),
            Err(_) => Err(Error::Counter),
        }
    }
    fn reserve(
        &mut self,
        key: &[u8; 32],
        party: usize,
        counter: u64,
        _: usize,
    ) -> Result<(), Error> {
        use std::io::Write;
        if key != &self.key
            || party != self.party
            || self.high_water()?.is_some_and(|last| counter <= last)
        {
            return Err(Error::Counter);
        }
        let mut file = std::fs::File::create(&self.path).map_err(|_| Error::Counter)?;
        file.write_all(&counter.to_le_bytes())
            .map_err(|_| Error::Counter)?;
        file.sync_all().map_err(|_| Error::Counter)
    }
}

#[test]
fn toprf_server_recovers_after_100_batches_restart() {
    let (mut servers, mut endpoints, _) = setup();
    let key = servers[0].public_key().clone();
    let dir = std::env::temp_dir().join(format!("toprf-restart-{}", std::process::id()));
    std::fs::create_dir(&dir).unwrap();
    let open_stores = || {
        core::array::from_fn(|party| DurableStore {
            path: dir.join(party.to_string()),
            key: key.commitment(),
            party,
        })
    };
    let mut stores: [DurableStore; 5] = open_stores();
    for counter in 1..=100 {
        let (client, requests) = blind(&key, &[b"restart"], [9; 32], counter, [10; 32]).unwrap();
        client
            .finalize(evaluate(
                &mut servers,
                &mut endpoints,
                requests,
                &mut stores,
            ))
            .unwrap();
    }
    drop(servers);
    drop(stores);
    // Deterministically reload the same test custody with empty RAM counters.
    let (mut servers, mut endpoints, _) = setup();
    assert_eq!(servers[0].public_key(), &key);
    let mut stores: [DurableStore; 5] = open_stores();
    for counter in (0..=100).chain([100 + MAX_COUNTER_WINDOW + 1, u64::MAX]) {
        let (_, requests) = blind(&key, &[b"restart"], [9; 32], counter, [10; 32]).unwrap();
        for (((server, endpoint), store), request) in servers
            .iter_mut()
            .zip(&mut endpoints)
            .zip(&mut stores)
            .zip(requests)
        {
            assert_eq!(
                server.evaluate(request, store, endpoint).unwrap_err(),
                Error::Counter
            );
            assert_eq!(store.high_water().unwrap(), Some(100));
        }
    }
    let (client, requests) = blind(&key, &[b"restart"], [9; 32], 101, [10; 32]).unwrap();
    client
        .finalize(evaluate(
            &mut servers,
            &mut endpoints,
            requests,
            &mut stores,
        ))
        .unwrap();
    for store in &stores {
        assert_eq!(store.high_water().unwrap(), Some(101));
    }
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn persisted_party_shares_restore_without_dkg_and_bind_custody() {
    let (mut servers, mut endpoints, net) = setup();
    let public = servers[0].public_key().clone();
    let rounds = *net.rounds.lock().unwrap();
    for (party, server) in servers.iter_mut().enumerate() {
        let mut bytes = server.to_secret_bytes();
        assert_eq!(bytes.len(), 370);
        assert!(Server::from_secret_bytes(&bytes, &public, (party + 1) % 5).is_err());
        assert!(
            Server::from_secret_bytes(&bytes, &PublicKey::from_commitment([0; 32]), party).is_err()
        );
        assert!(Server::from_secret_bytes(&bytes[..369], &public, party).is_err());
        bytes.push(0);
        assert!(Server::from_secret_bytes(&bytes, &public, party).is_err());
        bytes.pop();
        bytes[41] = 2;
        assert!(Server::from_secret_bytes(&bytes, &public, party).is_err());
        bytes[41] = 0;
        *server = Server::from_secret_bytes(&bytes, &public, party).unwrap();
        assert_eq!(server.party(), party);
        assert_eq!(server.to_secret_bytes(), bytes);
        qsag_accel::ct::ct_zeroize_bytes(&mut bytes);
    }
    assert_eq!(*net.rounds.lock().unwrap(), rounds);
    let (client, requests) = blind(&public, &[b"persisted"], [12; 32], 0, [13; 32]).unwrap();
    let mut stores: [Store; 5] = std::array::from_fn(|_| Store::default());
    let outputs = evaluate(&mut servers, &mut endpoints, requests, &mut stores);
    assert_eq!(
        client.finalize(outputs).unwrap().values()[0],
        plaintext(&reference_key(&public), b"persisted")
    );
    for (party, server) in servers.iter_mut().enumerate() {
        let mut bytes = server.to_secret_bytes();
        *server = Server::from_secret_bytes(&bytes, &public, party).unwrap();
        qsag_accel::ct::ct_zeroize_bytes(&mut bytes);
    }
    // Even a regressed external counter cannot unburn the serialized local counter.
    let (_, requests) = blind(&public, &[b"persisted"], [14; 32], 0, [15; 32]).unwrap();
    for (((server, endpoint), request), store) in servers
        .iter_mut()
        .zip(&mut endpoints)
        .zip(requests)
        .zip(&mut stores)
    {
        store.last = None;
        assert_eq!(
            server.evaluate(request, store, endpoint),
            Err(Error::Counter)
        );
    }
}
