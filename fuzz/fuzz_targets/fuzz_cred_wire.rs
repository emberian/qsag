// SPDX-License-Identifier: Apache-2.0 OR MIT
#![no_main]

//! Coverage-guided hostile wire-decoder fuzzer for the `qsag-cred` protocol messages:
//!
//! 1. `voprf::Request::from_wire` (client to server) and `Server::evaluate` on the decoded
//!    request with a peer transport that answers with the fuzzer's choice of garbage.
//! 2. `voprf::Output::from_wire` (server to client) and `Client::finalize` on five decoded
//!    outputs.
//! 3. `voprf::Server::from_secret_bytes` (`QTOPRF01`) and
//!    `voprf_spdz::{SpdzPublic::from_bytes (QTOPRFP1), SpdzServer::from_secret_bytes (QTOPRFS1)}`.
//! 4. `ThresholdVerificationPack::from_bytes` (`QTMLDSP1`) and
//!    `ThresholdMlDsaSignerShare::from_shamir_bytes` (`QTMLDSS1`).
//!
//! Every accepted encoding must re-encode to its input. Honest messages built in
//! `LLVMFuzzerInitialize` (the `init:` block) seed sparse-edit mutations, so the protocol
//! code behind each decoder runs on messages one field away from valid.

use std::sync::OnceLock;

use libfuzzer_sys::fuzz_target;
use qsag_cred::fips204_ntt::{MLDSA_Q, Poly256, power2round};
use qsag_cred::threshold_mldsa::{ThresholdMlDsaSignerShare, ThresholdVerificationPack};
use qsag_cred::voprf::{
    Client, CounterStore, Error, Output, PublicKey, Request, Server, Transport, blind,
};
use qsag_cred::voprf_spdz::{SpdzPublic, SpdzServer};
use qsag_cred::{MlDsaLevel, ml_dsa_verify, pk_encode};

const KEY_COMMITMENT: [u8; 32] = [0x5C; 32];
const SERVER_PARTY: usize = 2;
const SESSION: [u8; 32] = [0x24; 32];
const OPRF_INPUTS: [&[u8]; 2] = [b"fuzz-oprf-input-0", b"fuzz-oprf-input-1"];
/// Offset of the sender index in both voprf wire headers.
const PARTY_OFFSET: usize = 74;
const HEADER_BYTES: usize = 107;

/// Peers that answer each round with this server's own message, altered as `mode` says.
/// Mode 0 is a consistent echo, which passes the context and input agreement rounds.
struct HostilePeers {
    mode: u8,
    rounds: u32,
}

impl HostilePeers {
    fn answer(&mut self, mut message: Vec<u8>, sender: usize) -> Vec<u8> {
        match self.mode % 6 {
            1 => message.clear(),
            2 => {
                message.pop();
            }
            3 => message.iter_mut().for_each(|b| *b = !*b),
            4 if sender == (self.rounds as usize) % 5 => {
                if let Some(first) = message.first_mut() {
                    *first ^= 1;
                }
            }
            5 => message.push(0),
            _ => {}
        }
        message
    }
}

impl Transport for HostilePeers {
    fn exchange(
        &mut self,
        _phase: [u8; 32],
        outgoing: [Vec<u8>; 5],
    ) -> Result<[Vec<u8>; 5], Error> {
        self.rounds += 1;
        if self.mode == 0xff {
            return Err(Error::Transport);
        }
        // Echo: what this server addressed to peer `i` comes back as peer `i`'s message.
        let mut sender = 0;
        Ok(outgoing.map(|message| {
            sender += 1;
            self.answer(message, sender - 1)
        }))
    }

    fn broadcast(&mut self, phase: [u8; 32], message: Vec<u8>) -> Result<[Vec<u8>; 5], Error> {
        self.exchange(phase, core::array::from_fn(|_| message.clone()))
    }
}

/// Counter store with the documented contract: strictly increasing counters, bounded quota.
#[derive(Default)]
struct MonotoneStore {
    last: Option<u64>,
    charged: usize,
}

impl CounterStore for MonotoneStore {
    fn high_water(&self) -> Result<Option<u64>, Error> {
        Ok(self.last)
    }

    fn reserve(&mut self, _: &[u8; 32], _: usize, counter: u64, items: usize) -> Result<(), Error> {
        if self.last.is_some_and(|last| counter <= last) {
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

struct Fixtures {
    key: PublicKey,
    /// `QTOPRF01` custody bundle of server [`SERVER_PARTY`].
    server_secret: Vec<u8>,
    /// The honest request addressed to each server.
    request_wires: [Vec<u8>; 5],
    pack: ThresholdVerificationPack,
    pack_wire: Vec<u8>,
    share_len: usize,
}

fn fresh_client() -> (Client, [Request; 5]) {
    blind(
        &PublicKey::from_commitment(KEY_COMMITMENT),
        &OPRF_INPUTS,
        SESSION,
        1,
        [0x25; 32],
    )
    .expect("blinded batch")
}

fn fixtures() -> &'static Fixtures {
    static FX: OnceLock<Fixtures> = OnceLock::new();
    FX.get_or_init(|| {
        let key = PublicKey::from_commitment(KEY_COMMITMENT);

        // Custody bundle: magic, party, key commitment, "no counter yet", then the ten
        // subset seeds this party holds.
        let mut server_secret = b"QTOPRF01".to_vec();
        server_secret.push(SERVER_PARTY as u8);
        server_secret.extend_from_slice(&KEY_COMMITMENT);
        server_secret.push(0);
        server_secret.extend_from_slice(&0u64.to_le_bytes());
        for seed in 0..10u8 {
            server_secret.extend_from_slice(&[0x80 | seed; 32]);
        }
        let server = Server::from_secret_bytes(&server_secret, &key, SERVER_PARTY)
            .expect("custody bundle restores");
        assert_eq!(server.to_secret_bytes(), server_secret);

        let (_, requests) = fresh_client();
        let request_wires = requests.map(|request| request.to_wire());
        for (party, wire) in request_wires.iter().enumerate() {
            assert_eq!(usize::from(wire[PARTY_OFFSET]), party);
            assert_eq!(wire.len(), 235 + 128 * OPRF_INPUTS.len());
        }

        // A consistent ML-DSA-44 2-of-3 verification pack: `pk = pkEncode(rho, t1)` with
        // `t1` the high part of an arbitrary public `t`.
        let level = MlDsaLevel::MlDsa44;
        let params = level.params();
        let rho = [0x6D; 32];
        let t: Vec<Poly256> = (0..params.k as u32)
            .map(|row| {
                let mut poly = Poly256::zero();
                for (i, coeff) in poly.coeffs.iter_mut().enumerate() {
                    *coeff = (row * 1_000_003 + i as u32 * 7_919 + 5) % MLDSA_Q;
                }
                poly
            })
            .collect();
        let t1: Vec<Poly256> = t
            .iter()
            .map(|poly| {
                let mut high = Poly256::zero();
                for (out, &value) in high.coeffs.iter_mut().zip(&poly.coeffs) {
                    *out = power2round(value).0;
                }
                high
            })
            .collect();
        let pack = ThresholdVerificationPack {
            level,
            threshold: 2,
            party_ids: vec![1, 2, 3],
            rho,
            pk_bytes: pk_encode(&params, &rho, &t1),
            t,
        };
        let pack_wire = pack.to_bytes();
        assert_eq!(ThresholdVerificationPack::from_bytes(&pack_wire).as_ref(), Ok(&pack));

        Fixtures {
            key,
            server_secret,
            request_wires,
            share_len: 18 + 3 * 256 * (params.ell + params.k),
            pack,
            pack_wire,
        }
    })
}

/// `seed` with sparse `(offset: u32 LE, xor: u8)` edits applied.
fn edited(seed: &[u8], edits: &[u8]) -> Vec<u8> {
    let mut candidate = seed.to_vec();
    for edit in edits.as_chunks::<5>().0 {
        let offset = u32::from_le_bytes([edit[0], edit[1], edit[2], edit[3]]) as usize;
        let index = offset % candidate.len();
        candidate[index] ^= edit[4];
    }
    candidate
}

/// Decode a request, check its encoding, and let the server evaluate it against peers that
/// misbehave as `mode` says.
fn check_request(fx: &Fixtures, bytes: &[u8], mode: u8) {
    let Ok(request) = Request::from_wire(bytes) else {
        return;
    };
    assert_eq!(request.to_wire(), bytes);
    let mut server = Server::from_secret_bytes(&fx.server_secret, &fx.key, SERVER_PARTY)
        .expect("custody bundle restores");
    let mut store = MonotoneStore::default();
    let mut peers = HostilePeers { mode, rounds: 0 };
    let outcome = server.evaluate(request, &mut store, &mut peers);
    let addressed_here = usize::from(bytes[PARTY_OFFSET]) == SERVER_PARTY
        && bytes[..32] == KEY_COMMITMENT;
    match outcome {
        Ok(output) => {
            // Only a request for this server and this key is answered, and the answer
            // is itself a canonical wire message.
            assert!(addressed_here);
            let wire = output.to_wire(SERVER_PARTY).expect("server output encodes");
            assert_eq!(Output::from_wire(&wire, SERVER_PARTY), Ok(output));
        }
        Err(_) if !addressed_here => {
            // A request for another server or key is refused before any peer round and
            // before the counter is spent.
            assert_eq!(peers.rounds, 0);
            assert_eq!(store.last, None);
        }
        Err(_) => {}
    }
}

/// Decode `bytes` as the output of each of the five servers and finalize a fresh client
/// with them.
fn check_outputs(fx: &Fixtures, bytes: &[u8]) {
    if bytes.len() <= PARTY_OFFSET {
        return;
    }
    let mut stamped = bytes.to_vec();
    let outputs: [Option<Output>; 5] = core::array::from_fn(|party| {
        stamped[PARTY_OFFSET] = party as u8;
        let output = Output::from_wire(&stamped, party).ok()?;
        assert_eq!(output.to_wire(party).as_deref(), Ok(stamped.as_slice()));
        Some(output)
    });
    if outputs.iter().all(Option::is_none) {
        return;
    }
    let (client, _) = fresh_client();
    if let Ok(evaluation) = client.finalize(outputs) {
        // Outputs are accepted only for the context the client blinded under: key, session,
        // counter, batch size and request root, as the honest request header states them.
        let honest = &fx.request_wires[0];
        assert_eq!(bytes[..PARTY_OFFSET], honest[..PARTY_OFFSET]);
        assert_eq!(
            bytes[PARTY_OFFSET + 1..HEADER_BYTES],
            honest[PARTY_OFFSET + 1..HEADER_BYTES]
        );
        assert_eq!(evaluation.values().len(), OPRF_INPUTS.len());
        for input in OPRF_INPUTS {
            assert!(evaluation.value_for(&fx.key, input).is_some());
        }
        assert!(evaluation.value_for(&fx.key, b"an input nobody blinded").is_none());
    }
}

fn check_pack(bytes: &[u8]) {
    let Ok(pack) = ThresholdVerificationPack::from_bytes(bytes) else {
        return;
    };
    assert_eq!(pack.to_bytes(), bytes);
    // What signing relies on, stated without the crate's own validator.
    let params = pack.level.params();
    assert!(pack.party_ids.windows(2).all(|pair| pair[0] < pair[1]));
    assert!(pack.threshold >= 2 && pack.threshold <= pack.party_ids.len());
    assert_eq!(pack.t.len(), params.k);
    assert!(pack.t.iter().flat_map(|poly| &poly.coeffs).all(|&c| c < MLDSA_Q));
    assert_eq!(pack.pk_bytes.len(), params.pk_bytes);
    assert_eq!(pack.pk_bytes[..32], pack.rho);
    // The embedded key is a well-formed FIPS 204 public key; nothing verifies under it
    // without a signature.
    assert!(!ml_dsa_verify(pack.level, &pack.pk_bytes, b"fuzz-pack", b"ctx", bytes));
}

fn check_share(fx: &Fixtures, bytes: &[u8], expected_party: u16) {
    let Ok(share) = ThresholdMlDsaSignerShare::from_shamir_bytes(bytes, fx.pack.clone(), expected_party)
    else {
        return;
    };
    assert_eq!(share.to_shamir_bytes().as_deref(), Some(bytes));
    assert_eq!(bytes[8..10], expected_party.to_le_bytes());
    assert!(fx.pack.party_ids.contains(&expected_party));
}

fuzz_target!(init: {
    fixtures();
}, |data: &[u8]| {
    let fx = fixtures();
    let mode = data.last().copied().unwrap_or(0);

    // 1. Raw bytes through every decoder.
    check_request(fx, data, mode);
    check_outputs(fx, data);
    check_pack(data);
    if let Some(&party) = data.get(8) {
        if let Ok(server) = Server::from_secret_bytes(data, &fx.key, usize::from(party)) {
            assert_eq!(server.to_secret_bytes(), data);
            assert_eq!(server.party(), usize::from(party));
        }
        check_share(fx, data, u16::from(party));
    }
    if let Ok(public) = SpdzPublic::from_bytes(data) {
        assert_eq!(public.to_bytes(), data);
        // The key commitment is a function of the whole record.
        let mut other = data.to_vec();
        let last = other.len() - 1;
        other[last] ^= 1;
        let other = SpdzPublic::from_bytes(&other).expect("same shape, different digest");
        assert_ne!(other.public_key().commitment(), public.public_key().commitment());
        // Server custody bytes are checked against the record's share digests.
        for party in 0..public.config().servers() {
            if let Ok(server) = SpdzServer::from_secret_bytes(data, &public, party) {
                assert_eq!(server.to_secret_bytes(), data);
            }
        }
    }

    // 2. Structured inputs: `[0xed, kind]` selects what the rest of the input drives.
    if let [0xed, kind, rest @ ..] = data {
        match kind % 5 {
            // Sparse edits of the honest request addressed to this server.
            0 => check_request(fx, &edited(&fx.request_wires[SERVER_PARTY], rest), mode),
            // Fuzzer body under the honest request header.
            1 => {
                let mut candidate = fx.request_wires[SERVER_PARTY].clone();
                let body = &mut candidate[HEADER_BYTES..];
                for (slot, &byte) in body.iter_mut().zip(rest) {
                    *slot = byte;
                }
                check_request(fx, &candidate, mode);
            }
            // Fuzzer shares under the honest output header (same layout as the request's).
            2 => {
                let items = OPRF_INPUTS.len();
                let mut candidate = fx.request_wires[0][..HEADER_BYTES].to_vec();
                candidate.extend(rest.iter().copied().chain(core::iter::repeat(0)).take(128 * items));
                check_outputs(fx, &candidate);
            }
            3 => check_pack(&edited(&fx.pack_wire, rest)),
            // A full-length Shamir share for one of the pack's custodians.
            _ => {
                let party = 1 + u16::from(mode % 3);
                let mut candidate = b"QTMLDSS1".to_vec();
                candidate.extend_from_slice(&party.to_le_bytes());
                candidate.extend(rest.iter().copied().chain(core::iter::repeat(0)).take(fx.share_len - 10));
                check_share(fx, &candidate, party);
            }
        }
    }
});
