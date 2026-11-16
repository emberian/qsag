// SPDX-License-Identifier: Apache-2.0 OR MIT
#![no_main]

//! Coverage-guided fuzzer for the `qsag-cred` selective-disclosure presentation:
//! `SelectiveDisclosurePresentation::from_compact_wire_bytes` (`QSAG.BVC.SD.LIMBO256.V2`),
//! its canonical re-encoding, and `verify_presentation_with_profile`.
//!
//! A presentation is megabytes on the wire, far beyond what a mutator assembles from
//! nothing. `LLVMFuzzerInitialize` (the `init:` block) therefore runs the real pipeline once:
//! a five-server threshold OPRF key generation and evaluation, blind issuance into the
//! issuer's accumulator, an ML-DSA root attestation, and a presentation disclosing one
//! attribute. Inputs are sparse edits of that presentation's wire bytes; raw inputs still go
//! through the decoder's length and header checks.
//!
//! Invariants: the unedited presentation verifies; an accepted encoding re-encodes to
//! itself; and whatever verifies discloses exactly what the holder disclosed (anything else
//! is a forged statement).

use std::sync::{Arc, Barrier, Mutex, OnceLock};

use libfuzzer_sys::fuzz_target;
use qsag_cred::blind_vc::{
    IssuerCredentialAccumulator, IssuerRootAttestation, PresentationMode, PresentationRequest,
    SelectiveDisclosurePresentation, ZkSoundnessProfile, holder_prepare_blind_issuance_with_profile,
    issuance_input, prove_selective_disclosure_with_profile,
    threshold_issue_blind_vc_with_profile, verify_presentation_with_profile,
};
use qsag_cred::voprf::{
    Config, CounterStore, Error, IssuanceReceiptKey, Output, PublicKey, Request, Server,
    Transport, blind, dkg,
};
use qsag_cred::{MlDsaLevel, ml_dsa_keygen_from_seed};

/// The smaller of the two wire sizes (about 4.7 MiB against 9.2 MiB).
const PROFILE: ZkSoundnessProfile = ZkSoundnessProfile::Classical128;
const SCHEMA_ID: u64 = 42;
const ATTRS: [u64; 3] = [840, 1994, 3];
const ISSUER_EPOCH: u64 = 7;
const VERIFIER_SCOPE: &[u8] = b"verifier";
const VERIFIER_CHALLENGE: [u8; 32] = [27; 32];

type Rows = [Option<([u8; 32], [Vec<u8>; 5])>; 5];

/// Synchronous five-party network: every round, each party posts its row and collects the
/// column addressed to it.
struct Network {
    barrier: Barrier,
    rows: Mutex<Rows>,
}

struct Endpoint {
    party: usize,
    network: Arc<Network>,
}

impl Transport for Endpoint {
    fn exchange(
        &mut self,
        phase: [u8; 32],
        outgoing: [Vec<u8>; 5],
    ) -> Result<[Vec<u8>; 5], Error> {
        self.network.rows.lock().expect("network lock")[self.party] = Some((phase, outgoing));
        self.network.barrier.wait();
        let result = {
            let mut rows = self.network.rows.lock().expect("network lock");
            let mut incoming: [Vec<u8>; 5] = core::array::from_fn(|_| Vec::new());
            for (sender, slot) in incoming.iter_mut().enumerate() {
                let row = rows[sender].as_mut().ok_or(Error::Transport)?;
                if row.0 != phase {
                    return Err(Error::Transport);
                }
                *slot = std::mem::take(&mut row.1[self.party]);
            }
            incoming
        };
        self.network.barrier.wait();
        Ok(result)
    }

    fn broadcast(&mut self, phase: [u8; 32], message: Vec<u8>) -> Result<[Vec<u8>; 5], Error> {
        self.exchange(phase, core::array::from_fn(|_| message.clone()))
    }
}

/// Counter store with the documented contract: strictly increasing counters.
#[derive(Default)]
struct MonotoneStore(Option<u64>);

impl CounterStore for MonotoneStore {
    fn high_water(&self) -> Result<Option<u64>, Error> {
        Ok(self.0)
    }

    fn reserve(&mut self, _: &[u8; 32], _: usize, counter: u64, _: usize) -> Result<(), Error> {
        if self.0.is_some_and(|last| counter <= last) {
            return Err(Error::Counter);
        }
        self.0 = Some(counter);
        Ok(())
    }
}

struct Fixtures {
    root: IssuerRootAttestation,
    issuer_mldsa_pk: Vec<u8>,
    oprf_key: PublicKey,
    disclosed: Vec<(usize, u64)>,
    wire: Vec<u8>,
}

fn run_servers<T: Send>(
    endpoints: &mut [Endpoint],
    work: impl Fn(usize, &mut Endpoint) -> T + Sync,
) -> Vec<T> {
    std::thread::scope(|scope| {
        let handles: Vec<_> = endpoints
            .iter_mut()
            .enumerate()
            .map(|(party, endpoint)| {
                let work = &work;
                scope.spawn(move || work(party, endpoint))
            })
            .collect();
        handles
            .into_iter()
            .map(|handle| handle.join().expect("server thread"))
            .collect()
    })
}

fn fixtures() -> &'static Fixtures {
    static FX: OnceLock<Fixtures> = OnceLock::new();
    FX.get_or_init(|| {
        let network = Arc::new(Network {
            barrier: Barrier::new(5),
            rows: Mutex::new(core::array::from_fn(|_| None)),
        });
        let mut endpoints: Vec<Endpoint> = (0..5)
            .map(|party| Endpoint {
                party,
                network: network.clone(),
            })
            .collect();

        // Threshold OPRF key generation, then one evaluation for the issuance input.
        let servers: Vec<Mutex<Server>> = run_servers(&mut endpoints, |party, endpoint| {
            let config = Config::new(2, 5).expect("2-of-5");
            dkg(config, party, [91; 32], [party as u8 + 1; 32], endpoint).expect("dkg")
        })
        .into_iter()
        .map(Mutex::new)
        .collect();
        let oprf_key = PublicKey::from_commitment(
            servers[0].lock().expect("server lock").public_key().commitment(),
        );
        let (request, holder) = holder_prepare_blind_issuance_with_profile(
            SCHEMA_ID,
            &ATTRS,
            oprf_key.commitment(),
            ISSUER_EPOCH,
            [22; 32],
            [23; 32],
            PROFILE,
        )
        .expect("blind issuance request");
        let input = issuance_input(&request);
        let (client, requests) =
            blind(&oprf_key, &[&input], [24; 32], 0, [25; 32]).expect("blinded input");
        let requests: Vec<Mutex<Option<Request>>> =
            requests.into_iter().map(|r| Mutex::new(Some(r))).collect();
        let outputs: Vec<Output> = run_servers(&mut endpoints, |party, endpoint| {
            let request = requests[party]
                .lock()
                .expect("request lock")
                .take()
                .expect("one request per server");
            servers[party]
                .lock()
                .expect("server lock")
                .evaluate(request, &mut MonotoneStore::default(), endpoint)
                .expect("oprf evaluation")
        });
        let mut outputs = outputs.into_iter().map(Some);
        let outputs: [Option<Output>; 5] =
            core::array::from_fn(|_| outputs.next().expect("five outputs"));
        let receipt_key = IssuanceReceiptKey::new([93; 32]);
        let evaluation = client
            .finalize_for_issuance(outputs, &receipt_key)
            .expect("oprf finalization");

        // Issuance, root attestation and a presentation disclosing attribute 0.
        let mut accumulator = IssuerCredentialAccumulator::new(oprf_key.clone(), ISSUER_EPOCH);
        let credential = threshold_issue_blind_vc_with_profile(
            &mut accumulator,
            &request,
            &ATTRS,
            &evaluation,
            &receipt_key,
            SCHEMA_ID,
            PROFILE,
        )
        .expect("issued credential");
        let (issuer_mldsa_pk, issuer_mldsa_sk) =
            ml_dsa_keygen_from_seed(MlDsaLevel::MlDsa44, &[0x5A; 32]);
        let root = accumulator
            .attest_root_deterministic(MlDsaLevel::MlDsa44, &issuer_mldsa_sk, issuer_mldsa_pk.clone())
            .expect("root attestation");
        let membership = accumulator
            .membership_witness(credential.accumulator_leaf_index)
            .expect("membership witness");
        let presentation = prove_selective_disclosure_with_profile(
            &credential,
            &holder,
            &membership,
            &[0],
            PresentationRequest {
                verifier_scope: VERIFIER_SCOPE,
                verifier_challenge: &VERIFIER_CHALLENGE,
                mode: PresentationMode::UnlinkableFresh,
            },
            [26; 32],
            PROFILE,
        )
        .expect("presentation");
        assert_eq!(presentation.disclosed_attrs, vec![(0, ATTRS[0])]);

        let fx = Fixtures {
            root,
            issuer_mldsa_pk,
            oprf_key,
            disclosed: presentation.disclosed_attrs.clone(),
            wire: presentation.to_compact_wire_bytes().expect("presentation wire"),
        };
        assert_eq!(check(&fx, &fx.wire), Some(true));
        fx
    })
}

/// Decode, check the encoding and verify. Returns whether the presentation verified.
fn check(fx: &Fixtures, bytes: &[u8]) -> Option<bool> {
    let presentation = SelectiveDisclosurePresentation::from_compact_wire_bytes(bytes).ok()?;
    let reencoded = presentation
        .to_compact_wire_bytes()
        .expect("decoded presentation re-encodes");
    assert_eq!(reencoded, bytes);
    let verify = |schema_id: u64, challenge: &[u8; 32]| {
        verify_presentation_with_profile(
            &presentation,
            &fx.root,
            &fx.issuer_mldsa_pk,
            &fx.oprf_key,
            VERIFIER_SCOPE,
            challenge,
            PresentationMode::UnlinkableFresh,
            schema_id,
            ATTRS.len(),
            PROFILE,
        )
    };
    let verified = verify(SCHEMA_ID, &VERIFIER_CHALLENGE);
    if verified {
        assert_eq!(presentation.disclosed_attrs, fx.disclosed, "forged disclosure");
        // The proof is bound to the verifier's schema and challenge.
        assert!(!verify(SCHEMA_ID + 1, &VERIFIER_CHALLENGE));
        assert!(!verify(SCHEMA_ID, &[28; 32]));
    }
    Some(verified)
}

fuzz_target!(init: {
    fixtures();
}, |data: &[u8]| {
    let fx = fixtures();

    // 1. Raw bytes: the decoder's magic, bounds and exact-length checks.
    let _ = check(fx, data);

    // 2. Sparse `(offset: u32 LE, xor: u8)` edits of the real presentation. `[0xed, 0]`
    //    spreads them over the whole encoding, `[0xed, 1]` over its first 4 KiB, where the
    //    statement fields live.
    if let [0xed, kind, edits @ ..] = data {
        let window = if kind & 1 == 0 { fx.wire.len() } else { fx.wire.len().min(4096) };
        let mut candidate = fx.wire.clone();
        for edit in edits.as_chunks::<5>().0 {
            let offset = u32::from_le_bytes([edit[0], edit[1], edit[2], edit[3]]) as usize;
            candidate[offset % window] ^= edit[4];
        }
        let outcome = check(fx, &candidate);
        if candidate == fx.wire {
            assert_eq!(outcome, Some(true));
        }
    }
});
