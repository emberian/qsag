// SPDX-License-Identifier: Apache-2.0 OR MIT
//! NIST FIPS 204 (`ML-DSA-44`, `ML-DSA-65`, `ML-DSA-87`), Zen 5 `AVX-512` / `AVX2`
//! Seiler Signed-Montgomery NTT Differential PBT (`10,000+` polynomials), and 2-of-3 Dealerless
//! Threshold `ML-DSA` Cross-Verification Against Upstream `fips204` (`v0.4`).

use std::collections::BTreeSet;
use std::sync::{Arc, Condvar, Mutex};

use fips204::traits::{KeyGen, SerDes, Signer, Verifier};
use fips204::{ml_dsa_44, ml_dsa_65, ml_dsa_87};
use proptest::prelude::*;
use qsag_asm::{
    SimdBackend, detect_backend, mldsa_inv_ntt_with_backend, mldsa_ntt_with_backend,
    mldsa_pointwise_mul_with_backend, probe_capabilities,
};
use qsag_cred::{
    FsNonceBurnStore, MLDSA_N, MLDSA_Q, MlDsaLevel, MpcTransport, MpcTransportError,
    NonceBurnPersistence, Poly256, RoundInbox, RoundInfo, RoundKind, ThresholdMlDsaDkgConfig,
    ThresholdMlDsaError, ThresholdMlDsaSignerShare, ThresholdSignOutput, ThresholdSignSession,
    ml_dsa_keygen_from_seed, ml_dsa_sign_deterministic, ml_dsa_verify, threshold_mldsa_dkg_party,
    threshold_sign_mldsa_party,
};
use qsag_external_validation::{ALL_SIMD_BACKENDS, mldsa_poly_mul_negacyclic_ref};

fn poly_u32_strategy() -> impl Strategy<Value = [u32; MLDSA_N]> {
    prop::collection::vec(
        prop_oneof![
            8 => 0u32..MLDSA_Q,
            1 => Just(0u32),
            1 => Just(1u32),
            1 => Just(MLDSA_Q / 2),
            1 => Just(MLDSA_Q - 1),
        ],
        MLDSA_N,
    )
    .prop_map(|v| v.try_into().unwrap())
}

#[test]
fn seiler_ntt_extremal_boundary_exhaustion_across_all_backends() {
    let caps = probe_capabilities();
    if std::env::var("QSAG_REQUIRE_AVX512").as_deref() == Ok("1") {
        assert!(
            caps.avx512,
            "QSAG_REQUIRE_AVX512=1 requires AVX-512 capability on target host"
        );
        assert_eq!(detect_backend(), SimdBackend::X86Avx512GfniVpclmul);
    }

    let qm1 = MLDSA_Q - 1;
    let extremes: [[u32; MLDSA_N]; 6] = [
        [0; MLDSA_N],
        [1; MLDSA_N],
        [qm1; MLDSA_N],
        core::array::from_fn(|i| if i % 2 == 0 { qm1 } else { 0 }),
        core::array::from_fn(|i| if i < 128 { qm1 } else { 1 }),
        core::array::from_fn(|i| ((i as u64 * 104_729 + 8_380_400) % (MLDSA_Q as u64)) as u32),
    ];

    for a in &extremes {
        for b in &extremes {
            let a_i32: [i32; MLDSA_N] = core::array::from_fn(|i| a[i] as i32);
            let b_i32: [i32; MLDSA_N] = core::array::from_fn(|i| b[i] as i32);
            let expected_i32 = mldsa_poly_mul_negacyclic_ref(&a_i32, &b_i32);
            let expected: [u32; MLDSA_N] = core::array::from_fn(|i| expected_i32[i] as u32);

            for backend in ALL_SIMD_BACKENDS {
                let mut a_hat = *a;
                let mut b_hat = *b;
                mldsa_ntt_with_backend(&mut a_hat, backend);
                mldsa_ntt_with_backend(&mut b_hat, backend);

                // Verify roundtrip `InvNTT(NTT(a)) == a`
                let mut roundtrip = a_hat;
                mldsa_inv_ntt_with_backend(&mut roundtrip, backend);
                assert_eq!(&roundtrip, a, "InvNTT(NTT(a)) mismatch on {backend:?}");

                // Verify negacyclic convolution `InvNTT(PointwiseMul(NTT(a), NTT(b))) == a * b mod (X^256 + 1, q)`
                let mut prod_hat = [0u32; MLDSA_N];
                mldsa_pointwise_mul_with_backend(&mut prod_hat, &a_hat, &b_hat, backend);
                mldsa_inv_ntt_with_backend(&mut prod_hat, backend);
                assert_eq!(
                    prod_hat, expected,
                    "negacyclic convolution mismatch on {backend:?}"
                );
            }
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10_000))]

    /// 10,000-case property-based test checking `qsag_asm` (`AVX-512`, `AVX2`, `Portable`) and
    /// `qsag_cred::Poly256` NTT roundtrip, linearity, and pointwise Montgomery multiplication!
    #[test]
    fn seiler_ntt_10000_poly_roundtrip_linearity_and_pointwise_equivalence(
        a in poly_u32_strategy(),
        b in poly_u32_strategy(),
        alpha in 0u32..MLDSA_Q,
    ) {
        let mut ref_ntt_a = a;
        let mut ref_ntt_b = b;
        mldsa_ntt_with_backend(&mut ref_ntt_a, SimdBackend::Portable);
        mldsa_ntt_with_backend(&mut ref_ntt_b, SimdBackend::Portable);

        let mut ref_pw = [0u32; MLDSA_N];
        mldsa_pointwise_mul_with_backend(&mut ref_pw, &ref_ntt_a, &ref_ntt_b, SimdBackend::Portable);

        // Linear combination `NTT(alpha * a + b) == alpha * NTT(a) + NTT(b) (mod q)`
        let lin_in: [u32; MLDSA_N] = core::array::from_fn(|i| {
            (((alpha as u64) * (a[i] as u64) + (b[i] as u64)) % (MLDSA_Q as u64)) as u32
        });
        let expected_lin_hat: [u32; MLDSA_N] = core::array::from_fn(|i| {
            (((alpha as u64) * (ref_ntt_a[i] as u64) + (ref_ntt_b[i] as u64)) % (MLDSA_Q as u64)) as u32
        });

        for backend in [SimdBackend::X86Avx2Pclmul, SimdBackend::X86Avx512GfniVpclmul] {
            let mut got_a = a;
            mldsa_ntt_with_backend(&mut got_a, backend);
            prop_assert_eq!(got_a, ref_ntt_a);

            let mut got_lin = lin_in;
            mldsa_ntt_with_backend(&mut got_lin, backend);
            prop_assert_eq!(got_lin, expected_lin_hat);

            let mut got_pw = [0u32; MLDSA_N];
            mldsa_pointwise_mul_with_backend(&mut got_pw, &got_a, &ref_ntt_b, backend);
            prop_assert_eq!(got_pw, ref_pw);

            let mut inv_a = got_a;
            mldsa_inv_ntt_with_backend(&mut inv_a, backend);
            prop_assert_eq!(inv_a, a);
        }

        // Cross-check `qsag_cred::Poly256` against `qsag_asm`
        let mut cred_poly = Poly256 { coeffs: a };
        cred_poly.ntt();
        prop_assert_eq!(cred_poly.coeffs, ref_ntt_a);
        cred_poly.inv_ntt();
        prop_assert_eq!(cred_poly.coeffs, a);
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(512))]

    /// Full negacyclic polynomial ring homomorphism `InvNTT(NTT(a) ⊙ NTT(b)) == a * b mod (X^256 + 1, q)`
    /// against `O(N^2)` schoolbook reference in `Z_q[X]/(X^256 + 1)`.
    #[test]
    fn seiler_avx512_ntt_matches_schoolbook_negacyclic_ring_product(
        a in poly_u32_strategy(),
        b in poly_u32_strategy(),
    ) {
        let a_i32: [i32; MLDSA_N] = core::array::from_fn(|i| a[i] as i32);
        let b_i32: [i32; MLDSA_N] = core::array::from_fn(|i| b[i] as i32);
        let expected_i32 = mldsa_poly_mul_negacyclic_ref(&a_i32, &b_i32);
        let expected: [u32; MLDSA_N] = core::array::from_fn(|i| expected_i32[i] as u32);

        for backend in [
            SimdBackend::Portable,
            SimdBackend::X86Avx2Pclmul,
            SimdBackend::X86Avx512GfniVpclmul,
        ] {
            let mut fa = a;
            let mut fb = b;
            mldsa_ntt_with_backend(&mut fa, backend);
            mldsa_ntt_with_backend(&mut fb, backend);
            let mut fc = [0u32; MLDSA_N];
            mldsa_pointwise_mul_with_backend(&mut fc, &fa, &fb, backend);
            mldsa_inv_ntt_with_backend(&mut fc, backend);
            prop_assert_eq!(fc, expected);
        }
    }
}

macro_rules! mldsa_fips204_diff_suite {
    ($mod_name:ident, $level:expr, $up_mod:ident, $cases:expr) => {
        mod $mod_name {
            use super::*;

            proptest! {
                #![proptest_config(ProptestConfig::with_cases($cases))]

                /// Deterministic `ML-DSA.KeyGen_internal(\xi)` + `ML-DSA.Sign(\xi, M, ctx, rnd=0^32)`
                /// byte-for-byte identity & bidirectional verification against upstream `fips204`!
                #[test]
                fn keygen_deterministic_sign_and_bidirectional_verify(
                    xi in any::<[u8; 32]>(),
                    rnd in any::<[u8; 32]>(),
                    msg in prop::collection::vec(any::<u8>(), 0..1024),
                    ctx in prop::collection::vec(any::<u8>(), 0..=255),
                    flip_pos in any::<usize>(),
                    flip_bit in 0u8..8u8,
                ) {
                    let (q_pk_bytes, q_sk) = ml_dsa_keygen_from_seed($level, &xi);
                    let (u_pk, u_sk) = $up_mod::KG::keygen_from_seed(&xi);

                    // 1. Public keys MUST be byte-for-byte identical!
                    let u_pk_bytes = u_pk.clone().into_bytes();
                    prop_assert_eq!(q_pk_bytes.as_slice(), u_pk_bytes.as_slice());

                    // 2. Deterministic signatures (`rnd = [0u8; 32]`) MUST be byte-for-byte identical!
                    let q_sig_det = ml_dsa_sign_deterministic(&q_sk, &msg, &ctx)
                        .expect("qsag ml_dsa_sign_deterministic");
                    let u_sig_det = u_sk
                        .try_sign_with_seed(&[0u8; 32], &msg, &ctx)
                        .expect("upstream try_sign_with_seed(0)");
                    prop_assert_eq!(q_sig_det.as_slice(), u_sig_det.as_slice());

                    // 3. Both verifiers accept deterministic & hedged upstream signatures
                    prop_assert!(ml_dsa_verify($level, &q_pk_bytes, &msg, &ctx, &q_sig_det));
                    prop_assert!(u_pk.verify(&msg, &u_sig_det, &ctx));

                    let u_sig_hedged = u_sk
                        .try_sign_with_seed(&rnd, &msg, &ctx)
                        .expect("upstream hedged try_sign_with_seed");
                    prop_assert!(ml_dsa_verify($level, &q_pk_bytes, &msg, &ctx, &u_sig_hedged));
                    prop_assert!(u_pk.verify(&msg, &u_sig_hedged, &ctx));

                    // 4. Single-bit signature mutation rejected by BOTH implementations
                    let mut bad_sig = u_sig_det;
                    let idx = flip_pos % $up_mod::SIG_LEN;
                    bad_sig[idx] ^= 1u8 << flip_bit;
                    prop_assert!(!u_pk.verify(&msg, &bad_sig, &ctx));
                    prop_assert!(!ml_dsa_verify($level, &q_pk_bytes, &msg, &ctx, &bad_sig));

                    // 5. Context mismatch rejected by BOTH implementations
                    let mut bad_ctx = ctx.clone();
                    if bad_ctx.len() < 255 {
                        bad_ctx.push(0xA5);
                    } else {
                        bad_ctx.pop();
                    }
                    prop_assert!(!u_pk.verify(&msg, &u_sig_det, &bad_ctx));
                    prop_assert!(!ml_dsa_verify($level, &q_pk_bytes, &msg, &bad_ctx, &q_sig_det));
                }
            }
        }
    };
}

mldsa_fips204_diff_suite!(diff_ml_dsa_44, MlDsaLevel::MlDsa44, ml_dsa_44, 128);
mldsa_fips204_diff_suite!(diff_ml_dsa_65, MlDsaLevel::MlDsa65, ml_dsa_65, 96);
mldsa_fips204_diff_suite!(diff_ml_dsa_87, MlDsaLevel::MlDsa87, ml_dsa_87, 64);

// ============================================================================
// In-Memory Synchronous MPC Network for 2-of-3 Threshold ML-DSA Interop
// ============================================================================

struct Posted {
    kind: RoundKind,
    private: Vec<Vec<u8>>,
    broadcast: Vec<u8>,
}

struct NetState {
    round: u64,
    posted: Vec<Option<Posted>>,
    taken: Vec<bool>,
    stopped: bool,
}

struct LocalNet {
    state: Mutex<NetState>,
    changed: Condvar,
}

struct Endpoint {
    net: Arc<LocalNet>,
    me: usize,
}

impl MpcTransport for Endpoint {
    fn exchange(
        &mut self,
        info: RoundInfo,
        private: Vec<Vec<u8>>,
        broadcast: Vec<u8>,
    ) -> Result<RoundInbox, MpcTransportError> {
        let mut state = self.net.state.lock().unwrap();
        if state.stopped {
            return Err(MpcTransportError);
        }
        let my_round = state.round;
        state.posted[self.me] = Some(Posted {
            kind: info.kind,
            private,
            broadcast,
        });
        self.net.changed.notify_all();
        while !state.posted.iter().all(Option::is_some) && !state.stopped {
            state = self.net.changed.wait(state).unwrap();
        }
        if !state.posted.iter().all(Option::is_some) {
            return Err(MpcTransportError);
        }
        let parties = state.posted.len();
        let mut inbox = RoundInbox {
            private: vec![Vec::new(); parties],
            broadcast: vec![Vec::new(); parties],
        };
        for sender in 0..parties {
            let posted = state.posted[sender].as_ref().unwrap();
            if posted.kind != info.kind {
                return Err(MpcTransportError);
            }
            if sender != self.me {
                inbox.private[sender] = posted.private[self.me].clone();
                inbox.broadcast[sender] = posted.broadcast.clone();
            }
        }
        state.taken[self.me] = true;
        if state.taken.iter().all(|&t| t) {
            for slot in &mut state.posted {
                *slot = None;
            }
            state.taken.fill(false);
            state.round += 1;
            self.net.changed.notify_all();
        } else {
            while state.round == my_round && !state.stopped {
                state = self.net.changed.wait(state).unwrap();
            }
        }
        Ok(inbox)
    }
}

impl Drop for Endpoint {
    fn drop(&mut self) {
        let mut state = self.net.state.lock().unwrap();
        state.stopped = true;
        self.net.changed.notify_all();
    }
}

fn run_mpc_parties<S: Send, R: Send>(
    states: Vec<S>,
    f: impl Fn(usize, S, &mut Endpoint) -> R + Sync,
) -> Vec<R> {
    let parties = states.len();
    let net = Arc::new(LocalNet {
        state: Mutex::new(NetState {
            round: 0,
            posted: (0..parties).map(|_| None).collect(),
            taken: vec![false; parties],
            stopped: false,
        }),
        changed: Condvar::new(),
    });
    std::thread::scope(|scope| {
        let handles: Vec<_> = states
            .into_iter()
            .enumerate()
            .map(|(me, state)| {
                let mut endpoint = Endpoint {
                    net: net.clone(),
                    me,
                };
                let f = &f;
                scope.spawn(move || f(me, state, &mut endpoint))
            })
            .collect();
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    })
}

/// A custodian's nonce ledger that enforces the [`NonceBurnPersistence`] contract in
/// memory: an epoch is granted only above every earlier one, a `(session, attempt)` pair
/// only once, and both only for the key and custodian the ledger was provisioned for.
struct StrictBurnLedger {
    key_id: [u8; 32],
    party_id: u16,
    max_epoch: Option<u64>,
    burned: BTreeSet<([u8; 32], u32)>,
    granted: u32,
    refused: u32,
}

impl StrictBurnLedger {
    fn provision(share: &ThresholdMlDsaSignerShare) -> Self {
        Self {
            key_id: share.verification_pack().policy_signing_key_id(),
            party_id: share.party_id(),
            max_epoch: None,
            burned: BTreeSet::new(),
            granted: 0,
            refused: 0,
        }
    }
}

impl NonceBurnPersistence for StrictBurnLedger {
    fn reserve(&mut self, party_id: u16, epoch: u64, session_id: &[u8; 32], attempt: u32) -> bool {
        let fresh = party_id == self.party_id
            && epoch != u64::MAX
            && self.max_epoch.is_none_or(|max| epoch > max)
            && !self.burned.contains(&(*session_id, attempt));
        if !fresh {
            self.refused += 1;
            return false;
        }
        self.max_epoch = Some(epoch);
        self.burned.insert((*session_id, attempt));
        self.granted += 1;
        true
    }

    fn next_epoch(&self, key_id: &[u8; 32], party_id: u16) -> Result<u64, ThresholdMlDsaError> {
        if *key_id != self.key_id || party_id != self.party_id {
            return Err(ThresholdMlDsaError::NoncePersistenceFailed);
        }
        Ok(self.max_epoch.map_or(0, |max| max + 1))
    }
}

/// Runs the dealerless key generation for `party_ids` (ascending) and returns the public
/// key with every custodian's share.
fn threshold_mldsa_dkg(
    level: MlDsaLevel,
    threshold: usize,
    party_ids: &[u16],
    session_tag: u8,
) -> (Vec<u8>, Vec<ThresholdMlDsaSignerShare>) {
    let dkg_cfg = ThresholdMlDsaDkgConfig {
        level,
        threshold,
        party_ids: party_ids.to_vec(),
        session_id: [session_tag; 32],
    };
    let shares: Vec<ThresholdMlDsaSignerShare> =
        run_mpc_parties(party_ids.to_vec(), |me, id, net| {
            let entropy = [session_tag.wrapping_add((me as u8) * 17 + 3); 32];
            threshold_mldsa_dkg_party(&dkg_cfg, id, &entropy, net).expect("threshold ML-DSA DKG")
        });
    let pk_bytes = shares[0].verification_pack().pk_bytes.clone();
    for (share, &id) in shares.iter().zip(party_ids) {
        assert_eq!(share.party_id(), id);
        assert_eq!(share.verification_pack().pk_bytes, pk_bytes);
        assert_eq!(share.verification_pack().signing_quorum(), 2 * threshold - 1);
    }
    (pk_bytes, shares)
}

/// One signing session among the custodians named by `quorum` (ascending). `burns[i]`
/// is the ledger of `shares[i]`. Returns each quorum member's result in quorum order.
fn threshold_mldsa_sign_quorum<B: NonceBurnPersistence + Send>(
    shares: &mut [ThresholdMlDsaSignerShare],
    burns: &mut [B],
    quorum: &[u16],
    session_id: [u8; 32],
    msg: &[u8],
    ctx: &[u8],
) -> Vec<Result<ThresholdSignOutput, ThresholdMlDsaError>> {
    let session = ThresholdSignSession {
        session_id,
        quorum: quorum.to_vec(),
    };
    let members: Vec<(&mut ThresholdMlDsaSignerShare, &mut B)> = shares
        .iter_mut()
        .zip(burns.iter_mut())
        .filter(|(share, _)| quorum.contains(&share.party_id()))
        .collect();
    run_mpc_parties(members, |me, (share, burn), net| {
        let mut entropy = session_id;
        entropy[0] ^= 0x41;
        entropy[1] = entropy[1].wrapping_add(me as u8 * 29);
        threshold_sign_mldsa_party(share, &session, msg, ctx, &entropy, burn, net)
    })
}

/// Upstream `fips204` verification of `sig` under `pk` for the parameter set of `level`.
fn upstream_fips204_verify(level: MlDsaLevel, pk: &[u8], msg: &[u8], sig: &[u8], ctx: &[u8]) -> bool {
    match level {
        MlDsaLevel::MlDsa44 => {
            let pk = ml_dsa_44::PublicKey::try_from_bytes(pk.try_into().expect("ML-DSA-44 pk length"))
                .expect("upstream ml_dsa_44 PublicKey::try_from_bytes");
            sig.try_into().is_ok_and(|sig: &[u8; ml_dsa_44::SIG_LEN]| pk.verify(msg, sig, ctx))
        }
        MlDsaLevel::MlDsa65 => {
            let pk = ml_dsa_65::PublicKey::try_from_bytes(pk.try_into().expect("ML-DSA-65 pk length"))
                .expect("upstream ml_dsa_65 PublicKey::try_from_bytes");
            sig.try_into().is_ok_and(|sig: &[u8; ml_dsa_65::SIG_LEN]| pk.verify(msg, sig, ctx))
        }
        MlDsaLevel::MlDsa87 => {
            let pk = ml_dsa_87::PublicKey::try_from_bytes(pk.try_into().expect("ML-DSA-87 pk length"))
                .expect("upstream ml_dsa_87 PublicKey::try_from_bytes");
            sig.try_into().is_ok_and(|sig: &[u8; ml_dsa_87::SIG_LEN]| pk.verify(msg, sig, ctx))
        }
    }
}

/// Every subset of `ids` with exactly `size` members, each ascending.
fn subsets_of_size(ids: &[u16], size: usize) -> Vec<Vec<u16>> {
    (0u32..1 << ids.len())
        .filter(|mask| mask.count_ones() as usize == size)
        .map(|mask| {
            ids.iter()
                .enumerate()
                .filter(|(bit, _)| mask >> bit & 1 == 1)
                .map(|(_, &id)| id)
                .collect()
        })
        .collect()
}

/// For one committee: every quorum of at least `2t - 1` custodians signs a standard
/// signature that upstream `fips204` accepts and that fails after any single bit flip;
/// every smaller quorum and every quorum naming a stranger is refused before a signature
/// exists. Each ledger grants exactly as many reservations as the signer reports attempts.
fn check_threshold_mldsa_committee(level: MlDsaLevel, threshold: usize, party_ids: &[u16], tag: u8) {
    let msg = b"dealerless-threshold-mldsa-verified-by-upstream-fips204";
    let ctx = b"qsag-threshold-fips204-ctx";
    let (pk, mut shares) = threshold_mldsa_dkg(level, threshold, party_ids, tag);
    let mut ledgers: Vec<StrictBurnLedger> = shares.iter().map(StrictBurnLedger::provision).collect();
    let need = 2 * threshold - 1;
    let mut session_counter = 0u8;
    let mut next_session = || {
        session_counter += 1;
        let mut id = [tag ^ 0xA5; 32];
        id[31] = session_counter;
        id
    };

    let mut signatures = BTreeSet::new();
    for size in need..=party_ids.len() {
        for quorum in subsets_of_size(party_ids, size) {
            let granted_before: Vec<u32> = ledgers.iter().map(|l| l.granted).collect();
            let outputs: Vec<ThresholdSignOutput> =
                threshold_mldsa_sign_quorum(&mut shares, &mut ledgers, &quorum, next_session(), msg, ctx)
                    .into_iter()
                    .map(|r| r.unwrap_or_else(|e| panic!("{level:?} quorum {quorum:?}: {e}")))
                    .collect();
            assert_eq!(outputs.len(), quorum.len());
            let sig = &outputs[0].signature;
            for output in &outputs {
                assert_eq!(&output.signature, sig, "{level:?} quorum {quorum:?}");
            }
            for (ledger, before) in ledgers.iter().zip(granted_before) {
                let spent = ledger.granted - before;
                match quorum.iter().position(|&id| id == ledger.party_id) {
                    Some(at) => assert_eq!(spent, outputs[at].attempts, "{level:?} {quorum:?}"),
                    None => assert_eq!(spent, 0, "a custodian outside the quorum burned a nonce"),
                }
                assert_eq!(ledger.refused, 0);
            }

            assert!(upstream_fips204_verify(level, &pk, msg, sig, ctx), "{level:?} {quorum:?}");
            assert!(ml_dsa_verify(level, &pk, msg, ctx, sig));
            assert!(!upstream_fips204_verify(level, &pk, b"another message", sig, ctx));
            assert!(!upstream_fips204_verify(level, &pk, msg, sig, b"another context"));
            for byte in [0, 1, sig.len() / 3, sig.len() / 2, sig.len() - 1] {
                for bit in [0u8, 7] {
                    let mut bad = sig.clone();
                    bad[byte] ^= 1 << bit;
                    assert!(
                        !upstream_fips204_verify(level, &pk, msg, &bad, ctx),
                        "{level:?} {quorum:?}: upstream accepted a flip at byte {byte} bit {bit}"
                    );
                    assert!(
                        !ml_dsa_verify(level, &pk, msg, ctx, &bad),
                        "{level:?} {quorum:?}: qsag accepted a flip at byte {byte} bit {bit}"
                    );
                }
            }
            signatures.insert(sig.clone());
        }
    }
    // Sessions differ, so the hedged nonces and with them the signatures differ.
    let valid_quorums: usize = (need..=party_ids.len())
        .map(|size| subsets_of_size(party_ids, size).len())
        .sum();
    assert_eq!(signatures.len(), valid_quorums);

    // Below `2t - 1` custodians: refused by every member, and no nonce is spent.
    let granted_before: Vec<u32> = ledgers.iter().map(|l| l.granted).collect();
    for size in 1..need {
        for quorum in subsets_of_size(party_ids, size) {
            let results =
                threshold_mldsa_sign_quorum(&mut shares, &mut ledgers, &quorum, next_session(), msg, ctx);
            assert_eq!(results.len(), size);
            for result in results {
                assert_eq!(
                    result.map(|output| output.signature),
                    Err(ThresholdMlDsaError::QuorumTooSmall { have: size, need }),
                    "{level:?} quorum {quorum:?}"
                );
            }
        }
    }
    // A quorum of the right size that names a custodian outside the committee.
    let stranger = party_ids.iter().max().unwrap() + 7;
    let mut with_stranger = party_ids[..need - 1].to_vec();
    with_stranger.push(stranger);
    for result in
        threshold_mldsa_sign_quorum(&mut shares, &mut ledgers, &with_stranger, next_session(), msg, ctx)
    {
        assert_eq!(
            result.map(|output| output.signature),
            Err(ThresholdMlDsaError::DuplicateOrUnknownParty { party_id: stranger })
        );
    }
    let granted_after: Vec<u32> = ledgers.iter().map(|l| l.granted).collect();
    assert_eq!(granted_before, granted_after, "a refused quorum spent a nonce");
}

/// Dealerless threshold `ML-DSA-44`, `-65` and `-87` under upstream `fips204`, for a
/// 2-of-3 committee (whose only signing quorum is all three custodians) and a 2-of-4
/// committee (four quorums of three and one of four).
#[test]
fn threshold_mldsa_44_65_87_every_valid_quorum_verifies_under_upstream_fips204() {
    for (level, tag) in [
        (MlDsaLevel::MlDsa44, 0x44u8),
        (MlDsaLevel::MlDsa65, 0x65),
        (MlDsaLevel::MlDsa87, 0x87),
    ] {
        check_threshold_mldsa_committee(level, 2, &[1, 2, 3], tag);
        check_threshold_mldsa_committee(level, 2, &[2, 5, 7, 11], tag ^ 0x10);
    }
}

/// Signs one session, expects success, and returns the signature.
fn sign_session_ok<B: NonceBurnPersistence + Send>(
    shares: &mut [ThresholdMlDsaSignerShare],
    burns: &mut [B],
    session_id: [u8; 32],
    msg: &[u8],
) -> Vec<u8> {
    let mut signatures: Vec<Vec<u8>> =
        threshold_mldsa_sign_quorum(shares, burns, &[1, 2, 3], session_id, msg, b"burn-ctx")
            .into_iter()
            .map(|r| r.expect("fresh session signs").signature)
            .collect();
    signatures.dedup();
    assert_eq!(signatures.len(), 1);
    signatures.pop().unwrap()
}

/// Signs one session and expects every custodian to stop at its nonce ledger.
fn sign_session_refused_by_ledger<B: NonceBurnPersistence + Send>(
    shares: &mut [ThresholdMlDsaSignerShare],
    burns: &mut [B],
    session_id: [u8; 32],
    msg: &[u8],
) {
    for result in threshold_mldsa_sign_quorum(shares, burns, &[1, 2, 3], session_id, msg, b"burn-ctx") {
        assert_eq!(
            result.map(|output| output.signature),
            Err(ThresholdMlDsaError::NoncePersistenceFailed)
        );
    }
}

/// A signing session cannot be run twice: the second run of the same session identifier
/// (the same or a different message) is refused by each custodian's ledger and yields no
/// signature, while a new session identifier still signs. Checked with the in-memory
/// ledger above and with the crate's durable [`FsNonceBurnStore`], including after the
/// store is closed and reopened. Signing code that stopped consulting the ledger, or a
/// store that forgot its burns, would produce a second signature here.
#[test]
fn threshold_mldsa_nonce_ledger_refuses_a_replayed_session() {
    let level = MlDsaLevel::MlDsa44;
    let (pk, mut shares) = threshold_mldsa_dkg(level, 2, &[1, 2, 3], 0xB7);
    let msg = b"single-use signing session";

    // 1. In-memory ledger.
    let mut ledgers: Vec<StrictBurnLedger> = shares.iter().map(StrictBurnLedger::provision).collect();
    let sig_a = sign_session_ok(&mut shares, &mut ledgers, [0xA1; 32], msg);
    assert!(upstream_fips204_verify(level, &pk, msg, &sig_a, b"burn-ctx"));
    let granted: Vec<u32> = ledgers.iter().map(|l| l.granted).collect();
    sign_session_refused_by_ledger(&mut shares, &mut ledgers, [0xA1; 32], msg);
    sign_session_refused_by_ledger(&mut shares, &mut ledgers, [0xA1; 32], b"a different message");
    for (ledger, before) in ledgers.iter().zip(&granted) {
        assert_eq!(ledger.granted, *before, "a replayed session was granted a nonce");
        assert_eq!(ledger.refused, 2);
    }
    let sig_b = sign_session_ok(&mut shares, &mut ledgers, [0xA2; 32], msg);
    assert!(upstream_fips204_verify(level, &pk, msg, &sig_b, b"burn-ctx"));
    assert_ne!(sig_a, sig_b);

    // 2. The durable store, across a close and reopen.
    let dir = std::env::temp_dir().join(format!(
        "qsag-validation-burn-{}-{:x}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir(&dir).unwrap();
    let key_id = shares[0].verification_pack().policy_signing_key_id();
    let path_of = |party: u16| dir.join(format!("party-{party}.burn"));
    let mac_key_of = |party: u16| [0x60 + party as u8; 32];
    let mut stores: Vec<FsNonceBurnStore> = shares
        .iter()
        .map(|share| {
            let party = share.party_id();
            FsNonceBurnStore::create(path_of(party), key_id, mac_key_of(party)).unwrap()
        })
        .collect();
    let sig_c = sign_session_ok(&mut shares, &mut stores, [0xC1; 32], msg);
    assert!(upstream_fips204_verify(level, &pk, msg, &sig_c, b"burn-ctx"));
    sign_session_refused_by_ledger(&mut shares, &mut stores, [0xC1; 32], msg);
    drop(stores);
    let mut stores: Vec<FsNonceBurnStore> = shares
        .iter()
        .map(|share| {
            let party = share.party_id();
            FsNonceBurnStore::open(path_of(party), key_id, mac_key_of(party)).unwrap()
        })
        .collect();
    sign_session_refused_by_ledger(&mut shares, &mut stores, [0xC1; 32], msg);
    let sig_d = sign_session_ok(&mut shares, &mut stores, [0xC2; 32], msg);
    assert!(upstream_fips204_verify(level, &pk, msg, &sig_d, b"burn-ctx"));
    drop(stores);
    std::fs::remove_dir_all(&dir).unwrap();
}
