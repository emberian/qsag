// SPDX-License-Identifier: Apache-2.0 OR MIT
//! NIST FIPS 204 (`ML-DSA-44`, `ML-DSA-65`, `ML-DSA-87`), Zen 5 `AVX-512` / `AVX2`
//! Seiler Signed-Montgomery NTT Differential PBT (`10,000+` polynomials), and 2-of-3 Dealerless
//! Threshold `ML-DSA` Cross-Verification Against Upstream `fips204` (`v0.4`).

use std::sync::{Arc, Condvar, Mutex};

use fips204::traits::{KeyGen, SerDes, Signer, Verifier};
use fips204::{ml_dsa_44, ml_dsa_65, ml_dsa_87};
use proptest::prelude::*;
use qsag_asm::{
    SimdBackend, detect_backend, mldsa_inv_ntt_with_backend, mldsa_ntt_with_backend,
    mldsa_pointwise_mul_with_backend, probe_capabilities,
};
use qsag_cred::{
    MLDSA_N, MLDSA_Q, MlDsaLevel, MpcTransport, MpcTransportError, NonceBurnPersistence, Poly256,
    RoundInbox, RoundInfo, RoundKind, ThresholdMlDsaDkgConfig, ThresholdMlDsaSignerShare,
    ThresholdSignSession, ml_dsa_keygen_from_seed, ml_dsa_sign_deterministic, ml_dsa_verify,
    threshold_mldsa_dkg_party, threshold_sign_mldsa_party,
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

struct InMemoryBurn;
impl NonceBurnPersistence for InMemoryBurn {
    fn reserve(&mut self, _: u16, _: u64, _: &[u8; 32], _: u32) -> bool {
        true
    }
}

fn run_threshold_mldsa_2of3_sign(
    level: MlDsaLevel,
    session_tag: u8,
    msg: &[u8],
    ctx: &[u8],
) -> (Vec<u8>, Vec<u8>) {
    let party_ids = vec![1u16, 2u16, 3u16];
    let dkg_cfg = ThresholdMlDsaDkgConfig {
        level,
        threshold: 2,
        party_ids: party_ids.clone(),
        session_id: [session_tag; 32],
    };
    let mut shares: Vec<ThresholdMlDsaSignerShare> =
        run_mpc_parties(party_ids.clone(), |me, id, net| {
            let entropy = [session_tag.wrapping_add((me as u8) * 17 + 3); 32];
            threshold_mldsa_dkg_party(&dkg_cfg, id, &entropy, net).expect("threshold ML-DSA DKG")
        });

    let pk_bytes = shares[0].verification_pack().pk_bytes.clone();
    assert_eq!(pk_bytes, shares[1].verification_pack().pk_bytes);
    assert_eq!(pk_bytes, shares[2].verification_pack().pk_bytes);

    let sign_session = ThresholdSignSession {
        session_id: [session_tag ^ 0xA5; 32],
        quorum: vec![1u16, 2u16, 3u16],
    };
    // Run across all 3 RSS custodians (`2t - 1 = 3` active quorum for `t = 2`)
    let outputs = run_mpc_parties(shares.drain(..).collect(), |me, mut share, net| {
        let entropy = [session_tag.wrapping_add((me as u8) * 29 + 0x41); 32];
        let mut burn = InMemoryBurn;
        threshold_sign_mldsa_party(&mut share, &sign_session, msg, ctx, &entropy, &mut burn, net)
            .expect("threshold ML-DSA sign")
    });
    assert_eq!(outputs[0].signature, outputs[1].signature);
    assert_eq!(outputs[1].signature, outputs[2].signature);
    (pk_bytes, outputs.into_iter().next().unwrap().signature)
}

/// Cross-verifies dealerless 2-of-3 threshold `ML-DSA-44`, `ML-DSA-65`, and `ML-DSA-87`
/// public keys and signatures directly under **upstream `fips204::{ml_dsa_44, ml_dsa_65, ml_dsa_87}`**!
#[test]
fn threshold_mldsa_44_65_87_dkg_and_signatures_verify_under_upstream_fips204() {
    let msg = b"dealerless-2of3-threshold-mldsa-verified-by-upstream-fips204";
    let ctx = b"qsag-threshold-fips204-ctx";

    // ML-DSA-44
    let (pk44, sig44) = run_threshold_mldsa_2of3_sign(MlDsaLevel::MlDsa44, 0x44, msg, ctx);
    let u_pk44 = ml_dsa_44::PublicKey::try_from_bytes(pk44.as_slice().try_into().unwrap())
        .expect("upstream ml_dsa_44 PublicKey::try_from_bytes");
    let u_sig44: [u8; ml_dsa_44::SIG_LEN] = sig44.as_slice().try_into().unwrap();
    assert!(u_pk44.verify(msg, &u_sig44, ctx));
    let mut bad44 = u_sig44;
    bad44[0] ^= 1;
    assert!(!u_pk44.verify(msg, &bad44, ctx));

    // ML-DSA-65
    let (pk65, sig65) = run_threshold_mldsa_2of3_sign(MlDsaLevel::MlDsa65, 0x65, msg, ctx);
    let u_pk65 = ml_dsa_65::PublicKey::try_from_bytes(pk65.as_slice().try_into().unwrap())
        .expect("upstream ml_dsa_65 PublicKey::try_from_bytes");
    let u_sig65: [u8; ml_dsa_65::SIG_LEN] = sig65.as_slice().try_into().unwrap();
    assert!(u_pk65.verify(msg, &u_sig65, ctx));

    // ML-DSA-87
    let (pk87, sig87) = run_threshold_mldsa_2of3_sign(MlDsaLevel::MlDsa87, 0x87, msg, ctx);
    let u_pk87 = ml_dsa_87::PublicKey::try_from_bytes(pk87.as_slice().try_into().unwrap())
        .expect("upstream ml_dsa_87 PublicKey::try_from_bytes");
    let u_sig87: [u8; ml_dsa_87::SIG_LEN] = sig87.as_slice().try_into().unwrap();
    assert!(u_pk87.verify(msg, &u_sig87, ctx));
}
