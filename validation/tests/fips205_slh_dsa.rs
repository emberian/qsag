// SPDX-License-Identifier: Apache-2.0 OR MIT
//! NIST FIPS 205 (`SLH-DSA-SHAKE`) Bidirectional Interoperability,
//! Bit-Exactness Property-Based Testing (`proptest`), Pre-Hash `HashSLH-DSA`,
//! X.509 SPKI DER, and 2-of-3 Dealerless Threshold MPC (`RssSlhMpcCluster`)
//! Cross-Verification Against Upstream `fips205` (`v0.4`).

use fips205::Ph;
use fips205::traits::{KeyGen, SerDes, Signer, Verifier};
use proptest::prelude::*;
use qsag_core::fips205::{
    CommittedHedgedRandomizer, Fips205Params, HedgedRandomizerOpen, SlhPreHash, SlhPublicKey,
    hash_slh_sign, hash_slh_verify, slh_keygen_internal, slh_keygen_mpc, slh_sign, slh_sign_mpc,
    slh_verify,
};
use qsag_core::keccak_mpc::{RssSlhMpcCluster, run_dealerless_rss_dkg_2of3};
use qsag_core::preprocessing::PartyPrivateRng;

/// Helper macro generating deterministic bit-exactness, bidirectional hedged sign/verify,
/// HashSLH-DSA pre-hash interop, SPKI DER roundtrip, and single-bit mutation rejection
/// `proptest` suites for any `(qsag_params, upstream_module)` pair.
macro_rules! slh_dsa_diff_suite {
    (
        $mod_name:ident,
        $qsag_params:expr,
        $up_mod:ident,
        $seed_len:literal,
        $cases:expr
    ) => {
        mod $mod_name {
            use super::*;

            proptest! {
                #![proptest_config(ProptestConfig::with_cases($cases))]

                #[test]
                fn keygen_deterministic_sign_and_bidirectional_hedged_interop(
                    sk_seed in any::<[u8; $seed_len]>(),
                    sk_prf in any::<[u8; $seed_len]>(),
                    pk_seed in any::<[u8; $seed_len]>(),
                    opt_rand in any::<[u8; $seed_len]>(),
                    msg in prop::collection::vec(any::<u8>(), 0..512),
                    ctx in prop::collection::vec(any::<u8>(), 0..=255),
                    flip_sig_pos in any::<usize>(),
                    flip_bit in 0u8..8u8,
                ) {
                    let params = $qsag_params;

                    // 1A. Keygen bit-exactness (`PK` and `SK` wire bytes)
                    let (q_sk, q_pk) = slh_keygen_internal(&params, &sk_seed, &sk_prf, &pk_seed)
                        .expect("qsag slh_keygen_internal");
                    let (u_pk, u_sk) = $up_mod::KG::keygen_with_seeds(&sk_seed, &sk_prf, &pk_seed);

                    let q_pk_bytes = q_pk.to_bytes();
                    let u_pk_bytes = u_pk.clone().into_bytes();
                    prop_assert_eq!(q_pk_bytes.as_slice(), u_pk_bytes.as_slice());

                    let q_sk_bytes = q_sk.to_bytes();
                    let u_sk_bytes = u_sk.clone().into_bytes();
                    prop_assert_eq!(q_sk_bytes.as_slice(), u_sk_bytes.as_slice());

                    // X.509 SPKI DER roundtrip
                    let spki = q_pk.to_spki_der(&params).expect("to_spki_der");
                    let (parsed_params, parsed_pk) = SlhPublicKey::from_spki_der(&spki)
                        .expect("from_spki_der");
                    prop_assert_eq!(parsed_params, params);
                    prop_assert_eq!(parsed_pk, q_pk);

                    // 1A. Deterministic pure SLH-DSA signature byte-for-byte identity
                    let q_sig_det = slh_sign(&params, &msg, &ctx, &q_sk, None)
                        .expect("qsag deterministic slh_sign");
                    let u_sig_det = u_sk.try_sign(&msg, &ctx, false)
                        .expect("upstream deterministic try_sign");
                    prop_assert_eq!(q_sig_det.as_slice(), u_sig_det.as_slice());

                    // Both verifiers accept
                    prop_assert!(slh_verify(&params, &msg, &q_sig_det, &ctx, &q_pk));
                    prop_assert!(u_pk.verify(&msg, &u_sig_det, &ctx));

                    // 1B. Hedged signing from QSAG -> verified by upstream `fips205`
                    let q_sig_hedged = slh_sign(&params, &msg, &ctx, &q_sk, Some(&opt_rand))
                        .expect("qsag hedged slh_sign");
                    let q_sig_arr: [u8; $up_mod::SIG_LEN] = q_sig_hedged
                        .as_slice()
                        .try_into()
                        .expect("exact SIG_LEN");
                    prop_assert!(u_pk.verify(&msg, &q_sig_arr, &ctx));
                    prop_assert!(slh_verify(&params, &msg, &q_sig_hedged, &ctx, &q_pk));

                    // 1B. Hedged signing from upstream `fips205` -> verified by QSAG
                    let u_sig_hedged = u_sk.try_sign(&msg, &ctx, true)
                        .expect("upstream hedged try_sign");
                    prop_assert!(slh_verify(&params, &msg, &u_sig_hedged, &ctx, &q_pk));
                    prop_assert!(u_pk.verify(&msg, &u_sig_hedged, &ctx));

                    // Single-bit signature corruption rejected by BOTH implementations
                    let mut bad_sig = u_sig_det;
                    let idx = flip_sig_pos % $up_mod::SIG_LEN;
                    bad_sig[idx] ^= 1u8 << flip_bit;
                    prop_assert!(!u_pk.verify(&msg, &bad_sig, &ctx));
                    prop_assert!(!slh_verify(&params, &msg, &bad_sig, &ctx, &q_pk));

                    // Single-bit message corruption rejected by BOTH implementations
                    let mut bad_msg = msg.clone();
                    if bad_msg.is_empty() {
                        bad_msg.push(0x01);
                    } else {
                        bad_msg[0] ^= 1u8 << flip_bit;
                    }
                    prop_assert!(!u_pk.verify(&bad_msg, &u_sig_det, &ctx));
                    prop_assert!(!slh_verify(&params, &bad_msg, &q_sig_det, &ctx, &q_pk));

                    // Single-bit public-key root corruption rejected by BOTH implementations
                    let mut bad_pk_arr = u_pk_bytes;
                    bad_pk_arr[$seed_len + (flip_sig_pos % $seed_len)] ^= 1u8 << flip_bit;
                    let bad_u_pk = $up_mod::PublicKey::try_from_bytes(&bad_pk_arr)
                        .expect("upstream PublicKey::try_from_bytes");
                    let bad_q_pk = SlhPublicKey::from_bytes_for_params(&params, &bad_pk_arr)
                        .expect("qsag SlhPublicKey::from_bytes_for_params");
                    prop_assert!(!bad_u_pk.verify(&msg, &u_sig_det, &ctx));
                    prop_assert!(!slh_verify(&params, &msg, &q_sig_det, &ctx, &bad_q_pk));
                }
            }
        }
    };
}

use fips205::{
    slh_dsa_shake_128f, slh_dsa_shake_128s, slh_dsa_shake_192f, slh_dsa_shake_192s,
    slh_dsa_shake_256f, slh_dsa_shake_256s,
};

// Fast hypertree profiles (`128f`, `192f`, `256f`) with high case counts
slh_dsa_diff_suite!(
    shake_128f,
    Fips205Params::SLH_DSA_SHAKE_128F,
    slh_dsa_shake_128f,
    16,
    64
);
slh_dsa_diff_suite!(
    shake_192f,
    Fips205Params::SLH_DSA_SHAKE_192F,
    slh_dsa_shake_192f,
    24,
    32
);
slh_dsa_diff_suite!(
    shake_256f,
    Fips205Params::SLH_DSA_SHAKE_256F,
    slh_dsa_shake_256f,
    32,
    24
);

// Small-signature hypertree profiles (`128s`, `192s`, `256s` — 512/256 leaves per XMSS tree)
slh_dsa_diff_suite!(
    shake_128s,
    Fips205Params::SLH_DSA_SHAKE_128S,
    slh_dsa_shake_128s,
    16,
    8
);
slh_dsa_diff_suite!(
    shake_192s,
    Fips205Params::SLH_DSA_SHAKE_192S,
    slh_dsa_shake_192s,
    24,
    4
);
slh_dsa_diff_suite!(
    shake_256s,
    Fips205Params::SLH_DSA_SHAKE_256S,
    slh_dsa_shake_256s,
    32,
    4
);

proptest! {
    #![proptest_config(ProptestConfig::with_cases(48))]

    /// NIST FIPS 205 §9.3 Pre-Hash `HashSLH-DSA` (`SHA-256`, `SHA-512`, `SHAKE256`)
    /// byte-for-byte deterministic signature equivalence & oversized `|ctx| > 255` rejection.
    #[test]
    fn hash_slh_dsa_and_oversized_context_differential(
        sk_seed in any::<[u8; 16]>(),
        sk_prf in any::<[u8; 16]>(),
        pk_seed in any::<[u8; 16]>(),
        msg in prop::collection::vec(any::<u8>(), 0..1024),
        ctx in prop::collection::vec(any::<u8>(), 0..=255),
        extra_ctx in prop::collection::vec(any::<u8>(), 256..=300),
    ) {
        let params = Fips205Params::SLH_DSA_SHAKE_128F;
        let (q_sk, q_pk) = slh_keygen_internal(&params, &sk_seed, &sk_prf, &pk_seed).unwrap();
        let (u_pk, u_sk) = slh_dsa_shake_128f::KG::keygen_with_seeds(&sk_seed, &sk_prf, &pk_seed);

        for (q_ph, u_ph) in [
            (SlhPreHash::Sha256, Ph::SHA256),
            (SlhPreHash::Sha512, Ph::SHA512),
            (SlhPreHash::Shake256, Ph::SHAKE256),
        ] {
            let q_sig = hash_slh_sign(&params, q_ph, &msg, &ctx, &q_sk, None).unwrap();
            let u_sig = u_sk.try_hash_sign(&msg, &ctx, &u_ph, false).unwrap();
            prop_assert_eq!(q_sig.as_slice(), u_sig.as_slice());
            prop_assert!(hash_slh_verify(&params, q_ph, &msg, &q_sig, &ctx, &q_pk));
            prop_assert!(u_pk.hash_verify(&msg, &u_sig, &ctx, &u_ph));
        }

        // Oversized context `|ctx| > 255` rejected by BOTH QSAG and upstream `fips205`
        prop_assert!(slh_sign(&params, &msg, &extra_ctx, &q_sk, None).is_err());
        prop_assert!(u_sk.try_sign(&msg, &extra_ctx, false).is_err());
    }
}

/// Full 2-of-3 Dealerless Replicated Secret Sharing (`RssSlhMpcCluster`)
/// Threshold MPC Keygen + Signing Verified Directly Under Upstream `fips205`!
///
/// Proves without central secret reconstruction that `run_dealerless_rss_dkg_2of3`,
/// `slh_keygen_mpc`, and `slh_sign_mpc` (both deterministic and coin-tossed hedged)
/// emit genuine standard-compliant NIST FIPS 205 `SLH-DSA-SHAKE-128f` keys and signatures
/// accepted by `fips205::slh_dsa_shake_128f::PublicKey::verify`!
#[test]
fn threshold_rss_2of3_mpc_slh_dsa_128f_verifies_under_upstream_fips205() {
    let sid = [0x5Au8; 32];
    let mut party_rngs = [
        PartyPrivateRng::from_seed([0x11; 32], b"val-rss-p0"),
        PartyPrivateRng::from_seed([0x22; 32], b"val-rss-p1"),
        PartyPrivateRng::from_seed([0x33; 32], b"val-rss-p2"),
    ];
    let (keys, _) = run_dealerless_rss_dkg_2of3(sid, 16, &mut party_rngs)
        .expect("dealerless 2-of-3 RSS DKG");

    let pk_seed: [u8; 16] = keys[0].pk_seed[..16].try_into().unwrap();
    let params = Fips205Params::SLH_DSA_SHAKE_128F;
    let mut cluster = RssSlhMpcCluster::new(sid, keys, party_rngs).expect("RssSlhMpcCluster::new");

    // 1. Distributed threshold keygen produces canonical 32-byte FIPS 205 public key
    let mpc_pk = slh_keygen_mpc(&params, &mut cluster, &pk_seed).expect("slh_keygen_mpc");
    let mpc_pk_arr: [u8; slh_dsa_shake_128f::PK_LEN] = mpc_pk.to_bytes().try_into().unwrap();
    assert_eq!(&mpc_pk_arr[..16], &pk_seed);
    let u_pk = slh_dsa_shake_128f::PublicKey::try_from_bytes(&mpc_pk_arr)
        .expect("upstream PublicKey::try_from_bytes");

    // 2. Deterministic MPC signature verifies under upstream `fips205` AND is deterministic on repeat!
    let msg = b"threshold-mpc-rss-2of3-slh-dsa-shake-128f-external-interop";
    let ctx = b"nist-fips-205-external-oracle";
    let mpc_sig_det =
        slh_sign_mpc(&params, &mut cluster, msg, ctx, &mpc_pk, None).expect("slh_sign_mpc det");
    let mpc_sig_det_2 =
        slh_sign_mpc(&params, &mut cluster, msg, ctx, &mpc_pk, None).expect("slh_sign_mpc det 2");
    assert_eq!(mpc_sig_det.len(), slh_dsa_shake_128f::SIG_LEN);
    assert_eq!(mpc_sig_det, mpc_sig_det_2);
    let mpc_sig_arr: [u8; slh_dsa_shake_128f::SIG_LEN] = mpc_sig_det.try_into().unwrap();
    assert!(u_pk.verify(msg, &mpc_sig_arr, ctx));
    let mut bad_mpc_sig = mpc_sig_arr;
    bad_mpc_sig[4096] ^= 0x01;
    assert!(!u_pk.verify(msg, &bad_mpc_sig, ctx));

    // 3. Coin-tossed hedged MPC signature (`CommittedHedgedRandomizer`) ALSO verifies under upstream `fips205`!
    let coin_sid = [0xA7u8; 32];
    let roster = [0u64, 1u64, 2u64];
    let (c0, o0) = HedgedRandomizerOpen::commit_and_open(&coin_sid, 0, vec![0x12; 16], [0x81; 32]);
    let (c1, o1) = HedgedRandomizerOpen::commit_and_open(&coin_sid, 1, vec![0x34; 16], [0x82; 32]);
    let (c2, o2) = HedgedRandomizerOpen::commit_and_open(&coin_sid, 2, vec![0x56; 16], [0x83; 32]);
    let hedged = CommittedHedgedRandomizer::from_coin_toss(
        &coin_sid,
        &roster,
        16,
        &[c0, c1, c2],
        &[o0, o1, o2],
    )
    .expect("CommittedHedgedRandomizer::from_coin_toss");

    let mpc_sig_hedged = slh_sign_mpc(&params, &mut cluster, msg, ctx, &mpc_pk, Some(&hedged))
        .expect("slh_sign_mpc hedged");
    let mpc_hedged_arr: [u8; slh_dsa_shake_128f::SIG_LEN] = mpc_sig_hedged.try_into().unwrap();
    assert_ne!(mpc_hedged_arr, mpc_sig_arr);
    assert!(u_pk.verify(msg, &mpc_hedged_arr, ctx));
}
