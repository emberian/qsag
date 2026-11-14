//! Quickstart: FIPS 205 `SLH-DSA-SHAKE` signing and verification, and dealerless 2-of-3 key
//! shares (`qsag-core`).
//!
//! ```bash
//! cargo run --release -p qsag-cli --example slh_dsa_quickstart
//! ```
//!
//! 1. Key generation, hedged and deterministic signing, verification, and the context string,
//!    for `SLH-DSA-SHAKE-128f` (17,088-byte signatures) and `SLH-DSA-SHAKE-128s` (7,856 bytes).
//! 2. The pre-hash variant (`HashSLH-DSA` with SHAKE256) and the SPKI DER public key encoding.
//! 3. Dealerless 2-of-3 replicated key shares (`run_dealerless_rss_dkg_2of3`): three parties
//!    end with shares of `SK.seed` and `SK.prf` and one agreed public seed; no party holds a key.
//!
//! Signing under those shares is `slh_keygen_mpc` and `slh_sign_mpc` over an
//! `RssSlhMpcCluster`; it produces the same standard signatures but takes minutes per
//! signature, so it is not run here.

use qsag_core::fips205::{
    Fips205Params, SlhPreHash, SlhPublicKey, hash_slh_sign, hash_slh_verify, slh_keygen_from_seed,
    slh_sign, slh_verify,
};
use qsag_core::keccak_mpc::run_dealerless_rss_dkg_2of3;
use qsag_core::preprocessing::PartyPrivateRng;

fn main() {
    let message = b"Transfer 250,000 units from treasury vault #7";
    let context = b"treasury:v1";

    println!("=== 1. Sign and verify ===");
    for params in [
        Fips205Params::SLH_DSA_SHAKE_128F,
        Fips205Params::SLH_DSA_SHAKE_128S,
    ] {
        let (secret_key, public_key) =
            slh_keygen_from_seed(&params, b"example master seed").expect("official parameters");
        let hedged = slh_sign(&params, message, context, &secret_key, Some(&[0x5C; 16]))
            .expect("context fits");
        let deterministic =
            slh_sign(&params, message, context, &secret_key, None).expect("context fits");
        assert_eq!(hedged.len(), params.sig_bytes());
        assert_ne!(hedged, deterministic);
        assert_eq!(
            deterministic,
            slh_sign(&params, message, context, &secret_key, None).expect("context fits")
        );
        for signature in [&hedged, &deterministic] {
            assert!(slh_verify(
                &params,
                message,
                signature,
                context,
                &public_key
            ));
            assert!(!slh_verify(
                &params,
                b"another message",
                signature,
                context,
                &public_key
            ));
            assert!(!slh_verify(
                &params,
                message,
                signature,
                b"another context",
                &public_key
            ));
        }
        let mut tampered = hedged.clone();
        tampered[params.sig_bytes() / 2] ^= 1;
        assert!(!slh_verify(
            &params,
            message,
            &tampered,
            context,
            &public_key
        ));
        println!(
            "  [ok] {}: {}-byte public key, {}-byte signature",
            params.name,
            params.pk_bytes(),
            hedged.len()
        );
    }

    println!("\n=== 2. Pre-hash signing and SPKI DER ===");
    let params = Fips205Params::SLH_DSA_SHAKE_128F;
    let (secret_key, public_key) =
        slh_keygen_from_seed(&params, b"example master seed").expect("official parameters");
    let prehashed = hash_slh_sign(
        &params,
        SlhPreHash::Shake256,
        message,
        context,
        &secret_key,
        None,
    )
    .expect("allowed pre-hash");
    assert!(hash_slh_verify(
        &params,
        SlhPreHash::Shake256,
        message,
        &prehashed,
        context,
        &public_key
    ));
    // Pure and pre-hash signatures are domain separated: neither verifies as the other.
    assert!(!slh_verify(
        &params,
        message,
        &prehashed,
        context,
        &public_key
    ));
    let der = public_key
        .to_spki_der(&params)
        .expect("official parameter set");
    assert_eq!(
        SlhPublicKey::from_spki_der(&der).expect("canonical DER"),
        (params, public_key)
    );
    println!(
        "  [ok] pre-hash signature verified; {}-byte SPKI DER round trip",
        der.len()
    );

    println!("\n=== 3. Dealerless 2-of-3 key shares ===");
    let mut rngs = core::array::from_fn(|party| {
        PartyPrivateRng::from_seed([0x11 * (party as u8 + 1); 32], b"example.rss.dkg")
    });
    let (shares, public_seed) =
        run_dealerless_rss_dkg_2of3([0xA0; 32], params.n, &mut rngs).expect("three honest parties");
    assert_eq!(shares.len(), 3);
    assert!(
        shares
            .iter()
            .all(|share| share.pk_seed == shares[0].pk_seed)
    );
    println!(
        "  [ok] 3 parties hold replicated shares; agreed public seed {:02x?}..",
        &public_seed[..4]
    );
}
