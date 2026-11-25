// SPDX-License-Identifier: Apache-2.0 OR MIT
#![no_main]

//! Coverage-guided hostile wire-decoder & canonical roundtrip fuzzer across
//! `qsag-core` (FIPS 205 `SLH-DSA` keys/signatures/SPKI/ADRS for all six SHAKE parameter
//! sets), `qsag-fts` (`FrontierSumFts` signatures & `RotatedEpochVote` in both profiles), `qsag-cred` (FIPS 204 `ML-DSA-44/65/87`
//! `pk_decode` and `sig_decode`), and `qsag-addr` (`Bech32m` `QsagAddress`,
//! `HybridPinnedEnvelope`, and 128-byte `CanonicalIntent128`).
//!
//! Every fixture is built in `LLVMFuzzerInitialize` (the `init:` block), before libFuzzer
//! arms its per-input watchdog.

use libfuzzer_sys::fuzz_target;
use qsag_addr::{
    HybridPinnedEnvelope, QsagAddress, decode_intent_128, decode_verified_intent_128,
    encode_intent_128, try_encode_intent_128,
};
use qsag_core::fips205::{Fips205Params, SlhPublicKey, decode_slh_sig, slh_verify};
use qsag_core::tsw_baggy::decode_adrs;
use qsag_cred::{MlDsaLevel, ml_dsa_verify, pk_decode, pk_encode, sig_decode, sig_encode};
use qsag_fts::{
    FrontierDpTable, FrontierFtsProfile, FrontierFtsPublicKey, FrontierFtsSignature,
    RotatedEpochVote, verify_frontier_fts,
};
use std::sync::OnceLock;

struct Fixtures {
    dp_compact: FrontierDpTable,
    dp_full: FrontierDpTable,
}

fn fixtures() -> &'static Fixtures {
    static FX: OnceLock<Fixtures> = OnceLock::new();
    FX.get_or_init(|| Fixtures {
        dp_compact: FrontierDpTable::build(FrontierFtsProfile::Compact1122),
        dp_full: FrontierDpTable::build(FrontierFtsProfile::Full256Bit),
    })
}

fuzz_target!(init: {
    fixtures();
}, |data: &[u8]| {
    let fx = fixtures();

    // 1. `qsag-addr`: Bech32m address codec, HybridPinnedEnvelope, and CanonicalIntent128
    if let Ok(s) = core::str::from_utf8(data) {
        if let Ok(addr) = QsagAddress::decode(s) {
            let reencoded = addr.encode().expect("decoded QsagAddress must re-encode");
            let addr2 = QsagAddress::decode(&reencoded).expect("roundtrip QsagAddress::decode");
            assert_eq!(addr, addr2);
        }
        let _ = QsagAddress::decode_for_hrp(s, "qsp");
    }
    if let Ok(env) = HybridPinnedEnvelope::from_bytes(data) {
        let wire = env.to_bytes().expect("valid HybridPinnedEnvelope must serialize");
        assert_eq!(wire.as_slice(), data);
    }
    if let Ok(arr128) = <[u8; 128]>::try_from(data) {
        if let Some(intent) = decode_intent_128(&arr128) {
            assert_eq!(encode_intent_128(&intent), arr128);
        }
        // The MIR-verified intent namespace shares the canonical wire words, so whatever it
        // accepts (after the canonical `(suite, kind)` check) is the same intent the canonical
        // decoder reads, and it re-encodes to the input bytes. The converse need not hold: the
        // verified namespace admits only a subset of the canonical suites.
        if let Some(v_intent) = decode_verified_intent_128(&arr128) {
            assert_eq!(v_intent.validate(), Ok(()));
            assert_eq!(decode_intent_128(&arr128), Some(v_intent));
            assert_eq!(
                decode_intent_128(&encode_intent_128(&v_intent)),
                Some(v_intent)
            );
            assert_eq!(
                try_encode_intent_128(&v_intent).expect("validated intent must encode"),
                arr128
            );
        }
    }

    // 2. `qsag-core`: FIPS 205 SLH-DSA public keys, SPKI DER, ADRS, and signature verification
    if let Ok(arr32) = <[u8; 32]>::try_from(data) {
        let _ = decode_adrs(&arr32);
    }
    if let Ok(pk) = SlhPublicKey::from_bytes(data) {
        assert_eq!(pk.to_bytes(), data);
    }
    if let Ok((params, pk)) = SlhPublicKey::from_spki_der(data) {
        let der = pk.to_spki_der(&params).expect("decoded SPKI key must re-encode");
        assert_eq!(der, data);
    }
    for params in [
        Fips205Params::SLH_DSA_SHAKE_128S,
        Fips205Params::SLH_DSA_SHAKE_128F,
        Fips205Params::SLH_DSA_SHAKE_192S,
        Fips205Params::SLH_DSA_SHAKE_192F,
        Fips205Params::SLH_DSA_SHAKE_256S,
        Fips205Params::SLH_DSA_SHAKE_256F,
    ] {
        if let Ok(pk) = SlhPublicKey::from_bytes_for_params(&params, data) {
            assert_eq!(pk.to_bytes(), data);
        }
        let _ = decode_slh_sig(&params, data);
        let dummy_pk = SlhPublicKey::new(&[0x42; 32][..params.n], &[0x24; 32][..params.n])
            .expect("n-byte seed and root form a public key");
        let _ = slh_verify(&params, b"fuzz-slh-msg", data, b"ctx", &dummy_pk);
    }

    // 3. `qsag-cred`: FIPS 204 ML-DSA-44 / 65 / 87 untrusted `pk_decode`, `sig_decode`, `ml_dsa_verify`
    for level in [MlDsaLevel::MlDsa44, MlDsaLevel::MlDsa65, MlDsaLevel::MlDsa87] {
        let p = &level.params();
        if let Some((rho, t1)) = pk_decode(p, data) {
            assert_eq!(pk_encode(p, &rho, &t1), data);
        }
        if let Some((c_tilde, z, h)) = sig_decode(p, data) {
            assert_eq!(sig_encode(p, &c_tilde, &z, &h), data);
        }
        let dummy_pk = vec![0u8; p.pk_bytes];
        let _ = ml_dsa_verify(level, &dummy_pk, b"fuzz-mldsa", b"ctx", data);
    }

    // 4. `qsag-fts`: FrontierSumFts signatures and `RotatedEpochVote`, decoded, re-encoded
    //    and verified in both profiles.
    for (profile, dp) in [
        (FrontierFtsProfile::Compact1122, &fx.dp_compact),
        (FrontierFtsProfile::Full256Bit, &fx.dp_full),
    ] {
        let node_bytes = profile.params().node_bytes;
        if let Ok(sig) = FrontierFtsSignature::from_bytes(profile, data) {
            assert_eq!(sig.to_bytes(profile).as_slice(), data);
            let dummy_pk = FrontierFtsPublicKey {
                profile,
                pk_seed: [0x11; 32],
                root: vec![0x22; node_bytes],
            };
            let _ = verify_frontier_fts(&dummy_pk, dp, b"fuzz-fts", &sig);
        }
        if let Ok(vote) = RotatedEpochVote::from_bytes(profile, data) {
            assert_eq!(vote.to_bytes(profile).as_slice(), data);
            let dummy_pk = FrontierFtsPublicKey {
                profile,
                pk_seed: [0x33; 32],
                root: vec![0x44; node_bytes],
            };
            let _ = vote.verify(&dummy_pk, dp, &[0x55; 32], 1, &[0x66; 32]);
        }
    }

});
