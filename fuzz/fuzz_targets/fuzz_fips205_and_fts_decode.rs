// SPDX-License-Identifier: Apache-2.0 OR MIT
#![no_main]

//! Coverage-guided hostile wire-decoder & canonical roundtrip fuzzer across
//! `qsag-core` (FIPS 205 `SLH-DSA` keys/signatures/SPKI/ADRS), `qsag-fts` (`FrontierSumFts`
//! signatures & `RotatedEpochVote`), `qsag-cred` (FIPS 204 `ML-DSA-44/65/87` `pk_decode`
//! and `sig_decode`), and `qsag-addr` (`Bech32m` `QsagAddress`, `HybridPinnedEnvelope`,
//! and 128-byte `CanonicalIntent128`).

use libfuzzer_sys::fuzz_target;
use qsag_addr::{HybridPinnedEnvelope, QsagAddress, decode_intent_128, encode_intent_128};
use qsag_core::fips205::{
    Fips205Params, SlhPublicKey, decode_slh_sig, slh_verify,
};
use qsag_core::tsw_baggy::decode_adrs;
use qsag_cred::{MlDsaLevel, ml_dsa_verify, pk_decode, pk_encode, sig_decode, sig_encode};
use qsag_fts::{
    FrontierDpTable, FrontierFtsProfile, FrontierFtsPublicKey, FrontierFtsSignature,
    RotatedEpochVote, verify_frontier_fts,
};
use std::sync::OnceLock;

fn dp_compact1122() -> &'static FrontierDpTable {
    static DP: OnceLock<FrontierDpTable> = OnceLock::new();
    DP.get_or_init(|| FrontierDpTable::build(FrontierFtsProfile::Compact1122))
}

fuzz_target!(|data: &[u8]| {
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
    if let Ok(arr128) = <[u8; 128]>::try_from(data)
        && let Some(intent) = decode_intent_128(&arr128)
    {
        assert_eq!(encode_intent_128(&intent), arr128);
    }

    // 2. `qsag-core`: FIPS 205 SLH-DSA public keys, SPKI DER, ADRS, and signature verification
    if let Ok(arr32) = <[u8; 32]>::try_from(data) {
        let _ = decode_adrs(&arr32);
    }
    let _ = SlhPublicKey::from_bytes(data);
    for params in [
        Fips205Params::SLH_DSA_SHAKE_128S,
        Fips205Params::SLH_DSA_SHAKE_128F,
        Fips205Params::SLH_DSA_SHAKE_192S,
        Fips205Params::SLH_DSA_SHAKE_256S,
    ] {
        let _ = SlhPublicKey::from_bytes_for_params(&params, data);
        let _ = SlhPublicKey::from_spki_der(&params, data);
        let _ = decode_slh_sig(&params, data);
        let dummy_pk = SlhPublicKey {
            params,
            pk_seed: vec![0x42; params.n],
            pk_root: vec![0x24; params.n],
        };
        let _ = slh_verify(&params, b"fuzz-slh-msg", data, b"ctx", &dummy_pk);
    }

    // 3. `qsag-cred`: FIPS 204 ML-DSA-44 / 65 / 87 untrusted `pk_decode`, `sig_decode`, `ml_dsa_verify`
    for level in [MlDsaLevel::MlDsa44, MlDsaLevel::MlDsa65, MlDsaLevel::MlDsa87] {
        let p = level.params();
        if let Some((rho, t1)) = pk_decode(p, data) {
            assert_eq!(pk_encode(p, &rho, &t1), data);
        }
        if let Some((c_tilde, z, h)) = sig_decode(p, data) {
            assert_eq!(sig_encode(p, &c_tilde, &z, &h), data);
        }
        let dummy_pk = vec![0u8; p.pk_bytes];
        let _ = ml_dsa_verify(level, &dummy_pk, b"fuzz-mldsa", b"ctx", data);
    }

    // 4. `qsag-fts`: FrontierSumFts compact profiles (`514B..=2338B`) & `RotatedEpochVote`
    for profile in [
        FrontierFtsProfile::Compact514,
        FrontierFtsProfile::Compact770,
        FrontierFtsProfile::Compact1122,
        FrontierFtsProfile::Compact1314,
        FrontierFtsProfile::Full256Bit,
    ] {
        if let Ok(sig) = FrontierFtsSignature::from_bytes(profile, data) {
            assert_eq!(sig.to_bytes(profile).as_slice(), data);
            if profile == FrontierFtsProfile::Compact1122 {
                let dummy_pk = FrontierFtsPublicKey {
                    profile,
                    pk_seed: [0x11; 32],
                    root: vec![0x22; 32],
                };
                let _ = verify_frontier_fts(&dummy_pk, dp_compact1122(), b"fuzz-fts", &sig);
            }
        }
        if let Ok(vote) = RotatedEpochVote::from_bytes(profile, data) {
            assert_eq!(vote.to_bytes(profile).as_slice(), data);
            if profile == FrontierFtsProfile::Compact1122 {
                let dummy_pk = FrontierFtsPublicKey {
                    profile,
                    pk_seed: [0x33; 32],
                    root: vec![0x44; 32],
                };
                let _ = vote.verify(&dummy_pk, dp_compact1122(), &[0x55; 32], 1, &[0x66; 32]);
            }
        }
    }
});
