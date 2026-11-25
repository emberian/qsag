// SPDX-License-Identifier: Apache-2.0 OR MIT
#![no_main]

//! Coverage-guided hostile wire-decoder fuzzer for the `qsag-cred` protocol messages:
//!
//! Shamir-SPDZ public records and party shares, `ThresholdVerificationPack::from_bytes` (`QTMLDSP1`) and
//!    `ThresholdMlDsaSignerShare::from_shamir_bytes` (`QTMLDSS1`).
//!
//! Every accepted encoding must re-encode to its input. Honest messages built in
//! `LLVMFuzzerInitialize` (the `init:` block) seed sparse-edit mutations, so the protocol
//! code behind each decoder runs on messages one field away from valid.

use std::sync::OnceLock;

use libfuzzer_sys::fuzz_target;
use qsag_cred::fips204_ntt::{MLDSA_Q, Poly256, power2round};
use qsag_cred::threshold_mldsa::{ThresholdMlDsaSignerShare, ThresholdVerificationPack};
use qsag_cred::voprf_spdz::{SpdzConfig, SpdzPublic, SpdzServer, spdz_dkg};
use qsag_cred::{MlDsaLevel, ml_dsa_verify, pk_encode};

struct Fixtures {
    pack: ThresholdVerificationPack,
    pack_wire: Vec<u8>,
    share_len: usize,
    oprf_public: SpdzPublic,
    oprf_share: Vec<u8>,
}

fn fixtures() -> &'static Fixtures {
    static FX: OnceLock<Fixtures> = OnceLock::new();
    FX.get_or_init(|| {
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

        let servers = spdz_dkg(
            SpdzConfig::new(2, 2).unwrap(), [0x37; 32], &[[0x41; 32], [0x52; 32]],
        ).unwrap();
        Fixtures {
            oprf_public: servers[1].public().clone(),
            oprf_share: servers[1].to_secret_bytes(),
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
    check_pack(data);
    if let Some(&party) = data.get(8) {
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
    }
    let check_oprf_share = |bytes: &[u8]| {
        if let Ok(server) = SpdzServer::from_secret_bytes(bytes, &fx.oprf_public, 1) {
            assert_eq!(server.to_secret_bytes(), bytes);
        }
    };
    check_oprf_share(data);

    // 2. Structured inputs: `[0xed, kind]` selects what the rest of the input drives.
    if let [0xed, kind, rest @ ..] = data {
        match kind % 4 {
            0 => check_pack(&edited(&fx.pack_wire, rest)),
            1 => check_oprf_share(&edited(&fx.oprf_share, rest)),
            2 => {
                let candidate = edited(&fx.oprf_public.to_bytes(), rest);
                if let Ok(record) = SpdzPublic::from_bytes(&candidate) {
                    assert_eq!(record.to_bytes(), candidate);
                }
            }
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
