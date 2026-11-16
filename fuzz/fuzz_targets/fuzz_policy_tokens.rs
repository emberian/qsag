// SPDX-License-Identifier: Apache-2.0 OR MIT
#![no_main]

//! Coverage-guided hostile wire-decoder and verifier fuzzer for the `qsag-policy` bearer
//! tokens: `SpongeMacaroon` (`QSMAC001`, primary tokens and third-party discharges),
//! `PqBiscuit` (`QSBSC001`), `PqBiscuitAuthorityPublicKey` (`QSBSCPK1`) and the tagged
//! secret-key containers `PqBiscuitAuthorityKey` (`QSBSCAK1`) and `PqBiscuitStepKey`
//! (`QSBSCSK1`).
//!
//! Every accepted encoding must re-encode to its input and is then verified against keys the
//! input never saw. Real tokens built in `LLVMFuzzerInitialize` (the `init:` block) seed
//! sparse-edit mutations, so the verifiers also run on tokens one field away from valid.
//!
//! Invariants, each a forgery if it fails:
//! - a macaroon that authenticates under the fixture root key carries the fixture token's
//!   identifier and audience and extends its caveat list (attenuation only appends);
//! - a biscuit that verifies under the fixture authority key is the fixture's sealed token,
//!   byte for byte.

use std::sync::OnceLock;

use libfuzzer_sys::fuzz_target;
use qsag_accel::CpuReferenceBackend;
use qsag_fts::{FrontierDpTable, FrontierFtsProfile};
use qsag_policy::{
    CapabilityError, CapabilityRequest, Caveat, Discharge, MacaroonVerifier, PqBiscuit,
    PqBiscuitAuthorityKey, PqBiscuitAuthorityPublicKey, PqBiscuitStepKey, SpongeMacaroon,
};

const ROOT_KEY: [u8; 32] = [0xA1; 32];
const THIRD_PARTY_KEY: [u8; 32] = [0xB2; 32];
const IDENTIFIER: [u8; 32] = [0xC3; 32];
const THIRD_PARTY_ID: [u8; 32] = [0xD4; 32];
const AUDIENCE: [u8; 32] = [0x22; 32];
const RESOURCE: [u8; 32] = [0x33; 32];

fn request() -> CapabilityRequest {
    CapabilityRequest {
        audience: AUDIENCE,
        resource: RESOURCE,
        actions: 0b0011,
        amount: 500,
        now: 1_700_000_100,
    }
}

struct Fixtures {
    primary: SpongeMacaroon,
    primary_wire: Vec<u8>,
    discharge: SpongeMacaroon,
    discharge_wire: Vec<u8>,
    verifier: MacaroonVerifier,
    dp: FrontierDpTable,
    authority_pk: PqBiscuitAuthorityPublicKey,
    open_biscuit_wire: Vec<u8>,
    sealed_biscuit_wire: Vec<u8>,
}

fn fixtures() -> &'static Fixtures {
    static FX: OnceLock<Fixtures> = OnceLock::new();
    FX.get_or_init(|| {
        // Macaroon with every first-party caveat kind and one third-party caveat, plus the
        // discharge that answers it, bound to the finished primary token.
        let mut primary = SpongeMacaroon::issue(&ROOT_KEY, IDENTIFIER, AUDIENCE);
        for caveat in [
            Caveat::ExpiresAt(1_800_000_000),
            Caveat::NotBefore(1_600_000_000),
            Caveat::Resource(RESOURCE),
            Caveat::Actions(0b0111),
            Caveat::MaxAmount(1_000),
            Caveat::ThirdParty(THIRD_PARTY_ID),
        ] {
            primary.attenuate(caveat).expect("primary caveat");
        }
        let mut discharge =
            SpongeMacaroon::issue_discharge(&THIRD_PARTY_KEY, THIRD_PARTY_ID, AUDIENCE);
        discharge
            .attenuate(Caveat::ExpiresAt(1_750_000_000))
            .expect("discharge caveat");
        primary.bind_discharge(&mut discharge).expect("bound discharge");
        let verifier = MacaroonVerifier::new(&ROOT_KEY, IDENTIFIER, AUDIENCE);
        let presented = [Discharge {
            token: &discharge,
            root_key: &THIRD_PARTY_KEY,
        }];
        assert_eq!(primary.verify(&ROOT_KEY, &request(), &presented), Ok(()));
        assert_eq!(verifier.verify(&primary, &request(), &presented), Ok(()));
        assert_eq!(
            primary.verify(&ROOT_KEY, &request(), &[]),
            Err(CapabilityError::MissingDischarge)
        );

        // Two-hop biscuit: authority mint, offline attenuation, request-bound seal.
        let accel = CpuReferenceBackend::new();
        let dp = FrontierDpTable::build(FrontierFtsProfile::Compact1122);
        let mut authority = PqBiscuitAuthorityKey::keygen([0x11; 32], [0xAA; 32], 2, &accel)
            .expect("authority key");
        let authority_pk = *authority.public_key();
        let (minted, step) = authority
            .mint(
                &dp,
                [0x44; 32],
                AUDIENCE,
                &[Caveat::Resource(RESOURCE), Caveat::MaxAmount(1_000)],
                [0x51; 32],
                &[0x61; 32],
                &accel,
            )
            .expect("minted biscuit");
        let (attenuated, tail) = step
            .attenuate(
                &minted,
                &dp,
                &[Caveat::MaxAmount(600), Caveat::Actions(0b0111)],
                [0x52; 32],
                &[0x62; 32],
                &accel,
            )
            .expect("attenuated biscuit");
        let sealed = tail
            .seal(&attenuated, &dp, Some(&request()), &[0x63; 32], &accel)
            .expect("sealed biscuit");
        assert_eq!(sealed.verify(&authority_pk, &dp, &request()), Ok(()));
        assert_eq!(
            attenuated.verify(&authority_pk, &dp, &request()),
            Err(CapabilityError::Denied)
        );

        Fixtures {
            primary_wire: primary.to_bytes(),
            primary,
            discharge_wire: discharge.to_bytes(),
            discharge,
            verifier,
            dp,
            authority_pk,
            open_biscuit_wire: attenuated.to_bytes().expect("open biscuit wire"),
            sealed_biscuit_wire: sealed.to_bytes().expect("sealed biscuit wire"),
        }
    })
}

/// Whether `token` is `base` or an attenuation of it: same kind, identifier and audience,
/// and a caveat list that starts with `base`'s.
fn extends(token: &SpongeMacaroon, base: &SpongeMacaroon) -> bool {
    token.is_discharge() == base.is_discharge()
        && token.identifier() == base.identifier()
        && token.audience() == base.audience()
        && token.caveats().starts_with(base.caveats())
}

fn check_macaroon(fx: &Fixtures, bytes: &[u8]) {
    let Ok(token) = SpongeMacaroon::from_bytes(bytes) else {
        return;
    };
    assert_eq!(token.to_bytes(), bytes);
    let req = request();

    // As a primary token under the fixture root key, with and without the real discharge.
    let presented = [Discharge {
        token: &fx.discharge,
        root_key: &THIRD_PARTY_KEY,
    }];
    for discharges in [&presented[..], &[]] {
        let direct = token.verify(&ROOT_KEY, &req, discharges);
        if direct.is_ok() {
            assert!(extends(&token, &fx.primary), "forged primary macaroon");
        }
        // The session verifier caches the root tag; it must decide exactly as the
        // key-holding verifier does for the session it was created for.
        if token.identifier() == &IDENTIFIER && token.audience() == &AUDIENCE {
            assert_eq!(fx.verifier.verify(&token, &req, discharges), direct);
        } else {
            assert_eq!(
                fx.verifier.verify(&token, &req, discharges),
                Err(CapabilityError::Denied)
            );
        }
    }

    // As the discharge presented with the real primary token.
    let as_discharge = [Discharge {
        token: &token,
        root_key: &THIRD_PARTY_KEY,
    }];
    if fx.primary.verify(&ROOT_KEY, &req, &as_discharge).is_ok() {
        assert!(extends(&token, &fx.discharge), "forged discharge macaroon");
    }
}

fn check_biscuit(fx: &Fixtures, bytes: &[u8]) {
    let Ok(token) = PqBiscuit::from_bytes(bytes) else {
        return;
    };
    assert_eq!(token.to_bytes().as_deref(), Ok(bytes));
    let verdict = token.verify(&fx.authority_pk, &fx.dp, &request());
    if !token.is_sealed() {
        assert_eq!(verdict, Err(CapabilityError::Denied));
    }
    if verdict.is_ok() {
        assert_eq!(bytes, fx.sealed_biscuit_wire, "forged biscuit");
    }
    // The seal binds the request it was made for.
    let other = CapabilityRequest {
        amount: 501,
        ..request()
    };
    assert!(token.verify(&fx.authority_pk, &fx.dp, &other).is_err());
}

/// `seed` with sparse `(offset: u32 LE, xor: u8)` edits applied.
fn edited(seed: &[u8], edits: &[u8]) -> Vec<u8> {
    let mut candidate = seed.to_vec();
    for edit in edits.chunks_exact(5) {
        let offset = u32::from_le_bytes([edit[0], edit[1], edit[2], edit[3]]) as usize;
        let index = offset % candidate.len();
        candidate[index] ^= edit[4];
    }
    candidate
}

fuzz_target!(init: {
    fixtures();
}, |data: &[u8]| {
    let fx = fixtures();

    // 1. Raw bytes through every decoder.
    check_macaroon(fx, data);
    check_biscuit(fx, data);
    if let Ok(pk) = PqBiscuitAuthorityPublicKey::from_bytes(data) {
        assert_eq!(pk.to_bytes().as_slice(), data);
        // A biscuit is bound to the authority that minted it.
        if pk != fx.authority_pk {
            let sealed = PqBiscuit::from_bytes(&fx.sealed_biscuit_wire).expect("sealed seed");
            assert!(sealed.verify(&pk, &fx.dp, &request()).is_err());
        }
    }
    if let Ok(key) = PqBiscuitAuthorityKey::from_secret_bytes(data) {
        assert_eq!(key.to_secret_bytes().as_slice(), data);
    }
    if let Ok(key) = PqBiscuitStepKey::from_secret_bytes(data) {
        assert_eq!(key.to_secret_bytes().as_slice(), data);
    }

    // 2. Sparse edits of the real tokens: `[0xed, kind]` then `(offset, xor)` records.
    if let [0xed, kind, edits @ ..] = data {
        match kind & 3 {
            0 => check_macaroon(fx, &edited(&fx.primary_wire, edits)),
            1 => check_macaroon(fx, &edited(&fx.discharge_wire, edits)),
            2 => check_biscuit(fx, &edited(&fx.open_biscuit_wire, edits)),
            _ => {
                let candidate = edited(&fx.sealed_biscuit_wire, edits);
                check_biscuit(fx, &candidate);
                if candidate == fx.sealed_biscuit_wire {
                    let token = PqBiscuit::from_bytes(&candidate).expect("sealed seed");
                    assert_eq!(token.verify(&fx.authority_pk, &fx.dp, &request()), Ok(()));
                }
            }
        }
    }
});
