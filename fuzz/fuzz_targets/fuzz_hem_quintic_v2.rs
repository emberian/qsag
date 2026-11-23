// SPDX-License-Identifier: Apache-2.0 OR MIT
#![no_main]

//! Coverage-guided adversarial wire-decoder, canonical roundtrip, and soundness fuzzer for
//! `HemQuinticProof::from_bytes` (`QSAGHQM2`) + `verify_hem_quintic_128` across both
//! `TurboShake400` and `Poseidon2Gl24` profiles and both `SharedMessage` and `PerSignerMessages`.

use std::sync::OnceLock;

use libfuzzer_sys::fuzz_target;
use qsag_agg::sig::{EpochWalSink, SigError, WalEpochState};
use qsag_agg::{
    AggSigProfile, HemQuinticProfile, HemQuinticProof, SignerBitmap, SigningMode,
    ValidatorKeypair, ValidatorPublicKey, prove_hem_quintic_128, verify_hem_quintic_128,
};

const HQM2_MAGIC: &[u8; 8] = b"QSAGHQM2";

#[derive(Default)]
struct MemWal(Option<WalEpochState>);

impl EpochWalSink for MemWal {
    fn recovered_state(&self, _pk_root: &[u8; 32]) -> Result<Option<WalEpochState>, SigError> {
        Ok(self.0)
    }
    fn persist_latched_epoch(
        &mut self,
        _pk_root: &[u8; 32],
        next: u32,
        epoch: u32,
        mu: &[u8; 32],
    ) -> Result<(), SigError> {
        self.0 = Some((next, epoch, *mu));
        Ok(())
    }
}

struct Hqm2Fixtures {
    pks: [ValidatorPublicKey; 2],
    turbo_wire: Vec<u8>,
    gl24_wire: Vec<u8>,
}

const MSG_SHARED: &[u8] = b"fuzz-hqm2-shared-v2";

fn fixtures() -> &'static Hqm2Fixtures {
    static FX: OnceLock<Hqm2Fixtures> = OnceLock::new();
    FX.get_or_init(|| {
        let mut w0 = MemWal::default();
        let w1 = MemWal::default();
        let mut kp0 = ValidatorKeypair::from_master_seed_with_wal(
            AggSigProfile::JortsPoseidon2,
            &[0x11; 32],
            0,
            &w0,
        )
        .expect("kp0");
        let kp1 = ValidatorKeypair::from_master_seed_with_wal(
            AggSigProfile::JortsPoseidon2,
            &[0x22; 32],
            1,
            &w1,
        )
        .expect("kp1");
        let pks = [kp0.pk, kp1.pk];
        let bm = SignerBitmap::from_active_indices(2, &[0]).expect("bitmap");
        let sig0 = kp0.sign_stateful(MSG_SHARED, 0, &mut w0).expect("sig0");
        let mode = SigningMode::SharedMessage(MSG_SHARED);

        let turbo = prove_hem_quintic_128(
            HemQuinticProfile::TurboShake400,
            &pks,
            &bm,
            &mode,
            std::slice::from_ref(&sig0),
        )
        .expect("turbo seed proof");
        assert!(verify_hem_quintic_128(&pks, &mode, &turbo));

        let gl24 = prove_hem_quintic_128(
            HemQuinticProfile::Poseidon2Gl24,
            &pks,
            &bm,
            &mode,
            std::slice::from_ref(&sig0),
        )
        .expect("gl24 seed proof");
        assert!(verify_hem_quintic_128(&pks, &mode, &gl24));

        Hqm2Fixtures {
            pks,
            turbo_wire: turbo.to_bytes(),
            gl24_wire: gl24.to_bytes(),
        }
    })
}

fn mutate_seed(seed: &[u8], edits: &[u8]) -> Vec<u8> {
    let mut out = seed.to_vec();
    let mut chunks = edits.chunks_exact(5);
    for edit in chunks.by_ref().take(8) {
        let idx = (u32::from_le_bytes([edit[0], edit[1], edit[2], edit[3]]) as usize) % out.len();
        out[idx] ^= edit[4];
    }
    match chunks.remainder() {
        [1, ..] => {
            out.pop();
        }
        [2, b, ..] => out.push(*b),
        _ => {}
    }
    out
}

fuzz_target!(init: {
    fixtures();
}, |data: &[u8]| {
    let fx = fixtures();
    let Some((&sel, rest)) = data.split_first() else {
        return;
    };

    // 1. Arbitrary untrusted wire bytes (raw and magic-prefixed)
    let mut prefixed = Vec::with_capacity(8 + rest.len());
    prefixed.extend_from_slice(HQM2_MAGIC);
    prefixed.extend_from_slice(rest);
    for candidate in [rest, prefixed.as_slice()] {
        if let Some(proof) = HemQuinticProof::from_bytes(candidate) {
            assert_eq!(proof.to_bytes(), candidate, "non-canonical HemQuinticProof decode");
            let _ = verify_hem_quintic_128(
                &fx.pks,
                &SigningMode::SharedMessage(MSG_SHARED),
                &proof,
            );
            let per_msgs: Vec<&[u8]> = (0..proof.bitmap.count_ones())
                .map(|i| if i & 1 == 0 { &b"m0"[..] } else { &b"m1"[..] })
                .collect();
            let _ = verify_hem_quintic_128(
                &fx.pks,
                &SigningMode::PerSignerMessages(&per_msgs),
                &proof,
            );
        }
    }

    // 2. Seeded differential byte-mutation over real TurboShake400 and Poseidon2Gl24 proofs
    if sel & 3 == 0 {
        let base = if sel & 4 == 0 {
            &fx.turbo_wire
        } else {
            &fx.gl24_wire
        };
        let mutated = mutate_seed(base, rest);
        if mutated == *base {
            return;
        }
        if let Some(proof) = HemQuinticProof::from_bytes(&mutated) {
            assert_eq!(proof.to_bytes(), mutated);
            assert!(
                !verify_hem_quintic_128(
                    &fx.pks,
                    &SigningMode::SharedMessage(MSG_SHARED),
                    &proof,
                ),
                "mutated HemQuinticProof forged verification"
            );
        }
    }
});
