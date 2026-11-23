mod statement;
use qsag_agg::hem_quintic::{HemQuinticProfile, prove_hem_quintic_128, verify_hem_quintic_128};
use qsag_agg::sig::{EpochWalSink, SigError, WalEpochState};
use qsag_agg::{AggSigProfile, SignerBitmap, SigningMode, ValidatorKeypair};
use std::fs;
// Ephemeral deterministic test key, confined to this fixture process.
#[derive(Default)]
struct FixtureLatch(Option<([u8; 32], WalEpochState)>);
impl EpochWalSink for FixtureLatch {
    fn recovered_state(&self, pk: &[u8; 32]) -> Result<Option<WalEpochState>, SigError> {
        Ok(self.0.filter(|s| s.0 == *pk).map(|s| s.1))
    }
    fn persist_latched_epoch(
        &mut self,
        pk: &[u8; 32],
        next: u32,
        epoch: u32,
        mu: &[u8; 32],
    ) -> Result<(), SigError> {
        self.0 = Some((*pk, (next, epoch, *mu)));
        Ok(())
    }
}
fn main() {
    let multi = std::env::args().any(|s| s == "--multi");
    let path = if multi { "hqm2_multi" } else { "hqm2" };
    let scheme = AggSigProfile::JortsPoseidon2;
    let mut keys: Vec<_> = (0..if multi { 2 } else { 1 })
        .map(|i| ValidatorKeypair::keygen_deterministic(scheme, &[9 + i; 32], 0))
        .collect();
    let pks: Vec<_> = keys.iter().map(|k| k.pk).collect();
    let msgs: &[&[u8]] = &[b"QSAG-NI autonomous HQM2", &[0xa5; 135]];
    let mode = if multi {
        SigningMode::PerSignerMessages(msgs)
    } else {
        SigningMode::SharedMessage(msgs[0])
    };
    let bm =
        SignerBitmap::from_active_indices(pks.len() as u32, &(0..pks.len()).collect::<Vec<_>>())
            .unwrap();
    let descriptor = statement::hqm(&pks, &bm, &mode);
    fs::write(format!("vec/statement_{path}.bin"), &descriptor).unwrap();
    println!("{path} descriptor bytes={}", descriptor.len());
    if std::env::args().any(|s| s == "--descriptor-only") {
        return;
    }
    let signatures: Vec<_> = keys
        .iter_mut()
        .zip(msgs)
        .map(|(key, msg)| {
            key.sign_stateful(msg, 0, &mut FixtureLatch::default())
                .unwrap()
        })
        .collect();
    let proof = prove_hem_quintic_128(
        HemQuinticProfile::TurboShake400,
        &pks,
        &bm,
        &mode,
        &signatures,
    )
    .unwrap();
    assert!(verify_hem_quintic_128(&pks, &mode, &proof));
    let bytes = proof.to_bytes();
    fs::write(format!("vec/proof_{path}.bin"), &bytes).unwrap();
    println!("Rust accepted live {path} proof bytes={}", bytes.len());
}
