//! Known-answer digests of `cSHAKE256`-regime proof bytes produced through the public API.
//! The default regime's wire bytes must not move when other regimes or larger sizes are added.
#![cfg(feature = "std")]

use qsag_agg::field::mle_eval_base_at_ext4;
use qsag_agg::sig::{EpochWalSink, SigError, WalEpochState};
use qsag_agg::sponge::{FiatShamirTranscript, InstanceBound, cshake256_32};
use qsag_agg::{
    AggSigProfile, Goldilocks, GoldilocksExt4, SignerBitmap, SigningMode, ValidatorKeypair,
    aggregate_signatures, verify_aggregate, whir_commit, whir_commit_batch_owned, whir_open,
    whir_open_batch, whir_stage_schedule, whir_verify, whir_verify_batch,
};

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn digest(bytes: &[u8]) -> String {
    hex(&cshake256_32(b"QSAG.TEST.PROOF_BYTES_KAT", bytes))
}

fn poly(num_vars: usize, tag: u64) -> Vec<Goldilocks> {
    (0..1u64 << num_vars)
        .map(|i| {
            Goldilocks::from_u64_reduced(
                (i + 1)
                    .wrapping_mul(0x9E37_79B9_7F4A_7C15)
                    .wrapping_add(tag.wrapping_mul(0xD1B5_4A32_D192_ED03)),
            )
        })
        .collect()
}

fn point(num_vars: usize, tag: u64) -> Vec<GoldilocksExt4> {
    (0..num_vars as u64)
        .map(|k| {
            GoldilocksExt4::from_limbs([
                Goldilocks::from_u64_reduced((k + 1) * 31_337 + tag),
                Goldilocks::from_u64_reduced((k + 5) * 4_242 + tag),
                Goldilocks::from_u64_reduced((k + 9) * 1_717 + tag),
                Goldilocks::from_u64_reduced((k + 13) * 9_001 + tag),
            ])
        })
        .collect()
}

fn transcript(num_vars: usize) -> FiatShamirTranscript<InstanceBound> {
    FiatShamirTranscript::new()
        .bind_relation(b"KAT.PCS", b"v1", &whir_stage_schedule(num_vars))
        .bind_instance(&[b"kat-instance"])
}

#[derive(Default)]
struct MemoryWal(Option<WalEpochState>);

impl EpochWalSink for MemoryWal {
    fn recovered_state(&self, _pk_root: &[u8; 32]) -> Result<Option<WalEpochState>, SigError> {
        Ok(self.0)
    }

    fn persist_latched_epoch(
        &mut self,
        _pk_root: &[u8; 32],
        next_unused_epoch: u32,
        latched_epoch: u32,
        mu_bytes: &[u8; 32],
    ) -> Result<(), SigError> {
        self.0 = Some((next_unused_epoch, latched_epoch, *mu_bytes));
        Ok(())
    }
}

#[test]
fn default_regime_single_opening_bytes() {
    let num_vars = 12;
    let evals = poly(num_vars, 1);
    let pt = point(num_vars, 3);
    let value = mle_eval_base_at_ext4(&evals, &pt);
    let (comm, state) = whir_commit(&evals, &[7; 32]);
    let proof = whir_open(&state, &pt, value, &mut transcript(num_vars));
    assert!(whir_verify(
        &comm,
        num_vars,
        &pt,
        value,
        &proof,
        &mut transcript(num_vars)
    ));
    let mut bytes = comm.to_bytes().to_vec();
    proof.push_bytes(&mut bytes);
    println!(
        "KAT single nv=12 len={} digest={}",
        bytes.len(),
        digest(&bytes)
    );
    assert_eq!(bytes.len(), SINGLE_NV12_LEN);
    assert_eq!(digest(&bytes), SINGLE_NV12_DIGEST);
}

#[test]
fn default_regime_batch_opening_bytes() {
    let num_vars = 16;
    let polys: Vec<Vec<Goldilocks>> = (0..3).map(|t| poly(num_vars, 10 + t)).collect();
    let points: Vec<Vec<GoldilocksExt4>> = (0..3).map(|t| point(num_vars, 20 + t)).collect();
    let evals: Vec<GoldilocksExt4> = polys
        .iter()
        .zip(&points)
        .map(|(w, p)| mle_eval_base_at_ext4(w, p))
        .collect();
    let point_refs: Vec<&[GoldilocksExt4]> = points.iter().map(Vec::as_slice).collect();
    let (comm, state) = whir_commit_batch_owned(polys, &[9; 32]);
    let proof = whir_open_batch(&state, &point_refs, &evals, &mut transcript(num_vars));
    assert!(whir_verify_batch(
        &comm,
        num_vars,
        &point_refs,
        &evals,
        &proof,
        &mut transcript(num_vars)
    ));
    let mut bytes = comm.to_bytes().to_vec();
    proof.push_bytes(&mut bytes);
    println!(
        "KAT batch nv=16 len={} digest={}",
        bytes.len(),
        digest(&bytes)
    );
    assert_eq!(bytes.len(), BATCH_NV16_LEN);
    assert_eq!(digest(&bytes), BATCH_NV16_DIGEST);
}

#[test]
fn default_config_aggregate_bytes() {
    let msg = b"proof-bytes-kat";
    let mut pks = Vec::new();
    let mut sigs = Vec::new();
    for idx in 0..4u32 {
        let mut kp =
            ValidatorKeypair::keygen_deterministic(AggSigProfile::JortsPoseidon2, &[5; 32], idx);
        let mut wal = MemoryWal::default();
        sigs.push(kp.sign_stateful(msg, 0, &mut wal).unwrap());
        pks.push(kp.pk);
    }
    let bitmap = SignerBitmap::from_active_indices(4, &[0, 1, 2, 3]).unwrap();
    let mode = SigningMode::SharedMessage(msg);
    let proof = aggregate_signatures(&pks, &bitmap, &mode, &sigs, [11; 32]).unwrap();
    assert!(verify_aggregate(&pks, &mode, &proof));
    let bytes = proof.to_bytes();
    println!(
        "KAT aggregate K=4 len={} digest={}",
        bytes.len(),
        digest(&bytes)
    );
    assert_eq!(bytes.len(), AGG_K4_LEN);
    assert_eq!(digest(&bytes), AGG_K4_DIGEST);
}

// PCS vectors retain the original default regime. The aggregate vector below
// additionally pins the canonical Poseidon2 signature/trace profile.
const SINGLE_NV12_LEN: usize = 97_891;
const SINGLE_NV12_DIGEST: &str = "0670fbfdd9348c47af1da8c486db306e11c17a8430a9bf09052d179e4dd9730e";
const BATCH_NV16_LEN: usize = 243_011;
const BATCH_NV16_DIGEST: &str = "665403b05f370b337bc95db3f6e5990a4217f9e9a72dddc19f64fa155603e13e";
const AGG_K4_LEN: usize = 270_272;
const AGG_K4_DIGEST: &str = "b6ccae6c28d0d14a8d3f49cfb3b4aee9762605a863dbef46880a556f7868fca2";
