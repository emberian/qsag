// SPDX-License-Identifier: Apache-2.0 OR MIT
#![no_main]

//! Coverage-guided hostile wire-decoder & verifier fuzzer for `qsag-agg` (`Hem` WHIR
//! polynomial commitments and opening proofs, Steiner Merkle-Canopy multi-proofs,
//! `HemAggregatedProof`, `HierarchicalHemAggregate`, `SuccinctHierarchicalHemAggregate`, and
//! the `Jorts-Poseidon2` validator key and signature codecs).
//!
//! Security contract: arbitrary untrusted byte streams (including magic-prefixed adversarial
//! length frames, non-canonical Goldilocks limbs, and malformed merge trees) MUST NEVER
//! panic, unwrap, slice out of bounds, overflow integer sizes, or trigger unbounded OOM.
//! Every accepted encoding re-encodes to its input and is handed to the verifier of its
//! type. Real proofs built in `LLVMFuzzerInitialize` (the `init:` block) seed sparse-edit
//! mutations, so the verifiers run on inputs that are one field away from valid.
//!
//! `qsag_cred::blind_vc::SelectiveDisclosurePresentation` is megabytes on the wire; its
//! decoder and verifier are driven from a real presentation in `fuzz_blind_vc_presentation`.

use std::sync::OnceLock;

use libfuzzer_sys::fuzz_target;
use qsag_agg::field::{Goldilocks, GoldilocksExt4, mle_eval_base_at_ext4};
use qsag_agg::pcs::{
    CanopyCommitment, CanopyMultiProof, HemWhirBatchOpeningProof, HemWhirOpeningProof,
    WhirSchedule, WhirSecurityRegime, whir_commit_batch_owned_with_schedule, whir_open,
    whir_open_batch, whir_verify_batch_with_schedule, whir_verify_with_schedule,
};
use qsag_agg::recursive::{
    ShardHemWitness, VerifiedHierarchicalHemEvidence, check_hierarchical_hem_commitment,
    compress_hierarchical_hem_evidence, hierarchical_hem_message, prove_hierarchical_hem,
    verify_hierarchical_hem, verify_hierarchical_hem_evidence, verify_succinct_hierarchical_hem,
};
use qsag_agg::sig::{EpochWalSink, WalEpochState};
use qsag_agg::{
    AGG_WIRE_MAGIC, AggSigProfile, FiatShamirTranscript, HIERARCHICAL_HEM_WIRE_MAGIC,
    HemAggConfig, HemAggregatedProof, HemAggregator, HierarchicalHemAggregate, InstanceBound,
    SUCCINCT_HIERARCHICAL_HEM_WIRE_MAGIC, ShardHemPolicy, SigError, SignerBitmap, SigningMode,
    SuccinctHierarchicalHemAggregate, ValidatorKeypair, ValidatorPublicKey, ValidatorSignature,
    compute_policy_registry_root, verify_individual_signature,
};

/// Regime of every seed proof. Its proof-of-work grinds through the assembly Keccak
/// kernel, which coverage instrumentation does not slow down.
const REGIME: WhirSecurityRegime = WhirSecurityRegime::BciksJohnsonQrom128;
const PCS_NUM_VARS: usize = 6;
const HIER_EPOCH: u64 = 17;
const HIER_MESSAGE: [u8; 32] = [42; 32];
const HIER_MINIMUM: usize = 2;

/// In-memory epoch log with the semantics of the durable one: it returns exactly what
/// was last persisted for a key and nothing for any other key.
#[derive(Default)]
struct MemoryEpochWal(Vec<([u8; 32], WalEpochState)>);

impl EpochWalSink for MemoryEpochWal {
    fn recovered_state(&self, pk_root: &[u8; 32]) -> Result<Option<WalEpochState>, SigError> {
        Ok(self.0.iter().find(|(key, _)| key == pk_root).map(|(_, state)| *state))
    }

    fn persist_latched_epoch(
        &mut self,
        pk_root: &[u8; 32],
        next_unused_epoch: u32,
        latched_epoch: u32,
        mu_bytes: &[u8; 32],
    ) -> Result<(), SigError> {
        let state = (next_unused_epoch, latched_epoch, *mu_bytes);
        match self.0.iter_mut().find(|(key, _)| key == pk_root) {
            Some(entry) => entry.1 = state,
            None => self.0.push((*pk_root, state)),
        }
        Ok(())
    }
}

struct Fixtures {
    schedule: WhirSchedule,
    point: Vec<GoldilocksExt4>,
    single_commitment: CanopyCommitment,
    single_value: GoldilocksExt4,
    single_seed: Vec<u8>,
    batch_commitment: CanopyCommitment,
    batch_values: [GoldilocksExt4; 2],
    batch_seed: Vec<u8>,
    policies: Vec<ShardHemPolicy>,
    hierarchical_seed: Vec<u8>,
    evidence: VerifiedHierarchicalHemEvidence,
    succinct_seed: Vec<u8>,
}

fn single_transcript(schedule: &WhirSchedule) -> FiatShamirTranscript<InstanceBound> {
    FiatShamirTranscript::new()
        .bind_relation(b"FUZZ_PCS_SINGLE", b"", schedule)
        .bind_instance(&[b"fuzz"])
}

fn batch_transcript(schedule: &WhirSchedule) -> FiatShamirTranscript<InstanceBound> {
    FiatShamirTranscript::new()
        .bind_relation(b"FUZZ_PCS_BATCH", b"", schedule)
        .bind_instance(&[b"fuzz"])
}

fn fixtures() -> &'static Fixtures {
    static FX: OnceLock<Fixtures> = OnceLock::new();
    FX.get_or_init(|| {
        let f = Goldilocks::from_u64_reduced;

        // 1. One real single-polynomial and one real two-polynomial WHIR opening.
        let schedule = REGIME.schedule(PCS_NUM_VARS);
        let poly_a: Vec<_> = (0..1u64 << PCS_NUM_VARS).map(|i| f(3 * i + 1)).collect();
        let poly_b: Vec<_> = (0..1u64 << PCS_NUM_VARS).map(|i| f(i * i + 7)).collect();
        let point: Vec<_> = (0..PCS_NUM_VARS as u64)
            .map(|i| GoldilocksExt4::from_limbs([f(5 + i), f(11), f(13 * i), f(2)]))
            .collect();
        let single_value = mle_eval_base_at_ext4(&poly_a, &point);
        let (single_commitment, single_state) =
            whir_commit_batch_owned_with_schedule(vec![poly_a.clone()], &[8; 32], &schedule);
        let single = whir_open(
            &single_state,
            &point,
            single_value,
            &mut single_transcript(&schedule),
        );
        assert!(whir_verify_with_schedule(
            &single_commitment,
            PCS_NUM_VARS,
            &point,
            single_value,
            &single,
            &mut single_transcript(&schedule),
            &schedule,
        ));
        let mut single_seed = Vec::new();
        single.push_bytes(&mut single_seed);

        let batch_values = [
            mle_eval_base_at_ext4(&poly_a, &point),
            mle_eval_base_at_ext4(&poly_b, &point),
        ];
        let (batch_commitment, batch_state) =
            whir_commit_batch_owned_with_schedule(vec![poly_a, poly_b], &[9; 32], &schedule);
        let batch = whir_open_batch(
            &batch_state,
            &[&point, &point],
            &batch_values,
            &mut batch_transcript(&schedule),
        );
        assert!(whir_verify_batch_with_schedule(
            &batch_commitment,
            PCS_NUM_VARS,
            &[&point, &point],
            &batch_values,
            &batch,
            &mut batch_transcript(&schedule),
            &schedule,
        ));
        let mut batch_seed = Vec::new();
        batch.push_bytes(&mut batch_seed);

        // 2. One real single-shard hierarchy signed by both keys of its committee, and the
        //    compact commitment derived from its verification evidence.
        let mut keys: Vec<_> = (0..2)
            .map(|i| {
                ValidatorKeypair::keygen_deterministic(AggSigProfile::JortsPoseidon2, &[0x31; 32], i)
            })
            .collect();
        let policies = vec![ShardHemPolicy {
            shard_id: 0,
            custodian_cluster: [0x32; 32],
            quorum_keys: keys.iter().map(|k| k.pk).collect(),
            minimum_quorums: HIER_MINIMUM,
        }];
        let registry_root = compute_policy_registry_root(&policies);
        let signed =
            hierarchical_hem_message(&registry_root, &policies[0], HIER_EPOCH, HIER_MESSAGE);
        let mut wal = MemoryEpochWal::default();
        let signatures: Vec<_> = keys
            .iter_mut()
            .map(|k| k.sign_stateful(&signed, 0, &mut wal).expect("committee signature"))
            .collect();
        let bitmap = SignerBitmap::from_active_indices(2, &[0, 1]).expect("bitmap");
        let config = HemAggConfig {
            regime: REGIME,
            ..HemAggConfig::default_for(AggSigProfile::JortsPoseidon2, [7; 32])
        };
        let hierarchical = prove_hierarchical_hem(
            &policies,
            &[ShardHemWitness {
                bitmap: &bitmap,
                signatures: &signatures,
            }],
            HIER_EPOCH,
            HIER_MESSAGE,
            HIER_MINIMUM,
            &config,
        )
        .expect("hierarchical seed proof");
        let evidence = verify_hierarchical_hem_evidence(
            &policies,
            HIER_EPOCH,
            HIER_MESSAGE,
            HIER_MINIMUM,
            REGIME,
            &hierarchical,
        )
        .expect("hierarchical seed verifies");
        let succinct =
            compress_hierarchical_hem_evidence(&evidence, [0x33; 32]).expect("compact commitment");
        assert!(verify_succinct_hierarchical_hem(
            &policies,
            HIER_EPOCH,
            HIER_MESSAGE,
            HIER_MINIMUM,
            &succinct,
            &evidence,
        ));

        Fixtures {
            schedule,
            point,
            single_commitment,
            single_value,
            single_seed,
            batch_commitment,
            batch_values,
            batch_seed,
            policies,
            hierarchical_seed: hierarchical.to_bytes(),
            evidence,
            succinct_seed: succinct.to_bytes(),
        }
    })
}

/// A single-polynomial opening: canonical re-encoding, then the verifier. Returns whether
/// the opening verified.
fn check_single_opening(fx: &Fixtures, bytes: &[u8]) -> Option<bool> {
    let (proof, used) = HemWhirOpeningProof::from_bytes_canonical(bytes)?;
    let mut reencoded = Vec::new();
    proof.push_bytes(&mut reencoded);
    assert_eq!(&bytes[..used], reencoded.as_slice());
    Some(whir_verify_with_schedule(
        &fx.single_commitment,
        PCS_NUM_VARS,
        &fx.point,
        fx.single_value,
        &proof,
        &mut single_transcript(&fx.schedule),
        &fx.schedule,
    ))
}

fn check_batch_opening(fx: &Fixtures, bytes: &[u8]) -> Option<bool> {
    let (proof, used) = HemWhirBatchOpeningProof::from_bytes_canonical(bytes)?;
    let mut reencoded = Vec::new();
    proof.push_bytes(&mut reencoded);
    assert_eq!(&bytes[..used], reencoded.as_slice());
    Some(whir_verify_batch_with_schedule(
        &fx.batch_commitment,
        PCS_NUM_VARS,
        &[&fx.point, &fx.point],
        &fx.batch_values,
        &proof,
        &mut batch_transcript(&fx.schedule),
        &fx.schedule,
    ))
}

fn check_hierarchical(fx: &Fixtures, bytes: &[u8]) -> Option<bool> {
    let aggregate = HierarchicalHemAggregate::from_bytes_canonical(bytes).ok()?;
    assert_eq!(aggregate.to_bytes(), bytes);
    let verified = verify_hierarchical_hem(
        &fx.policies,
        HIER_EPOCH,
        HIER_MESSAGE,
        HIER_MINIMUM,
        REGIME,
        &aggregate,
    );
    // The evidence-producing verifier accepts exactly what the boolean one accepts.
    let evidence = verify_hierarchical_hem_evidence(
        &fx.policies,
        HIER_EPOCH,
        HIER_MESSAGE,
        HIER_MINIMUM,
        REGIME,
        &aggregate,
    );
    assert_eq!(evidence.is_some(), verified);
    // No aggregate verifies for a statement nobody signed.
    assert!(!verify_hierarchical_hem(
        &fx.policies,
        HIER_EPOCH + 1,
        HIER_MESSAGE,
        HIER_MINIMUM,
        REGIME,
        &aggregate,
    ));
    Some(verified)
}

fn check_succinct(fx: &Fixtures, bytes: &[u8]) -> Option<bool> {
    let aggregate = SuccinctHierarchicalHemAggregate::from_bytes_canonical(bytes).ok()?;
    assert_eq!(aggregate.to_bytes(), bytes);
    let committed = check_hierarchical_hem_commitment(
        &fx.policies,
        HIER_EPOCH,
        HIER_MESSAGE,
        HIER_MINIMUM,
        &aggregate,
    );
    let verified = verify_succinct_hierarchical_hem(
        &fx.policies,
        HIER_EPOCH,
        HIER_MESSAGE,
        HIER_MINIMUM,
        &aggregate,
        &fx.evidence,
    );
    // Full verification implies the commitment relation it is built on.
    assert!(committed || !verified);
    Some(verified)
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

fuzz_target!(init: {
    fixtures();
}, |data: &[u8]| {
    let fx = fixtures();

    // 1. Canonical PCS schedule, Merkle-Canopy commitment, multi-proof, and WHIR opening decoders
    let num_vars = 2 + (data.first().copied().unwrap_or(0) as usize % 23);
    if let Some((sched, used)) = WhirSchedule::from_bytes_canonical(data, num_vars) {
        let reencoded = sched.to_bytes();
        assert_eq!(&data[..used], reencoded.as_slice());
    }
    if let Some((comm, used)) = CanopyCommitment::from_bytes_canonical(data) {
        assert_eq!(used, 33);
        assert_eq!(&data[..33], comm.to_bytes().as_slice());
    }
    if let Some((mp, used)) = CanopyMultiProof::from_bytes_canonical(data) {
        let mut reencoded = Vec::new();
        mp.push_bytes(&mut reencoded);
        assert_eq!(&data[..used], reencoded.as_slice());
    }
    let _ = check_single_opening(fx, data);
    let _ = check_batch_opening(fx, data);

    // 2. Validator key and `Jorts-Poseidon2` signature codecs: every accepted encoding is the
    //    canonical one, and verification of a decoded signature never panics.
    let dummy_pk = ValidatorPublicKey {
        profile: AggSigProfile::JortsPoseidon2,
        pk_seed: [Goldilocks::from_u64_reduced(0x11); 4],
        pk_root: [Goldilocks::from_u64_reduced(0x22); 4],
    };
    if let Some(pk_bytes) = data.first_chunk::<65>()
        && let Some(pk) = ValidatorPublicKey::from_bytes_canonical(pk_bytes)
    {
        assert_eq!(&pk.to_bytes(), pk_bytes);
    }
    if let Ok(sig) = ValidatorSignature::from_bytes_canonical(AggSigProfile::JortsPoseidon2, data) {
        assert_eq!(sig.to_bytes(), data);
        let _ = verify_individual_signature(&dummy_pk, b"fuzz-msg", &sig);
    }

    // 3. Top-level `HemAggregatedProof` raw + magic-prefixed adversarial framing
    for candidate in [
        data.to_vec(),
        {
            let mut v = Vec::with_capacity(AGG_WIRE_MAGIC.len() + data.len());
            v.extend_from_slice(AGG_WIRE_MAGIC);
            v.extend_from_slice(data);
            v
        },
    ] {
        if let Ok(proof) = HemAggregatedProof::from_bytes_canonical(&candidate) {
            // Canonical roundtrip determinism check on every accepted wire payload!
            assert_eq!(proof.to_bytes(), candidate);
            let _ = HemAggregator::verify_with_regime(
                &[dummy_pk],
                &SigningMode::SharedMessage(b"fuzz-msg"),
                &proof,
                WhirSecurityRegime::BciksJohnsonQrom128,
            );
        }
    }

    // 4. `HierarchicalHemAggregate` & `SuccinctHierarchicalHemAggregate` wire decoders,
    //    canonical re-encoding and verification, raw and magic-prefixed.
    let mut hier_prefixed = Vec::with_capacity(HIERARCHICAL_HEM_WIRE_MAGIC.len() + data.len());
    hier_prefixed.extend_from_slice(HIERARCHICAL_HEM_WIRE_MAGIC);
    hier_prefixed.extend_from_slice(data);
    let _ = check_hierarchical(fx, &hier_prefixed);
    let _ = check_hierarchical(fx, data);

    let mut succ_prefixed =
        Vec::with_capacity(SUCCINCT_HIERARCHICAL_HEM_WIRE_MAGIC.len() + data.len());
    succ_prefixed.extend_from_slice(SUCCINCT_HIERARCHICAL_HEM_WIRE_MAGIC);
    succ_prefixed.extend_from_slice(data);
    let _ = check_succinct(fx, &succ_prefixed);
    let _ = check_succinct(fx, data);

    // 5. Sparse edits of the real proofs. `[0xed, kind]` followed by `(offset, xor)` records
    //    selects a seed; with no records the unedited proof must still verify.
    if let [0xed, kind, edits @ ..] = data {
        type Check = fn(&Fixtures, &[u8]) -> Option<bool>;
        let (seed, check): (&[u8], Check) = match kind & 3 {
            0 => (&fx.single_seed, check_single_opening),
            1 => (&fx.batch_seed, check_batch_opening),
            2 => (&fx.hierarchical_seed, check_hierarchical),
            _ => (&fx.succinct_seed, check_succinct),
        };
        let candidate = edited(seed, edits);
        let outcome = check(fx, &candidate);
        if candidate == seed {
            assert_eq!(outcome, Some(true));
        }
    }
});
