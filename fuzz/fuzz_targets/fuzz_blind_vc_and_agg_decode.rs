// SPDX-License-Identifier: Apache-2.0 OR MIT
#![no_main]

//! Coverage-guided hostile wire-decoder & verifier fuzzer for `qsag-agg` (`Hem` WHIR
//! polynomial commitments, Steiner Merkle-Canopy multi-proofs, `HemAggregatedProof`,
//! `HierarchicalHemAggregate`, `SuccinctHierarchicalHemAggregate`, and the `Jorts-Poseidon2`
//! validator key and signature codecs).
//!
//! Security contract: arbitrary untrusted byte streams (including magic-prefixed adversarial
//! length frames, non-canonical Goldilocks limbs, and malformed merge trees) MUST NEVER
//! panic, unwrap, slice out of bounds, overflow integer sizes, or trigger unbounded OOM.

use libfuzzer_sys::fuzz_target;
use qsag_agg::field::Goldilocks;
use qsag_agg::pcs::{
    CanopyCommitment, CanopyMultiProof, HemWhirBatchOpeningProof, HemWhirOpeningProof,
    WhirSchedule, WhirSecurityRegime,
};
use qsag_agg::{
    AGG_WIRE_MAGIC, AggSigProfile, HIERARCHICAL_HEM_WIRE_MAGIC, HemAggregatedProof, HemAggregator,
    HierarchicalHemAggregate, SUCCINCT_HIERARCHICAL_HEM_WIRE_MAGIC, SigningMode,
    SuccinctHierarchicalHemAggregate, ValidatorPublicKey, ValidatorSignature,
    verify_individual_signature,
};

fuzz_target!(|data: &[u8]| {
    if let Ok(proof) = qsag_cred::blind_vc::SelectiveDisclosurePresentation::from_compact_wire_bytes(data) {
        assert_eq!(proof.to_compact_wire_bytes().unwrap(), data);
    }

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
    let _ = HemWhirOpeningProof::from_bytes_canonical(data);
    let _ = HemWhirBatchOpeningProof::from_bytes_canonical(data);

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

    // 4. `HierarchicalHemAggregate` & `SuccinctHierarchicalHemAggregate` wire decoders
    let mut hier_prefixed = Vec::with_capacity(HIERARCHICAL_HEM_WIRE_MAGIC.len() + data.len());
    hier_prefixed.extend_from_slice(HIERARCHICAL_HEM_WIRE_MAGIC);
    hier_prefixed.extend_from_slice(data);
    if let Ok(h) = HierarchicalHemAggregate::from_bytes_canonical(&hier_prefixed) {
        assert_eq!(h.to_bytes(), hier_prefixed);
    }
    let _ = HierarchicalHemAggregate::from_bytes_canonical(data);

    let mut succ_prefixed =
        Vec::with_capacity(SUCCINCT_HIERARCHICAL_HEM_WIRE_MAGIC.len() + data.len());
    succ_prefixed.extend_from_slice(SUCCINCT_HIERARCHICAL_HEM_WIRE_MAGIC);
    succ_prefixed.extend_from_slice(data);
    if let Ok(s) = SuccinctHierarchicalHemAggregate::from_bytes_canonical(&succ_prefixed) {
        assert_eq!(s.to_bytes(), succ_prefixed);
    }
    let _ = SuccinctHierarchicalHemAggregate::from_bytes_canonical(data);
});
