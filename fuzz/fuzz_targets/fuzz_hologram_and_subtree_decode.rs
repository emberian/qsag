// SPDX-License-Identifier: Apache-2.0 OR MIT
#![no_main]

//! Coverage-guided hostile wire-decoder and verifier fuzzer for the hologram and `zk-Hem v2`
//! masked proof formats of `qsag-agg`, driven by small compiled relations:
//!
//! 1. `zk_hem::protocol::ShapeVerifierKey::from_bytes`.
//! 2. `zk_hem::protocol::HologramPublicProof::from_bytes` + `verify_public_hologram`.
//! 3. `recursive::SuccinctSubtreeAggregate::from_bytes_canonical` (`QSAGSTA1`) +
//!    `verify_succinct_subtree_aggregate_against_roster_root`.
//! 4. `recursive::split::SplitSubtreeAggregate::from_bytes_canonical` +
//!    `verify_against_roster_root`.
//! 5. `zk_hem::v2::protocol::ZkHemV2Proof::from_bytes` + `v2::protocol::verify`, and full-shard
//!    wrapper encoders.

use std::sync::OnceLock;

use libfuzzer_sys::fuzz_target;
use qsag_agg::field::Goldilocks;
use qsag_agg::pcs::WhirSecurityRegime;
use qsag_agg::recursive::split::SplitSubtreeAggregate;
use qsag_agg::recursive::{
    RosterRootStatement, SUBTREE_PUBLIC_WORDS, SUCCINCT_FULL_SHARD_WIRE_MAGIC,
    SUCCINCT_SUBTREE_WIRE_MAGIC, SubtreePublic, SuccinctFullShardAggregate,
    SuccinctSubtreeAggregate, subtree_message_digest,
    verify_succinct_subtree_aggregate_against_roster_root,
};
use qsag_agg::zk_hem::full_shard::FullShardMergeProof;
use qsag_agg::zk_hem::protocol::{
    HologramPublicProof, ShapeHologram, ShapeVerifierKey, prove_public_hologram,
    verify_public_hologram,
};
use qsag_agg::zk_hem::relation::{ConstraintSystem, Lc, Shape, poseidon2_perm};
use qsag_agg::zk_hem::v2::params::Profile;
use qsag_agg::zk_hem::v2::protocol::{self as v2, ZkHemV2Proof};

const REGIME: WhirSecurityRegime = WhirSecurityRegime::BciksJohnsonQrom128;
const PROFILE: Profile = Profile::CshakeJohnson400;
const SUBTREE_ROOT_LABEL: &[u8] = b"QSAG.SUBTREE.ROOT.HOLOGRAM/v1";
const FULL_SHARD_LABEL: &[u8] = b"QSAG.FULL.SHARD.MERGE/v2";
const SPLIT_PUBLIC_WORDS: usize = SUBTREE_PUBLIC_WORDS + 4;

const MESSAGE: &[u8] = b"fuzz-subtree-message";
const EPOCH_FLOOR: u64 = 17;
const SIGNERS: u64 = 5;
const WEIGHT: u64 = 6;
const MIN_KEY: u64 = 3;
const MAX_KEY: u64 = 9;

struct Fixtures {
    vk: ShapeVerifierKey,
    vk_wire: Vec<u8>,
    split_vk: ShapeVerifierKey,
    roster_root: [u8; 32],
    public_words: [Goldilocks; SUBTREE_PUBLIC_WORDS],
    proof_wire: Vec<u8>,
    aggregate_wire: Vec<u8>,
    masked_shape: Shape,
    masked_proof_wire: Vec<u8>,
}

fn small_relation_cs(publics: &[Goldilocks]) -> ConstraintSystem {
    let f = Goldilocks::from_u64_reduced;
    let mut cs = ConstraintSystem::new_hologram_aligned();
    for &word in publics {
        let _ = cs.public_input(word);
    }
    let mut state: [Lc; 12] = core::array::from_fn(|i| cs.alloc(f(3 + i as u64)).into());
    for _ in 0..3 {
        poseidon2_perm(&mut cs, &mut state);
    }
    let product = cs.mul(&state[0], &state[5]);
    let value = cs.eval(&product.into());
    cs.enforce_equal(&product.into(), &Lc::constant(value));
    cs
}

fn statement(fx: &Fixtures) -> RosterRootStatement<'static> {
    RosterRootStatement {
        roster_root: fx.roster_root,
        epoch_floor: EPOCH_FLOOR,
        message: MESSAGE,
        minimum_global_quorums: 2,
        minimum_active_weight: 2,
        min_key_idx: MIN_KEY,
        max_key_idx: MAX_KEY,
    }
}

fn fixtures() -> &'static Fixtures {
    static FX: OnceLock<Fixtures> = OnceLock::new();
    FX.get_or_init(|| {
        let f = Goldilocks::from_u64_reduced;
        let root_limbs = [f(0x1111), f(0x2222), f(0x3333), f(0x4444)];
        let mut roster_root = [0u8; 32];
        for (chunk, limb) in roster_root.as_chunks_mut::<8>().0.iter_mut().zip(root_limbs) {
            chunk.copy_from_slice(&limb.to_le_bytes());
        }
        let public = SubtreePublic {
            subtree_registry_root: root_limbs,
            epoch_floor: f(EPOCH_FLOOR),
            message_digest: subtree_message_digest(MESSAGE),
            total_active_signers: f(SIGNERS),
            min_key_idx: MIN_KEY,
            max_key_idx: MAX_KEY,
            total_active_weight: WEIGHT,
        };
        let public_words = public.words();

        let (shape, assignment) = small_relation_cs(&public_words).finish();
        let (masked_shape, masked_assignment) = small_relation_cs(&public_words).finish_v2();
        let hologram = ShapeHologram::compile_native(&shape, REGIME).expect("subtree hologram");
        let vk = hologram.verifier_key().clone();
        assert_eq!(vk.num_public, SUBTREE_PUBLIC_WORDS);
        let masked_proof = v2::prove(
            &masked_shape,
            masked_assignment,
            FULL_SHARD_LABEL,
            PROFILE,
            &[0x43; 32],
        )
        .expect("seed masked proof");
        assert!(v2::verify(
            &masked_shape,
            &public_words,
            FULL_SHARD_LABEL,
            PROFILE,
            &masked_proof,
        ));
        let proof = prove_public_hologram(
            &shape,
            &hologram,
            assignment,
            SUBTREE_ROOT_LABEL,
            &[0x42; 32],
        )
        .expect("seed hologram proof");
        assert!(verify_public_hologram(
            &vk,
            &public_words,
            SUBTREE_ROOT_LABEL,
            &proof
        ));
        let proof_wire = proof.to_bytes();
        let aggregate = SuccinctSubtreeAggregate {
            total_active_signers: SIGNERS,
            min_key_idx: MIN_KEY,
            max_key_idx: MAX_KEY,
            total_active_weight: WEIGHT,
            proof,
        };

        let (split_shape, _) = small_relation_cs(&[f(1); SPLIT_PUBLIC_WORDS]).finish();
        let split_vk = ShapeHologram::compile_native(&split_shape, REGIME)
            .expect("split hologram")
            .verifier_key()
            .clone();
        assert_eq!(split_vk.num_public, SPLIT_PUBLIC_WORDS);

        let fx = Fixtures {
            vk_wire: vk.to_bytes(),
            vk,
            split_vk,
            roster_root,
            public_words,
            proof_wire,
            aggregate_wire: aggregate.to_bytes(),
            masked_shape,
            masked_proof_wire: masked_proof.to_bytes(),
        };
        assert!(verify_succinct_subtree_aggregate_against_roster_root(
            &fx.vk,
            &statement(&fx),
            &aggregate,
        ));
        fx
    })
}

fn check_verifier_key(fx: &Fixtures, bytes: &[u8]) {
    let Some(vk) = ShapeVerifierKey::from_bytes(bytes) else {
        return;
    };
    assert_eq!(vk.to_bytes(), bytes);
    assert!(vk.is_well_formed());
    if let Some(proof) = HologramPublicProof::from_bytes(&fx.proof_wire, &vk) {
        let verified = verify_public_hologram(&vk, &fx.public_words, SUBTREE_ROOT_LABEL, &proof);
        assert_eq!(verified, vk == fx.vk, "proof accepted under a foreign key");
    }
}

fn check_proof(fx: &Fixtures, bytes: &[u8]) -> Option<bool> {
    let proof = HologramPublicProof::from_bytes(bytes, &fx.vk)?;
    assert_eq!(proof.to_bytes(), bytes);

    let verified = verify_public_hologram(&fx.vk, &fx.public_words, SUBTREE_ROOT_LABEL, &proof);
    if verified {
        assert!(!verify_public_hologram(
            &fx.vk,
            &fx.public_words,
            b"another label",
            &proof
        ));
        let mut other_words = fx.public_words;
        other_words[10] += Goldilocks::ONE;
        assert!(!verify_public_hologram(
            &fx.vk,
            &other_words,
            SUBTREE_ROOT_LABEL,
            &proof
        ));
    }
    Some(verified)
}

fn check_masked_proof(fx: &Fixtures, bytes: &[u8]) -> Option<bool> {
    let proof = ZkHemV2Proof::from_bytes(bytes, &fx.masked_shape)?;
    assert_eq!(proof.to_bytes(), bytes);

    let merge = FullShardMergeProof { proof };
    let merge_wire = merge.to_bytes();
    assert_eq!(merge_wire[..8], *b"QSAGFSM2");
    assert_eq!(&merge_wire[8..], bytes);
    let counts = vec![1u32, 2, 3];
    let carrier = SuccinctFullShardAggregate {
        signer_counts: counts.clone(),
        proof: merge,
    };
    let carrier_wire = carrier.to_bytes();
    assert_eq!(carrier_wire[..8], *SUCCINCT_FULL_SHARD_WIRE_MAGIC);
    assert_eq!(carrier_wire[8..12], (counts.len() as u32).to_le_bytes());
    for (chunk, count) in carrier_wire[12..24].as_chunks::<4>().0.iter().zip(&counts) {
        assert_eq!(*chunk, count.to_le_bytes());
    }
    assert_eq!(carrier_wire[24..], merge_wire);

    let proof = &carrier.proof.proof;
    let verified = v2::verify(
        &fx.masked_shape,
        &fx.public_words,
        FULL_SHARD_LABEL,
        PROFILE,
        proof,
    );
    if verified {
        assert!(!v2::verify(
            &fx.masked_shape,
            &fx.public_words,
            b"another label",
            PROFILE,
            proof,
        ));
        let mut other_words = fx.public_words;
        other_words[10] += Goldilocks::ONE;
        assert!(!v2::verify(
            &fx.masked_shape,
            &other_words,
            FULL_SHARD_LABEL,
            PROFILE,
            proof,
        ));
    }
    Some(verified)
}

fn check_aggregate(fx: &Fixtures, bytes: &[u8]) -> Option<bool> {
    let aggregate = SuccinctSubtreeAggregate::from_bytes_canonical(&fx.vk, bytes)?;
    assert_eq!(aggregate.to_bytes(), bytes);
    let verified =
        verify_succinct_subtree_aggregate_against_roster_root(&fx.vk, &statement(fx), &aggregate);
    if verified {
        assert_eq!(
            (
                aggregate.total_active_signers,
                aggregate.min_key_idx,
                aggregate.max_key_idx,
                aggregate.total_active_weight
            ),
            (SIGNERS, MIN_KEY, MAX_KEY, WEIGHT),
            "aggregate accepted for totals nobody proved"
        );
        let other = RosterRootStatement {
            epoch_floor: EPOCH_FLOOR + 1,
            ..statement(fx)
        };
        assert!(!verify_succinct_subtree_aggregate_against_roster_root(
            &fx.vk, &other, &aggregate
        ));
    }
    Some(verified)
}

fn check_split_aggregate(fx: &Fixtures, bytes: &[u8]) {
    let Some(aggregate) = SplitSubtreeAggregate::from_bytes_canonical(&fx.split_vk, bytes) else {
        return;
    };
    assert_eq!(aggregate.to_bytes(), bytes);
    assert!(!aggregate.verify_against_roster_root(&fx.split_vk, &statement(fx)));
    let _ = aggregate.public().words();
    let _ = aggregate.deferred_openings();
}

fn edited(seed: &[u8], edits: &[u8]) -> Vec<u8> {
    let mut candidate = seed.to_vec();
    for edit in edits.as_chunks::<5>().0 {
        let offset = u32::from_le_bytes([edit[0], edit[1], edit[2], edit[3]]) as usize;
        let index = offset % candidate.len();
        candidate[index] ^= edit[4];
    }
    candidate
}

fn with_magic(magic: &[u8; 8], data: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(8 + data.len());
    out.extend_from_slice(magic);
    out.extend_from_slice(data);
    out
}

fuzz_target!(init: {
    fixtures();
}, |data: &[u8]| {
    let fx = fixtures();

    check_verifier_key(fx, data);
    let _ = check_proof(fx, data);
    let _ = check_masked_proof(fx, data);
    let _ = check_aggregate(fx, data);
    let _ = check_aggregate(fx, &with_magic(SUCCINCT_SUBTREE_WIRE_MAGIC, data));
    check_split_aggregate(fx, data);

    if let [0xed, kind, edits @ ..] = data {
        match kind % 4 {
            0 => check_verifier_key(fx, &edited(&fx.vk_wire, edits)),
            1 => {
                let candidate = edited(&fx.proof_wire, edits);
                let outcome = check_proof(fx, &candidate);
                if candidate == fx.proof_wire {
                    assert_eq!(outcome, Some(true));
                }
            }
            2 => {
                let candidate = edited(&fx.aggregate_wire, edits);
                let outcome = check_aggregate(fx, &candidate);
                if candidate == fx.aggregate_wire {
                    assert_eq!(outcome, Some(true));
                }
            }
            _ => {
                let candidate = edited(&fx.masked_proof_wire, edits);
                let outcome = check_masked_proof(fx, &candidate);
                if candidate == fx.masked_proof_wire {
                    assert_eq!(outcome, Some(true));
                }
            }
        }
    }
});
