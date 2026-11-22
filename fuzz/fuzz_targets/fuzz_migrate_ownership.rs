// SPDX-License-Identifier: Apache-2.0 OR MIT
#![no_main]

//! Coverage-guided fuzzer for the migration ownership wire formats and verifiers of
//! `qsag_migrate::hem::relations`: `OwnershipStatement`, `BatchStatement` and
//! `OwnershipProof` (single and batch), `verify_ownership` and `verify_batch`.
//!
//! Security contract:
//!
//! * arbitrary bytes never panic a decoder, and every accepted encoding re-encodes to its
//!   input (the encodings are canonical);
//! * a decoded statement's registry binding is computed without panicking;
//! * a real proof, edited in a few places chosen by the input, is decoded strictly against
//!   its statement and handed to the verifier, which must not panic;
//! * the real proof never verifies under a different statement of the same relation (an
//!   edited credential, target commitment, nullifier, domain or epoch). The relation is
//!   held fixed because building the relation of an arbitrary statement costs up to a
//!   second and hundreds of megabytes, which the per-input watchdog does not allow.
//!
//! The fixtures (the `init:` block) are one single-key proof and one two-entry batch proof
//! below an extended private key; building them takes about 50 s under coverage
//! instrumentation. Byte 0 of the input selects what the rest is used for. A verifier run
//! costs about a second instrumented, so half of the selector values go to the decoders,
//! the batch verifier gets one eighth, and an input that leaves a fixture unedited is not
//! verified again (the `init:` block already did).

use std::sync::OnceLock;

use qsag_agg::zk_hem::v2::params::Profile;
use qsag_migrate::hem::relations::{
    BatchStatement, Bip32Root, HdNode, KeySource, Lock, OwnershipProof, OwnershipStatement,
    OwnershipWitness, prove_batch, prove_ownership, verify_batch, verify_ownership,
};
use libfuzzer_sys::fuzz_target;

/// Regime of the seed proofs. Its proof-of-work grinds through the assembly Keccak
/// kernel, which coverage instrumentation does not slow down.
const REGIME: Profile = Profile::TurboShakeJohnson400;

struct Fixtures {
    statement: OwnershipStatement,
    statement_wire: Vec<u8>,
    proof_wire: Vec<u8>,
    batch: BatchStatement,
    batch_wire: Vec<u8>,
    batch_proof_wire: Vec<u8>,
}

fn fixtures() -> &'static Fixtures {
    static FX: OnceLock<Fixtures> = OnceLock::new();
    FX.get_or_init(|| {
        let mut key = [0u8; 32];
        key[31] = 1;
        let witness = OwnershipWitness::secp256k1_key(&key);
        let statement = OwnershipStatement::derive(
            Lock::P2pkh,
            KeySource::Secp256k1Key,
            &witness,
            [0x11; 32],
            [0x22; 32],
            7,
        )
        .expect("fixture statement");
        let proof =
            prove_ownership(&statement, &witness, REGIME, &[0x33; 32]).expect("fixture proof");
        assert!(verify_ownership(&statement, REGIME, &proof));

        let node = HdNode {
            private_key: [0x44; 32],
            chain_code: [0x55; 32],
        };
        let root = OwnershipWitness::extended_key(&node);
        let batch = BatchStatement::derive(
            Lock::P2pkh,
            Bip32Root::ExtendedKey,
            &[],
            &[(vec![0], [0x66; 32]), (vec![1], [0x77; 32])],
            &root,
            [0x22; 32],
            7,
        )
        .expect("fixture batch");
        let batch_proof = prove_batch(&batch, &root, REGIME, &[0x88; 32]).expect("batch proof");
        assert!(verify_batch(&batch, REGIME, &batch_proof));

        Fixtures {
            statement_wire: statement.to_bytes(),
            proof_wire: proof.to_bytes(),
            statement,
            batch_wire: batch.to_bytes(),
            batch_proof_wire: batch_proof.to_bytes(),
            batch,
        }
    })
}

/// `base` with up to eight edits read from `edits`: four bytes each, a 24-bit offset and
/// the byte to XOR in. A trailing odd byte truncates or extends the result by one byte.
fn edited(base: &[u8], edits: &[u8]) -> Vec<u8> {
    let mut out = base.to_vec();
    let mut chunks = edits.chunks_exact(4);
    for edit in chunks.by_ref().take(8) {
        let offset = usize::from(edit[0]) | usize::from(edit[1]) << 8 | usize::from(edit[2]) << 16;
        let len = out.len();
        out[offset % len] ^= edit[3];
    }
    match chunks.remainder() {
        [1, ..] => {
            out.pop();
        }
        [2, extra, ..] => out.push(*extra),
        _ => {}
    }
    out
}

fn check_statement(data: &[u8]) {
    if let Some(statement) = OwnershipStatement::from_bytes(data) {
        assert_eq!(statement.to_bytes(), data, "statement encoding is not canonical");
        let binding = statement.binding();
        assert_eq!(binding.nullifier, statement.nullifier);
        assert_eq!(binding.legacy_id, statement.credential.identifier());
    }
}

fn check_batch(data: &[u8]) {
    if let Some(batch) = BatchStatement::from_bytes(data) {
        assert_eq!(batch.to_bytes(), data, "batch encoding is not canonical");
        let bindings = batch.bindings();
        assert_eq!(bindings.len(), batch.entries.len());
        for (index, binding) in bindings.iter().enumerate() {
            let single = batch.statement(index).expect("entry in range");
            assert_eq!(*binding, single.binding());
            assert_eq!(
                OwnershipStatement::from_bytes(&single.to_bytes()).as_ref(),
                Some(&single)
            );
        }
    }
}

fuzz_target!(init: {
    fixtures();
}, |data: &[u8]| {
    let fx = fixtures();
    let Some((&mode, rest)) = data.split_first() else {
        return;
    };

    match mode % 16 {
        // Raw bytes through the statement decoders.
        0..=5 => {
            check_statement(rest);
            check_batch(rest);
        }
        // Raw bytes as a proof of the fixture statements.
        6 | 7 => {
            if let Some(proof) = OwnershipProof::from_bytes(rest, &fx.statement) {
                assert_eq!(proof.to_bytes(), rest, "proof encoding is not canonical");
                let _ = verify_ownership(&fx.statement, REGIME, &proof);
            }
            if let Some(proof) = OwnershipProof::from_bytes_batch(rest, &fx.batch) {
                assert_eq!(proof.to_bytes(), rest, "batch proof encoding is not canonical");
            }
        }
        // The real proof, edited.
        8..=10 => {
            let wire = edited(&fx.proof_wire, rest);
            if wire == fx.proof_wire {
                return;
            }
            if let Some(proof) = OwnershipProof::from_bytes(&wire, &fx.statement) {
                assert_eq!(proof.to_bytes(), wire);
                let _ = verify_ownership(&fx.statement, REGIME, &proof);
            }
        }
        // The real proof under an edited statement of the same relation.
        11..=13 => {
            let wire = edited(&fx.statement_wire, rest);
            check_statement(&wire);
            if let Some(statement) = OwnershipStatement::from_bytes(&wire) {
                if statement.lock == fx.statement.lock
                    && statement.source == fx.statement.source
                    && statement != fx.statement
                {
                    let proof = OwnershipProof::from_bytes(&fx.proof_wire, &statement)
                        .expect("same relation, same proof layout");
                    assert!(
                        !verify_ownership(&statement, REGIME, &proof),
                        "a proof verified under another statement"
                    );
                }
            }
        }
        // The real batch proof, edited.
        14 => {
            let wire = edited(&fx.batch_proof_wire, rest);
            if wire == fx.batch_proof_wire {
                return;
            }
            if let Some(proof) = OwnershipProof::from_bytes_batch(&wire, &fx.batch) {
                assert_eq!(proof.to_bytes(), wire);
                let _ = verify_batch(&fx.batch, REGIME, &proof);
            }
        }
        // The real batch proof under an edited batch of the same relation.
        _ => {
            let wire = edited(&fx.batch_wire, rest);
            check_batch(&wire);
            if let Some(batch) = BatchStatement::from_bytes(&wire) {
                let same_relation = batch.lock == fx.batch.lock
                    && batch.root == fx.batch.root
                    && batch.prefix == fx.batch.prefix
                    && batch.entries.len() == fx.batch.entries.len()
                    && batch.entries.iter().zip(&fx.batch.entries).all(|(a, b)| a.tail == b.tail);
                if same_relation && batch != fx.batch {
                    let proof = OwnershipProof::from_bytes_batch(&fx.batch_proof_wire, &batch)
                        .expect("same relation, same proof layout");
                    assert!(
                        !verify_batch(&batch, REGIME, &proof),
                        "a batch proof verified under another batch"
                    );
                }
            }
        }
    }
});
