//! Shared shard circuit geometry and statement-framing helpers for Quintic `Fp5` `Hem`
//! (`QSAGHQM2`, [`crate::hem_quintic`]).

use alloc::vec::Vec;

use crate::field::Goldilocks;
use crate::pcs::MAX_PCS_NUM_VARS;
use crate::sig::{AggSigProfile, Digest5, SigningMode, ValidatorPublicKey};
use crate::sponge::{cshake256_32, encode_multi_frame};
use crate::trace::{
    ConstraintKind, LOG_TRACE_COLS, StepOp, build_signer_program, index_unique_program_ops,
    rows_per_signer,
};

/// Largest number of signers one shard can hold under `profile`: the shard's witness polynomial
/// has `LOG_TRACE_COLS + log2(num_signer_slots * rows_per_signer)` variables, which must not
/// exceed [`MAX_PCS_NUM_VARS`].
pub const fn max_shard_signers(profile: AggSigProfile) -> usize {
    1usize
        << (MAX_PCS_NUM_VARS - LOG_TRACE_COLS - rows_per_signer(profile).trailing_zeros() as usize)
}

/// Witness size (in variables) of a full shard under the default aggregation configuration.
/// A `2^24`-entry witness commits in about 1 GiB; every extra variable doubles prover memory.
pub const DEFAULT_SHARD_PCS_NUM_VARS: usize = 24;

/// Signers per shard under the default configuration: the largest count whose witness has
/// [`DEFAULT_SHARD_PCS_NUM_VARS`] variables. Configurations may raise it up to
/// [`max_shard_signers`].
pub const fn default_shard_signers(profile: AggSigProfile) -> usize {
    1usize
        << (DEFAULT_SHARD_PCS_NUM_VARS
            - LOG_TRACE_COLS
            - rows_per_signer(profile).trailing_zeros() as usize)
}

/// Domain-separated 32-byte digest binding the exact `SigningMode` statement for `active_indices`.
pub fn compute_signing_mode_digest(
    pks: &[ValidatorPublicKey],
    active_indices: &[usize],
    mode: &SigningMode<'_>,
) -> Option<[u8; 32]> {
    match mode {
        SigningMode::SharedMessage(msg) => {
            let framed = encode_multi_frame(&[b"SHARED_MSG_V2", msg]);
            Some(cshake256_32(b"QSAG.SIGNING.MODE/v2", &framed))
        }
        SigningMode::PerSignerMessages(msgs) => {
            if msgs.len() != active_indices.len() {
                return None;
            }
            let mut slices: Vec<&[u8]> = Vec::with_capacity(1 + 2 * msgs.len());
            slices.push(b"PER_SIGNER_MSGS_V2");
            let pk_bytes_vec: Vec<[u8; 65]> = active_indices
                .iter()
                .map(|&idx| pks[idx].to_bytes())
                .collect();
            for (pk_b, m) in pk_bytes_vec.iter().zip(msgs.iter()) {
                slices.push(pk_b);
                slices.push(m);
            }
            let framed = encode_multi_frame(&slices);
            Some(cshake256_32(b"QSAG.SIGNING.MODE/v2", &framed))
        }
    }
}

/// One shard signer's public inputs to the row constraints.
#[derive(Clone, Copy)]
pub(crate) struct ShardSigner {
    pub(crate) pk: ValidatorPublicKey,
    pub(crate) mu: Digest5,
}

/// The per-signer step program and its constraint index, shared by every shard of a batch.
#[derive(Clone)]
pub(crate) struct ShardCircuit {
    pub(crate) program: Vec<StepOp>,
    pub(crate) unique_ops: Vec<ConstraintKind>,
    pub(crate) step_to_uid: Vec<usize>,
    pub(crate) step_c0_base: Vec<Goldilocks>,
    pub(crate) num_signer_slots: usize,
}

impl ShardCircuit {
    pub(crate) fn new(profile: AggSigProfile, num_signer_slots: usize) -> Self {
        let _phase = crate::profile::span("shard_circuit_new");
        let program = build_signer_program(profile);
        let (unique_ops, step_to_uid, step_c0_base) = index_unique_program_ops(&program);
        Self {
            program,
            unique_ops,
            step_to_uid,
            step_c0_base,
            num_signer_slots,
        }
    }

    #[inline]
    pub(crate) fn rows_per_signer(&self) -> usize {
        self.program.len()
    }

    #[inline]
    pub(crate) fn log_local(&self) -> usize {
        self.rows_per_signer().trailing_zeros() as usize
    }

    #[inline]
    pub(crate) fn log_rows(&self) -> usize {
        self.log_local() + self.num_signer_slots.trailing_zeros() as usize
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sig::ValidatorKeypair;

    #[test]
    fn shard_capacities_and_signing_mode_digest_injectivity() {
        assert_eq!(max_shard_signers(AggSigProfile::JortsPoseidon2), 2048);
        assert_eq!(max_shard_signers(AggSigProfile::CorduroyPoseidon2), 128);
        assert_eq!(default_shard_signers(AggSigProfile::JortsPoseidon2), 128);
        assert_eq!(default_shard_signers(AggSigProfile::CorduroyPoseidon2), 8);

        let kp0 =
            ValidatorKeypair::keygen_deterministic(AggSigProfile::JortsPoseidon2, &[1; 32], 0);
        let kp1 =
            ValidatorKeypair::keygen_deterministic(AggSigProfile::JortsPoseidon2, &[2; 32], 1);
        let pks = [kp0.pk, kp1.pk];
        let d_shared =
            compute_signing_mode_digest(&pks, &[0, 1], &SigningMode::SharedMessage(b"ab")).unwrap();
        let d_per_a = compute_signing_mode_digest(
            &pks,
            &[0, 1],
            &SigningMode::PerSignerMessages(&[b"a", b"b"]),
        )
        .unwrap();
        let d_per_b = compute_signing_mode_digest(
            &pks,
            &[0, 1],
            &SigningMode::PerSignerMessages(&[b"ab", b""]),
        )
        .unwrap();
        assert_ne!(d_shared, d_per_a);
        assert_ne!(d_per_a, d_per_b);
        assert!(
            compute_signing_mode_digest(&pks, &[0, 1], &SigningMode::PerSignerMessages(&[b"only"]))
                .is_none()
        );
    }
}
