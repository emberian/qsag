//! Credentials enrolled using the threshold symmetric OPRF in `voprf`.
//!
//! The issuer authorizes the disclosed issuance attributes and a proof of their
//! blinded commitment. An authenticated TOPRF evaluation of the canonical
//! issuance message replaces the former threshold lattice signature. The issuer
//! enrolls that commitment in its authoritative accumulator. Verifiers must pin
//! the accumulator root, epoch policy, schema and fresh challenge externally.
//! A token alone is not an independently publicly verifiable signature. Anyone
//! with trusted issuer ML-DSA and OPRF public records can verify a membership
//! presentation and the issuer's root attestation; that verifies enrollment and
//! the proved attributes, not an independent credential signature or the truth
//! of the issuer's attribute claims. Revocation/freshness requires external root
//! and epoch policy. Replay is refused by the verifier's challenge ledger:
//! [`verify_presentation`] accepts a presentation only by consuming a challenge
//! from a [`PresentationChallenges`] ([`VerifierChallengeLedger`], or the durable
//! `FsVerifierChallengeLedger` with feature `std`).
//!
//! Attribute, presentation, scope and Merkle commitments use a rate-6,
//! capacity-6 Poseidon2 sponge with six-limb digests.
//! Issuance commitments use 3-party Goldilocks ZKBoo; selective-disclosure
//! membership presentations use an N=256 seed-tree MPC-in-the-head polynomial
//! multiplication check over GF(p^5) = GF(p)\[T\]/(T^5 - 3). No quantum Fiat-Shamir
//! theorem is claimed. Fresh mode requires fresh private holder entropy for every
//! presentation and avoids an intentional stable scope pseudonym;
//! revealed attributes and application metadata may still identify the holder.
//! Issuance attributes and the accumulator leaf are visible to the issuer.
//! The OPRF protects its input against one server, not against a caller that
//! separately discloses the same input through an issuance request.
//!
use alloc::collections::BTreeSet;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;
use qsag_asm::wipe::{SecretBuffer, SecretWipe, secret_vec_push};

use qsag_accel::ct::{ct_eq_bytes, ct_zeroize_bytes, ct_zeroize_u64s};
use qsag_accel::goldilocks::{gl_add, gl_is_canonical, gl_mul, gl_reduce_u64, gl_sub};
use qsag_accel::keccak::{
    InterleavedTranscript, Shake256, commit_mpc_broadcast, cshake256_framed_32,
};
use qsag_accel::poseidon2::{
    POSEIDON2_CONST_IV, POSEIDON2_HALF_EXTERNAL_ROUNDS, POSEIDON2_INTERNAL_ROUNDS,
    poseidon2_apply_me, poseidon2_apply_mi, poseidon2_const_at, poseidon2_perm12,
};

use qsag_core::field::goldilocks::{GOLDILOCKS_EPSILON, Goldilocks};

use crate::fips204_ntt::{MlDsaLevel, MlDsaSigningKey, ml_dsa_sign_deterministic, ml_dsa_verify};
#[cfg(feature = "std")]
pub use crate::presentation_challenge::FsVerifierChallengeLedger;
pub use crate::presentation_challenge::{
    ChallengeError, MAX_OUTSTANDING_CHALLENGES, PresentationChallenges, ReplayNotPrevented,
    VerifierChallengeLedger,
};
use crate::voprf::{Evaluation, PublicKey};

mod fp5;
mod issuance;
mod presentation;
mod sd_circuit;
mod seed_tree;
mod wire;
mod zkboo;

use fp5::*;
pub use issuance::*;
pub use presentation::*;
use sd_circuit::*;
use seed_tree::*;
pub use zkboo::*;
/// Maximum canonical Goldilocks field attributes per `PiBlindVc` credential.
pub const MAX_VC_ATTRS: usize = 32;
/// Poseidon2 Merkle accumulator depth ($2^{20}$ credentials per epoch).
pub const VC_ACCUMULATOR_DEPTH: usize = 20;
/// Default repetitions: 438, targeting 128-bit Grover challenge-grinding soundness.
pub const VC_ZKBOO_REPS: usize = 438;

/// Challenge soundness budget. Repetition counts bound classical challenge grinding;
/// Quantum128 targets 128 bits under a quadratic Grover speedup. This is not a
/// standalone QROM proof of the complete protocol or its other primitives.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ZkSoundnessProfile {
    Classical128,
    Quantum128,
}
/// Number of emulated MPC parties per selective-disclosure repetition (`2^8 = 256`).
pub const VC_SD_LIMBO_PARTIES: usize = 256;
/// Binary GGM seed-tree depth (`log2(256) = 8`).
pub const VC_SD_GGM_DEPTH: usize = 8;

impl ZkSoundnessProfile {
    /// Statement tag of the blind-issuance proof. Both profiles carry one, so a
    /// proof never verifies under a profile other than the one it was made for
    /// by the absence of a tag alone.
    const fn issuance_statement_tag(self) -> &'static [u8] {
        match self {
            Self::Classical128 => b"QSAG.VC.PROFILE.Classical128:219",
            Self::Quantum128 => b"QSAG.VC.PROFILE.Quantum128:438",
        }
    }

    /// Transcript tag of the blind-issuance proof.
    const fn issuance_transcript_tag(self) -> &'static [u8] {
        match self {
            Self::Classical128 => b"Classical128:219",
            Self::Quantum128 => b"Quantum128:438",
        }
    }

    /// Repetition count for 3-party ZKBoo blind issuance (`(2/3)^r` soundness).
    pub const fn repetitions(self) -> usize {
        match self {
            Self::Classical128 => 219,
            Self::Quantum128 => 438,
        }
    }

    /// Repetition count for 256-party selective disclosure (`(1/256)^tau` soundness:
    /// `tau = 17` gives `2^-136` classical; `tau = 33` gives `2^-264` classical / `2^-132` Grover).
    pub const fn sd_repetitions(self) -> usize {
        match self {
            Self::Classical128 => 17,
            Self::Quantum128 => 33,
        }
    }
}

pub const VC_FINAL_OUTPUTS: usize = 18 + VC_ACCUMULATOR_DEPTH;

pub(crate) const VC_ATTR_COMMIT_TAG: u64 = 0x5643_4154_5452_5631; // "VCATTRV1"
pub(crate) const VC_PRES_COMMIT_TAG: u64 = 0x5643_5052_4553_5631; // "VCPRESV1"
pub(crate) const VC_SCOPE_TAG_DOM: u64 = 0x5643_5343_4F50_5631; // "VCSCOPV1"
pub(crate) const VC_MERKLE_NODE_TAG: u64 = 0x5643_4D4B_4C45_5631; // "VCMKLEV1"

/// Errors returned by `PiBlindVc` issuance, accumulator enrollment, or selective disclosure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BlindVcError {
    AttributeCountExceeded { count: usize },
    NonCanonicalGoldilocksAttribute { index: usize },
    InvalidDisclosedAttributeIndex { index: usize },
    DuplicateDisclosedAttributeIndex { index: usize },
    DisclosedAttributeValueMismatch { index: usize },
    BlindIssuanceProofInvalid,
    InvalidOprfEvaluation,
    AccumulatorFull,
    InvalidAccumulatorLeafIndex,
    CredentialBindingMismatch,
    RootAttestationFailed,
    SelectiveDisclosureProofInvalid,
}

/// Sample `count` unbiased canonical Goldilocks field elements from `Shake256`, rejecting every
/// word the strict core lift [`Goldilocks::from_le_bytes_canonical`] refuses.
fn sample_canonical_gl_vec(
    domain: &[u8],
    seed: &[u8; 32],
    extra: &[u8],
    count: usize,
) -> SecretBuffer<Vec<u64>> {
    let mut sp = Shake256::new();
    sp.absorb(domain);
    sp.absorb(seed);
    sp.absorb(extra);
    sp.finalize(0x1F);

    let mut out = SecretBuffer(Vec::with_capacity(count));
    let mut buf = [0u8; 136];
    while out.0.len() < count {
        sp.squeeze(&mut buf);
        let mut pos = 0usize;
        while pos + 8 <= buf.len() && out.0.len() < count {
            let cand = Goldilocks::from_le_bytes_canonical(buf[pos..pos + 8].try_into().unwrap());
            pos += 8;
            if let Ok(limb) = cand {
                out.0.push(limb.to_canonical_u64());
            }
        }
    }
    ct_zeroize_bytes(&mut buf);
    out
}

fn sponge12(message: &mut [u64]) {
    let mut state = [0; 12];
    for chunk in message.chunks(6) {
        for (lane, &value) in state.iter_mut().zip(chunk) {
            *lane = gl_add(*lane, value);
        }
        if chunk.len() < 6 {
            state[chunk.len()] = gl_add(state[chunk.len()], 1);
        }
        poseidon2_perm12(&mut state);
    }
    if message.len().is_multiple_of(6) {
        state[0] = gl_add(state[0], 1);
        poseidon2_perm12(&mut state);
    }
    message[..12].copy_from_slice(&state);
    ct_zeroize_u64s(&mut state);
}

/// Plaintext Width-12 `Poseidon2` attribute/presentation commitment:
/// Absorb padded attributes, blind, schema, domain and explicit arity at rate
/// six with six zero-initialized capacity limbs; squeeze six limbs.
pub fn compute_vc_poseidon2_commit(
    schema_id: u64,
    attrs: &[u64],
    blind_limbs: &[u64; 4],
    domain_tag: u64,
) -> Result<[u64; 6], BlindVcError> {
    if !(1..=MAX_VC_ATTRS).contains(&attrs.len()) {
        return Err(BlindVcError::AttributeCountExceeded { count: attrs.len() });
    }
    let arity = attrs.len() as u64;
    let mut padded = SecretBuffer([0; MAX_VC_ATTRS]);
    for (index, &value) in attrs.iter().enumerate() {
        if !gl_is_canonical(value) {
            return Err(BlindVcError::NonCanonicalGoldilocksAttribute { index });
        }
        padded[index] = value;
    }
    // Keep the original six-slot padding for small credentials. Larger schemas
    // absorb every attribute into the same rate-six, capacity-six sponge.
    let mut st = SecretBuffer(Vec::with_capacity(attrs.len().max(6) + 7));
    st.extend_from_slice(&padded[..attrs.len().max(6)]);
    st.extend_from_slice(blind_limbs);
    st.extend_from_slice(&[
        schema_id & 0xffff_ffff,
        gl_add(schema_id >> 32, gl_reduce_u64(domain_tag)),
        arity,
    ]);
    sponge12(&mut st);
    let out = [st[0], st[1], st[2], st[3], st[4], st[5]];
    ct_zeroize_u64s(&mut st);
    Ok(out)
}

/// Plaintext scope-bound pseudonym/nullifier `Poseidon2([holder_blind[0..4], scope[0..4], 0, 0, schema_id, VC_SCOPE_TAG_DOM])`.
pub fn compute_vc_scope_tag(
    schema_id: u64,
    holder_blind: &[u64; 4],
    scope_limbs: &[u64; 4],
) -> [u64; 6] {
    let mut st = [
        holder_blind[0],
        holder_blind[1],
        holder_blind[2],
        holder_blind[3],
        scope_limbs[0],
        scope_limbs[1],
        scope_limbs[2],
        scope_limbs[3],
        0,
        0,
        (schema_id & 0xffff_ffff),
        gl_add(schema_id >> 32, gl_reduce_u64(VC_SCOPE_TAG_DOM)),
    ];
    sponge12(&mut st);
    let out = [st[0], st[1], st[2], st[3], st[4], st[5]];
    ct_zeroize_u64s(&mut st);
    out
}

/// Hash a verifier scope byte string into 4 canonical Goldilocks field limbs.
pub fn hash_verifier_scope_to_limbs(verifier_scope: &[u8]) -> [u64; 4] {
    let seed = cshake256_framed_32(b"QSAG.BLIND_VC.SCOPE.V1", &[verifier_scope]);
    let v = sample_canonical_gl_vec(b"QSAG.BLIND_VC.SCOPE_GL.V1", &seed, b"", 4);
    [v[0], v[1], v[2], v[3]]
}

fn merkle_hash_pair(left: &[u64; 6], right: &[u64; 6], epoch: u64, layer: u32) -> [u64; 6] {
    let mut st = [
        left[0],
        left[1],
        left[2],
        left[3],
        left[4],
        left[5],
        right[0],
        right[1],
        right[2],
        right[3],
        right[4],
        right[5],
        (epoch & 0xffff_ffff),
        layer as u64,
        gl_reduce_u64(VC_MERKLE_NODE_TAG),
        gl_add(epoch >> 32, gl_reduce_u64(POSEIDON2_CONST_IV)),
    ];
    sponge12(&mut st);
    [st[0], st[1], st[2], st[3], st[4], st[5]]
}

fn encode_issuance_message(
    issuer_epoch: u64,
    schema_id: u64,
    attr_commit: &[u64; 6],
    issuer_pk_digest: &[u8; 32],
    session_id: &[u8; 32],
) -> [u8; 136] {
    let mut out = [0u8; 136];
    out[0..8].copy_from_slice(b"VCISSUE2");
    out[8..16].copy_from_slice(&issuer_epoch.to_le_bytes());
    out[16..24].copy_from_slice(&schema_id.to_le_bytes());
    for (i, &limb) in attr_commit.iter().enumerate() {
        out[24 + i * 8..32 + i * 8].copy_from_slice(&limb.to_le_bytes());
    }
    out[72..104].copy_from_slice(issuer_pk_digest);
    out[104..136].copy_from_slice(session_id);
    out
}

impl core::fmt::Display for BlindVcError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{self:?}")
    }
}
impl core::error::Error for BlindVcError {}

#[cfg(test)]
mod tests;
