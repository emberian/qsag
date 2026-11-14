//! Credentials enrolled using the threshold symmetric OPRF in `voprf`.
//!
//! The issuer authorizes the disclosed issuance attributes and a proof of their
//! blinded commitment. An authenticated TOPRF evaluation of the canonical
//! issuance message replaces the former threshold lattice signature. The issuer
//! enrolls that commitment in its authoritative accumulator. Verifiers must pin
//! the accumulator root, epoch policy, schema and fresh challenge externally.
//! A token alone is not an independently publicly verifiable signature.
//!
//! Attribute, presentation, scope and Merkle commitments use a rate-6,
//! capacity-6 Poseidon2 sponge with six-limb digests.
//! The repeated-view membership proof hides the leaf and undisclosed attributes
//! under its classical Fiat-Shamir/ZKBoo assumptions. No quantum Fiat-Shamir
//! theorem is claimed. Fresh mode avoids an intentional stable scope pseudonym;
//! revealed attributes and application metadata may still identify the holder.
//! Issuance attributes and the accumulator leaf are visible to the issuer.
//! The OPRF protects its input against one server, not against a caller that
//! separately discloses the same input through an issuance request.
//!
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use qsag_accel::ct::{ct_eq_bytes, ct_zeroize_bytes, ct_zeroize_u64s};
use qsag_accel::goldilocks::{
    GOLDILOCKS_PRIME, gl_add, gl_is_canonical, gl_mul, gl_neg, gl_reduce_u64, gl_sub,
};
use qsag_accel::keccak::{
    InterleavedTranscript, Shake256, commit_mpc_broadcast, cshake256_framed_32,
};
use qsag_accel::poseidon2::{
    POSEIDON2_CONST_IV, POSEIDON2_HALF_EXTERNAL_ROUNDS, POSEIDON2_INTERNAL_ROUNDS,
    poseidon2_apply_me, poseidon2_apply_mi, poseidon2_const_at, poseidon2_perm12,
};

use crate::fips204_ntt::{MlDsaLevel, MlDsaSigningKey, ml_dsa_sign_deterministic, ml_dsa_verify};
use crate::voprf::{Evaluation, PublicKey};

/// Maximum canonical Goldilocks field attributes per `PiBlindVc` credential.
pub const MAX_VC_ATTRS: usize = 6;
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
impl ZkSoundnessProfile {
    pub const fn repetitions(self) -> usize {
        match self {
            Self::Classical128 => 219,
            Self::Quantum128 => 438,
        }
    }
}

pub const VC_FINAL_OUTPUTS: usize = 18 + VC_ACCUMULATOR_DEPTH;

const VC_ATTR_COMMIT_TAG: u64 = 0x5643_4154_5452_5631; // "VCATTRV1"
const VC_PRES_COMMIT_TAG: u64 = 0x5643_5052_4553_5631; // "VCPRESV1"
const VC_SCOPE_TAG_DOM: u64 = 0x5643_5343_4F50_5631; // "VCSCOPV1"
const VC_MERKLE_NODE_TAG: u64 = 0x5643_4D4B_4C45_5631; // "VCMKLEV1"

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

/// Sample `count` unbiased canonical Goldilocks field elements (`< GOLDILOCKS_PRIME`) from `Shake256`.
fn sample_canonical_gl_vec(domain: &[u8], seed: &[u8; 32], extra: &[u8], count: usize) -> Vec<u64> {
    let mut sp = Shake256::new();
    sp.absorb(domain);
    sp.absorb(seed);
    sp.absorb(extra);
    sp.finalize(0x1F);

    let mut out = Vec::with_capacity(count);
    let mut buf = [0u8; 136];
    while out.len() < count {
        sp.squeeze(&mut buf);
        let mut pos = 0usize;
        while pos + 8 <= buf.len() && out.len() < count {
            let cand = u64::from_le_bytes(buf[pos..pos + 8].try_into().unwrap());
            pos += 8;
            if cand < GOLDILOCKS_PRIME {
                out.push(cand);
            }
        }
    }
    ct_zeroize_bytes(&mut buf);
    out
}

fn sponge12<const N: usize>(message: &mut [u64; N]) {
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
    if N.is_multiple_of(6) {
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
    let mut padded = [0; MAX_VC_ATTRS];
    for (index, &value) in attrs.iter().enumerate() {
        if !gl_is_canonical(value) {
            return Err(BlindVcError::NonCanonicalGoldilocksAttribute { index });
        }
        padded[index] = value;
    }
    let attrs = padded;
    let mut st = [
        attrs[0],
        attrs[1],
        attrs[2],
        attrs[3],
        attrs[4],
        attrs[5],
        blind_limbs[0],
        blind_limbs[1],
        blind_limbs[2],
        blind_limbs[3],
        (schema_id & 0xffff_ffff),
        gl_add(schema_id >> 32, gl_reduce_u64(domain_tag)),
        arity,
    ];
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

fn encode_issuance_message(issuer_epoch: u64, schema_id: u64, attr_commit: &[u64; 6]) -> [u8; 72] {
    let mut out = [0u8; 72];
    out[0..8].copy_from_slice(b"VCISSUE1");
    out[8..16].copy_from_slice(&issuer_epoch.to_le_bytes());
    out[16..24].copy_from_slice(&schema_id.to_le_bytes());
    for (i, &limb) in attr_commit.iter().enumerate() {
        out[24 + i * 8..32 + i * 8].copy_from_slice(&limb.to_le_bytes());
    }
    out
}

// ============================================================================
// 3-Party Goldilocks ZKBoo Gate Engine
// ============================================================================

struct ZkBooProverTape {
    r: [Vec<u64>; 3],
    out: [Vec<u64>; 3],
    gate_cursor: usize,
}

impl Drop for ZkBooProverTape {
    fn drop(&mut self) {
        for row in self.r.iter_mut().chain(self.out.iter_mut()) {
            ct_zeroize_u64s(row);
        }
    }
}

impl ZkBooProverTape {
    fn new(tape_seeds: &[[u8; 32]; 3], num_gates: usize) -> Self {
        let r0 = sample_canonical_gl_vec(b"QSAG.VC.ZKBOO_R.V1", &tape_seeds[0], &[0], num_gates);
        let r1 = sample_canonical_gl_vec(b"QSAG.VC.ZKBOO_R.V1", &tape_seeds[1], &[1], num_gates);
        let r2 = sample_canonical_gl_vec(b"QSAG.VC.ZKBOO_R.V1", &tape_seeds[2], &[2], num_gates);
        Self {
            r: [r0, r1, r2],
            out: [
                Vec::with_capacity(num_gates),
                Vec::with_capacity(num_gates),
                Vec::with_capacity(num_gates),
            ],
            gate_cursor: 0,
        }
    }

    #[inline]
    fn mul_gate(&mut self, x: [u64; 3], y: [u64; 3]) -> [u64; 3] {
        let g = self.gate_cursor;
        self.gate_cursor += 1;
        let mut z = [0u64; 3];
        for (m, slot) in z.iter_mut().enumerate() {
            let m1 = (m + 1) % 3;
            let cross = gl_add(
                gl_mul(x[m], y[m]),
                gl_add(gl_mul(x[m], y[m1]), gl_mul(x[m1], y[m])),
            );
            let masked = gl_sub(gl_add(cross, self.r[m][g]), self.r[m1][g]);
            *slot = masked;
            self.out[m].push(masked);
        }
        z
    }

    #[inline]
    fn sbox7(&mut self, x: [u64; 3]) -> [u64; 3] {
        let x2 = self.mul_gate(x, x);
        let x3 = self.mul_gate(x2, x);
        let x4 = self.mul_gate(x2, x2);
        self.mul_gate(x4, x3)
    }

    fn perm12<const N: usize>(&mut self, message: &mut [[u64; 3]; N]) {
        let mut state = [[0; 3]; 12];
        for chunk in message.chunks(6) {
            for (wire, value) in state.iter_mut().zip(chunk) {
                for m in 0..3 {
                    wire[m] = gl_add(wire[m], value[m]);
                }
            }
            if chunk.len() < 6 {
                state[chunk.len()][0] = gl_add(state[chunk.len()][0], 1);
            }
            self.raw_perm12(&mut state);
        }
        if N.is_multiple_of(6) {
            state[0][0] = gl_add(state[0][0], 1);
            self.raw_perm12(&mut state);
        }
        message[..12].copy_from_slice(&state);
    }
    fn raw_perm12(&mut self, st: &mut [[u64; 3]; 12]) {
        apply_me_3(st);
        for r in 0..POSEIDON2_HALF_EXTERNAL_ROUNDS {
            for (lane, wire) in st.iter_mut().enumerate() {
                wire[0] = gl_add(wire[0], poseidon2_const_at(0, r, lane as u64));
                *wire = self.sbox7(*wire);
            }
            apply_me_3(st);
        }
        for r in 0..POSEIDON2_INTERNAL_ROUNDS {
            st[0][0] = gl_add(st[0][0], poseidon2_const_at(1, r, 0));
            st[0] = self.sbox7(st[0]);
            apply_mi_3(st);
        }
        for r in 0..POSEIDON2_HALF_EXTERNAL_ROUNDS {
            for (lane, wire) in st.iter_mut().enumerate() {
                wire[0] = gl_add(wire[0], poseidon2_const_at(2, r, lane as u64));
                *wire = self.sbox7(*wire);
            }
            apply_me_3(st);
        }
    }
}

struct ZkBooVerifierTape<'a> {
    e: usize,
    e1: usize,
    r_e: Vec<u64>,
    r_e1: Vec<u64>,
    out_e: &'a [u64],
    out_e1: &'a [u64],
    gate_cursor: usize,
    ok: bool,
}

impl<'a> ZkBooVerifierTape<'a> {
    fn new(
        e: usize,
        seed_e: &[u8; 32],
        seed_e1: &[u8; 32],
        out_e: &'a [u64],
        out_e1: &'a [u64],
        num_gates: usize,
    ) -> Self {
        let e1 = (e + 1) % 3;
        let ok = out_e.len() == num_gates && out_e1.len() == num_gates;
        let r_e = sample_canonical_gl_vec(b"QSAG.VC.ZKBOO_R.V1", seed_e, &[e as u8], num_gates);
        let r_e1 = sample_canonical_gl_vec(b"QSAG.VC.ZKBOO_R.V1", seed_e1, &[e1 as u8], num_gates);
        Self {
            e,
            e1,
            r_e,
            r_e1,
            out_e,
            out_e1,
            gate_cursor: 0,
            ok,
        }
    }

    #[inline]
    fn add_const(&self, mut x: [u64; 2], c: u64) -> [u64; 2] {
        if self.e == 0 {
            x[0] = gl_add(x[0], c);
        } else if self.e1 == 0 {
            x[1] = gl_add(x[1], c);
        }
        x
    }

    #[inline]
    fn mul_gate(&mut self, x: [u64; 2], y: [u64; 2]) -> [u64; 2] {
        if !self.ok {
            return [0, 0];
        }
        let g = self.gate_cursor;
        self.gate_cursor += 1;
        let cross = gl_add(
            gl_mul(x[0], y[0]),
            gl_add(gl_mul(x[0], y[1]), gl_mul(x[1], y[0])),
        );
        let expected_ze = gl_sub(gl_add(cross, self.r_e[g]), self.r_e1[g]);
        // Opened-view multiplication equation, including the adjacent mask shares.
        let equation = gl_sub(self.out_e[g], expected_ze);
        if equation != 0 {
            self.ok = false;
        }
        [self.out_e[g], self.out_e1[g]]
    }

    #[inline]
    fn sbox7(&mut self, x: [u64; 2]) -> [u64; 2] {
        let x2 = self.mul_gate(x, x);
        let x3 = self.mul_gate(x2, x);
        let x4 = self.mul_gate(x2, x2);
        self.mul_gate(x4, x3)
    }

    fn perm12<const N: usize>(&mut self, message: &mut [[u64; 2]; N]) {
        let mut state = [[0; 2]; 12];
        for chunk in message.chunks(6) {
            for (wire, value) in state.iter_mut().zip(chunk) {
                for m in 0..2 {
                    wire[m] = gl_add(wire[m], value[m]);
                }
            }
            if chunk.len() < 6 {
                state[chunk.len()] = self.add_const(state[chunk.len()], 1);
            }
            self.raw_perm12(&mut state);
        }
        if N.is_multiple_of(6) {
            state[0] = self.add_const(state[0], 1);
            self.raw_perm12(&mut state);
        }
        message[..12].copy_from_slice(&state);
    }
    fn raw_perm12(&mut self, st: &mut [[u64; 2]; 12]) {
        apply_me_2(st);
        for r in 0..POSEIDON2_HALF_EXTERNAL_ROUNDS {
            for (lane, wire) in st.iter_mut().enumerate() {
                *wire = self.add_const(*wire, poseidon2_const_at(0, r, lane as u64));
                *wire = self.sbox7(*wire);
            }
            apply_me_2(st);
        }
        for r in 0..POSEIDON2_INTERNAL_ROUNDS {
            st[0] = self.add_const(st[0], poseidon2_const_at(1, r, 0));
            st[0] = self.sbox7(st[0]);
            apply_mi_2(st);
        }
        for r in 0..POSEIDON2_HALF_EXTERNAL_ROUNDS {
            for (lane, wire) in st.iter_mut().enumerate() {
                *wire = self.add_const(*wire, poseidon2_const_at(2, r, lane as u64));
                *wire = self.sbox7(*wire);
            }
            apply_me_2(st);
        }
    }
}

fn apply_me_3(st: &mut [[u64; 3]; 12]) {
    for m in 0..3 {
        let mut lane_m: [u64; 12] = core::array::from_fn(|i| st[i][m]);
        poseidon2_apply_me(&mut lane_m);
        for (wire, value) in st.iter_mut().zip(lane_m) {
            wire[m] = value;
        }
    }
}

fn apply_mi_3(st: &mut [[u64; 3]; 12]) {
    for m in 0..3 {
        let mut lane_m: [u64; 12] = core::array::from_fn(|i| st[i][m]);
        poseidon2_apply_mi(&mut lane_m);
        for (wire, value) in st.iter_mut().zip(lane_m) {
            wire[m] = value;
        }
    }
}

fn apply_me_2(st: &mut [[u64; 2]; 12]) {
    for m in 0..2 {
        let mut lane_m: [u64; 12] = core::array::from_fn(|i| st[i][m]);
        poseidon2_apply_me(&mut lane_m);
        for (wire, value) in st.iter_mut().zip(lane_m) {
            wire[m] = value;
        }
    }
}

fn apply_mi_2(st: &mut [[u64; 2]; 12]) {
    for m in 0..2 {
        let mut lane_m: [u64; 12] = core::array::from_fn(|i| st[i][m]);
        poseidon2_apply_mi(&mut lane_m);
        for (wire, value) in st.iter_mut().zip(lane_m) {
            wire[m] = value;
        }
    }
}

const GATES_PER_PERM12: usize = (2 * (POSEIDON2_HALF_EXTERNAL_ROUNDS as usize) * 12
    + (POSEIDON2_INTERNAL_ROUNDS as usize))
    * 12; // Three permutations, four multiplication gates per S-box.

fn split_secret_3(val: u64, s0: u64, s1: u64) -> [u64; 3] {
    let s2 = gl_sub(val, gl_add(s0, s1));
    [s0, s1, s2]
}

fn digest_party_view(
    in_shares: &[u64],
    tape_seed: &[u8; 32],
    gate_outs: &[u64],
    final_outs: &[u64],
) -> [u8; 32] {
    let mut sp = Shake256::new();
    sp.absorb(b"QSAG.VC.VIEW_COM.V1");
    sp.absorb(tape_seed);
    sp.absorb(&(in_shares.len() as u32).to_le_bytes());
    for &x in in_shares {
        sp.absorb(&x.to_le_bytes());
    }
    sp.absorb(&(gate_outs.len() as u32).to_le_bytes());
    for &x in gate_outs {
        sp.absorb(&x.to_le_bytes());
    }
    sp.absorb(&(final_outs.len() as u32).to_le_bytes());
    for &x in final_outs {
        sp.absorb(&x.to_le_bytes());
    }
    sp.finalize(0x1F);
    let mut out = [0u8; 32];
    sp.squeeze(&mut out);
    out
}

/// Unbiased ternary challenge extractor (`byte < 243` yields 5 independent uniform `{0, 1, 2}` trits!).
fn squeeze_ternary_challenges(tr: &mut InterleavedTranscript, count: usize) -> Vec<usize> {
    let mut out = Vec::with_capacity(count);
    let mut raw = [0u8; 64];
    tr.squeeze_bytes(b"VC_ZKBOO_OPEN_TRITS", &mut raw);
    let mut cursor = 0usize;
    let mut extra_round = 0u32;
    while out.len() < count {
        if cursor >= raw.len() {
            tr.absorb(b"VC_TRIT_EXTEND", &extra_round.to_le_bytes());
            extra_round += 1;
            tr.squeeze_bytes(b"VC_ZKBOO_OPEN_TRITS_MORE", &mut raw);
            cursor = 0;
        }
        let b = raw[cursor];
        cursor += 1;
        if b < 243 {
            let mut v = b;
            for _ in 0..5 {
                if out.len() < count {
                    out.push((v % 3) as usize);
                }
                v /= 3;
            }
        }
    }
    out
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OpenedZkBooRepetition {
    pub e: u8,
    pub unopened_commitment: [u8; 32],
    pub salt_e: [u8; 32],
    pub salt_e1: [u8; 32],
    pub in_shares_e: Vec<u64>,
    pub in_shares_e1: Vec<u64>,
    pub tape_seed_e: [u8; 32],
    pub tape_seed_e1: [u8; 32],
    pub gate_outs_e: Vec<u64>,
    pub gate_outs_e1: Vec<u64>,
    pub final_outs_all3: [[u64; 3]; VC_FINAL_OUTPUTS],
    pub num_active_final_outs: usize,
}

// ============================================================================
// Phase 1 & 2: Blind Issuance (`holder_prepare_blind_issuance` + `threshold_issue_blind_vc`)
// ============================================================================

/// Holder secret state with redacted `Debug` and zeroizing `Drop`.
pub struct HolderCredentialSecret {
    pub schema_id: u64,
    arity: usize,
    attrs: [u64; MAX_VC_ATTRS],
    holder_blind: [u64; 4],
}

impl fmt::Debug for HolderCredentialSecret {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("HolderCredentialSecret")
            .field("schema_id", &self.schema_id)
            .field("attrs", &"<REDACTED>")
            .field("holder_blind", &"<REDACTED>")
            .finish()
    }
}

impl Drop for HolderCredentialSecret {
    fn drop(&mut self) {
        ct_zeroize_u64s(&mut self.attrs);
        ct_zeroize_u64s(&mut self.holder_blind);
    }
}

/// Issuance request proving an attested-attribute commitment while hiding its holder blind.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BlindIssuanceRequest {
    pub issuer_pk_digest: [u8; 32],
    pub issuer_epoch: u64,
    pub issuer_attested_attrs: Vec<u64>,
    pub session_id: [u8; 32],
    pub schema_id: u64,
    pub attr_commit: [u64; 6],
    pub opened_reps: Vec<OpenedZkBooRepetition>,
}

/// OPRF-issued credential enrolled in the issuer accumulator.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BlindVerifiableCredential {
    pub issuer_epoch: u64,
    pub schema_id: u64,
    pub attr_commit: [u64; 6],
    /// OPRF token; accumulator membership supplies public authorization.
    pub issuance_token: [u8; 32],
    pub accumulator_leaf_index: usize,
}

/// Prepare a blind issuance request + holder secret from canonical Goldilocks attributes (`<= 6`).
pub fn holder_prepare_blind_issuance(
    schema_id: u64,
    issuer_attested_attrs: &[u64],
    issuer_pk_digest: [u8; 32],
    issuer_epoch: u64,
    holder_entropy: [u8; 32],
    session_id: [u8; 32],
) -> Result<(BlindIssuanceRequest, HolderCredentialSecret), BlindVcError> {
    holder_prepare_blind_issuance_with_profile(
        schema_id,
        issuer_attested_attrs,
        issuer_pk_digest,
        issuer_epoch,
        holder_entropy,
        session_id,
        ZkSoundnessProfile::Quantum128,
    )
}

/// Use an explicit verifier-selected soundness budget.
#[allow(clippy::too_many_arguments)]
pub fn holder_prepare_blind_issuance_with_profile(
    schema_id: u64,
    issuer_attested_attrs: &[u64],
    issuer_pk_digest: [u8; 32],
    issuer_epoch: u64,
    holder_entropy: [u8; 32],
    session_id: [u8; 32],
    profile: ZkSoundnessProfile,
) -> Result<(BlindIssuanceRequest, HolderCredentialSecret), BlindVcError> {
    if !(1..=MAX_VC_ATTRS).contains(&issuer_attested_attrs.len()) {
        return Err(BlindVcError::AttributeCountExceeded {
            count: issuer_attested_attrs.len(),
        });
    }
    let mut attrs = [0u64; MAX_VC_ATTRS];
    for (i, &v) in issuer_attested_attrs.iter().enumerate() {
        if !gl_is_canonical(v) {
            return Err(BlindVcError::NonCanonicalGoldilocksAttribute { index: i });
        }
        attrs[i] = v;
    }

    let mut ent = holder_entropy;
    let mut blind_ctx = Vec::with_capacity(60 + issuer_attested_attrs.len() * 8);
    blind_ctx.extend_from_slice(&session_id);
    blind_ctx.extend_from_slice(&schema_id.to_le_bytes());
    blind_ctx.extend_from_slice(&issuer_pk_digest);
    blind_ctx.extend_from_slice(&issuer_epoch.to_le_bytes());
    blind_ctx.extend_from_slice(&(issuer_attested_attrs.len() as u32).to_le_bytes());
    for value in issuer_attested_attrs {
        blind_ctx.extend_from_slice(&value.to_le_bytes());
    }
    let blind_vec = sample_canonical_gl_vec(b"QSAG.VC.HOLDER_BLIND.V1", &ent, &blind_ctx, 4);
    let holder_blind = [blind_vec[0], blind_vec[1], blind_vec[2], blind_vec[3]];
    let attr_commit = compute_vc_poseidon2_commit(
        schema_id,
        issuer_attested_attrs,
        &holder_blind,
        VC_ATTR_COMMIT_TAG,
    )?;

    // Build the selected ZKBoo repetitions over the 10 secret inputs `(attrs[0..6], holder_blind[0..4])`:
    let mut inst_bytes = Vec::with_capacity(72);
    inst_bytes.extend_from_slice(&session_id);
    inst_bytes.extend_from_slice(&schema_id.to_le_bytes());
    inst_bytes.extend_from_slice(&issuer_pk_digest);
    inst_bytes.extend_from_slice(&issuer_epoch.to_le_bytes());
    inst_bytes.extend_from_slice(&(issuer_attested_attrs.len() as u32).to_le_bytes());
    for value in issuer_attested_attrs {
        inst_bytes.extend_from_slice(&value.to_le_bytes());
    }
    for &c in &attr_commit {
        inst_bytes.extend_from_slice(&c.to_le_bytes());
    }
    if profile == ZkSoundnessProfile::Quantum128 {
        inst_bytes.extend_from_slice(b"QSAG.VC.PROFILE.Quantum128:438");
    }
    let statement_digest = cshake256_framed_32(b"QSAG.VC.ISS_STMT_DIGEST.V1", &[&inst_bytes]);
    let mut hedged_zk_seed = cshake256_framed_32(
        b"QSAG.VC.ISS_ZK_SEED.V1",
        &[&statement_digest, &ent, &session_id],
    );
    let mut tr = InterleavedTranscript::new(b"QSAG.BLIND_VC.ISSUE_ZK.V1", &inst_bytes);
    if profile == ZkSoundnessProfile::Quantum128 {
        tr.absorb(b"VC_SOUNDNESS_PROFILE", b"Quantum128:438");
    }

    let secret_wires: [u64; 10] = [
        attrs[0],
        attrs[1],
        attrs[2],
        attrs[3],
        attrs[4],
        attrs[5],
        holder_blind[0],
        holder_blind[1],
        holder_blind[2],
        holder_blind[3],
    ];

    struct RepData {
        commits: [[u8; 32]; 3],
        salts: [[u8; 32]; 3],
        in_shares: [Vec<u64>; 3],
        tape_seeds: [[u8; 32]; 3],
        gate_outs: [Vec<u64>; 3],
        final_outs: [[u64; 3]; VC_FINAL_OUTPUTS],
    }
    impl Drop for RepData {
        fn drop(&mut self) {
            for row in &mut self.in_shares {
                ct_zeroize_u64s(row);
            }
            for row in &mut self.gate_outs {
                ct_zeroize_u64s(row);
            }
            for row in &mut self.tape_seeds {
                ct_zeroize_bytes(row);
            }
            for row in &mut self.salts {
                ct_zeroize_bytes(row);
            }
            for row in &mut self.final_outs {
                ct_zeroize_u64s(row);
            }
        }
    }

    let mut reps = Vec::with_capacity(profile.repetitions());
    let mut round1_bundle = Vec::with_capacity(profile.repetitions() * 192);

    for rep in 0..profile.repetitions() {
        let rep_be = (rep as u32).to_be_bytes();
        let mut share_ctx = [0u8; 36];
        share_ctx[..32].copy_from_slice(&statement_digest);
        share_ctx[32..].copy_from_slice(&rep_be);
        let in_rand =
            sample_canonical_gl_vec(b"QSAG.VC.ISS_IN_SH.V1", &hedged_zk_seed, &share_ctx, 20);
        let mut in0 = Vec::with_capacity(10);
        let mut in1 = Vec::with_capacity(10);
        let mut in2 = Vec::with_capacity(10);
        let mut wire_3 = [[0u64; 3]; 10];
        for (w, wire) in wire_3.iter_mut().enumerate() {
            let s = if w < MAX_VC_ATTRS {
                [secret_wires[w], 0, 0]
            } else {
                split_secret_3(secret_wires[w], in_rand[2 * w], in_rand[2 * w + 1])
            };
            *wire = s;
            in0.push(s[0]);
            in1.push(s[1]);
            in2.push(s[2]);
        }

        let tape_seeds: [[u8; 32]; 3] = core::array::from_fn(|m| {
            cshake256_framed_32(
                b"QSAG.VC.ISS_TAPE.V1",
                &[
                    &statement_digest,
                    &hedged_zk_seed,
                    &session_id,
                    &rep_be,
                    &[m as u8],
                ],
            )
        });
        let salts: [[u8; 32]; 3] = core::array::from_fn(|m| {
            cshake256_framed_32(
                b"QSAG.VC.ISS_SALT.V1",
                &[
                    &statement_digest,
                    &hedged_zk_seed,
                    &session_id,
                    &rep_be,
                    &[m as u8],
                ],
            )
        });

        let mut prover = ZkBooProverTape::new(&tape_seeds, GATES_PER_PERM12);
        let mut st: [[u64; 3]; 13] = [
            wire_3[0],
            wire_3[1],
            wire_3[2],
            wire_3[3],
            wire_3[4],
            wire_3[5],
            wire_3[6],
            wire_3[7],
            wire_3[8],
            wire_3[9],
            [(schema_id & 0xffff_ffff), 0, 0],
            [
                gl_add(schema_id >> 32, gl_reduce_u64(VC_ATTR_COMMIT_TAG)),
                0,
                0,
            ],
            [issuer_attested_attrs.len() as u64, 0, 0],
        ];
        prover.perm12(&mut st);

        let mut final_outs = [[0u64; 3]; VC_FINAL_OUTPUTS];
        final_outs[..6].copy_from_slice(&st[..6]);

        let in_shares = [in0, in1, in2];
        let commits: [[u8; 32]; 3] = core::array::from_fn(|m| {
            let f_m: [u64; 6] = core::array::from_fn(|j| final_outs[j][m]);
            let d = digest_party_view(&in_shares[m], &tape_seeds[m], &prover.out[m], &f_m);
            commit_mpc_broadcast(&session_id, rep as u32, m as u16, &d, &salts[m])
        });

        for c in &commits {
            round1_bundle.extend_from_slice(c);
        }
        for fout in final_outs.iter().take(6) {
            for &val in fout {
                round1_bundle.extend_from_slice(&val.to_le_bytes());
            }
        }

        reps.push(RepData {
            commits,
            salts,
            in_shares,
            tape_seeds,
            gate_outs: core::mem::take(&mut prover.out),
            final_outs,
        });
    }

    // Absorb ALL Round-1 view commitments & output shares BEFORE ZKBoo challenges!
    tr.absorb(b"VC_ISS_R1_COMMITS", &round1_bundle);
    let open_trits = squeeze_ternary_challenges(&mut tr, profile.repetitions());
    ct_zeroize_bytes(&mut hedged_zk_seed);
    ct_zeroize_bytes(&mut ent);

    let mut opened_reps = Vec::with_capacity(profile.repetitions());
    for (rep_d, e) in reps.into_iter().zip(open_trits) {
        let e1 = (e + 1) % 3;
        let e2 = (e + 2) % 3;
        opened_reps.push(OpenedZkBooRepetition {
            e: e as u8,
            unopened_commitment: rep_d.commits[e2],
            salt_e: rep_d.salts[e],
            salt_e1: rep_d.salts[e1],
            in_shares_e: rep_d.in_shares[e].clone(),
            in_shares_e1: rep_d.in_shares[e1].clone(),
            tape_seed_e: rep_d.tape_seeds[e],
            tape_seed_e1: rep_d.tape_seeds[e1],
            gate_outs_e: rep_d.gate_outs[e].clone(),
            gate_outs_e1: rep_d.gate_outs[e1].clone(),
            final_outs_all3: rep_d.final_outs,
            num_active_final_outs: 6,
        });
    }

    Ok((
        BlindIssuanceRequest {
            issuer_pk_digest,
            issuer_epoch,
            issuer_attested_attrs: issuer_attested_attrs.to_vec(),
            session_id,
            schema_id,
            attr_commit,
            opened_reps,
        },
        HolderCredentialSecret {
            schema_id,
            arity: issuer_attested_attrs.len(),
            attrs,
            holder_blind,
        },
    ))
}

/// Verify a request against externally authorized attributes and schema.
pub fn verify_blind_issuance_request(
    req: &BlindIssuanceRequest,
    issuer_attested_attrs: &[u64],
    expected_schema_id: u64,
) -> bool {
    verify_blind_issuance_request_with_profile(
        req,
        issuer_attested_attrs,
        expected_schema_id,
        ZkSoundnessProfile::Quantum128,
    )
}

/// Use an explicit verifier-selected soundness budget.
#[allow(clippy::too_many_arguments)]
pub fn verify_blind_issuance_request_with_profile(
    req: &BlindIssuanceRequest,
    issuer_attested_attrs: &[u64],
    expected_schema_id: u64,
    profile: ZkSoundnessProfile,
) -> bool {
    if req.schema_id != expected_schema_id
        || !(1..=MAX_VC_ATTRS).contains(&issuer_attested_attrs.len())
        || req.issuer_attested_attrs != issuer_attested_attrs
        || !issuer_attested_attrs.iter().all(|&v| gl_is_canonical(v))
    {
        return false;
    }
    if req.opened_reps.len() != profile.repetitions() {
        return false;
    }
    for &c in &req.attr_commit {
        if !gl_is_canonical(c) {
            return false;
        }
    }

    let mut inst_bytes = Vec::with_capacity(72);
    inst_bytes.extend_from_slice(&req.session_id);
    inst_bytes.extend_from_slice(&req.schema_id.to_le_bytes());
    inst_bytes.extend_from_slice(&req.issuer_pk_digest);
    inst_bytes.extend_from_slice(&req.issuer_epoch.to_le_bytes());
    inst_bytes.extend_from_slice(&(issuer_attested_attrs.len() as u32).to_le_bytes());
    for value in issuer_attested_attrs {
        inst_bytes.extend_from_slice(&value.to_le_bytes());
    }
    for &c in &req.attr_commit {
        inst_bytes.extend_from_slice(&c.to_le_bytes());
    }
    if profile == ZkSoundnessProfile::Quantum128 {
        inst_bytes.extend_from_slice(b"QSAG.VC.PROFILE.Quantum128:438");
    }
    let mut tr = InterleavedTranscript::new(b"QSAG.BLIND_VC.ISSUE_ZK.V1", &inst_bytes);
    if profile == ZkSoundnessProfile::Quantum128 {
        tr.absorb(b"VC_SOUNDNESS_PROFILE", b"Quantum128:438");
    }

    let mut round1_bundle = Vec::with_capacity(profile.repetitions() * 192);

    for (rep, o) in req.opened_reps.iter().enumerate() {
        let e = o.e as usize;
        if e >= 3
            || o.num_active_final_outs != 6
            || o.final_outs_all3[6..].iter().flatten().any(|&v| v != 0)
            || o.in_shares_e.len() != 10
            || o.in_shares_e1.len() != 10
        {
            return false;
        }
        let e1 = (e + 1) % 3;
        let e2 = (e + 2) % 3;

        for index in 0..MAX_VC_ATTRS {
            let value = issuer_attested_attrs.get(index).copied().unwrap_or(0);
            if o.in_shares_e[index] != if e == 0 { value } else { 0 }
                || o.in_shares_e1[index] != if e1 == 0 { value } else { 0 }
            {
                return false;
            }
        }
        for &x in o.in_shares_e.iter().chain(o.in_shares_e1.iter()) {
            if !gl_is_canonical(x) {
                return false;
            }
        }
        for &x in o.gate_outs_e.iter().chain(o.gate_outs_e1.iter()) {
            if !gl_is_canonical(x) {
                return false;
            }
        }

        let mut verifier = ZkBooVerifierTape::new(
            e,
            &o.tape_seed_e,
            &o.tape_seed_e1,
            &o.gate_outs_e,
            &o.gate_outs_e1,
            GATES_PER_PERM12,
        );
        let wire_2: [[u64; 2]; 10] =
            core::array::from_fn(|w| [o.in_shares_e[w], o.in_shares_e1[w]]);
        let mut st: [[u64; 2]; 13] = [
            wire_2[0],
            wire_2[1],
            wire_2[2],
            wire_2[3],
            wire_2[4],
            wire_2[5],
            wire_2[6],
            wire_2[7],
            wire_2[8],
            wire_2[9],
            verifier.add_const([0, 0], req.schema_id & 0xffff_ffff),
            verifier.add_const(
                [0, 0],
                gl_add(req.schema_id >> 32, gl_reduce_u64(VC_ATTR_COMMIT_TAG)),
            ),
            verifier.add_const([0, 0], issuer_attested_attrs.len() as u64),
        ];
        verifier.perm12(&mut st);
        if !verifier.ok {
            return false;
        }

        for (j, wire) in st.iter().take(6).enumerate() {
            for &s_val in &o.final_outs_all3[j] {
                if !gl_is_canonical(s_val) {
                    return false;
                }
            }
            if wire[0] != o.final_outs_all3[j][e] || wire[1] != o.final_outs_all3[j][e1] {
                return false;
            }
            let recon = gl_add(
                o.final_outs_all3[j][0],
                gl_add(o.final_outs_all3[j][1], o.final_outs_all3[j][2]),
            );
            if recon != req.attr_commit[j] {
                return false;
            }
        }

        let f_e: [u64; 6] = core::array::from_fn(|j| o.final_outs_all3[j][e]);
        let f_e1: [u64; 6] = core::array::from_fn(|j| o.final_outs_all3[j][e1]);
        let d_e = digest_party_view(&o.in_shares_e, &o.tape_seed_e, &o.gate_outs_e, &f_e);
        let d_e1 = digest_party_view(&o.in_shares_e1, &o.tape_seed_e1, &o.gate_outs_e1, &f_e1);
        let com_e = commit_mpc_broadcast(&req.session_id, rep as u32, e as u16, &d_e, &o.salt_e);
        let com_e1 =
            commit_mpc_broadcast(&req.session_id, rep as u32, e1 as u16, &d_e1, &o.salt_e1);

        let mut commits = [[0u8; 32]; 3];
        commits[e] = com_e;
        commits[e1] = com_e1;
        commits[e2] = o.unopened_commitment;
        for c in &commits {
            round1_bundle.extend_from_slice(c);
        }
        for fout in o.final_outs_all3.iter().take(6) {
            for &val in fout {
                round1_bundle.extend_from_slice(&val.to_le_bytes());
            }
        }
    }

    tr.absorb(b"VC_ISS_R1_COMMITS", &round1_bundle);
    let expected_trits = squeeze_ternary_challenges(&mut tr, profile.repetitions());
    for (o, exp_e) in req.opened_reps.iter().zip(expected_trits) {
        if (o.e as usize) != exp_e {
            return false;
        }
    }
    true
}

/// Domain-separated 32-byte commitment tag binding `(issuer_pk_digest, issuer_epoch, accumulator_root)`.
pub fn compute_accumulator_root_tag(
    issuer_pk_digest: &[u8; 32],
    issuer_epoch: u64,
    accumulator_root: &[u64; 6],
) -> [u8; 32] {
    let mut root_le = [0u8; 48];
    for (i, &limb) in accumulator_root.iter().enumerate() {
        root_le[i * 8..(i + 1) * 8].copy_from_slice(&limb.to_le_bytes());
    }
    cshake256_framed_32(
        b"QSAG.VC.ACC_ROOT_TAG.V1",
        &[issuer_pk_digest, &issuer_epoch.to_le_bytes(), &root_le],
    )
}

/// Issuer-signed commitment/attestation binding `(issuer_pk_digest, issuer_epoch, accumulator_root)`
/// under FIPS 204 `ML-DSA` (compatible with both single-signer [`ml_dsa_sign_deterministic`] and
/// dealerless [`crate::threshold_mldsa::threshold_sign_mldsa_party`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IssuerRootAttestation {
    issuer_pk_digest: [u8; 32],
    mldsa_level: MlDsaLevel,
    issuer_mldsa_pk: Vec<u8>,
    issuer_epoch: u64,
    accumulator_root: [u64; 6],
    root_tag: [u8; 32],
    mldsa_signature: Vec<u8>,
}

impl IssuerRootAttestation {
    pub const SIGNING_CONTEXT: &'static [u8] = b"QSAG.VC.ROOT_ATTEST.CTX.V1";

    pub fn signing_message(
        issuer_pk_digest: &[u8; 32],
        issuer_epoch: u64,
        accumulator_root: &[u64; 6],
        root_tag: &[u8; 32],
    ) -> [u8; 142] {
        let mut msg = [0u8; 142];
        msg[..22].copy_from_slice(b"QSAG.VC.ROOT_ATTEST.V1");
        msg[22..54].copy_from_slice(issuer_pk_digest);
        msg[54..62].copy_from_slice(&issuer_epoch.to_le_bytes());
        for (i, &limb) in accumulator_root.iter().enumerate() {
            msg[62 + i * 8..62 + (i + 1) * 8].copy_from_slice(&limb.to_le_bytes());
        }
        msg[110..142].copy_from_slice(root_tag);
        msg
    }

    pub const fn issuer_pk_digest(&self) -> &[u8; 32] {
        &self.issuer_pk_digest
    }

    pub const fn mldsa_level(&self) -> MlDsaLevel {
        self.mldsa_level
    }

    pub fn issuer_mldsa_pk(&self) -> &[u8] {
        &self.issuer_mldsa_pk
    }

    pub const fn issuer_epoch(&self) -> u64 {
        self.issuer_epoch
    }

    pub const fn accumulator_root(&self) -> &[u64; 6] {
        &self.accumulator_root
    }

    pub const fn root_tag(&self) -> &[u8; 32] {
        &self.root_tag
    }

    pub fn mldsa_signature(&self) -> &[u8] {
        &self.mldsa_signature
    }

    /// Cryptographically verify `(issuer_pk_digest, issuer_epoch, accumulator_root, root_tag)`
    /// against `expected_issuer_mldsa_pk` and `expected_oprf_pk`.
    pub fn verify(&self, expected_issuer_mldsa_pk: &[u8], expected_oprf_pk: &PublicKey) -> bool {
        if !ct_eq_bytes(&self.issuer_pk_digest, &expected_oprf_pk.commitment()) {
            return false;
        }
        if self.issuer_mldsa_pk.len() != expected_issuer_mldsa_pk.len()
            || !ct_eq_bytes(&self.issuer_mldsa_pk, expected_issuer_mldsa_pk)
        {
            return false;
        }
        if self.accumulator_root.iter().any(|&x| !gl_is_canonical(x)) {
            return false;
        }
        let expected_tag = compute_accumulator_root_tag(
            &self.issuer_pk_digest,
            self.issuer_epoch,
            &self.accumulator_root,
        );
        if !ct_eq_bytes(&self.root_tag, &expected_tag) {
            return false;
        }
        let msg = Self::signing_message(
            &self.issuer_pk_digest,
            self.issuer_epoch,
            &self.accumulator_root,
            &self.root_tag,
        );
        ml_dsa_verify(
            self.mldsa_level,
            expected_issuer_mldsa_pk,
            &msg,
            Self::SIGNING_CONTEXT,
            &self.mldsa_signature,
        )
    }
}

/// Holder-local authorization path; contains no other holders' leaves or tokens.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CredentialMembershipWitness {
    pub leaf_index: usize,
    pub siblings: [[u64; 6]; VC_ACCUMULATOR_DEPTH],
    pub accumulator_root: [u64; 6],
    pub issuer_epoch: u64,
    pub issuer_pk_digest: [u8; 32],
    pub issuance_token: Option<[u8; 32]>,
}

/// Authoritative issuer accumulator of OPRF-issued credential commitments.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IssuerCredentialAccumulator {
    pub oprf_key: PublicKey,
    pub issuer_epoch: u64,
    leaves: Vec<[u64; 6]>,
    enrolled_tokens: Vec<Option<[u8; 32]>>,
    empty_leaf: [u64; 6],
}

impl IssuerCredentialAccumulator {
    pub const CAPACITY: usize = 1 << VC_ACCUMULATOR_DEPTH;

    pub fn new(oprf_key: PublicKey, issuer_epoch: u64) -> Self {
        let empty_leaf = [
            gl_reduce_u64(0x454D_5054_595F_4C30),
            gl_reduce_u64(0x454D_5054_595F_4C31),
            (issuer_epoch & 0xffff_ffff),
            issuer_epoch >> 32,
            0,
            0,
        ];
        Self {
            oprf_key,
            issuer_epoch,
            leaves: Vec::new(),
            enrolled_tokens: Vec::new(),
            empty_leaf,
        }
    }

    #[cfg(test)]
    fn enroll(&mut self, attr_commit: [u64; 6]) -> Result<usize, BlindVcError> {
        if self.leaves.len() >= Self::CAPACITY {
            return Err(BlindVcError::AccumulatorFull);
        }
        let idx = self.leaves.len();
        self.leaves.push(attr_commit);
        self.enrolled_tokens.push(None);
        Ok(idx)
    }

    fn enroll_issued(
        &mut self,
        attr_commit: [u64; 6],
        issuance_token: [u8; 32],
    ) -> Result<usize, BlindVcError> {
        if self.leaves.len() >= Self::CAPACITY {
            return Err(BlindVcError::AccumulatorFull);
        }
        let idx = self.leaves.len();
        self.leaves.push(attr_commit);
        self.enrolled_tokens.push(Some(issuance_token));
        Ok(idx)
    }

    pub fn root_tag(&self) -> [u8; 32] {
        compute_accumulator_root_tag(&self.oprf_key.commitment(), self.issuer_epoch, &self.root())
    }

    /// Produce an authenticated [`IssuerRootAttestation`] over `(oprf_key, issuer_epoch, root())`
    /// using an arbitrary FIPS 204 `ML-DSA` signer (single-party or threshold MPC).
    pub fn attest_root<F>(
        &self,
        mldsa_level: MlDsaLevel,
        issuer_mldsa_pk: Vec<u8>,
        sign_fn: F,
    ) -> Result<IssuerRootAttestation, BlindVcError>
    where
        F: FnOnce(&[u8], &[u8]) -> Result<Vec<u8>, BlindVcError>,
    {
        let issuer_pk_digest = self.oprf_key.commitment();
        let accumulator_root = self.root();
        let root_tag =
            compute_accumulator_root_tag(&issuer_pk_digest, self.issuer_epoch, &accumulator_root);
        let msg = IssuerRootAttestation::signing_message(
            &issuer_pk_digest,
            self.issuer_epoch,
            &accumulator_root,
            &root_tag,
        );
        let mldsa_signature = sign_fn(&msg, IssuerRootAttestation::SIGNING_CONTEXT)?;
        let attestation = IssuerRootAttestation {
            issuer_pk_digest,
            mldsa_level,
            issuer_mldsa_pk,
            issuer_epoch: self.issuer_epoch,
            accumulator_root,
            root_tag,
            mldsa_signature,
        };
        if !attestation.verify(&attestation.issuer_mldsa_pk, &self.oprf_key) {
            return Err(BlindVcError::RootAttestationFailed);
        }
        Ok(attestation)
    }

    /// Convenience deterministic FIPS 204 `ML-DSA` attestation for single-key or test issuers.
    pub fn attest_root_deterministic(
        &self,
        mldsa_level: MlDsaLevel,
        issuer_mldsa_sk: &MlDsaSigningKey,
        issuer_mldsa_pk: Vec<u8>,
    ) -> Result<IssuerRootAttestation, BlindVcError> {
        self.attest_root(mldsa_level, issuer_mldsa_pk, |msg, ctx| {
            ml_dsa_sign_deterministic(issuer_mldsa_sk, msg, ctx)
                .ok_or(BlindVcError::RootAttestationFailed)
        })
    }

    fn sparse_layers(&self) -> (Vec<Vec<[u64; 6]>>, Vec<[u64; 6]>) {
        let mut layers = vec![self.leaves.clone()];
        let mut empty = vec![self.empty_leaf];
        for level in 0..VC_ACCUMULATOR_DEPTH {
            let nodes = &layers[level];
            let next = nodes
                .chunks(2)
                .map(|pair| {
                    merkle_hash_pair(
                        &pair[0],
                        pair.get(1).unwrap_or(&empty[level]),
                        self.issuer_epoch,
                        level as u32,
                    )
                })
                .collect();
            empty.push(merkle_hash_pair(
                &empty[level],
                &empty[level],
                self.issuer_epoch,
                level as u32,
            ));
            layers.push(next);
        }
        (layers, empty)
    }

    pub fn root(&self) -> [u64; 6] {
        let (layers, empty) = self.sparse_layers();
        layers[VC_ACCUMULATOR_DEPTH]
            .first()
            .copied()
            .unwrap_or(empty[VC_ACCUMULATOR_DEPTH])
    }

    pub fn membership_witness(
        &self,
        leaf_index: usize,
    ) -> Result<CredentialMembershipWitness, BlindVcError> {
        Ok(CredentialMembershipWitness {
            leaf_index,
            siblings: self.merkle_path(leaf_index)?,
            accumulator_root: self.root(),
            issuer_epoch: self.issuer_epoch,
            issuer_pk_digest: self.oprf_key.commitment(),
            issuance_token: self.enrolled_tokens[leaf_index],
        })
    }

    pub fn merkle_path(
        &self,
        leaf_index: usize,
    ) -> Result<[[u64; 6]; VC_ACCUMULATOR_DEPTH], BlindVcError> {
        if leaf_index >= self.leaves.len() {
            return Err(BlindVcError::InvalidAccumulatorLeafIndex);
        }
        let (layers, empty) = self.sparse_layers();
        Ok(core::array::from_fn(|level| {
            layers[level]
                .get((leaf_index >> level) ^ 1)
                .copied()
                .unwrap_or(empty[level])
        }))
    }
}

/// Canonical input to the TOPRF, binding epoch, schema and the blinded leaf.
pub fn issuance_input(req: &BlindIssuanceRequest) -> [u8; 72] {
    encode_issuance_message(req.issuer_epoch, req.schema_id, &req.attr_commit)
}
/// Enroll an issuer-authorized request after obtaining its OPRF evaluation over
/// authenticated server channels. `evaluation` must be finalized by the issuer's
/// channel adapter, never accepted as a holder-supplied deserialized object.
pub fn threshold_issue_blind_vc(
    accumulator: &mut IssuerCredentialAccumulator,
    req: &BlindIssuanceRequest,
    issuer_attested_attrs: &[u64],
    evaluation: &Evaluation,
    expected_schema_id: u64,
) -> Result<BlindVerifiableCredential, BlindVcError> {
    threshold_issue_blind_vc_with_profile(
        accumulator,
        req,
        issuer_attested_attrs,
        evaluation,
        expected_schema_id,
        ZkSoundnessProfile::Quantum128,
    )
}

/// Use an explicit verifier-selected soundness budget.
#[allow(clippy::too_many_arguments)]
pub fn threshold_issue_blind_vc_with_profile(
    accumulator: &mut IssuerCredentialAccumulator,
    req: &BlindIssuanceRequest,
    issuer_attested_attrs: &[u64],
    evaluation: &Evaluation,
    expected_schema_id: u64,
    profile: ZkSoundnessProfile,
) -> Result<BlindVerifiableCredential, BlindVcError> {
    if req.issuer_epoch != accumulator.issuer_epoch
        || req.issuer_pk_digest != accumulator.oprf_key.commitment()
        || !verify_blind_issuance_request_with_profile(
            req,
            issuer_attested_attrs,
            expected_schema_id,
            profile,
        )
    {
        return Err(BlindVcError::BlindIssuanceProofInvalid);
    }
    let issuance_token = evaluation
        .value_for(&accumulator.oprf_key, &issuance_input(req))
        .ok_or(BlindVcError::InvalidOprfEvaluation)?;
    if ct_eq_bytes(&issuance_token, &[0u8; 32]) {
        return Err(BlindVcError::InvalidOprfEvaluation);
    }
    let accumulator_leaf_index = accumulator.enroll_issued(req.attr_commit, issuance_token)?;
    Ok(BlindVerifiableCredential {
        issuer_epoch: accumulator.issuer_epoch,
        schema_id: req.schema_id,
        attr_commit: req.attr_commit,
        issuance_token,
        accumulator_leaf_index,
    })
}

// ============================================================================
// Phase 3: Unlinkable Selective-Disclosure Presentation (`prove_selective_disclosure`)
// ============================================================================

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PresentationMode {
    UnlinkableFresh,
    ScopedPseudonym([u8; 32]),
}

fn presentation_scope(
    scope: &[u8],
    challenge: &[u8; 32],
    nonce: &[u8; 32],
    mode: PresentationMode,
) -> [u64; 4] {
    let domain = match mode {
        PresentationMode::UnlinkableFresh => {
            cshake256_framed_32(b"QSAG.VC.FRESH.V1", &[scope, challenge, nonce])
        }
        PresentationMode::ScopedPseudonym(id) => {
            cshake256_framed_32(b"QSAG.VC.SCOPED.V1", &[scope, &id])
        }
    };
    hash_verifier_scope_to_limbs(&domain)
}

/// Unlinkable selective-disclosure presentation (`0` `attr_commit`, `0` `leaf_idx`, `0` `issuance_token`!).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SelectiveDisclosurePresentation {
    pub arity: usize,
    pub verifier_challenge: [u8; 32],
    pub mode: PresentationMode,
    pub presentation_nonce: [u8; 32],
    pub issuer_epoch: u64,
    pub schema_id: u64,
    pub accumulator_root: [u64; 6],
    /// Domain-separated commitment tag binding `(issuer_pk_digest, issuer_epoch, accumulator_root)`.
    pub issuer_root_tag: [u8; 32],
    pub verifier_scope_limbs: [u64; 4],
    /// Sorted `(attr_index, disclosed_value)` pairs.
    pub disclosed_attrs: Vec<(usize, u64)>,
    /// Fresh per-presentation rerandomized commitment `Poseidon2(attrs, pres_blind)`.
    pub pres_commit: [u64; 6],
    /// Scope-bound pseudonym/nullifier `Poseidon2(holder_blind, verifier_scope_limbs)`.
    pub scope_tag: [u64; 6],
    pub opened_reps: Vec<OpenedZkBooRepetition>,
}

const SD_NUM_PERMS: usize = 3 + VC_ACCUMULATOR_DEPTH; // Attribute, Merkle path, presentation, scope.
const SD_MERKLE_MUX_GATES: usize = VC_ACCUMULATOR_DEPTH * (1 + 6); // One Boolean check and six limb swaps per level.
const SD_TOTAL_GATES: usize = SD_NUM_PERMS * GATES_PER_PERM12 + SD_MERKLE_MUX_GATES;

/// The public statement of a selective-disclosure proof.
struct SdInstance<'a> {
    arity: usize,
    presentation_nonce: &'a [u8; 32],
    issuer_epoch: u64,
    schema_id: u64,
    accumulator_root: &'a [u64; 6],
    issuer_root_tag: &'a [u8; 32],
    verifier_scope_limbs: &'a [u64; 4],
    disclosed_attrs: &'a [(usize, u64)],
    pres_commit: &'a [u64; 6],
    scope_tag: &'a [u64; 6],
}

fn serialize_sd_instance(instance: &SdInstance<'_>) -> Vec<u8> {
    let SdInstance {
        arity,
        presentation_nonce,
        issuer_epoch,
        schema_id,
        accumulator_root,
        issuer_root_tag,
        verifier_scope_limbs,
        disclosed_attrs,
        pres_commit,
        scope_tag,
    } = *instance;
    let mut out = Vec::with_capacity(256);
    out.extend_from_slice(&(arity as u64).to_le_bytes());
    out.extend_from_slice(presentation_nonce);
    out.extend_from_slice(&issuer_epoch.to_le_bytes());
    out.extend_from_slice(&schema_id.to_le_bytes());
    out.extend_from_slice(issuer_root_tag);
    for &x in accumulator_root
        .iter()
        .chain(verifier_scope_limbs.iter())
        .chain(pres_commit.iter())
        .chain(scope_tag.iter())
    {
        out.extend_from_slice(&x.to_le_bytes());
    }
    out.extend_from_slice(&(disclosed_attrs.len() as u32).to_le_bytes());
    for &(idx, val) in disclosed_attrs {
        out.extend_from_slice(&(idx as u32).to_le_bytes());
        out.extend_from_slice(&val.to_le_bytes());
    }
    out
}

/// What the verifier asked for: its scope, its fresh challenge, and whether
/// presentations to it may be linked.
pub struct PresentationRequest<'a> {
    pub verifier_scope: &'a [u8],
    pub verifier_challenge: &'a [u8; 32],
    pub mode: PresentationMode,
}

/// Generate an **unlinkable selective-disclosure ZK presentation** revealing ONLY `disclosed_indices`.
pub fn prove_selective_disclosure(
    cred: &BlindVerifiableCredential,
    holder_secret: &HolderCredentialSecret,
    membership: &CredentialMembershipWitness,
    disclosed_indices: &[usize],
    request: PresentationRequest<'_>,
    presentation_entropy: [u8; 32],
) -> Result<SelectiveDisclosurePresentation, BlindVcError> {
    prove_selective_disclosure_with_profile(
        cred,
        holder_secret,
        membership,
        disclosed_indices,
        request,
        presentation_entropy,
        ZkSoundnessProfile::Quantum128,
    )
}

/// Use an explicit verifier-selected soundness budget.
#[allow(clippy::too_many_arguments)]
