#![allow(clippy::needless_range_loop, clippy::type_complexity)]

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
//! Issuance commitments use 3-party Goldilocks ZKBoo; selective-disclosure
//! membership presentations use an N=256 seed-tree MPC-in-the-head polynomial
//! multiplication check over GF(p^5) = GF(p)[T]/(T^5 - 3). No quantum Fiat-Shamir
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
    GOLDILOCKS_PRIME, gl_add, gl_is_canonical, gl_mul, gl_reduce_u64, gl_reduce128, gl_sub,
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
/// Number of emulated MPC parties per selective-disclosure repetition (`2^8 = 256`).
pub const VC_SD_LIMBO_PARTIES: usize = 256;
/// Binary GGM seed-tree depth (`log2(256) = 8`).
pub const VC_SD_GGM_DEPTH: usize = 8;

impl ZkSoundnessProfile {
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
    ReplayedVerifierChallenge,
    AccumulatorFull,
    InvalidAccumulatorLeafIndex,
    CredentialBindingMismatch,
    RootAttestationFailed,
    SelectiveDisclosureProofInvalid,
}

struct ZeroizingU64Vec(Vec<u64>);

impl core::ops::Deref for ZeroizingU64Vec {
    type Target = [u64];
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Drop for ZeroizingU64Vec {
    fn drop(&mut self) {
        ct_zeroize_u64s(&mut self.0);
    }
}

/// Sample `count` unbiased canonical Goldilocks field elements (`< GOLDILOCKS_PRIME`) from `Shake256`.
fn sample_canonical_gl_vec(
    domain: &[u8],
    seed: &[u8; 32],
    extra: &[u8],
    count: usize,
) -> ZeroizingU64Vec {
    let mut sp = Shake256::new();
    sp.absorb(domain);
    sp.absorb(seed);
    sp.absorb(extra);
    sp.finalize(0x1F);

    let mut out = ZeroizingU64Vec(Vec::with_capacity(count));
    let mut buf = [0u8; 136];
    while out.0.len() < count {
        sp.squeeze(&mut buf);
        let mut pos = 0usize;
        while pos + 8 <= buf.len() && out.0.len() < count {
            let cand = u64::from_le_bytes(buf[pos..pos + 8].try_into().unwrap());
            pos += 8;
            if cand < GOLDILOCKS_PRIME {
                out.0.push(cand);
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

// ============================================================================
// 3-Party Goldilocks ZKBoo Gate Engine
// ============================================================================

struct ZkBooProverTape {
    r: [ZeroizingU64Vec; 3],
    out: [Vec<u64>; 3],
    gate_cursor: usize,
}

impl Drop for ZkBooProverTape {
    fn drop(&mut self) {
        for row in self.out.iter_mut() {
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
    r_e: ZeroizingU64Vec,
    r_e1: ZeroizingU64Vec,
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
        if gl_sub(self.out_e[g], expected_ze) != 0 {
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
/// Challenge history is retained for this credential's lifetime, independently
/// of caller entropy. Persist it with the credential when adding backup support;
/// rolling back the entire holder state cannot preserve replay protection.
pub struct HolderCredentialSecret {
    pub schema_id: u64,
    arity: usize,
    attrs: [u64; MAX_VC_ATTRS],
    holder_blind: [u64; 4],
    seen_challenges: core::cell::RefCell<Vec<[u8; 32]>>,
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
#[derive(Clone, PartialEq, Eq)]
pub struct BlindVerifiableCredential {
    pub issuer_epoch: u64,
    pub schema_id: u64,
    pub attr_commit: [u64; 6],
    /// OPRF token; accumulator membership supplies public authorization.
    pub issuance_token: [u8; 32],
    pub accumulator_leaf_index: usize,
}

impl core::fmt::Debug for BlindVerifiableCredential {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("BlindVerifiableCredential")
            .field("issuer_epoch", &self.issuer_epoch)
            .field("schema_id", &self.schema_id)
            .field("attr_commit", &self.attr_commit)
            .field("issuance_token", &"<REDACTED>")
            .field("accumulator_leaf_index", &self.accumulator_leaf_index)
            .finish()
    }
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

    let ent = qsag_accel::ct::RedactedSecret::new(holder_entropy);
    let mut blind_ctx = Vec::with_capacity(60 + issuer_attested_attrs.len() * 8);
    blind_ctx.extend_from_slice(&session_id);
    blind_ctx.extend_from_slice(&schema_id.to_le_bytes());
    blind_ctx.extend_from_slice(&issuer_pk_digest);
    blind_ctx.extend_from_slice(&issuer_epoch.to_le_bytes());
    blind_ctx.extend_from_slice(&(issuer_attested_attrs.len() as u32).to_le_bytes());
    for value in issuer_attested_attrs {
        blind_ctx.extend_from_slice(&value.to_le_bytes());
    }
    let blind_vec =
        sample_canonical_gl_vec(b"QSAG.VC.HOLDER_BLIND.V1", ent.expose(), &blind_ctx, 4);
    let mut holder_blind =
        ZeroizingU64Vec(vec![blind_vec[0], blind_vec[1], blind_vec[2], blind_vec[3]]);
    drop(blind_vec);
    let holder_blind_arr = [
        holder_blind[0],
        holder_blind[1],
        holder_blind[2],
        holder_blind[3],
    ];
    let attr_commit = compute_vc_poseidon2_commit(
        schema_id,
        issuer_attested_attrs,
        &holder_blind_arr,
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
    let hedged_zk_seed = qsag_accel::ct::RedactedSecret::new(cshake256_framed_32(
        b"QSAG.VC.ISS_ZK_SEED.V1",
        &[&statement_digest, ent.expose(), &session_id],
    ));
    let mut tr = InterleavedTranscript::new(b"QSAG.BLIND_VC.ISSUE_ZK.V1", &inst_bytes);
    if profile == ZkSoundnessProfile::Quantum128 {
        tr.absorb(b"VC_SOUNDNESS_PROFILE", b"Quantum128:438");
    }

    let secret_wires = ZeroizingU64Vec(vec![
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
    ]);

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
        let in_rand = sample_canonical_gl_vec(
            b"QSAG.VC.ISS_IN_SH.V1",
            hedged_zk_seed.expose(),
            &share_ctx,
            20,
        );
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
                    hedged_zk_seed.expose(),
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
                    hedged_zk_seed.expose(),
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
    drop(hedged_zk_seed);
    drop(ent);
    drop(secret_wires);

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

    let final_holder_blind = [
        holder_blind[0],
        holder_blind[1],
        holder_blind[2],
        holder_blind[3],
    ];
    let _ = &mut holder_blind;
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
            holder_blind: final_holder_blind,
            seen_challenges: core::cell::RefCell::new(Vec::new()),
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
    consumed_sessions: Vec<[u8; 32]>,
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
            consumed_sessions: Vec::new(),
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
        session_id: [u8; 32],
        attr_commit: [u64; 6],
        issuance_token: [u8; 32],
    ) -> Result<usize, BlindVcError> {
        let mut duplicate = false;
        for prior_session in &self.consumed_sessions {
            duplicate |= ct_eq_bytes(prior_session, &session_id);
        }
        for (prior_leaf, prior_tok) in self.leaves.iter().zip(&self.enrolled_tokens) {
            if let Some(tok) = prior_tok {
                duplicate |= (*prior_leaf == attr_commit) & ct_eq_bytes(tok, &issuance_token);
            }
        }
        if duplicate {
            return Err(BlindVcError::InvalidOprfEvaluation);
        }
        if self.leaves.len() >= Self::CAPACITY {
            return Err(BlindVcError::AccumulatorFull);
        }
        let idx = self.leaves.len();
        self.leaves.push(attr_commit);
        self.enrolled_tokens.push(Some(issuance_token));
        self.consumed_sessions.push(session_id);
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

/// Canonical input to the TOPRF, binding epoch, schema, blinded leaf, issuer key digest, and session.
pub fn issuance_input(req: &BlindIssuanceRequest) -> [u8; 136] {
    encode_issuance_message(
        req.issuer_epoch,
        req.schema_id,
        &req.attr_commit,
        &req.issuer_pk_digest,
        &req.session_id,
    )
}
/// Enroll an issuer-authorized request after obtaining its OPRF evaluation over
/// authenticated server channels. The issuer's independently provisioned receipt
/// key authenticates the evaluation before any accumulator mutation.
pub fn threshold_issue_blind_vc(
    accumulator: &mut IssuerCredentialAccumulator,
    req: &BlindIssuanceRequest,
    issuer_attested_attrs: &[u64],
    evaluation: &Evaluation,
    receipt_key: &crate::voprf::IssuanceReceiptKey,
    expected_schema_id: u64,
) -> Result<BlindVerifiableCredential, BlindVcError> {
    threshold_issue_blind_vc_with_profile(
        accumulator,
        req,
        issuer_attested_attrs,
        evaluation,
        receipt_key,
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
    receipt_key: &crate::voprf::IssuanceReceiptKey,
    expected_schema_id: u64,
    profile: ZkSoundnessProfile,
) -> Result<BlindVerifiableCredential, BlindVcError> {
    if req.issuer_epoch != accumulator.issuer_epoch
        || !ct_eq_bytes(&req.issuer_pk_digest, &accumulator.oprf_key.commitment())
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
        .authenticated_value_for(&accumulator.oprf_key, &issuance_input(req), receipt_key)
        .ok_or(BlindVcError::InvalidOprfEvaluation)?;
    if ct_eq_bytes(&issuance_token, &[0u8; 32]) {
        return Err(BlindVcError::InvalidOprfEvaluation);
    }
    let accumulator_leaf_index =
        accumulator.enroll_issued(req.session_id, req.attr_commit, issuance_token)?;
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
// ============================================================================
// Quintic Goldilocks Extension Field GF(p^5) = GF(p)[T] / (T^5 - 3)
// ============================================================================
//
// Since 5 | (p - 1) for p = 2^64 - 2^32 + 1 and 3^((p - 1) / 5) != 1 (mod p),
// Serret's theorem guarantees T^5 - 3 is irreducible over GF(p), giving an exact
// 320-bit extension field of order p^5 > 2^319.999999998.

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct Fp5([u64; 5]);

impl Fp5 {
    const ZERO: Self = Self([0; 5]);
    const ONE: Self = Self([1, 0, 0, 0, 0]);

    #[inline]
    fn is_zero(self) -> bool {
        (self.0[0] | self.0[1] | self.0[2] | self.0[3] | self.0[4]) == 0
    }

    #[inline]
    fn is_canonical(self) -> bool {
        gl_is_canonical(self.0[0])
            && gl_is_canonical(self.0[1])
            && gl_is_canonical(self.0[2])
            && gl_is_canonical(self.0[3])
            && gl_is_canonical(self.0[4])
    }

    #[inline]
    fn add(self, rhs: Self) -> Self {
        Self([
            gl_add(self.0[0], rhs.0[0]),
            gl_add(self.0[1], rhs.0[1]),
            gl_add(self.0[2], rhs.0[2]),
            gl_add(self.0[3], rhs.0[3]),
            gl_add(self.0[4], rhs.0[4]),
        ])
    }

    #[inline]
    fn sub(self, rhs: Self) -> Self {
        Self([
            gl_sub(self.0[0], rhs.0[0]),
            gl_sub(self.0[1], rhs.0[1]),
            gl_sub(self.0[2], rhs.0[2]),
            gl_sub(self.0[3], rhs.0[3]),
            gl_sub(self.0[4], rhs.0[4]),
        ])
    }

    #[inline]
    fn scale_fp(self, s: u64) -> Self {
        Self([
            gl_mul(self.0[0], s),
            gl_mul(self.0[1], s),
            gl_mul(self.0[2], s),
            gl_mul(self.0[3], s),
            gl_mul(self.0[4], s),
        ])
    }

    #[inline]
    fn mul_by_3(v: u64) -> u64 {
        let v2 = gl_add(v, v);
        gl_add(v2, v)
    }

    #[inline]
    fn mul(self, rhs: Self) -> Self {
        let a = self.0;
        let b = rhs.0;

        let t0_hi = gl_add(
            gl_add(gl_mul(a[1], b[4]), gl_mul(a[2], b[3])),
            gl_add(gl_mul(a[3], b[2]), gl_mul(a[4], b[1])),
        );
        let c0 = gl_add(gl_mul(a[0], b[0]), Self::mul_by_3(t0_hi));

        let t1_lo = gl_add(gl_mul(a[0], b[1]), gl_mul(a[1], b[0]));
        let t1_hi = gl_add(gl_add(gl_mul(a[2], b[4]), gl_mul(a[3], b[3])), gl_mul(a[4], b[2]));
        let c1 = gl_add(t1_lo, Self::mul_by_3(t1_hi));

        let t2_lo = gl_add(gl_add(gl_mul(a[0], b[2]), gl_mul(a[1], b[1])), gl_mul(a[2], b[0]));
        let t2_hi = gl_add(gl_mul(a[3], b[4]), gl_mul(a[4], b[3]));
        let c2 = gl_add(t2_lo, Self::mul_by_3(t2_hi));

        let t3_lo = gl_add(
            gl_add(gl_mul(a[0], b[3]), gl_mul(a[1], b[2])),
            gl_add(gl_mul(a[2], b[1]), gl_mul(a[3], b[0])),
        );
        let t3_hi = gl_mul(a[4], b[4]);
        let c3 = gl_add(t3_lo, Self::mul_by_3(t3_hi));

        let c4 = gl_add(
            gl_add(gl_mul(a[0], b[4]), gl_mul(a[1], b[3])),
            gl_add(gl_add(gl_mul(a[2], b[2]), gl_mul(a[3], b[1])), gl_mul(a[4], b[0])),
        );

        Self([c0, c1, c2, c3, c4])
    }

    #[inline]
    fn to_le_bytes(self) -> [u8; 40] {
        let mut out = [0u8; 40];
        for (i, &limb) in self.0.iter().enumerate() {
            out[i * 8..(i + 1) * 8].copy_from_slice(&limb.to_le_bytes());
        }
        out
    }
}

// ============================================================================
// N=256 GGM Seed Tree & 8-Way SIMD Shake256 Party Tape Engine
// ============================================================================

const SD_NUM_PERMS: usize = 3 + VC_ACCUMULATOR_DEPTH; // Attribute, Merkle path, presentation, scope.
const SD_MERKLE_MUX_GATES: usize = VC_ACCUMULATOR_DEPTH * (1 + 6); // One Boolean check and six limb swaps per level.
const SD_TOTAL_GATES: usize = SD_NUM_PERMS * GATES_PER_PERM12 + SD_MERKLE_MUX_GATES; // 32,708
const SD_CHECKED_GATES: usize = SD_TOTAL_GATES + VC_FINAL_OUTPUTS; // 32,708 + 38 = 32,746
const SD_GRID_B: usize = 181;
const SD_GRID_L: usize = 181; // 181 * 181 = 32,761 >= 32,746
const SD_RPOLY_COEFFS: usize = 2 * SD_GRID_B; // 362 coefficients (degrees 0..=2B except B)

const _: () = assert!(SD_GRID_B * SD_GRID_L >= SD_CHECKED_GATES);

fn ggm_expand_children(
    parent: &[u8; 32],
    presentation_nonce: &[u8; 32],
    rep: u32,
    depth: u8,
    node_idx: u16,
) -> ([u8; 32], [u8; 32]) {
    let mut msg = [0u8; 92];
    msg[0..20].copy_from_slice(b"QSAG.VC.SD_GGM_NODE1");
    msg[20..52].copy_from_slice(presentation_nonce);
    msg[52..56].copy_from_slice(&rep.to_le_bytes());
    msg[56] = depth;
    msg[57..59].copy_from_slice(&node_idx.to_le_bytes());
    msg[59] = 0;
    msg[60..92].copy_from_slice(parent);

    let mut sp = Shake256::new();
    sp.absorb(&msg);
    sp.finalize(0x1F);
    let mut children = [0u8; 64];
    sp.squeeze(&mut children);
    ct_zeroize_bytes(&mut msg);
    let mut left = [0u8; 32];
    let mut right = [0u8; 32];
    left.copy_from_slice(&children[0..32]);
    right.copy_from_slice(&children[32..64]);
    ct_zeroize_bytes(&mut children);
    (left, right)
}

struct ZeroizingGgmTree([[u8; 32]; 2 * VC_SD_LIMBO_PARTIES]);

impl Drop for ZeroizingGgmTree {
    fn drop(&mut self) {
        for node in &mut self.0 {
            ct_zeroize_bytes(node);
        }
    }
}

fn expand_ggm_tree_256(root_seed: &[u8; 32], presentation_nonce: &[u8; 32], rep: u32) -> ZeroizingGgmTree {
    let mut tree = ZeroizingGgmTree([[0u8; 32]; 2 * VC_SD_LIMBO_PARTIES]);
    tree.0[1] = *root_seed;
    for depth in 0..VC_SD_GGM_DEPTH {
        let level_start = 1usize << depth;
        let level_width = 1usize << depth;
        for idx in 0..level_width {
            let parent_pos = level_start + idx;
            let parent_seed = tree.0[parent_pos];
            let (left, right) = ggm_expand_children(
                &parent_seed,
                presentation_nonce,
                rep,
                depth as u8,
                idx as u16,
            );
            tree.0[2 * parent_pos] = left;
            tree.0[2 * parent_pos + 1] = right;
        }
    }
    tree
}

fn extract_ggm_copath(tree: &ZeroizingGgmTree, hidden_party: u8) -> [[u8; 32]; VC_SD_GGM_DEPTH] {
    let leaf_pos = VC_SD_LIMBO_PARTIES + (hidden_party as usize);
    core::array::from_fn(|step| tree.0[(leaf_pos >> step) ^ 1])
}

fn reconstruct_ggm_leaves_256(
    copath: &[[u8; 32]; VC_SD_GGM_DEPTH],
    hidden_party: u8,
    presentation_nonce: &[u8; 32],
    rep: u32,
) -> [[u8; 32]; VC_SD_LIMBO_PARTIES] {
    let mut tree = ZeroizingGgmTree([[0u8; 32]; 2 * VC_SD_LIMBO_PARTIES]);
    let mut known = [false; 2 * VC_SD_LIMBO_PARTIES];
    let leaf_pos = VC_SD_LIMBO_PARTIES + (hidden_party as usize);

    for step in 0..VC_SD_GGM_DEPTH {
        let sib_pos = (leaf_pos >> step) ^ 1;
        tree.0[sib_pos] = copath[step];
        known[sib_pos] = true;
    }

    for depth in 1..VC_SD_GGM_DEPTH {
        let level_start = 1usize << depth;
        let level_width = 1usize << depth;
        for idx in 0..level_width {
            let pos = level_start + idx;
            if known[pos] {
                let parent_seed = tree.0[pos];
                let (left, right) = ggm_expand_children(
                    &parent_seed,
                    presentation_nonce,
                    rep,
                    depth as u8,
                    idx as u16,
                );
                tree.0[2 * pos] = left;
                tree.0[2 * pos + 1] = right;
                known[2 * pos] = true;
                known[2 * pos + 1] = true;
            }
        }
    }

    let mut leaves = [[0u8; 32]; VC_SD_LIMBO_PARTIES];
    for p in 0..VC_SD_LIMBO_PARTIES {
        if p != hidden_party as usize {
            debug_assert!(known[VC_SD_LIMBO_PARTIES + p]);
            leaves[p] = tree.0[VC_SD_LIMBO_PARTIES + p];
        }
    }
    leaves
}

/// 8-way parallel `SHAKE256` (`rate = 136` bytes = `17` `u64` words) PRG sponge driven by
/// [`qsag_asm::keccak_f1600_x8`]. Produces bit-for-bit identical output to scalar [`Shake256`]
/// initialized with `domain(24B) || presentation_nonce(32B) || leaf_seed(32B) || (rep_u32 | (party_u32 << 32))(8B)`.
struct Shake256PartyBatch8 {
    state: qsag_asm::KeccakState8x,
    word_pos: [usize; 8],
}

impl Drop for Shake256PartyBatch8 {
    fn drop(&mut self) {
        qsag_asm::volatile_fill(&mut self.state.0, [0u64; 8]);
    }
}

const PARTY_TAPE_DOMAIN_24: &[u8; 24] = b"QSAG.VC.LIMBO_TAPE.V1\0\0\0";

impl Shake256PartyBatch8 {
    fn new(
        presentation_nonce: &[u8; 32],
        rep: u32,
        base_party: usize,
        leaf_seeds: &[[u8; 32]; 8],
    ) -> Self {
        let mut state = qsag_asm::KeccakState8x::default();
        for lane in 0..3 {
            let w = u64::from_le_bytes(PARTY_TAPE_DOMAIN_24[lane * 8..(lane + 1) * 8].try_into().unwrap());
            state.0[lane] = [w; 8];
        }
        for lane in 0..4 {
            let w = u64::from_le_bytes(presentation_nonce[lane * 8..(lane + 1) * 8].try_into().unwrap());
            state.0[3 + lane] = [w; 8];
        }
        for inst in 0..8 {
            for lane in 0..4 {
                let w = u64::from_le_bytes(
                    leaf_seeds[inst][lane * 8..(lane + 1) * 8].try_into().unwrap(),
                );
                state.0[7 + lane][inst] = w;
            }
            let tag = (rep as u64) | (((base_party + inst) as u64) << 32);
            state.0[11][inst] = tag;
        }
        // 96 bytes absorbed (lanes 0..12); SHAKE256 pad 0x1F at byte 96 (lane 12 LSB)
        // and 0x80 at byte 135 (lane 16 MSB).
        state.0[12] = [0x1Fu64; 8];
        state.0[16] = [0x80u64 << 56; 8];
        qsag_asm::keccak_f1600_x8(&mut state);
        Self {
            state,
            word_pos: [0usize; 8],
        }
    }

    /// Extract the initial 32-byte commitment salt (`lanes 0..4`) for each of the 8 parties.
    fn extract_salts_1(&mut self) -> [[u8; 32]; 8] {
        debug_assert_eq!(self.word_pos, [0usize; 8]);
        let mut salts = [[0u8; 32]; 8];
        for inst in 0..8 {
            for lane in 0..4 {
                salts[inst][lane * 8..(lane + 1) * 8]
                    .copy_from_slice(&self.state.0[lane][inst].to_le_bytes());
            }
            self.word_pos[inst] = 4;
        }
        salts
    }

    /// Squeeze `count` canonical Goldilocks field elements (`< GOLDILOCKS_PRIME`) into each
    /// active lane's destination buffer (`active_mask[inst] == false` skips inactive lanes).
    fn squeeze_canonical_gl(&mut self, active_mask: [bool; 8], outs: &mut [Vec<u64>; 8], count: usize) {
        let mut done = [false; 8];
        let mut all_done = true;
        for inst in 0..8 {
            if !active_mask[inst] || count == 0 {
                done[inst] = true;
            } else {
                outs[inst].clear();
                outs[inst].reserve(count);
                all_done = false;
            }
        }
        while !all_done {
            let mut need_perm = false;
            all_done = true;
            for inst in 0..8 {
                if done[inst] {
                    continue;
                }
                while self.word_pos[inst] < 17 {
                    let cand = self.state.0[self.word_pos[inst]][inst];
                    self.word_pos[inst] += 1;
                    if cand < GOLDILOCKS_PRIME {
                        outs[inst].push(cand);
                        if outs[inst].len() == count {
                            done[inst] = true;
                            break;
                        }
                    }
                }
                if !done[inst] {
                    all_done = false;
                    need_perm = true;
                }
            }
            if need_perm {
                qsag_asm::keccak_f1600_x8(&mut self.state);
                for inst in 0..8 {
                    if !done[inst] {
                        self.word_pos[inst] = 0;
                    }
                }
            }
        }
    }
}

fn digest_limbo_aux(delta_w: &[u64], delta_z: &[u64], delta_c: &[u64; 5]) -> [u8; 32] {
    let mut sp = Shake256::new();
    sp.absorb(b"QSAG.VC.LIMBO_AUX.V1");
    sp.absorb(&(delta_w.len() as u32).to_le_bytes());
    for &w in delta_w {
        sp.absorb(&w.to_le_bytes());
    }
    sp.absorb(&(delta_z.len() as u32).to_le_bytes());
    for &z in delta_z {
        sp.absorb(&z.to_le_bytes());
    }
    for &c in delta_c {
        sp.absorb(&c.to_le_bytes());
    }
    sp.finalize(0x1F);
    let mut out = [0u8; 32];
    sp.squeeze(&mut out);
    out
}

fn commit_limbo_party_r1(
    presentation_nonce: &[u8; 32],
    rep: u32,
    party: u16,
    leaf_seed: &[u8; 32],
    aux_digest: Option<&[u8; 32]>,
    salt_1: &[u8; 32],
) -> [u8; 32] {
    let mut sp = Shake256::new();
    sp.absorb(b"QSAG.VC.LIMBO_R1_COM.V1");
    sp.absorb(presentation_nonce);
    sp.absorb(&rep.to_le_bytes());
    sp.absorb(&party.to_le_bytes());
    sp.absorb(leaf_seed);
    match aux_digest {
        None => sp.absorb(&[0u8]),
        Some(d) => {
            sp.absorb(&[1u8]);
            sp.absorb(d);
        }
    }
    sp.absorb(salt_1);
    sp.finalize(0x1F);
    let mut out = [0u8; 32];
    sp.squeeze(&mut out);
    out
}

fn hash_limbo_party_online(
    presentation_nonce: &[u8; 32],
    rep: u32,
    party: u16,
    alpha_i: &[Fp5; SD_GRID_L],
    beta_i: &[Fp5; SD_GRID_L],
    sigma_i: Fp5,
) -> [u8; 32] {
    let mut sp = Shake256::new();
    sp.absorb(b"QSAG.VC.LIMBO_R2_HASH.V1");
    sp.absorb(presentation_nonce);
    sp.absorb(&rep.to_le_bytes());
    sp.absorb(&party.to_le_bytes());
    let mut raw: [u8; 40];
    for a in alpha_i {
        raw = a.to_le_bytes();
        sp.absorb(&raw);
    }
    for b in beta_i {
        raw = b.to_le_bytes();
        sp.absorb(&raw);
    }
    raw = sigma_i.to_le_bytes();
    sp.absorb(&raw);
    ct_zeroize_bytes(&mut raw);
    sp.finalize(0x1F);
    let mut out = [0u8; 32];
    sp.squeeze(&mut out);
    out
}

fn expand_gamma_weights(gamma_seed: &[u8; 32], rep: u32) -> ([Fp5; SD_GRID_B], [Fp5; SD_GRID_L]) {
    let needed = (SD_GRID_B + SD_GRID_L) * 5;
    let limbs = sample_canonical_gl_vec(
        b"QSAG.VC.LIMBO_GAMMA_EXP.V1",
        gamma_seed,
        &rep.to_le_bytes(),
        needed,
    );
    let mut theta = [Fp5::ZERO; SD_GRID_B];
    let mut eta = [Fp5::ZERO; SD_GRID_L];
    for b in 0..SD_GRID_B {
        let base = b * 5;
        theta[b] = Fp5([
            limbs[base],
            limbs[base + 1],
            limbs[base + 2],
            limbs[base + 3],
            limbs[base + 4],
        ]);
    }
    let off = SD_GRID_B * 5;
    for l in 0..SD_GRID_L {
        let base = off + l * 5;
        eta[l] = Fp5([
            limbs[base],
            limbs[base + 1],
            limbs[base + 2],
            limbs[base + 3],
            limbs[base + 4],
        ]);
    }
    (theta, eta)
}

fn squeeze_nonzero_eval_points(tr: &mut InterleavedTranscript, tau: usize) -> Vec<Fp5> {
    let mut seed = [0u8; 32];
    tr.squeeze_bytes(b"VC_SD_LIMBO_EVAL_SEED", &mut seed);
    let mut out = Vec::with_capacity(tau);
    let mut counter = 0u64;
    while out.len() < tau {
        let limbs = sample_canonical_gl_vec(
            b"QSAG.VC.LIMBO_EVAL_PT.V1",
            &seed,
            &counter.to_le_bytes(),
            5,
        );
        counter += 1;
        let pt = Fp5([limbs[0], limbs[1], limbs[2], limbs[3], limbs[4]]);
        if !pt.is_zero() {
            out.push(pt);
        }
    }
    ct_zeroize_bytes(&mut seed);
    out
}

// ============================================================================
// Plaintext & Single-Party Additive-Share Selective-Disclosure Circuit Engines
// ============================================================================

struct SdPlaintextCircuitTrace {
    x: ZeroizingU64Vec,
    y: ZeroizingU64Vec,
    z: ZeroizingU64Vec,
    final_outs: [u64; VC_FINAL_OUTPUTS],
}

struct PlaintextGateRecorder {
    x: Vec<u64>,
    y: Vec<u64>,
    z: Vec<u64>,
}

impl PlaintextGateRecorder {
    fn new() -> Self {
        Self {
            x: Vec::with_capacity(SD_GRID_B * SD_GRID_L),
            y: Vec::with_capacity(SD_GRID_B * SD_GRID_L),
            z: Vec::with_capacity(SD_GRID_B * SD_GRID_L),
        }
    }

    #[inline]
    fn mul_gate(&mut self, xv: u64, yv: u64) -> u64 {
        let zv = gl_mul(xv, yv);
        self.x.push(xv);
        self.y.push(yv);
        self.z.push(zv);
        zv
    }

    #[inline]
    fn sbox7(&mut self, xv: u64) -> u64 {
        let x2 = self.mul_gate(xv, xv);
        let x3 = self.mul_gate(x2, xv);
        let x4 = self.mul_gate(x2, x2);
        self.mul_gate(x4, x3)
    }

    fn perm12<const N: usize>(&mut self, message: &mut [u64; N]) {
        let mut state = [0u64; 12];
        for chunk in message.chunks(6) {
            for (wire, &value) in state.iter_mut().zip(chunk) {
                *wire = gl_add(*wire, value);
            }
            if chunk.len() < 6 {
                state[chunk.len()] = gl_add(state[chunk.len()], 1);
            }
            self.raw_perm12(&mut state);
        }
        if N.is_multiple_of(6) {
            state[0] = gl_add(state[0], 1);
            self.raw_perm12(&mut state);
        }
        message[..12].copy_from_slice(&state);
        ct_zeroize_u64s(&mut state);
    }

    fn raw_perm12(&mut self, st: &mut [u64; 12]) {
        poseidon2_apply_me(st);
        for r in 0..POSEIDON2_HALF_EXTERNAL_ROUNDS {
            for (lane, wire) in st.iter_mut().enumerate() {
                *wire = gl_add(*wire, poseidon2_const_at(0, r, lane as u64));
                *wire = self.sbox7(*wire);
            }
            poseidon2_apply_me(st);
        }
        for r in 0..POSEIDON2_INTERNAL_ROUNDS {
            st[0] = gl_add(st[0], poseidon2_const_at(1, r, 0));
            st[0] = self.sbox7(st[0]);
            poseidon2_apply_mi(st);
        }
        for r in 0..POSEIDON2_HALF_EXTERNAL_ROUNDS {
            for (lane, wire) in st.iter_mut().enumerate() {
                *wire = gl_add(*wire, poseidon2_const_at(2, r, lane as u64));
                *wire = self.sbox7(*wire);
            }
            poseidon2_apply_me(st);
        }
    }
}

fn eval_sd_plaintext_circuit(
    arity: usize,
    issuer_epoch: u64,
    schema_id: u64,
    verifier_scope_limbs: &[u64; 4],
    disclosed_attrs: &[(usize, u64)],
    expected_final_outs: &[u64; VC_FINAL_OUTPUTS],
    secret_vals: &[u64],
) -> SdPlaintextCircuitTrace {
    let mut rec = PlaintextGateRecorder::new();
    let mut cursor = 0usize;

    let mut attr_wires = [0u64; MAX_VC_ATTRS];
    for (i, slot_w) in attr_wires.iter_mut().enumerate() {
        if i >= arity {
            *slot_w = 0;
        } else if let Some(&(_, pub_val)) = disclosed_attrs.iter().find(|&&(idx, _)| idx == i) {
            *slot_w = pub_val;
        } else {
            *slot_w = secret_vals[cursor];
            cursor += 1;
        }
    }
    let hb_wires: [u64; 4] = core::array::from_fn(|_| {
        let v = secret_vals[cursor];
        cursor += 1;
        v
    });
    let pb_wires: [u64; 4] = core::array::from_fn(|_| {
        let v = secret_vals[cursor];
        cursor += 1;
        v
    });
    let bit_wires: [u64; VC_ACCUMULATOR_DEPTH] = core::array::from_fn(|_| {
        let v = secret_vals[cursor];
        cursor += 1;
        v
    });
    let sib_wires: [[u64; 6]; VC_ACCUMULATOR_DEPTH] = core::array::from_fn(|_| {
        core::array::from_fn(|_| {
            let v = secret_vals[cursor];
            cursor += 1;
            v
        })
    });
    debug_assert_eq!(cursor, secret_vals.len());

    let mut st_attr: [u64; 13] = [
        attr_wires[0],
        attr_wires[1],
        attr_wires[2],
        attr_wires[3],
        attr_wires[4],
        attr_wires[5],
        hb_wires[0],
        hb_wires[1],
        hb_wires[2],
        hb_wires[3],
        schema_id & 0xffff_ffff,
        gl_add(schema_id >> 32, gl_reduce_u64(VC_ATTR_COMMIT_TAG)),
        arity as u64,
    ];
    rec.perm12(&mut st_attr);
    let mut cur_node: [u64; 6] = core::array::from_fn(|j| st_attr[j]);
    ct_zeroize_u64s(&mut st_attr);

    let mut bool_zeros = [0u64; VC_ACCUMULATOR_DEPTH];
    for (lvl, (zero, &b)) in bool_zeros.iter_mut().zip(&bit_wires).enumerate() {
        let one_minus_b = gl_sub(1, b);
        *zero = rec.mul_gate(b, one_minus_b);

        let mut left = [0u64; 6];
        let mut right = [0u64; 6];
        for (j, (left_slot, right_slot)) in left.iter_mut().zip(&mut right).enumerate() {
            let sib_j = sib_wires[lvl][j];
            let diff = gl_sub(sib_j, cur_node[j]);
            let delta = rec.mul_gate(b, diff);
            *left_slot = gl_add(cur_node[j], delta);
            *right_slot = gl_sub(sib_j, delta);
        }

        let mut st_mk: [u64; 16] = [
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
            issuer_epoch & 0xffff_ffff,
            lvl as u64,
            gl_reduce_u64(VC_MERKLE_NODE_TAG),
            gl_add(issuer_epoch >> 32, gl_reduce_u64(POSEIDON2_CONST_IV)),
        ];
        rec.perm12(&mut st_mk);
        cur_node = core::array::from_fn(|j| st_mk[j]);
        ct_zeroize_u64s(&mut st_mk);
    }

    let mut st_pres: [u64; 13] = [
        attr_wires[0],
        attr_wires[1],
        attr_wires[2],
        attr_wires[3],
        attr_wires[4],
        attr_wires[5],
        pb_wires[0],
        pb_wires[1],
        pb_wires[2],
        pb_wires[3],
        schema_id & 0xffff_ffff,
        gl_add(schema_id >> 32, gl_reduce_u64(VC_PRES_COMMIT_TAG)),
        arity as u64,
    ];
    rec.perm12(&mut st_pres);

    let mut st_sc: [u64; 12] = [
        hb_wires[0],
        hb_wires[1],
        hb_wires[2],
        hb_wires[3],
        verifier_scope_limbs[0],
        verifier_scope_limbs[1],
        verifier_scope_limbs[2],
        verifier_scope_limbs[3],
        0,
        0,
        schema_id & 0xffff_ffff,
        gl_add(schema_id >> 32, gl_reduce_u64(VC_SCOPE_TAG_DOM)),
    ];
    rec.perm12(&mut st_sc);
    debug_assert_eq!(rec.x.len(), SD_TOTAL_GATES);

    let mut final_outs = [0u64; VC_FINAL_OUTPUTS];
    final_outs[0..6].copy_from_slice(&cur_node);
    final_outs[6..12].copy_from_slice(&st_pres[0..6]);
    final_outs[12..18].copy_from_slice(&st_sc[0..6]);
    final_outs[18..VC_FINAL_OUTPUTS].copy_from_slice(&bool_zeros);
    ct_zeroize_u64s(&mut st_pres);
    ct_zeroize_u64s(&mut st_sc);
    ct_zeroize_u64s(&mut attr_wires);

    debug_assert_eq!(&final_outs, expected_final_outs);

    // Append 38 public output-wire consistency gates `1 * final_outs[j] = expected_final_outs[j]`,
    // then pad to `SD_GRID_B * SD_GRID_L = 32,761` with `0 * 0 = 0`.
    for j in 0..VC_FINAL_OUTPUTS {
        rec.x.push(1);
        rec.y.push(final_outs[j]);
        rec.z.push(expected_final_outs[j]);
    }
    rec.x.resize(SD_GRID_B * SD_GRID_L, 0);
    rec.y.resize(SD_GRID_B * SD_GRID_L, 0);
    rec.z.resize(SD_GRID_B * SD_GRID_L, 0);

    SdPlaintextCircuitTrace {
        x: ZeroizingU64Vec(rec.x),
        y: ZeroizingU64Vec(rec.y),
        z: ZeroizingU64Vec(rec.z),
        final_outs,
    }
}

struct LinearShareEvaluator<'a> {
    is_party_zero: bool,
    z_shares: &'a [u64],
    gate_cursor: usize,
    x_out: &'a mut [u64],
    y_out: &'a mut [u64],
    z_out: &'a mut [u64],
}

impl<'a> LinearShareEvaluator<'a> {
    #[inline]
    fn const_share(&self, c: u64) -> u64 {
        if self.is_party_zero { c } else { 0 }
    }

    #[inline]
    fn add_const(&self, x: u64, c: u64) -> u64 {
        if self.is_party_zero { gl_add(x, c) } else { x }
    }

    #[inline]
    fn mul_gate(&mut self, x: u64, y: u64) -> u64 {
        let g = self.gate_cursor;
        self.gate_cursor += 1;
        let z = self.z_shares[g];
        self.x_out[g] = x;
        self.y_out[g] = y;
        self.z_out[g] = z;
        z
    }

    #[inline]
    fn sbox7(&mut self, x: u64) -> u64 {
        let x2 = self.mul_gate(x, x);
        let x3 = self.mul_gate(x2, x);
        let x4 = self.mul_gate(x2, x2);
        self.mul_gate(x4, x3)
    }

    fn perm12<const N: usize>(&mut self, message: &mut [u64; N]) {
        let mut state = [0u64; 12];
        for chunk in message.chunks(6) {
            for (wire, &value) in state.iter_mut().zip(chunk) {
                *wire = gl_add(*wire, value);
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

    fn raw_perm12(&mut self, st: &mut [u64; 12]) {
        poseidon2_apply_me(st);
        for r in 0..POSEIDON2_HALF_EXTERNAL_ROUNDS {
            if self.is_party_zero {
                for (lane, wire) in st.iter_mut().enumerate() {
                    *wire = gl_add(*wire, poseidon2_const_at(0, r, lane as u64));
                    *wire = self.sbox7(*wire);
                }
            } else {
                for wire in st.iter_mut() {
                    *wire = self.sbox7(*wire);
                }
            }
            poseidon2_apply_me(st);
        }
        for r in 0..POSEIDON2_INTERNAL_ROUNDS {
            if self.is_party_zero {
                st[0] = gl_add(st[0], poseidon2_const_at(1, r, 0));
            }
            st[0] = self.sbox7(st[0]);
            poseidon2_apply_mi(st);
        }
        for r in 0..POSEIDON2_HALF_EXTERNAL_ROUNDS {
            if self.is_party_zero {
                for (lane, wire) in st.iter_mut().enumerate() {
                    *wire = gl_add(*wire, poseidon2_const_at(2, r, lane as u64));
                    *wire = self.sbox7(*wire);
                }
            } else {
                for wire in st.iter_mut() {
                    *wire = self.sbox7(*wire);
                }
            }
            poseidon2_apply_me(st);
        }
    }
}

#[expect(
    clippy::too_many_arguments,
    reason = "Explicit selective-disclosure statement and per-party additive wire share slices"
)]
fn eval_sd_party_shares(
    party: usize,
    arity: usize,
    issuer_epoch: u64,
    schema_id: u64,
    verifier_scope_limbs: &[u64; 4],
    disclosed_attrs: &[(usize, u64)],
    expected_final_outs: &[u64; VC_FINAL_OUTPUTS],
    w_shares: &[u64],
    z_shares: &[u64],
    x_grid: &mut [u64; SD_GRID_B * SD_GRID_L],
    y_grid: &mut [u64; SD_GRID_B * SD_GRID_L],
    z_grid: &mut [u64; SD_GRID_B * SD_GRID_L],
) {
    let mut ev = LinearShareEvaluator {
        is_party_zero: party == 0,
        z_shares,
        gate_cursor: 0,
        x_out: x_grid,
        y_out: y_grid,
        z_out: z_grid,
    };

    let mut cursor = 0usize;
    let mut attr_wires = [0u64; MAX_VC_ATTRS];
    for (i, slot_w) in attr_wires.iter_mut().enumerate() {
        if i >= arity {
            *slot_w = 0;
        } else if let Some(&(_, pub_val)) = disclosed_attrs.iter().find(|&&(idx, _)| idx == i) {
            *slot_w = ev.const_share(pub_val);
        } else {
            *slot_w = w_shares[cursor];
            cursor += 1;
        }
    }
    let hb_wires: [u64; 4] = core::array::from_fn(|_| {
        let v = w_shares[cursor];
        cursor += 1;
        v
    });
    let pb_wires: [u64; 4] = core::array::from_fn(|_| {
        let v = w_shares[cursor];
        cursor += 1;
        v
    });
    let bit_wires: [u64; VC_ACCUMULATOR_DEPTH] = core::array::from_fn(|_| {
        let v = w_shares[cursor];
        cursor += 1;
        v
    });
    let sib_wires: [[u64; 6]; VC_ACCUMULATOR_DEPTH] = core::array::from_fn(|_| {
        core::array::from_fn(|_| {
            let v = w_shares[cursor];
            cursor += 1;
            v
        })
    });
    debug_assert_eq!(cursor, w_shares.len());

    let mut st_attr: [u64; 13] = [
        attr_wires[0],
        attr_wires[1],
        attr_wires[2],
        attr_wires[3],
        attr_wires[4],
        attr_wires[5],
        hb_wires[0],
        hb_wires[1],
        hb_wires[2],
        hb_wires[3],
        ev.const_share(schema_id & 0xffff_ffff),
        ev.const_share(gl_add(schema_id >> 32, gl_reduce_u64(VC_ATTR_COMMIT_TAG))),
        ev.const_share(arity as u64),
    ];
    ev.perm12(&mut st_attr);
    let mut cur_node: [u64; 6] = core::array::from_fn(|j| st_attr[j]);

    let mut bool_zeros = [0u64; VC_ACCUMULATOR_DEPTH];
    for (lvl, (zero, &b)) in bool_zeros.iter_mut().zip(&bit_wires).enumerate() {
        let one_share = ev.const_share(1);
        let one_minus_b = gl_sub(one_share, b);
        *zero = ev.mul_gate(b, one_minus_b);

        let mut left = [0u64; 6];
        let mut right = [0u64; 6];
        for (j, (left_slot, right_slot)) in left.iter_mut().zip(&mut right).enumerate() {
            let sib_j = sib_wires[lvl][j];
            let diff = gl_sub(sib_j, cur_node[j]);
            let delta = ev.mul_gate(b, diff);
            *left_slot = gl_add(cur_node[j], delta);
            *right_slot = gl_sub(sib_j, delta);
        }

        let mut st_mk: [u64; 16] = [
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
            ev.const_share(issuer_epoch & 0xffff_ffff),
            ev.const_share(lvl as u64),
            ev.const_share(gl_reduce_u64(VC_MERKLE_NODE_TAG)),
            ev.const_share(gl_add(
                issuer_epoch >> 32,
                gl_reduce_u64(POSEIDON2_CONST_IV),
            )),
        ];
        ev.perm12(&mut st_mk);
        cur_node = core::array::from_fn(|j| st_mk[j]);
    }

    let mut st_pres: [u64; 13] = [
        attr_wires[0],
        attr_wires[1],
        attr_wires[2],
        attr_wires[3],
        attr_wires[4],
        attr_wires[5],
        pb_wires[0],
        pb_wires[1],
        pb_wires[2],
        pb_wires[3],
        ev.const_share(schema_id & 0xffff_ffff),
        ev.const_share(gl_add(schema_id >> 32, gl_reduce_u64(VC_PRES_COMMIT_TAG))),
        ev.const_share(arity as u64),
    ];
    ev.perm12(&mut st_pres);

    let mut st_sc: [u64; 12] = [
        hb_wires[0],
        hb_wires[1],
        hb_wires[2],
        hb_wires[3],
        ev.const_share(verifier_scope_limbs[0]),
        ev.const_share(verifier_scope_limbs[1]),
        ev.const_share(verifier_scope_limbs[2]),
        ev.const_share(verifier_scope_limbs[3]),
        0,
        0,
        ev.const_share(schema_id & 0xffff_ffff),
        ev.const_share(gl_add(schema_id >> 32, gl_reduce_u64(VC_SCOPE_TAG_DOM))),
    ];
    ev.perm12(&mut st_sc);
    debug_assert_eq!(ev.gate_cursor, SD_TOTAL_GATES);

    let mut final_outs = [0u64; VC_FINAL_OUTPUTS];
    final_outs[0..6].copy_from_slice(&cur_node);
    final_outs[6..12].copy_from_slice(&st_pres[0..6]);
    final_outs[12..18].copy_from_slice(&st_sc[0..6]);
    final_outs[18..VC_FINAL_OUTPUTS].copy_from_slice(&bool_zeros);

    let one_const = if party == 0 { 1 } else { 0 };
    for j in 0..VC_FINAL_OUTPUTS {
        let g = SD_TOTAL_GATES + j;
        x_grid[g] = one_const;
        y_grid[g] = final_outs[j];
        z_grid[g] = if party == 0 { expected_final_outs[j] } else { 0 };
    }
    for g in SD_CHECKED_GATES..(SD_GRID_B * SD_GRID_L) {
        x_grid[g] = 0;
        y_grid[g] = 0;
        z_grid[g] = 0;
    }
}

/// Evaluate `R~(r) = sum_{d=0..B-1} coeff[d]*r^d + sum_{d=B+1..=2B} coeff[d-1]*r^d`
/// (where the degree-`B` coefficient is identically zero).
fn eval_r_poly_without_b(r_poly_without_b: &[[u64; 5]], r_powers: &[Fp5; 2 * SD_GRID_B + 1]) -> Fp5 {
    debug_assert_eq!(r_poly_without_b.len(), SD_RPOLY_COEFFS);
    let mut acc = Fp5::ZERO;
    for d in 0..SD_GRID_B {
        acc = acc.add(Fp5(r_poly_without_b[d]).mul(r_powers[d]));
    }
    for idx in SD_GRID_B..SD_RPOLY_COEFFS {
        let d = idx + 1;
        acc = acc.add(Fp5(r_poly_without_b[idx]).mul(r_powers[d]));
    }
    acc
}

fn precompute_eval_powers(r: Fp5) -> [Fp5; 2 * SD_GRID_B + 1] {
    let mut powers = [Fp5::ZERO; 2 * SD_GRID_B + 1];
    powers[0] = Fp5::ONE;
    for d in 1..=2 * SD_GRID_B {
        powers[d] = powers[d - 1].mul(r);
    }
    powers
}

struct EvalTables {
    r_powers: [Fp5; 2 * SD_GRID_B + 1],
    theta_r_pow: [Fp5; SD_GRID_B],
    theta: [Fp5; SD_GRID_B],
    eta: [Fp5; SD_GRID_L],
}

impl EvalTables {
    fn new(theta: [Fp5; SD_GRID_B], eta: [Fp5; SD_GRID_L], r: Fp5) -> Self {
        let r_powers = precompute_eval_powers(r);
        let mut theta_r_pow = [Fp5::ZERO; SD_GRID_B];
        for b in 0..SD_GRID_B {
            theta_r_pow[b] = theta[b].mul(r_powers[b + 1]);
        }
        Self {
            r_powers,
            theta_r_pow,
            theta,
            eta,
        }
    }
}

#[inline]
fn gl_reduce_split_u192(lo: u128, hi: u128) -> u64 {
    // Exact modulo p = 2^64 - 2^32 + 1 since 2^64 === 0xffff_ffff (mod p).
    gl_add(gl_reduce128(lo), gl_mul(gl_reduce128(hi), 0xffff_ffff))
}

#[inline]
fn reduce_fp5_split(lo: &[u128; 5], hi: &[u128; 5]) -> Fp5 {
    Fp5([
        gl_reduce_split_u192(lo[0], hi[0]),
        gl_reduce_split_u192(lo[1], hi[1]),
        gl_reduce_split_u192(lo[2], hi[2]),
        gl_reduce_split_u192(lo[3], hi[3]),
        gl_reduce_split_u192(lo[4], hi[4]),
    ])
}

/// Evaluate one party's polynomial shares `(alpha^(i), beta^(i), sigma^(i))` at `r` using
/// lazy 192-bit `(lo, hi)` scalar-in-GF(p) accumulation across rows `b in 0..B` (`0` modular
/// reductions inside the 32,761-gate loop).
#[expect(
    clippy::too_many_arguments,
    reason = "Flat tape slice and precomputed folding/evaluation tables avoid extra heap copies"
)]
fn eval_party_polynomial_shares(
    u_pad: &[Fp5; SD_GRID_L],
    v_pad: &[Fp5; SD_GRID_L],
    c_share: Fp5,
    poly_mask: &[Fp5; SD_RPOLY_COEFFS],
    x_grid: &[u64; SD_GRID_B * SD_GRID_L],
    y_grid: &[u64; SD_GRID_B * SD_GRID_L],
    z_grid: &[u64; SD_GRID_B * SD_GRID_L],
    tables: &EvalTables,
) -> ([Fp5; SD_GRID_L], [Fp5; SD_GRID_L], Fp5) {
    const MASK64: u128 = 0xffff_ffff_ffff_ffff;
    let mut x_lo = [[0u128; 5]; SD_GRID_L];
    let mut x_hi = [[0u128; 5]; SD_GRID_L];
    let mut y_lo = [[0u128; 5]; SD_GRID_L];
    let mut y_hi = [[0u128; 5]; SD_GRID_L];
    let mut z_lo = [[0u128; 5]; SD_GRID_L];
    let mut z_hi = [[0u128; 5]; SD_GRID_L];

    for b in 0..SD_GRID_B {
        let row_off = b * SD_GRID_L;
        let wx = tables.theta_r_pow[b].0.map(|v| v as u128);
        let wy = tables.r_powers[SD_GRID_B - 1 - b].0.map(|v| v as u128);
        let wz = tables.theta[b].0.map(|v| v as u128);
        for l in 0..SD_GRID_L {
            let idx = row_off + l;
            let xv = x_grid[idx] as u128;
            if xv != 0 {
                for c in 0..5 {
                    let p = wx[c] * xv;
                    x_lo[l][c] += p & MASK64;
                    x_hi[l][c] += p >> 64;
                }
            }
            let yv = y_grid[idx] as u128;
            if yv != 0 {
                for c in 0..5 {
                    let p = wy[c] * yv;
                    y_lo[l][c] += p & MASK64;
                    y_hi[l][c] += p >> 64;
                }
            }
            let zv = z_grid[idx] as u128;
            if zv != 0 {
                for c in 0..5 {
                    let p = wz[c] * zv;
                    z_lo[l][c] += p & MASK64;
                    z_hi[l][c] += p >> 64;
                }
            }
        }
    }

    let r_b = tables.r_powers[SD_GRID_B];
    let mut alpha_i = [Fp5::ZERO; SD_GRID_L];
    let mut beta_i = [Fp5::ZERO; SD_GRID_L];
    let mut z_weighted = Fp5::ZERO;
    for l in 0..SD_GRID_L {
        let sum_x_l = reduce_fp5_split(&x_lo[l], &x_hi[l]);
        let sum_y_l = reduce_fp5_split(&y_lo[l], &y_hi[l]);
        let sum_z_l = reduce_fp5_split(&z_lo[l], &z_hi[l]);
        alpha_i[l] = u_pad[l].add(tables.eta[l].mul(sum_x_l));
        beta_i[l] = v_pad[l].mul(r_b).add(sum_y_l);
        z_weighted = z_weighted.add(tables.eta[l].mul(sum_z_l));
    }

    let mut mask_at_r = Fp5::ZERO;
    for d in 0..SD_GRID_B {
        mask_at_r = mask_at_r.add(poly_mask[d].mul(tables.r_powers[d]));
    }
    for idx in SD_GRID_B..SD_RPOLY_COEFFS {
        mask_at_r = mask_at_r.add(poly_mask[idx].mul(tables.r_powers[idx + 1]));
    }

    let sigma_i = c_share.add(z_weighted).mul(r_b).sub(mask_at_r);
    (alpha_i, beta_i, sigma_i)
}

/// Tape layout squeezed from `Shake256PartyBatch8` (after the 4-word `salt_1` prefix):
/// - `u_pad`: `SD_GRID_L * 5` (`905` limbs)
/// - `v_pad`: `SD_GRID_L * 5` (`905` limbs)
/// - `c_pad`: `5` limbs
/// - `poly_mask`: `SD_RPOLY_COEFFS * 5` (`1,810` limbs)
/// - `w_mask`: `num_secret_wires` limbs
/// - `z_mask`: `SD_TOTAL_GATES` (`32,708` limbs)
const PARTY_EXT_LIMBS: usize = (SD_GRID_L + SD_GRID_L + 1 + SD_RPOLY_COEFFS) * 5; // 3,625

fn unpack_party_ext_masks(
    tape: &[u64],
) -> (
    [Fp5; SD_GRID_L],
    [Fp5; SD_GRID_L],
    Fp5,
    [Fp5; SD_RPOLY_COEFFS],
) {
    let mut cur = 0usize;
    let mut u_pad = [Fp5::ZERO; SD_GRID_L];
    for slot in &mut u_pad {
        *slot = Fp5([
            tape[cur],
            tape[cur + 1],
            tape[cur + 2],
            tape[cur + 3],
            tape[cur + 4],
        ]);
        cur += 5;
    }
    let mut v_pad = [Fp5::ZERO; SD_GRID_L];
    for slot in &mut v_pad {
        *slot = Fp5([
            tape[cur],
            tape[cur + 1],
            tape[cur + 2],
            tape[cur + 3],
            tape[cur + 4],
        ]);
        cur += 5;
    }
    let c_pad = Fp5([
        tape[cur],
        tape[cur + 1],
        tape[cur + 2],
        tape[cur + 3],
        tape[cur + 4],
    ]);
    cur += 5;
    let mut poly_mask = [Fp5::ZERO; SD_RPOLY_COEFFS];
    for slot in &mut poly_mask {
        *slot = Fp5([
            tape[cur],
            tape[cur + 1],
            tape[cur + 2],
            tape[cur + 3],
            tape[cur + 4],
        ]);
        cur += 5;
    }
    debug_assert_eq!(cur, PARTY_EXT_LIMBS);
    (u_pad, v_pad, c_pad, poly_mask)
}

#[cfg(any(test, feature = "std"))]
fn parallel_map_indexed<T, F>(len: usize, f: F) -> Vec<T>
where
    T: Send,
    F: Fn(usize) -> T + Sync,
{
    if len <= 1 {
        return (0..len).map(f).collect();
    }
    let workers = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(1)
        .min(16)
        .min(len);
    if workers <= 1 {
        return (0..len).map(f).collect();
    }
    let chunk_size = len.div_ceil(workers);
    std::thread::scope(|s| {
        let f_ref = &f;
        let mut handles = Vec::with_capacity(workers);
        let mut start = 0usize;
        while start < len {
            let end = (start + chunk_size).min(len);
            handles.push(s.spawn(move || (start..end).map(f_ref).collect::<Vec<T>>()));
            start = end;
        }
        let mut out = Vec::with_capacity(len);
        for h in handles {
            out.extend(h.join().expect("selective-disclosure worker panicked"));
        }
        out
    })
}

#[cfg(not(any(test, feature = "std")))]
fn parallel_map_indexed<T, F>(len: usize, f: F) -> Vec<T>
where
    F: Fn(usize) -> T,
{
    (0..len).map(f).collect()
}

// ============================================================================
// Phase 3: Unlinkable Selective-Disclosure Presentation (`prove_selective_disclosure`)
// ============================================================================

/// Last-party (`party = 255`) additive offset bundle included iff `hidden_party != 255`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LimboPartyAux {
    pub delta_w: Vec<u64>,
    pub delta_z: Vec<u64>,
    pub delta_c: [u64; 5],
}

/// Opened `N = 256` seed-tree + polynomial-multiplication-check repetition (`~285 KiB`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OpenedLimboRepetition {
    pub hidden_party: u8,
    pub ggm_copath: [[u8; 32]; VC_SD_GGM_DEPTH],
    pub com_1_hidden: [u8; 32],
    pub aux: Option<LimboPartyAux>,
    pub r_poly_without_b: Vec<[u64; 5]>,
    pub alpha: Vec<[u64; 5]>,
    pub beta: Vec<[u64; 5]>,
}

/// Unlinkable selective-disclosure presentation (`0` `attr_commit`, `0` `leaf_idx`, `0` `issuance_token`).
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
    pub opened_reps: Vec<OpenedLimboRepetition>,
}

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

/// Generate an unlinkable selective-disclosure ZK presentation revealing only `disclosed_indices`.
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

/// Generate an unlinkable selective-disclosure presentation under an explicit soundness profile.
#[allow(clippy::too_many_arguments)]
pub fn prove_selective_disclosure_with_profile(
    cred: &BlindVerifiableCredential,
    holder_secret: &HolderCredentialSecret,
    membership: &CredentialMembershipWitness,
    disclosed_indices: &[usize],
    request: PresentationRequest<'_>,
    presentation_entropy: [u8; 32],
    profile: ZkSoundnessProfile,
) -> Result<SelectiveDisclosurePresentation, BlindVcError> {
    let PresentationRequest {
        verifier_scope,
        verifier_challenge,
        mode,
    } = request;
    let mut sorted_idx = disclosed_indices.to_vec();
    sorted_idx.sort_unstable();
    for (pos, &idx) in sorted_idx.iter().enumerate() {
        if idx >= holder_secret.arity {
            return Err(BlindVcError::InvalidDisclosedAttributeIndex { index: idx });
        }
        if pos > 0 && sorted_idx[pos - 1] == idx {
            return Err(BlindVcError::DuplicateDisclosedAttributeIndex { index: idx });
        }
    }

    if cred.issuer_epoch != membership.issuer_epoch || cred.schema_id != holder_secret.schema_id {
        return Err(BlindVcError::CredentialBindingMismatch);
    }
    let expected_attr_commit = compute_vc_poseidon2_commit(
        holder_secret.schema_id,
        &holder_secret.attrs[..holder_secret.arity],
        &holder_secret.holder_blind,
        VC_ATTR_COMMIT_TAG,
    )?;
    if cred.attr_commit != expected_attr_commit
        || membership.leaf_index != cred.accumulator_leaf_index
        || membership.leaf_index >= IssuerCredentialAccumulator::CAPACITY
    {
        return Err(BlindVcError::CredentialBindingMismatch);
    }
    if let Some(expected_tok) = &membership.issuance_token
        && !ct_eq_bytes(&cred.issuance_token, expected_tok)
    {
        return Err(BlindVcError::CredentialBindingMismatch);
    }

    let siblings = membership.siblings;
    let accumulator_root = membership.accumulator_root;
    if siblings
        .iter()
        .flatten()
        .chain(accumulator_root.iter())
        .any(|&v| !gl_is_canonical(v))
    {
        return Err(BlindVcError::CredentialBindingMismatch);
    }
    let mut node = cred.attr_commit;
    for (level, sibling) in siblings.iter().enumerate() {
        node = if (membership.leaf_index >> level) & 1 == 0 {
            merkle_hash_pair(&node, sibling, cred.issuer_epoch, level as u32)
        } else {
            merkle_hash_pair(sibling, &node, cred.issuer_epoch, level as u32)
        };
    }
    if node != accumulator_root {
        return Err(BlindVcError::CredentialBindingMismatch);
    }
    let issuer_root_tag = compute_accumulator_root_tag(
        &membership.issuer_pk_digest,
        cred.issuer_epoch,
        &accumulator_root,
    );

    // Burn before producing a proof, including failed attempts. Scope changes
    // must not let a verifier bypass the per-credential challenge history.
    let mut seen = holder_secret.seen_challenges.borrow_mut();
    if seen.contains(verifier_challenge) {
        return Err(BlindVcError::ReplayedVerifierChallenge);
    }
    seen.push(*verifier_challenge);
    drop(seen);

    let mut ent = presentation_entropy;
    let mut nonce_bind = Vec::with_capacity(64 + sorted_idx.len() * 12);
    nonce_bind.extend_from_slice(&cred.issuer_epoch.to_le_bytes());
    nonce_bind.extend_from_slice(&cred.schema_id.to_le_bytes());
    nonce_bind.extend_from_slice(&issuer_root_tag);
    match mode {
        PresentationMode::UnlinkableFresh => nonce_bind.push(0),
        PresentationMode::ScopedPseudonym(id) => {
            nonce_bind.push(1);
            nonce_bind.extend_from_slice(&id);
        }
    }
    nonce_bind.extend_from_slice(&(sorted_idx.len() as u32).to_le_bytes());
    for &idx in &sorted_idx {
        nonce_bind.extend_from_slice(&(idx as u32).to_le_bytes());
        nonce_bind.extend_from_slice(&holder_secret.attrs[idx].to_le_bytes());
    }
    let presentation_nonce = cshake256_framed_32(
        b"QSAG.VC.PRES_NONCE.V1",
        &[&ent, verifier_scope, verifier_challenge, &nonce_bind],
    );
    let verifier_scope_limbs = presentation_scope(
        verifier_scope,
        verifier_challenge,
        &presentation_nonce,
        mode,
    );
    let pres_blind_vec =
        sample_canonical_gl_vec(b"QSAG.VC.PRES_BLIND.V1", &ent, &presentation_nonce, 4);
    let mut pres_blind = [
        pres_blind_vec[0],
        pres_blind_vec[1],
        pres_blind_vec[2],
        pres_blind_vec[3],
    ];
    drop(pres_blind_vec);

    let pres_commit = match compute_vc_poseidon2_commit(
        cred.schema_id,
        &holder_secret.attrs[..holder_secret.arity],
        &pres_blind,
        VC_PRES_COMMIT_TAG,
    ) {
        Ok(commit) => commit,
        Err(err) => {
            ct_zeroize_u64s(&mut pres_blind);
            ct_zeroize_bytes(&mut ent);
            return Err(err);
        }
    };
    let scope_tag = compute_vc_scope_tag(
        cred.schema_id,
        &holder_secret.holder_blind,
        &verifier_scope_limbs,
    );

    let disclosed_attrs: Vec<(usize, u64)> = sorted_idx
        .iter()
        .map(|&idx| (idx, holder_secret.attrs[idx]))
        .collect();

    let mut secret_vals = ZeroizingU64Vec(Vec::with_capacity(
        MAX_VC_ATTRS + 8 + 7 * VC_ACCUMULATOR_DEPTH,
    ));
    for (attr_i, &attr_val) in holder_secret.attrs[..holder_secret.arity]
        .iter()
        .enumerate()
    {
        if !sorted_idx.contains(&attr_i) {
            secret_vals.0.push(attr_val);
        }
    }
    secret_vals.0.extend_from_slice(&holder_secret.holder_blind);
    secret_vals.0.extend_from_slice(&pres_blind);
    ct_zeroize_u64s(&mut pres_blind);
    for lvl in 0..VC_ACCUMULATOR_DEPTH {
        secret_vals
            .0
            .push(((cred.accumulator_leaf_index >> lvl) & 1) as u64);
    }
    for sib in &siblings {
        secret_vals.0.extend_from_slice(sib);
    }
    let num_secret_wires = secret_vals.len();

    let mut expected_final_outs = [0u64; VC_FINAL_OUTPUTS];
    expected_final_outs[0..6].copy_from_slice(&accumulator_root);
    expected_final_outs[6..12].copy_from_slice(&pres_commit);
    expected_final_outs[12..18].copy_from_slice(&scope_tag);

    let trace = eval_sd_plaintext_circuit(
        holder_secret.arity,
        cred.issuer_epoch,
        cred.schema_id,
        &verifier_scope_limbs,
        &disclosed_attrs,
        &expected_final_outs,
        &secret_vals,
    );
    if trace.final_outs != expected_final_outs {
        ct_zeroize_bytes(&mut ent);
        return Err(BlindVcError::CredentialBindingMismatch);
    }

    let profile_tag: &[u8] = match profile {
        ZkSoundnessProfile::Classical128 => b"QSAG.VC.SD.LIMBO256.Classical128:17",
        ZkSoundnessProfile::Quantum128 => b"QSAG.VC.SD.LIMBO256.Quantum128:33",
    };

    let mut inst_bytes = serialize_sd_instance(&SdInstance {
        arity: holder_secret.arity,
        presentation_nonce: &presentation_nonce,
        issuer_epoch: cred.issuer_epoch,
        schema_id: cred.schema_id,
        accumulator_root: &accumulator_root,
        issuer_root_tag: &issuer_root_tag,
        verifier_scope_limbs: &verifier_scope_limbs,
        disclosed_attrs: &disclosed_attrs,
        pres_commit: &pres_commit,
        scope_tag: &scope_tag,
    });
    inst_bytes.extend_from_slice(verifier_challenge);
    inst_bytes.extend_from_slice(profile_tag);

    let statement_digest = cshake256_framed_32(b"QSAG.VC.SD_STMT_DIGEST.V2", &[&inst_bytes]);
    let mut hedged_zk_seed =
        cshake256_framed_32(b"QSAG.VC.SD_ZK_SEED.V2", &[&statement_digest, &ent]);
    ct_zeroize_bytes(&mut ent);

    let mut tr = InterleavedTranscript::new(b"QSAG.BLIND_VC.SD_LIMBO.V1", &inst_bytes);
    tr.absorb(b"VC_SOUNDNESS_PROFILE", profile_tag);

    let tau = profile.sd_repetitions();
    let total_party_limbs = PARTY_EXT_LIMBS + num_secret_wires + SD_TOTAL_GATES;

    struct R1RepState {
        ggm_tree: ZeroizingGgmTree,
        com_1: [[u8; 32]; VC_SD_LIMBO_PARTIES],
        delta_w: ZeroizingU64Vec,
        delta_z: ZeroizingU64Vec,
        delta_c: Fp5,
        u_sum: [Fp5; SD_GRID_L],
        v_sum: [Fp5; SD_GRID_L],
        c_plain: Fp5,
        m_sum: [Fp5; SD_RPOLY_COEFFS],
    }

    // Round 1 (parallel across repetitions): expand GGM trees, stream 8-party SIMD tapes,
    // accumulate mask sums, compute Party 255 `aux`, and commit all 256 parties.
    let r1_reps: Vec<R1RepState> = parallel_map_indexed(tau, |rep| {
        let rep_u32 = rep as u32;
        let root_seed = cshake256_framed_32(
            b"QSAG.VC.SD_GGM_ROOT.V1",
            &[
                &statement_digest,
                &hedged_zk_seed,
                &presentation_nonce,
                &rep_u32.to_le_bytes(),
            ],
        );
        let ggm_tree = expand_ggm_tree_256(&root_seed, &presentation_nonce, rep_u32);

        let mut u_sum = [Fp5::ZERO; SD_GRID_L];
        let mut v_sum = [Fp5::ZERO; SD_GRID_L];
        let mut c_pad_sum = Fp5::ZERO;
        let mut m_sum = [Fp5::ZERO; SD_RPOLY_COEFFS];
        let mut w_mask_sum = ZeroizingU64Vec(vec![0u64; num_secret_wires]);
        let mut z_mask_sum = ZeroizingU64Vec(vec![0u64; SD_TOTAL_GATES]);
        let mut com_1 = [[0u8; 32]; VC_SD_LIMBO_PARTIES];
        let mut salt_255 = [0u8; 32];

        let mut batch_tapes: [Vec<u64>; 8] = core::array::from_fn(|_| Vec::new());
        for batch in 0..(VC_SD_LIMBO_PARTIES / 8) {
            let base_p = batch * 8;
            let seeds_8: [[u8; 32]; 8] =
                core::array::from_fn(|lane| ggm_tree.0[VC_SD_LIMBO_PARTIES + base_p + lane]);
            let mut prg =
                Shake256PartyBatch8::new(&presentation_nonce, rep_u32, base_p, &seeds_8);
            let salts = prg.extract_salts_1();
            prg.squeeze_canonical_gl([true; 8], &mut batch_tapes, total_party_limbs);

            for lane in 0..8 {
                let p = base_p + lane;
                let tape = &batch_tapes[lane];
                let (u_p, v_p, c_p, m_p) = unpack_party_ext_masks(&tape[..PARTY_EXT_LIMBS]);
                for l in 0..SD_GRID_L {
                    u_sum[l] = u_sum[l].add(u_p[l]);
                    v_sum[l] = v_sum[l].add(v_p[l]);
                }
                c_pad_sum = c_pad_sum.add(c_p);
                for d in 0..SD_RPOLY_COEFFS {
                    m_sum[d] = m_sum[d].add(m_p[d]);
                }
                let w_slice = &tape[PARTY_EXT_LIMBS..PARTY_EXT_LIMBS + num_secret_wires];
                for (acc, &wv) in w_mask_sum.0.iter_mut().zip(w_slice) {
                    *acc = gl_add(*acc, wv);
                }
                let z_slice = &tape[PARTY_EXT_LIMBS + num_secret_wires..];
                for (acc, &zv) in z_mask_sum.0.iter_mut().zip(z_slice) {
                    *acc = gl_add(*acc, zv);
                }
                if p < VC_SD_LIMBO_PARTIES - 1 {
                    com_1[p] = commit_limbo_party_r1(
                        &presentation_nonce,
                        rep_u32,
                        p as u16,
                        &seeds_8[lane],
                        None,
                        &salts[lane],
                    );
                } else {
                    salt_255 = salts[lane];
                }
                ct_zeroize_u64s(&mut batch_tapes[lane]);
            }
        }

        let mut delta_w = ZeroizingU64Vec(Vec::with_capacity(num_secret_wires));
        for k in 0..num_secret_wires {
            delta_w.0.push(gl_sub(secret_vals[k], w_mask_sum[k]));
        }
        let mut delta_z = ZeroizingU64Vec(Vec::with_capacity(SD_TOTAL_GATES));
        for g in 0..SD_TOTAL_GATES {
            delta_z.0.push(gl_sub(trace.z[g], z_mask_sum[g]));
        }
        let mut c_plain = Fp5::ZERO;
        for l in 0..SD_GRID_L {
            c_plain = c_plain.add(u_sum[l].mul(v_sum[l]));
        }
        let delta_c = c_plain.sub(c_pad_sum);

        let aux_digest = digest_limbo_aux(&delta_w, &delta_z, &delta_c.0);
        com_1[VC_SD_LIMBO_PARTIES - 1] = commit_limbo_party_r1(
            &presentation_nonce,
            rep_u32,
            (VC_SD_LIMBO_PARTIES - 1) as u16,
            &ggm_tree.0[VC_SD_LIMBO_PARTIES + VC_SD_LIMBO_PARTIES - 1],
            Some(&aux_digest),
            &salt_255,
        );
        ct_zeroize_bytes(&mut salt_255);

        R1RepState {
            ggm_tree,
            com_1,
            delta_w,
            delta_z,
            delta_c,
            u_sum,
            v_sum,
            c_plain,
            m_sum,
        }
    });

    ct_zeroize_bytes(&mut hedged_zk_seed);
    drop(secret_vals);

    let mut r1_bundle = Vec::with_capacity(tau * VC_SD_LIMBO_PARTIES * 32);
    for r1 in &r1_reps {
        for c in &r1.com_1 {
            r1_bundle.extend_from_slice(c);
        }
    }
    tr.absorb(b"VC_SD_LIMBO_R1_COMS", &r1_bundle);
    drop(r1_bundle);

    // Round 2a: squeeze folding challenge seed and compute masked polynomial R~(X) (degree <= 2B, coeff B == 0).
    let mut gamma_seed = [0u8; 32];
    tr.squeeze_bytes(b"VC_SD_LIMBO_GAMMA", &mut gamma_seed);

    let r2a_polys: Vec<([Fp5; SD_GRID_B], [Fp5; SD_GRID_L], Vec<[u64; 5]>)> =
        parallel_map_indexed(tau, |rep| {
            let r1 = &r1_reps[rep];
            let (theta, eta) = expand_gamma_weights(&gamma_seed, rep as u32);
            const MASK64: u128 = 0xffff_ffff_ffff_ffff;
            let mut poly_lo = [[0u128; 5]; 2 * SD_GRID_B + 1];
            let mut poly_hi = [[0u128; 5]; 2 * SD_GRID_B + 1];
            let mut poly_v = [Fp5::ZERO; 2 * SD_GRID_B + 1];

            for l in 0..SD_GRID_L {
                // P_l(X) = u_l + sum_{b=0}^{B-1} (theta_b * eta_l * x_{b,l}) * X^{b+1}
                // Q_l(X) = sum_{k=0}^{B-1} y_{B-1-k, l} * X^k + v_l * X^B
                let mut p_coeffs = [Fp5::ZERO; SD_GRID_B + 1];
                p_coeffs[0] = r1.u_sum[l];
                let eta_l = eta[l];
                for b in 0..SD_GRID_B {
                    let xv = trace.x[b * SD_GRID_L + l];
                    if xv != 0 {
                        p_coeffs[b + 1] = theta[b].mul(eta_l).scale_fp(xv);
                    }
                }
                let mut y_col = [0u128; SD_GRID_B];
                for k in 0..SD_GRID_B {
                    y_col[k] = trace.y[(SD_GRID_B - 1 - k) * SD_GRID_L + l] as u128;
                }
                let v_l = r1.v_sum[l];
                for j in 0..=SD_GRID_B {
                    let pj = p_coeffs[j];
                    if pj.is_zero() {
                        continue;
                    }
                    let pj_u128 = pj.0.map(|v| v as u128);
                    // Degrees k in 0..B have scalar GF(p) coefficients y_{B-1-k, l}
                    for k in 0..SD_GRID_B {
                        let yv = y_col[k];
                        if yv != 0 {
                            let dst = j + k;
                            for c in 0..5 {
                                let p = pj_u128[c] * yv;
                                poly_lo[dst][c] += p & MASK64;
                                poly_hi[dst][c] += p >> 64;
                            }
                        }
                    }
                    poly_v[j + SD_GRID_B] = poly_v[j + SD_GRID_B].add(pj.mul(v_l));
                }
            }
            let mut poly_full = [Fp5::ZERO; 2 * SD_GRID_B + 1];
            for d in 0..=(2 * SD_GRID_B) {
                poly_full[d] = reduce_fp5_split(&poly_lo[d], &poly_hi[d]).add(poly_v[d]);
            }

            // Verify degree-B coefficient equals `c_plain + sum_{b,l} theta_b * eta_l * z_{b,l}`:
            let mut z_comb = Fp5::ZERO;
            for l in 0..SD_GRID_L {
                let mut col_z = Fp5::ZERO;
                for b in 0..SD_GRID_B {
                    let zv = trace.z[b * SD_GRID_L + l];
                    if zv != 0 {
                        col_z = col_z.add(theta[b].scale_fp(zv));
                    }
                }
                z_comb = z_comb.add(eta[l].mul(col_z));
            }
            debug_assert_eq!(poly_full[SD_GRID_B], r1.c_plain.add(z_comb));

            let mut r_poly_without_b = Vec::with_capacity(SD_RPOLY_COEFFS);
            for d in 0..SD_GRID_B {
                r_poly_without_b.push(poly_full[d].add(r1.m_sum[d]).0);
            }
            for idx in SD_GRID_B..SD_RPOLY_COEFFS {
                let d = idx + 1;
                r_poly_without_b.push(poly_full[d].add(r1.m_sum[idx]).0);
            }
            (theta, eta, r_poly_without_b)
        });
    ct_zeroize_bytes(&mut gamma_seed);
    drop(trace);

    let mut rpoly_bundle = Vec::with_capacity(tau * SD_RPOLY_COEFFS * 40);
    for (_, _, r_poly) in &r2a_polys {
        for coeff in r_poly {
            for &limb in coeff {
                rpoly_bundle.extend_from_slice(&limb.to_le_bytes());
            }
        }
    }
    tr.absorb(b"VC_SD_LIMBO_RPOLY", &rpoly_bundle);
    drop(rpoly_bundle);

    // Round 2b: squeeze non-zero evaluation points r_rep in GF(p^5)* and evaluate all 256 parties' shares.
    let eval_points = squeeze_nonzero_eval_points(&mut tr, tau);
    let holder_arity = holder_secret.arity;
    let issuer_epoch = cred.issuer_epoch;
    let schema_id = cred.schema_id;

    struct R2bRepOut {
        alpha: Vec<[u64; 5]>,
        beta: Vec<[u64; 5]>,
        h_online: [[u8; 32]; VC_SD_LIMBO_PARTIES],
    }

    let r2b_outs: Vec<R2bRepOut> = parallel_map_indexed(tau, |rep| {
        let rep_u32 = rep as u32;
        let r1 = &r1_reps[rep];
        let (ref theta, ref eta, ref r_poly_without_b) = r2a_polys[rep];
        let tables = EvalTables::new(*theta, *eta, eval_points[rep]);

        let mut alpha_sum = [Fp5::ZERO; SD_GRID_L];
        let mut beta_sum = [Fp5::ZERO; SD_GRID_L];
        let mut sigma_sum = Fp5::ZERO;
        let mut h_online = [[0u8; 32]; VC_SD_LIMBO_PARTIES];

        let mut batch_tapes: [Vec<u64>; 8] = core::array::from_fn(|_| Vec::new());
        let mut x_grid = vec![0u64; SD_GRID_B * SD_GRID_L];
        let mut y_grid = vec![0u64; SD_GRID_B * SD_GRID_L];
        let mut z_grid = vec![0u64; SD_GRID_B * SD_GRID_L];
        let x_arr: &mut [u64; SD_GRID_B * SD_GRID_L] = x_grid.as_mut_slice().try_into().unwrap();
        let y_arr: &mut [u64; SD_GRID_B * SD_GRID_L] = y_grid.as_mut_slice().try_into().unwrap();
        let z_arr: &mut [u64; SD_GRID_B * SD_GRID_L] = z_grid.as_mut_slice().try_into().unwrap();
        let mut w_buf = ZeroizingU64Vec(vec![0u64; num_secret_wires]);
        let mut z_buf = ZeroizingU64Vec(vec![0u64; SD_TOTAL_GATES]);

        for batch in 0..(VC_SD_LIMBO_PARTIES / 8) {
            let base_p = batch * 8;
            let seeds_8: [[u8; 32]; 8] =
                core::array::from_fn(|lane| r1.ggm_tree.0[VC_SD_LIMBO_PARTIES + base_p + lane]);
            let mut prg =
                Shake256PartyBatch8::new(&presentation_nonce, rep_u32, base_p, &seeds_8);
            let _ = prg.extract_salts_1();
            prg.squeeze_canonical_gl([true; 8], &mut batch_tapes, total_party_limbs);

            for lane in 0..8 {
                let p = base_p + lane;
                let tape = &batch_tapes[lane];
                let (u_p, v_p, mut c_p, m_p) = unpack_party_ext_masks(&tape[..PARTY_EXT_LIMBS]);
                let w_raw = &tape[PARTY_EXT_LIMBS..PARTY_EXT_LIMBS + num_secret_wires];
                let z_raw = &tape[PARTY_EXT_LIMBS + num_secret_wires..];

                if p == VC_SD_LIMBO_PARTIES - 1 {
                    for k in 0..num_secret_wires {
                        w_buf.0[k] = gl_add(w_raw[k], r1.delta_w[k]);
                    }
                    for g in 0..SD_TOTAL_GATES {
                        z_buf.0[g] = gl_add(z_raw[g], r1.delta_z[g]);
                    }
                    c_p = c_p.add(r1.delta_c);
                    eval_sd_party_shares(
                        p,
                        holder_arity,
                        issuer_epoch,
                        schema_id,
                        &verifier_scope_limbs,
                        &disclosed_attrs,
                        &expected_final_outs,
                        &w_buf,
                        &z_buf,
                        x_arr,
                        y_arr,
                        z_arr,
                    );
                } else {
                    eval_sd_party_shares(
                        p,
                        holder_arity,
                        issuer_epoch,
                        schema_id,
                        &verifier_scope_limbs,
                        &disclosed_attrs,
                        &expected_final_outs,
                        w_raw,
                        z_raw,
                        x_arr,
                        y_arr,
                        z_arr,
                    );
                }

                let (alpha_i, beta_i, sigma_i) = eval_party_polynomial_shares(
                    &u_p, &v_p, c_p, &m_p, x_arr, y_arr, z_arr, &tables,
                );
                for l in 0..SD_GRID_L {
                    alpha_sum[l] = alpha_sum[l].add(alpha_i[l]);
                    beta_sum[l] = beta_sum[l].add(beta_i[l]);
                }
                sigma_sum = sigma_sum.add(sigma_i);
                h_online[p] = hash_limbo_party_online(
                    &presentation_nonce,
                    rep_u32,
                    p as u16,
                    &alpha_i,
                    &beta_i,
                    sigma_i,
                );
                ct_zeroize_u64s(&mut batch_tapes[lane]);
            }
        }
        ct_zeroize_u64s(&mut x_grid);
        ct_zeroize_u64s(&mut y_grid);
        ct_zeroize_u64s(&mut z_grid);

        #[cfg(debug_assertions)]
        {
            let mut prod_at_r = Fp5::ZERO;
            for l in 0..SD_GRID_L {
                prod_at_r = prod_at_r.add(alpha_sum[l].mul(beta_sum[l]));
            }
            let r_tilde_at_r = eval_r_poly_without_b(r_poly_without_b, &tables.r_powers);
            debug_assert_eq!(sigma_sum, prod_at_r.sub(r_tilde_at_r));
        }
        let _ = (r_poly_without_b, sigma_sum);

        R2bRepOut {
            alpha: alpha_sum.iter().map(|v| v.0).collect(),
            beta: beta_sum.iter().map(|v| v.0).collect(),
            h_online,
        }
    });

    let mut r2b_bundle =
        Vec::with_capacity(tau * (2 * SD_GRID_L * 40 + VC_SD_LIMBO_PARTIES * 32));
    for out in &r2b_outs {
        for v in out.alpha.iter().chain(out.beta.iter()) {
            for &limb in v {
                r2b_bundle.extend_from_slice(&limb.to_le_bytes());
            }
        }
        for h in &out.h_online {
            r2b_bundle.extend_from_slice(h);
        }
    }
    tr.absorb(b"VC_SD_LIMBO_R2_ONLINE", &r2b_bundle);
    drop(r2b_bundle);

    // Round 3: squeeze tau unbiased hidden-party indices in 0..=255.
    let mut hidden_parties = vec![0u8; tau];
    tr.squeeze_bytes(b"VC_SD_LIMBO_OPEN", &mut hidden_parties);

    let mut opened_reps = Vec::with_capacity(tau);
    for (((r1, (_, _, r_poly_without_b)), r2b), hidden_party) in r1_reps
        .into_iter()
        .zip(r2a_polys)
        .zip(r2b_outs)
        .zip(hidden_parties)
    {
        let ggm_copath = extract_ggm_copath(&r1.ggm_tree, hidden_party);
        let com_1_hidden = r1.com_1[hidden_party as usize];
        let aux = if (hidden_party as usize) == VC_SD_LIMBO_PARTIES - 1 {
            None
        } else {
            Some(LimboPartyAux {
                delta_w: r1.delta_w.0.clone(),
                delta_z: r1.delta_z.0.clone(),
                delta_c: r1.delta_c.0,
            })
        };
        opened_reps.push(OpenedLimboRepetition {
            hidden_party,
            ggm_copath,
            com_1_hidden,
            aux,
            r_poly_without_b,
            alpha: r2b.alpha,
            beta: r2b.beta,
        });
    }

    Ok(SelectiveDisclosurePresentation {
        arity: holder_secret.arity,
        verifier_challenge: *verifier_challenge,
        mode,
        presentation_nonce,
        issuer_epoch: cred.issuer_epoch,
        schema_id: cred.schema_id,
        accumulator_root,
        issuer_root_tag,
        verifier_scope_limbs,
        disclosed_attrs,
        pres_commit,
        scope_tag,
        opened_reps,
    })
}

/// Verify an unlinkable [`SelectiveDisclosurePresentation`] against an issuer-signed
/// [`IssuerRootAttestation`] (`trusted_root`), `expected_issuer_mldsa_pk`, `expected_oprf_pk`,
/// and `verifier_scope`.
#[allow(clippy::too_many_arguments)]
pub fn verify_presentation(
    pres: &SelectiveDisclosurePresentation,
    trusted_root: &IssuerRootAttestation,
    expected_issuer_mldsa_pk: &[u8],
    expected_oprf_pk: &PublicKey,
    verifier_scope: &[u8],
    verifier_challenge: &[u8; 32],
    mode: PresentationMode,
    expected_schema_id: u64,
    expected_arity: usize,
) -> bool {
    verify_presentation_with_profile(
        pres,
        trusted_root,
        expected_issuer_mldsa_pk,
        expected_oprf_pk,
        verifier_scope,
        verifier_challenge,
        mode,
        expected_schema_id,
        expected_arity,
        ZkSoundnessProfile::Quantum128,
    )
}

/// Verify a [`SelectiveDisclosurePresentation`] under an explicit soundness profile.
#[allow(clippy::too_many_arguments)]
pub fn verify_presentation_with_profile(
    pres: &SelectiveDisclosurePresentation,
    trusted_root: &IssuerRootAttestation,
    expected_issuer_mldsa_pk: &[u8],
    expected_oprf_pk: &PublicKey,
    verifier_scope: &[u8],
    verifier_challenge: &[u8; 32],
    mode: PresentationMode,
    expected_schema_id: u64,
    expected_arity: usize,
    profile: ZkSoundnessProfile,
) -> bool {
    if !trusted_root.verify(expected_issuer_mldsa_pk, expected_oprf_pk) {
        return false;
    }
    if !(1..=MAX_VC_ATTRS).contains(&expected_arity)
        || pres.arity != expected_arity
        || pres.schema_id != expected_schema_id
        || pres.verifier_challenge != *verifier_challenge
        || pres.mode != mode
        || pres.issuer_epoch != trusted_root.issuer_epoch
        || pres.accumulator_root != trusted_root.accumulator_root
        || !ct_eq_bytes(&pres.issuer_root_tag, &trusted_root.root_tag)
    {
        return false;
    }
    let expected_scope_limbs = presentation_scope(
        verifier_scope,
        verifier_challenge,
        &pres.presentation_nonce,
        mode,
    );
    if pres.verifier_scope_limbs != expected_scope_limbs {
        return false;
    }
    let tau = profile.sd_repetitions();
    if pres.opened_reps.len() != tau || pres.disclosed_attrs.len() > expected_arity {
        return false;
    }
    for (pos, &(idx, val)) in pres.disclosed_attrs.iter().enumerate() {
        if idx >= expected_arity || !gl_is_canonical(val) {
            return false;
        }
        if pos > 0 && pres.disclosed_attrs[pos - 1].0 >= idx {
            return false;
        }
    }
    for &x in pres.pres_commit.iter().chain(pres.scope_tag.iter()) {
        if !gl_is_canonical(x) {
            return false;
        }
    }

    let expected_num_secret_wires = (expected_arity - pres.disclosed_attrs.len())
        + 4
        + 4
        + VC_ACCUMULATOR_DEPTH
        + 6 * VC_ACCUMULATOR_DEPTH;

    // Validate repetition structural shapes and canonical Goldilocks limbs up front.
    for o in &pres.opened_reps {
        let is_last_hidden = (o.hidden_party as usize) == VC_SD_LIMBO_PARTIES - 1;
        match (&o.aux, is_last_hidden) {
            (None, true) => {}
            (Some(aux), false) => {
                if aux.delta_w.len() != expected_num_secret_wires
                    || aux.delta_z.len() != SD_TOTAL_GATES
                    || !Fp5(aux.delta_c).is_canonical()
                    || aux.delta_w.iter().any(|&v| !gl_is_canonical(v))
                    || aux.delta_z.iter().any(|&v| !gl_is_canonical(v))
                {
                    return false;
                }
            }
            _ => return false,
        }
        if o.r_poly_without_b.len() != SD_RPOLY_COEFFS
            || o.alpha.len() != SD_GRID_L
            || o.beta.len() != SD_GRID_L
        {
            return false;
        }
        for arr in o
            .r_poly_without_b
            .iter()
            .chain(o.alpha.iter())
            .chain(o.beta.iter())
        {
            if !Fp5(*arr).is_canonical() {
                return false;
            }
        }
    }

    let profile_tag: &[u8] = match profile {
        ZkSoundnessProfile::Classical128 => b"QSAG.VC.SD.LIMBO256.Classical128:17",
        ZkSoundnessProfile::Quantum128 => b"QSAG.VC.SD.LIMBO256.Quantum128:33",
    };

    let mut inst_bytes = serialize_sd_instance(&SdInstance {
        arity: expected_arity,
        presentation_nonce: &pres.presentation_nonce,
        issuer_epoch: pres.issuer_epoch,
        schema_id: pres.schema_id,
        accumulator_root: &pres.accumulator_root,
        issuer_root_tag: &pres.issuer_root_tag,
        verifier_scope_limbs: &pres.verifier_scope_limbs,
        disclosed_attrs: &pres.disclosed_attrs,
        pres_commit: &pres.pres_commit,
        scope_tag: &pres.scope_tag,
    });
    inst_bytes.extend_from_slice(verifier_challenge);
    inst_bytes.extend_from_slice(profile_tag);

    let mut tr = InterleavedTranscript::new(b"QSAG.BLIND_VC.SD_LIMBO.V1", &inst_bytes);
    tr.absorb(b"VC_SOUNDNESS_PROFILE", profile_tag);

    // Step V1 (parallel): reconstruct 255 GGM leaf seeds and Round-1 party commitments
    // (requiring only the first Keccak block per party to extract `salt_1[i]`).
    let v_r1: Vec<([[u8; 32]; VC_SD_LIMBO_PARTIES], [[u8; 32]; VC_SD_LIMBO_PARTIES])> =
        parallel_map_indexed(tau, |rep| {
            let rep_u32 = rep as u32;
            let o = &pres.opened_reps[rep];
            let hidden = o.hidden_party as usize;
            let leaves = reconstruct_ggm_leaves_256(
                &o.ggm_copath,
                o.hidden_party,
                &pres.presentation_nonce,
                rep_u32,
            );
            let aux_digest = o
                .aux
                .as_ref()
                .map(|a| digest_limbo_aux(&a.delta_w, &a.delta_z, &a.delta_c));

            let mut com_1 = [[0u8; 32]; VC_SD_LIMBO_PARTIES];
            com_1[hidden] = o.com_1_hidden;
            for batch in 0..(VC_SD_LIMBO_PARTIES / 8) {
                let base_p = batch * 8;
                let seeds_8: [[u8; 32]; 8] = core::array::from_fn(|lane| leaves[base_p + lane]);
                let mut prg = Shake256PartyBatch8::new(
                    &pres.presentation_nonce,
                    rep_u32,
                    base_p,
                    &seeds_8,
                );
                let salts = prg.extract_salts_1();
                for lane in 0..8 {
                    let p = base_p + lane;
                    if p == hidden {
                        continue;
                    }
                    let ad = if p == VC_SD_LIMBO_PARTIES - 1 {
                        aux_digest.as_ref()
                    } else {
                        None
                    };
                    com_1[p] = commit_limbo_party_r1(
                        &pres.presentation_nonce,
                        rep_u32,
                        p as u16,
                        &seeds_8[lane],
                        ad,
                        &salts[lane],
                    );
                }
            }
            (leaves, com_1)
        });

    let mut r1_bundle = Vec::with_capacity(tau * VC_SD_LIMBO_PARTIES * 32);
    for (_, com_1) in &v_r1 {
        for c in com_1 {
            r1_bundle.extend_from_slice(c);
        }
    }
    tr.absorb(b"VC_SD_LIMBO_R1_COMS", &r1_bundle);
    drop(r1_bundle);

    let mut gamma_seed = [0u8; 32];
    tr.squeeze_bytes(b"VC_SD_LIMBO_GAMMA", &mut gamma_seed);

    let mut rpoly_bundle = Vec::with_capacity(tau * SD_RPOLY_COEFFS * 40);
    for o in &pres.opened_reps {
        for coeff in &o.r_poly_without_b {
            for &limb in coeff {
                rpoly_bundle.extend_from_slice(&limb.to_le_bytes());
            }
        }
    }
    tr.absorb(b"VC_SD_LIMBO_RPOLY", &rpoly_bundle);
    drop(rpoly_bundle);

    let eval_points = squeeze_nonzero_eval_points(&mut tr, tau);

    let mut expected_final_outs = [0u64; VC_FINAL_OUTPUTS];
    expected_final_outs[0..6].copy_from_slice(&pres.accumulator_root);
    expected_final_outs[6..12].copy_from_slice(&pres.pres_commit);
    expected_final_outs[12..18].copy_from_slice(&pres.scope_tag);

    let total_party_limbs = PARTY_EXT_LIMBS + expected_num_secret_wires + SD_TOTAL_GATES;

    // Step V2 (single streaming pass per repetition, parallel across 16 cores):
    // evaluate all 255 opened parties and reconstruct the hidden party's online broadcast hash.
    let v_h_online: Vec<[[u8; 32]; VC_SD_LIMBO_PARTIES]> = parallel_map_indexed(tau, |rep| {
        let rep_u32 = rep as u32;
        let o = &pres.opened_reps[rep];
        let hidden = o.hidden_party as usize;
        let (ref leaves, _) = v_r1[rep];
        let (theta, eta) = expand_gamma_weights(&gamma_seed, rep_u32);
        let tables = EvalTables::new(theta, eta, eval_points[rep]);

        let mut open_alpha_sum = [Fp5::ZERO; SD_GRID_L];
        let mut open_beta_sum = [Fp5::ZERO; SD_GRID_L];
        let mut open_sigma_sum = Fp5::ZERO;
        let mut h_online = [[0u8; 32]; VC_SD_LIMBO_PARTIES];

        let mut batch_tapes: [Vec<u64>; 8] = core::array::from_fn(|_| Vec::new());
        let mut x_grid = vec![0u64; SD_GRID_B * SD_GRID_L];
        let mut y_grid = vec![0u64; SD_GRID_B * SD_GRID_L];
        let mut z_grid = vec![0u64; SD_GRID_B * SD_GRID_L];
        let x_arr: &mut [u64; SD_GRID_B * SD_GRID_L] = x_grid.as_mut_slice().try_into().unwrap();
        let y_arr: &mut [u64; SD_GRID_B * SD_GRID_L] = y_grid.as_mut_slice().try_into().unwrap();
        let z_arr: &mut [u64; SD_GRID_B * SD_GRID_L] = z_grid.as_mut_slice().try_into().unwrap();
        let mut w_buf = ZeroizingU64Vec(vec![0u64; expected_num_secret_wires]);
        let mut z_buf = ZeroizingU64Vec(vec![0u64; SD_TOTAL_GATES]);

        for batch in 0..(VC_SD_LIMBO_PARTIES / 8) {
            let base_p = batch * 8;
            let seeds_8: [[u8; 32]; 8] = core::array::from_fn(|lane| leaves[base_p + lane]);
            let active_mask: [bool; 8] = core::array::from_fn(|lane| base_p + lane != hidden);
            let mut prg =
                Shake256PartyBatch8::new(&pres.presentation_nonce, rep_u32, base_p, &seeds_8);
            let _ = prg.extract_salts_1();
            prg.squeeze_canonical_gl(active_mask, &mut batch_tapes, total_party_limbs);

            for lane in 0..8 {
                let p = base_p + lane;
                if p == hidden {
                    continue;
                }
                let tape = &batch_tapes[lane];
                let (u_p, v_p, mut c_p, m_p) = unpack_party_ext_masks(&tape[..PARTY_EXT_LIMBS]);
                let w_raw = &tape[PARTY_EXT_LIMBS..PARTY_EXT_LIMBS + expected_num_secret_wires];
                let z_raw = &tape[PARTY_EXT_LIMBS + expected_num_secret_wires..];

                if p == VC_SD_LIMBO_PARTIES - 1 {
                    let aux = o.aux.as_ref().expect("validated aux for opened party 255");
                    for k in 0..expected_num_secret_wires {
                        w_buf.0[k] = gl_add(w_raw[k], aux.delta_w[k]);
                    }
                    for g in 0..SD_TOTAL_GATES {
                        z_buf.0[g] = gl_add(z_raw[g], aux.delta_z[g]);
                    }
                    c_p = c_p.add(Fp5(aux.delta_c));
                    eval_sd_party_shares(
                        p,
                        expected_arity,
                        pres.issuer_epoch,
                        pres.schema_id,
                        &pres.verifier_scope_limbs,
                        &pres.disclosed_attrs,
                        &expected_final_outs,
                        &w_buf,
                        &z_buf,
                        x_arr,
                        y_arr,
                        z_arr,
                    );
                } else {
                    eval_sd_party_shares(
                        p,
                        expected_arity,
                        pres.issuer_epoch,
                        pres.schema_id,
                        &pres.verifier_scope_limbs,
                        &pres.disclosed_attrs,
                        &expected_final_outs,
                        w_raw,
                        z_raw,
                        x_arr,
                        y_arr,
                        z_arr,
                    );
                }

                let (alpha_i, beta_i, sigma_i) = eval_party_polynomial_shares(
                    &u_p, &v_p, c_p, &m_p, x_arr, y_arr, z_arr, &tables,
                );
                for l in 0..SD_GRID_L {
                    open_alpha_sum[l] = open_alpha_sum[l].add(alpha_i[l]);
                    open_beta_sum[l] = open_beta_sum[l].add(beta_i[l]);
                }
                open_sigma_sum = open_sigma_sum.add(sigma_i);
                h_online[p] = hash_limbo_party_online(
                    &pres.presentation_nonce,
                    rep_u32,
                    p as u16,
                    &alpha_i,
                    &beta_i,
                    sigma_i,
                );
                ct_zeroize_u64s(&mut batch_tapes[lane]);
            }
        }

        let mut alpha_hidden = [Fp5::ZERO; SD_GRID_L];
        let mut beta_hidden = [Fp5::ZERO; SD_GRID_L];
        let mut prod_at_r = Fp5::ZERO;
        for l in 0..SD_GRID_L {
            let a_l = Fp5(o.alpha[l]);
            let b_l = Fp5(o.beta[l]);
            alpha_hidden[l] = a_l.sub(open_alpha_sum[l]);
            beta_hidden[l] = b_l.sub(open_beta_sum[l]);
            prod_at_r = prod_at_r.add(a_l.mul(b_l));
        }
        let r_tilde_at_r = eval_r_poly_without_b(&o.r_poly_without_b, &tables.r_powers);
        let sigma_total = prod_at_r.sub(r_tilde_at_r);
        let sigma_hidden = sigma_total.sub(open_sigma_sum);

        h_online[hidden] = hash_limbo_party_online(
            &pres.presentation_nonce,
            rep_u32,
            hidden as u16,
            &alpha_hidden,
            &beta_hidden,
            sigma_hidden,
        );
        h_online
    });
    ct_zeroize_bytes(&mut gamma_seed);

    let mut r2b_bundle =
        Vec::with_capacity(tau * (2 * SD_GRID_L * 40 + VC_SD_LIMBO_PARTIES * 32));
    for (o, h_online) in pres.opened_reps.iter().zip(&v_h_online) {
        for v in o.alpha.iter().chain(o.beta.iter()) {
            for &limb in v {
                r2b_bundle.extend_from_slice(&limb.to_le_bytes());
            }
        }
        for h in h_online {
            r2b_bundle.extend_from_slice(h);
        }
    }
    tr.absorb(b"VC_SD_LIMBO_R2_ONLINE", &r2b_bundle);
    drop(r2b_bundle);

    let mut expected_hidden = vec![0u8; tau];
    tr.squeeze_bytes(b"VC_SD_LIMBO_OPEN", &mut expected_hidden);
    let actual_hidden: Vec<u8> = pres.opened_reps.iter().map(|o| o.hidden_party).collect();
    ct_eq_bytes(&actual_hidden, &expected_hidden)
}

// ============================================================================
// Canonical Sub-15 MiB Wire Serialization (`to_compact_wire_bytes` / `from_compact_wire_bytes`)
// ============================================================================

const SD_COMPACT_WIRE_MAGIC: &[u8; 24] = b"QSAG.BVC.SD.LIMBO256.V1\0";

impl SelectiveDisclosurePresentation {
    /// Serialize this [`SelectiveDisclosurePresentation`] to its canonical wire format
    /// (`~9.20 MiB` at [`ZkSoundnessProfile::Quantum128`], `~4.74 MiB` at
    /// [`ZkSoundnessProfile::Classical128`]).
    pub fn to_compact_wire_bytes(&self) -> Result<Vec<u8>, BlindVcError> {
        if !(1..=MAX_VC_ATTRS).contains(&self.arity)
            || self.disclosed_attrs.len() > self.arity
            || (self.opened_reps.len() != ZkSoundnessProfile::Classical128.sd_repetitions()
                && self.opened_reps.len() != ZkSoundnessProfile::Quantum128.sd_repetitions())
        {
            return Err(BlindVcError::SelectiveDisclosureProofInvalid);
        }
        for (pos, &(idx, val)) in self.disclosed_attrs.iter().enumerate() {
            if idx >= self.arity || !gl_is_canonical(val) {
                return Err(BlindVcError::SelectiveDisclosureProofInvalid);
            }
            if pos > 0 && self.disclosed_attrs[pos - 1].0 >= idx {
                return Err(BlindVcError::SelectiveDisclosureProofInvalid);
            }
        }
        if self
            .accumulator_root
            .iter()
            .chain(self.verifier_scope_limbs.iter())
            .chain(self.pres_commit.iter())
            .chain(self.scope_tag.iter())
            .any(|&v| !gl_is_canonical(v))
        {
            return Err(BlindVcError::SelectiveDisclosureProofInvalid);
        }

        let num_secret_wires = (self.arity - self.disclosed_attrs.len())
            + 4
            + 4
            + VC_ACCUMULATOR_DEPTH
            + 6 * VC_ACCUMULATOR_DEPTH;
        let base_rep_bytes = 1
            + VC_SD_GGM_DEPTH * 32
            + 32
            + (SD_RPOLY_COEFFS + 2 * SD_GRID_L) * 40;
        let aux_bytes = (num_secret_wires + SD_TOTAL_GATES + 5) * 8;
        let mode_extra = match self.mode {
            PresentationMode::UnlinkableFresh => 1,
            PresentationMode::ScopedPseudonym(_) => 33,
        };
        let header_bytes = 24
            + 8
            + 32
            + mode_extra
            + 32
            + 8
            + 8
            + 48
            + 32
            + 32
            + 4
            + self.disclosed_attrs.len() * 12
            + 48
            + 48
            + 4;

        let mut total_bytes = header_bytes;
        for o in &self.opened_reps {
            let is_last_hidden = (o.hidden_party as usize) == VC_SD_LIMBO_PARTIES - 1;
            if o.r_poly_without_b.len() != SD_RPOLY_COEFFS
                || o.alpha.len() != SD_GRID_L
                || o.beta.len() != SD_GRID_L
            {
                return Err(BlindVcError::SelectiveDisclosureProofInvalid);
            }
            match (&o.aux, is_last_hidden) {
                (None, true) => total_bytes += base_rep_bytes,
                (Some(aux), false) => {
                    if aux.delta_w.len() != num_secret_wires
                        || aux.delta_z.len() != SD_TOTAL_GATES
                        || !Fp5(aux.delta_c).is_canonical()
                        || aux.delta_w.iter().any(|&v| !gl_is_canonical(v))
                        || aux.delta_z.iter().any(|&v| !gl_is_canonical(v))
                    {
                        return Err(BlindVcError::SelectiveDisclosureProofInvalid);
                    }
                    total_bytes += base_rep_bytes + aux_bytes;
                }
                _ => return Err(BlindVcError::SelectiveDisclosureProofInvalid),
            }
            for arr in o
                .r_poly_without_b
                .iter()
                .chain(o.alpha.iter())
                .chain(o.beta.iter())
            {
                if !Fp5(*arr).is_canonical() {
                    return Err(BlindVcError::SelectiveDisclosureProofInvalid);
                }
            }
        }

        let mut out = Vec::with_capacity(total_bytes);
        out.extend_from_slice(SD_COMPACT_WIRE_MAGIC);
        out.extend_from_slice(&(self.arity as u64).to_le_bytes());
        out.extend_from_slice(&self.verifier_challenge);
        match self.mode {
            PresentationMode::UnlinkableFresh => out.push(0),
            PresentationMode::ScopedPseudonym(id) => {
                out.push(1);
                out.extend_from_slice(&id);
            }
        }
        out.extend_from_slice(&self.presentation_nonce);
        out.extend_from_slice(&self.issuer_epoch.to_le_bytes());
        out.extend_from_slice(&self.schema_id.to_le_bytes());
        for &v in &self.accumulator_root {
            out.extend_from_slice(&v.to_le_bytes());
        }
        out.extend_from_slice(&self.issuer_root_tag);
        for &v in &self.verifier_scope_limbs {
            out.extend_from_slice(&v.to_le_bytes());
        }
        out.extend_from_slice(&(self.disclosed_attrs.len() as u32).to_le_bytes());
        for &(idx, val) in &self.disclosed_attrs {
            out.extend_from_slice(&(idx as u32).to_le_bytes());
            out.extend_from_slice(&val.to_le_bytes());
        }
        for &v in self.pres_commit.iter().chain(self.scope_tag.iter()) {
            out.extend_from_slice(&v.to_le_bytes());
        }
        out.extend_from_slice(&(self.opened_reps.len() as u32).to_le_bytes());

        for o in &self.opened_reps {
            out.push(o.hidden_party);
            for node in &o.ggm_copath {
                out.extend_from_slice(node);
            }
            out.extend_from_slice(&o.com_1_hidden);
            if let Some(aux) = &o.aux {
                for &v in aux
                    .delta_w
                    .iter()
                    .chain(aux.delta_z.iter())
                    .chain(aux.delta_c.iter())
                {
                    out.extend_from_slice(&v.to_le_bytes());
                }
            }
            for arr in o
                .r_poly_without_b
                .iter()
                .chain(o.alpha.iter())
                .chain(o.beta.iter())
            {
                for &limb in arr {
                    out.extend_from_slice(&limb.to_le_bytes());
                }
            }
        }
        debug_assert_eq!(out.len(), total_bytes);
        Ok(out)
    }

    /// Alias for [`Self::to_compact_wire_bytes`].
    pub fn to_wire_bytes(&self) -> Result<Vec<u8>, BlindVcError> {
        self.to_compact_wire_bytes()
    }

    /// Deserialize a [`SelectiveDisclosurePresentation`] from [`Self::to_compact_wire_bytes`],
    /// validating magic, bounds, canonical Goldilocks field limbs, and exact payload length
    /// before allocating per-repetition buffers.
    pub fn from_compact_wire_bytes(bytes: &[u8]) -> Result<Self, BlindVcError> {
        fn take<'a>(cur: &mut &'a [u8], n: usize) -> Result<&'a [u8], BlindVcError> {
            if cur.len() < n {
                return Err(BlindVcError::SelectiveDisclosureProofInvalid);
            }
            let (head, tail) = cur.split_at(n);
            *cur = tail;
            Ok(head)
        }
        fn take_32(cur: &mut &[u8]) -> Result<[u8; 32], BlindVcError> {
            let s = take(cur, 32)?;
            let mut out = [0u8; 32];
            out.copy_from_slice(s);
            Ok(out)
        }
        fn take_u32(cur: &mut &[u8]) -> Result<u32, BlindVcError> {
            let s = take(cur, 4)?;
            Ok(u32::from_le_bytes([s[0], s[1], s[2], s[3]]))
        }
        fn take_u64(cur: &mut &[u8]) -> Result<u64, BlindVcError> {
            let s = take(cur, 8)?;
            let mut b = [0u8; 8];
            b.copy_from_slice(s);
            Ok(u64::from_le_bytes(b))
        }
        fn take_gl(cur: &mut &[u8]) -> Result<u64, BlindVcError> {
            let v = take_u64(cur)?;
            if !gl_is_canonical(v) {
                return Err(BlindVcError::SelectiveDisclosureProofInvalid);
            }
            Ok(v)
        }
        fn take_fp5(cur: &mut &[u8]) -> Result<[u64; 5], BlindVcError> {
            Ok([
                take_gl(cur)?,
                take_gl(cur)?,
                take_gl(cur)?,
                take_gl(cur)?,
                take_gl(cur)?,
            ])
        }

        let mut cur = bytes;
        let magic = take(&mut cur, 24)?;
        if !ct_eq_bytes(magic, SD_COMPACT_WIRE_MAGIC) {
            return Err(BlindVcError::SelectiveDisclosureProofInvalid);
        }
        let arity_u64 = take_u64(&mut cur)?;
        if !(1..=MAX_VC_ATTRS as u64).contains(&arity_u64) {
            return Err(BlindVcError::SelectiveDisclosureProofInvalid);
        }
        let arity = arity_u64 as usize;
        let verifier_challenge = take_32(&mut cur)?;
        let mode_tag = take(&mut cur, 1)?[0];
        let mode = match mode_tag {
            0 => PresentationMode::UnlinkableFresh,
            1 => PresentationMode::ScopedPseudonym(take_32(&mut cur)?),
            _ => return Err(BlindVcError::SelectiveDisclosureProofInvalid),
        };
        let presentation_nonce = take_32(&mut cur)?;
        let issuer_epoch = take_u64(&mut cur)?;
        let schema_id = take_u64(&mut cur)?;
        let mut accumulator_root = [0u64; 6];
        for slot in &mut accumulator_root {
            *slot = take_gl(&mut cur)?;
        }
        let issuer_root_tag = take_32(&mut cur)?;
        let mut verifier_scope_limbs = [0u64; 4];
        for slot in &mut verifier_scope_limbs {
            *slot = take_gl(&mut cur)?;
        }
        let disclosed_count = take_u32(&mut cur)? as usize;
        if disclosed_count > arity {
            return Err(BlindVcError::SelectiveDisclosureProofInvalid);
        }
        let mut disclosed_attrs = Vec::with_capacity(disclosed_count);
        let mut prev_idx: Option<usize> = None;
        for _ in 0..disclosed_count {
            let idx = take_u32(&mut cur)? as usize;
            let val = take_gl(&mut cur)?;
            if idx >= arity || prev_idx.is_some_and(|p| idx <= p) {
                return Err(BlindVcError::SelectiveDisclosureProofInvalid);
            }
            prev_idx = Some(idx);
            disclosed_attrs.push((idx, val));
        }
        let mut pres_commit = [0u64; 6];
        for slot in &mut pres_commit {
            *slot = take_gl(&mut cur)?;
        }
        let mut scope_tag = [0u64; 6];
        for slot in &mut scope_tag {
            *slot = take_gl(&mut cur)?;
        }
        let num_reps = take_u32(&mut cur)? as usize;
        if num_reps != ZkSoundnessProfile::Classical128.sd_repetitions()
            && num_reps != ZkSoundnessProfile::Quantum128.sd_repetitions()
        {
            return Err(BlindVcError::SelectiveDisclosureProofInvalid);
        }

        let num_secret_wires = (arity - disclosed_count)
            + 4
            + 4
            + VC_ACCUMULATOR_DEPTH
            + 6 * VC_ACCUMULATOR_DEPTH;
        let base_rep_tail = VC_SD_GGM_DEPTH * 32 + 32 + (SD_RPOLY_COEFFS + 2 * SD_GRID_L) * 40;
        let aux_bytes = (num_secret_wires + SD_TOTAL_GATES + 5) * 8;

        let mut opened_reps = Vec::with_capacity(num_reps);
        for _ in 0..num_reps {
            let hidden_party = take(&mut cur, 1)?[0];
            let is_last_hidden = (hidden_party as usize) == VC_SD_LIMBO_PARTIES - 1;
            let needed = base_rep_tail + if is_last_hidden { 0 } else { aux_bytes };
            if cur.len() < needed {
                return Err(BlindVcError::SelectiveDisclosureProofInvalid);
            }
            let mut ggm_copath = [[0u8; 32]; VC_SD_GGM_DEPTH];
            for node in &mut ggm_copath {
                *node = take_32(&mut cur)?;
            }
            let com_1_hidden = take_32(&mut cur)?;
            let aux = if is_last_hidden {
                None
            } else {
                let mut delta_w = Vec::with_capacity(num_secret_wires);
                for _ in 0..num_secret_wires {
                    delta_w.push(take_gl(&mut cur)?);
                }
                let mut delta_z = Vec::with_capacity(SD_TOTAL_GATES);
                for _ in 0..SD_TOTAL_GATES {
                    delta_z.push(take_gl(&mut cur)?);
                }
                let delta_c = take_fp5(&mut cur)?;
                Some(LimboPartyAux {
                    delta_w,
                    delta_z,
                    delta_c,
                })
            };
            let mut r_poly_without_b = Vec::with_capacity(SD_RPOLY_COEFFS);
            for _ in 0..SD_RPOLY_COEFFS {
                r_poly_without_b.push(take_fp5(&mut cur)?);
            }
            let mut alpha = Vec::with_capacity(SD_GRID_L);
            for _ in 0..SD_GRID_L {
                alpha.push(take_fp5(&mut cur)?);
            }
            let mut beta = Vec::with_capacity(SD_GRID_L);
            for _ in 0..SD_GRID_L {
                beta.push(take_fp5(&mut cur)?);
            }
            opened_reps.push(OpenedLimboRepetition {
                hidden_party,
                ggm_copath,
                com_1_hidden,
                aux,
                r_poly_without_b,
                alpha,
                beta,
            });
        }
        if !cur.is_empty() {
            return Err(BlindVcError::SelectiveDisclosureProofInvalid);
        }
        Ok(Self {
            arity,
            verifier_challenge,
            mode,
            presentation_nonce,
            issuer_epoch,
            schema_id,
            accumulator_root,
            issuer_root_tag,
            verifier_scope_limbs,
            disclosed_attrs,
            pres_commit,
            scope_tag,
            opened_reps,
        })
    }

    /// Alias for [`Self::from_compact_wire_bytes`].
    pub fn from_wire_bytes(bytes: &[u8]) -> Result<Self, BlindVcError> {
        Self::from_compact_wire_bytes(bytes)
    }
}

impl core::fmt::Display for BlindVcError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{self:?}")
    }
}
impl core::error::Error for BlindVcError {}

#[cfg(test)]
mod tests {
    use super::*;

    fn gl_pow(mut base: u64, mut exp: u64) -> u64 {
        let mut acc = 1u64;
        while exp > 0 {
            if exp & 1 == 1 {
                acc = gl_mul(acc, base);
            }
            base = gl_mul(base, base);
            exp >>= 1;
        }
        acc
    }

    fn fp5_pow_u64(mut base: Fp5, mut exp: u64) -> Fp5 {
        let mut acc = Fp5::ONE;
        while exp > 0 {
            if exp & 1 == 1 {
                acc = acc.mul(base);
            }
            base = base.mul(base);
            exp >>= 1;
        }
        acc
    }

    #[test]
    fn fp5_irreducibility_and_field_axioms() {
        // Serret's criterion: 5 | (p - 1) and 3^((p - 1) / 5) != 1 (mod p).
        assert_eq!((GOLDILOCKS_PRIME - 1) % 5, 0);
        let z5 = gl_pow(3, (GOLDILOCKS_PRIME - 1) / 5);
        assert_ne!(z5, 1);
        assert_eq!(gl_pow(z5, 5), 1);

        // T^5 == 3 in GF(p)[T]/(T^5 - 3).
        let t = Fp5([0, 1, 0, 0, 0]);
        assert_eq!(fp5_pow_u64(t, 5), Fp5([3, 0, 0, 0, 0]));

        // Frobenius endomorphism: a^(p^5) == a for non-trivial element a.
        let a = Fp5([
            0x1234_5678_9ABC_DEF0,
            GOLDILOCKS_PRIME - 17,
            42,
            0xDEAD_BEEF_CAFE_BABE % GOLDILOCKS_PRIME,
            7,
        ]);
        let b = Fp5([99, 1, GOLDILOCKS_PRIME - 3, 888_888, 55]);
        let c = Fp5([7, 8, 9, 10, 11]);
        assert_eq!(a.mul(b), b.mul(a));
        assert_eq!(a.mul(b).mul(c), a.mul(b.mul(c)));
        assert_eq!(a.mul(b.add(c)), a.mul(b).add(a.mul(c)));

        let mut frob = a;
        for _ in 0..5 {
            frob = fp5_pow_u64(frob, GOLDILOCKS_PRIME);
        }
        assert_eq!(frob, a);
    }

    #[test]
    fn shake256_party_batch8_matches_scalar_shake256_bit_for_bit() {
        let nonce = [0x3Cu8; 32];
        let rep = 19u32;
        let base_party = 40usize;
        let seeds: [[u8; 32]; 8] = core::array::from_fn(|i| [(i as u8).wrapping_mul(29) ^ 0xA5; 32]);

        let mut batch = Shake256PartyBatch8::new(&nonce, rep, base_party, &seeds);
        let salts = batch.extract_salts_1();
        let mut outs: [Vec<u64>; 8] = core::array::from_fn(|_| Vec::new());
        batch.squeeze_canonical_gl([true, false, true, true, true, false, true, true], &mut outs, 512);

        for inst in 0..8 {
            let mut sp = Shake256::new();
            sp.absorb(PARTY_TAPE_DOMAIN_24);
            sp.absorb(&nonce);
            sp.absorb(&seeds[inst]);
            let tag = (rep as u64) | (((base_party + inst) as u64) << 32);
            sp.absorb(&tag.to_le_bytes());
            sp.finalize(0x1F);

            let mut ref_salt = [0u8; 32];
            sp.squeeze(&mut ref_salt);
            assert_eq!(salts[inst], ref_salt);

            if !matches!(inst, 1 | 5) {
                let mut expected = Vec::with_capacity(512);
                let mut word_bytes = [0u8; 8];
                while expected.len() < 512 {
                    sp.squeeze(&mut word_bytes);
                    let w = u64::from_le_bytes(word_bytes);
                    if w < GOLDILOCKS_PRIME {
                        expected.push(w);
                    }
                }
                assert_eq!(outs[inst], expected);
            } else {
                assert!(outs[inst].is_empty());
            }
        }
    }

    #[test]
    fn ggm_tree_256_roundtrip_and_hidden_leaf_isolation() {
        let root = [0x77u8; 32];
        let nonce = [0x21u8; 32];
        let full = expand_ggm_tree_256(&root, &nonce, 3);
        for hidden in [0u8, 1, 127, 128, 254, 255] {
            let copath = extract_ggm_copath(&full, hidden);
            let rec = reconstruct_ggm_leaves_256(&copath, hidden, &nonce, 3);
            for p in 0..VC_SD_LIMBO_PARTIES {
                if p == hidden as usize {
                    assert_eq!(rec[p], [0u8; 32]);
                } else {
                    assert_eq!(rec[p], full.0[VC_SD_LIMBO_PARTIES + p]);
                }
            }
        }
    }

    #[test]
    fn arity_commitment_distinguishes_trailing_zero() {
        let blind = [17, 18, 19, 20];
        let one = compute_vc_poseidon2_commit(42, &[7], &blind, VC_ATTR_COMMIT_TAG).unwrap();
        let two = compute_vc_poseidon2_commit(42, &[7, 0], &blind, VC_ATTR_COMMIT_TAG).unwrap();
        assert_ne!(one, two);
        assert!(compute_vc_poseidon2_commit(42, &[], &blind, VC_ATTR_COMMIT_TAG).is_err());
        assert!(compute_vc_poseidon2_commit(42, &[0; 7], &blind, VC_ATTR_COMMIT_TAG).is_err());
    }

    #[test]
    fn quantum_issuance_roundtrip_and_downgrade_rejection() {
        let (mut req, _) = holder_prepare_blind_issuance_with_profile(
            42,
            &[1, 2],
            [3; 32],
            7,
            [4; 32],
            [5; 32],
            ZkSoundnessProfile::Quantum128,
        )
        .unwrap();
        assert_eq!(req.opened_reps.len(), 438);
        let (classical, _) = holder_prepare_blind_issuance_with_profile(
            42,
            &[1, 2],
            [3; 32],
            7,
            [4; 32],
            [5; 32],
            ZkSoundnessProfile::Classical128,
        )
        .unwrap();
        assert_ne!(
            classical.opened_reps[0].tape_seed_e,
            req.opened_reps[0].tape_seed_e
        );
        assert_ne!(
            classical.opened_reps[0].in_shares_e,
            req.opened_reps[0].in_shares_e
        );
        assert!(!verify_blind_issuance_request_with_profile(
            &classical,
            &[1, 2],
            42,
            ZkSoundnessProfile::Quantum128
        ));

        assert!(verify_blind_issuance_request_with_profile(
            &req,
            &[1, 2],
            42,
            ZkSoundnessProfile::Quantum128
        ));
        assert!(verify_blind_issuance_request(&req, &[1, 2], 42));
        req.opened_reps[0].gate_outs_e[0] = gl_add(req.opened_reps[0].gate_outs_e[0], 1);
        assert!(!verify_blind_issuance_request_with_profile(
            &req,
            &[1, 2],
            42,
            ZkSoundnessProfile::Quantum128
        ));
    }

    #[test]
    fn selective_disclosure_rejects_round_and_gate_tampering() {
        for profile in [
            ZkSoundnessProfile::Classical128,
            ZkSoundnessProfile::Quantum128,
        ] {
            selective_disclosure_profile(profile);
        }
    }

    fn selective_disclosure_profile(profile: ZkSoundnessProfile) {
        let holder = HolderCredentialSecret {
            schema_id: 42,
            arity: 5,
            attrs: [840, 1994, 3, 9910, 2030, 0],
            holder_blind: [17, 18, 19, 20],
            seen_challenges: core::cell::RefCell::new(Vec::new()),
        };
        let commitment = compute_vc_poseidon2_commit(
            holder.schema_id,
            &holder.attrs[..holder.arity],
            &holder.holder_blind,
            VC_ATTR_COMMIT_TAG,
        )
        .unwrap();
        let oprf_pk = PublicKey::test_key();
        let mut accumulator = IssuerCredentialAccumulator::new(oprf_pk.clone(), 7);
        let index = accumulator.enroll(commitment).unwrap();
        let cred = BlindVerifiableCredential {
            issuer_epoch: 7,
            schema_id: 42,
            attr_commit: commitment,
            issuance_token: [0; 32],
            accumulator_leaf_index: index,
        };
        let (issuer_mldsa_pk, issuer_mldsa_sk) =
            crate::fips204_ntt::ml_dsa_keygen_from_seed(MlDsaLevel::MlDsa44, &[0x41; 32]);
        let root_attestation = accumulator
            .attest_root_deterministic(
                MlDsaLevel::MlDsa44,
                &issuer_mldsa_sk,
                issuer_mldsa_pk.clone(),
            )
            .unwrap();
        let mode = PresentationMode::ScopedPseudonym([0x5Au8; 32]);
        let mut presentation = prove_selective_disclosure_with_profile(
            &cred,
            &holder,
            &accumulator.membership_witness(index).unwrap(),
            &[0, 2],
            PresentationRequest {
                verifier_scope: b"verifier",
                verifier_challenge: &[73; 32],
                mode,
            },
            [72; 32],
            profile,
        )
        .unwrap();
        assert_eq!(presentation.opened_reps.len(), profile.sd_repetitions());
        assert!(verify_presentation_with_profile(
            &presentation,
            &root_attestation,
            &issuer_mldsa_pk,
            &oprf_pk,
            b"verifier",
            &[73; 32],
            mode,
            42,
            holder.arity,
            profile
        ));

        // Cross-profile downgrade rejection:
        let other_profile = match profile {
            ZkSoundnessProfile::Classical128 => ZkSoundnessProfile::Quantum128,
            ZkSoundnessProfile::Quantum128 => ZkSoundnessProfile::Classical128,
        };
        assert!(!verify_presentation_with_profile(
            &presentation,
            &root_attestation,
            &issuer_mldsa_pk,
            &oprf_pk,
            b"verifier",
            &[73; 32],
            mode,
            42,
            holder.arity,
            other_profile,
        ));

        // Arity mismatch & tampering:
        assert!(!verify_presentation_with_profile(
            &presentation,
            &root_attestation,
            &issuer_mldsa_pk,
            &oprf_pk,
            b"verifier",
            &[73; 32],
            mode,
            42,
            6,
            profile,
        ));
        presentation.arity = 6;
        assert!(!verify_presentation_with_profile(
            &presentation,
            &root_attestation,
            &issuer_mldsa_pk,
            &oprf_pk,
            b"verifier",
            &[73; 32],
            mode,
            42,
            6,
            profile,
        ));
        presentation.arity = holder.arity;

        // Disclosed value tampering must be rejected!
        let orig_val = presentation.disclosed_attrs[0].1;
        presentation.disclosed_attrs[0].1 = gl_add(orig_val, 1);
        assert!(!verify_presentation_with_profile(
            &presentation,
            &root_attestation,
            &issuer_mldsa_pk,
            &oprf_pk,
            b"verifier",
            &[73; 32],
            mode,
            42,
            holder.arity,
            profile
        ));
        presentation.disclosed_attrs[0].1 = orig_val;

        // Tampering the issuer's attested epoch or signature must be rejected!
        let mut wrong_epoch_att = root_attestation.clone();
        wrong_epoch_att.issuer_epoch = 8;
        assert!(!verify_presentation_with_profile(
            &presentation,
            &wrong_epoch_att,
            &issuer_mldsa_pk,
            &oprf_pk,
            b"verifier",
            &[73; 32],
            mode,
            42,
            holder.arity,
            profile
        ));
        let (rogue_pk, rogue_sk) =
            crate::fips204_ntt::ml_dsa_keygen_from_seed(MlDsaLevel::MlDsa44, &[0x99; 32]);
        let rogue_att = accumulator
            .attest_root_deterministic(MlDsaLevel::MlDsa44, &rogue_sk, rogue_pk)
            .unwrap();
        assert!(!verify_presentation_with_profile(
            &presentation,
            &rogue_att,
            &issuer_mldsa_pk,
            &oprf_pk,
            b"verifier",
            &[73; 32],
            mode,
            42,
            holder.arity,
            profile
        ));

        // Tampering GGM copath, hidden commitment, r_poly, alpha, beta, and aux must all fail!
        presentation.opened_reps[0].ggm_copath[0][0] ^= 1;
        assert!(!verify_presentation_with_profile(
            &presentation,
            &root_attestation,
            &issuer_mldsa_pk,
            &oprf_pk,
            b"verifier",
            &[73; 32],
            mode,
            42,
            holder.arity,
            profile
        ));
        presentation.opened_reps[0].ggm_copath[0][0] ^= 1;

        presentation.opened_reps[0].com_1_hidden[0] ^= 1;
        assert!(!verify_presentation_with_profile(
            &presentation,
            &root_attestation,
            &issuer_mldsa_pk,
            &oprf_pk,
            b"verifier",
            &[73; 32],
            mode,
            42,
            holder.arity,
            profile
        ));
        presentation.opened_reps[0].com_1_hidden[0] ^= 1;

        presentation.opened_reps[0].r_poly_without_b[0][0] =
            gl_add(presentation.opened_reps[0].r_poly_without_b[0][0], 1);
        assert!(!verify_presentation_with_profile(
            &presentation,
            &root_attestation,
            &issuer_mldsa_pk,
            &oprf_pk,
            b"verifier",
            &[73; 32],
            mode,
            42,
            holder.arity,
            profile
        ));
        presentation.opened_reps[0].r_poly_without_b[0][0] =
            gl_sub(presentation.opened_reps[0].r_poly_without_b[0][0], 1);

        presentation.opened_reps[0].alpha[0][0] =
            gl_add(presentation.opened_reps[0].alpha[0][0], 1);
        assert!(!verify_presentation_with_profile(
            &presentation,
            &root_attestation,
            &issuer_mldsa_pk,
            &oprf_pk,
            b"verifier",
            &[73; 32],
            mode,
            42,
            holder.arity,
            profile
        ));
        presentation.opened_reps[0].alpha[0][0] =
            gl_sub(presentation.opened_reps[0].alpha[0][0], 1);

        presentation.opened_reps[0].beta[0][0] =
            gl_add(presentation.opened_reps[0].beta[0][0], 1);
        assert!(!verify_presentation_with_profile(
            &presentation,
            &root_attestation,
            &issuer_mldsa_pk,
            &oprf_pk,
            b"verifier",
            &[73; 32],
            mode,
            42,
            holder.arity,
            profile
        ));
        presentation.opened_reps[0].beta[0][0] =
            gl_sub(presentation.opened_reps[0].beta[0][0], 1);

        if let Some(aux_rep) = presentation.opened_reps.iter_mut().find(|r| r.aux.is_some()) {
            let aux = aux_rep.aux.as_mut().unwrap();
            aux.delta_z[0] = gl_add(aux.delta_z[0], 1);
            assert!(!verify_presentation_with_profile(
                &presentation,
                &root_attestation,
                &issuer_mldsa_pk,
                &oprf_pk,
                b"verifier",
                &[73; 32],
                mode,
                42,
                holder.arity,
                profile
            ));
            let aux = presentation
                .opened_reps
                .iter_mut()
                .find(|r| r.aux.is_some())
                .unwrap()
                .aux
                .as_mut()
                .unwrap();
            aux.delta_z[0] = gl_sub(aux.delta_z[0], 1);
        }
    }

    #[test]
    fn repeated_entropy_across_distinct_statements_produces_independent_zkboo_shares() {
        let holder = HolderCredentialSecret {
            schema_id: 42,
            arity: 6,
            attrs: [840, 1994, 3, 9910, 2030, 777],
            holder_blind: [17, 18, 19, 20],
            seen_challenges: core::cell::RefCell::new(Vec::new()),
        };
        let commitment = compute_vc_poseidon2_commit(
            holder.schema_id,
            &holder.attrs[..holder.arity],
            &holder.holder_blind,
            VC_ATTR_COMMIT_TAG,
        )
        .unwrap();
        let oprf_pk = PublicKey::test_key();
        let mut accumulator = IssuerCredentialAccumulator::new(oprf_pk, 7);
        let index = accumulator.enroll(commitment).unwrap();
        let cred = BlindVerifiableCredential {
            issuer_epoch: 7,
            schema_id: 42,
            attr_commit: commitment,
            issuance_token: [0; 32],
            accumulator_leaf_index: index,
        };
        let reused_entropy = [0xAAu8; 32];
        let pres1 = prove_selective_disclosure(
            &cred,
            &holder,
            &accumulator.membership_witness(index).unwrap(),
            &[0],
            PresentationRequest {
                verifier_scope: b"scope-alpha",
                verifier_challenge: &[0x11; 32],
                mode: PresentationMode::UnlinkableFresh,
            },
            reused_entropy,
        )
        .unwrap();
        assert_eq!(
            prove_selective_disclosure(
                &cred,
                &holder,
                &accumulator.membership_witness(index).unwrap(),
                &[0],
                PresentationRequest {
                    verifier_scope: b"scope-alpha",
                    verifier_challenge: &[0x11; 32],
                    mode: PresentationMode::UnlinkableFresh
                },
                reused_entropy,
            )
            .unwrap_err(),
            BlindVcError::ReplayedVerifierChallenge
        );
        let pres2 = prove_selective_disclosure(
            &cred,
            &holder,
            &accumulator.membership_witness(index).unwrap(),
            &[0],
            PresentationRequest {
                verifier_scope: b"scope-alpha",
                verifier_challenge: &[0x22; 32],
                mode: PresentationMode::UnlinkableFresh,
            },
            reused_entropy,
        )
        .unwrap();

        // Statement hedging must make all repetition GGM trees, commitments, and aux vectors independent:
        assert_ne!(pres1.presentation_nonce, pres2.presentation_nonce);
        assert_ne!(pres1.pres_commit, pres2.pres_commit);
        assert_ne!(pres1.scope_tag, pres2.scope_tag);
        for (r1, r2) in pres1.opened_reps.iter().zip(&pres2.opened_reps) {
            assert_ne!(r1.ggm_copath, r2.ggm_copath);
            assert_ne!(r1.com_1_hidden, r2.com_1_hidden);
            if let (Some(a1), Some(a2)) = (&r1.aux, &r2.aux) {
                assert_ne!(a1.delta_w, a2.delta_w);
                assert_ne!(a1.delta_z, a2.delta_z);
            }
        }
    }

    #[test]
    fn flat_view_wire_known_answer() {
        let expected = [
            61, 135, 171, 82, 130, 136, 55, 10, 124, 33, 88, 220, 132, 3, 153, 201, 11, 135, 206,
            216, 80, 196, 219, 81, 24, 19, 238, 51, 219, 46, 207, 21,
        ];
        assert_eq!(digest_party_view(&[2], &[1; 32], &[3], &[4]), expected);
        assert_ne!(digest_party_view(&[2, 3], &[1; 32], &[], &[4]), expected);
        assert_ne!(digest_party_view(&[2], &[1; 32], &[3, 0], &[4]), expected);
    }

    #[test]
    fn selective_disclosure_compact_wire_sub_15mib_and_roundtrips() {
        let holder = HolderCredentialSecret {
            schema_id: 42,
            arity: 5,
            attrs: [840, 1994, 3, 9910, 2030, 0],
            holder_blind: [17, 18, 19, 20],
            seen_challenges: core::cell::RefCell::new(Vec::new()),
        };
        let commitment = compute_vc_poseidon2_commit(
            holder.schema_id,
            &holder.attrs[..holder.arity],
            &holder.holder_blind,
            VC_ATTR_COMMIT_TAG,
        )
        .unwrap();
        let oprf_pk = PublicKey::test_key();
        let mut accumulator = IssuerCredentialAccumulator::new(oprf_pk.clone(), 7);
        let index = accumulator.enroll(commitment).unwrap();
        let (issuer_mldsa_pk, issuer_mldsa_sk) =
            crate::fips204_ntt::ml_dsa_keygen_from_seed(MlDsaLevel::MlDsa44, &[0x55; 32]);
        let root_attestation = accumulator
            .attest_root_deterministic(
                MlDsaLevel::MlDsa44,
                &issuer_mldsa_sk,
                issuer_mldsa_pk.clone(),
            )
            .unwrap();
        let cred = BlindVerifiableCredential {
            issuer_epoch: 7,
            schema_id: 42,
            attr_commit: commitment,
            issuance_token: [0; 32],
            accumulator_leaf_index: index,
        };

        for (profile, challenge_byte, max_bytes) in [
            (ZkSoundnessProfile::Classical128, 0x73u8, 6 * 1024 * 1024),
            (ZkSoundnessProfile::Quantum128, 0x74u8, 15 * 1024 * 1024),
        ] {
            let pres = prove_selective_disclosure_with_profile(
                &cred,
                &holder,
                &accumulator.membership_witness(index).unwrap(),
                &[0, 2],
                PresentationRequest {
                    verifier_scope: b"compact-wire",
                    verifier_challenge: &[challenge_byte; 32],
                    mode: PresentationMode::UnlinkableFresh,
                },
                [0x42; 32],
                profile,
            )
            .unwrap();

            let compact = pres.to_compact_wire_bytes().unwrap();
            assert!(
                compact.len() < max_bytes,
                "{profile:?} wire size {} exceeded cap {max_bytes}",
                compact.len()
            );
            assert_eq!(pres.to_wire_bytes().unwrap(), compact);

            let decoded =
                SelectiveDisclosurePresentation::from_compact_wire_bytes(&compact).unwrap();
            assert_eq!(decoded, pres);
            assert!(verify_presentation_with_profile(
                &decoded,
                &root_attestation,
                &issuer_mldsa_pk,
                &oprf_pk,
                b"compact-wire",
                &[challenge_byte; 32],
                PresentationMode::UnlinkableFresh,
                42,
                holder.arity,
                profile,
            ));

            // Truncated, trailing-byte, and bit-flipped payloads fail cleanly.
            assert!(
                SelectiveDisclosurePresentation::from_compact_wire_bytes(
                    &compact[..compact.len() - 1]
                )
                .is_err()
            );
            let mut trailing = compact.clone();
            trailing.push(0);
            assert!(SelectiveDisclosurePresentation::from_compact_wire_bytes(&trailing).is_err());

            let mut tampered = compact;
            let last = tampered.len() - 64;
            tampered[last] ^= 1;
            if let Ok(bad_pres) = SelectiveDisclosurePresentation::from_compact_wire_bytes(&tampered)
            {
                assert!(!verify_presentation_with_profile(
                    &bad_pres,
                    &root_attestation,
                    &issuer_mldsa_pk,
                    &oprf_pk,
                    b"compact-wire",
                    &[challenge_byte; 32],
                    PresentationMode::UnlinkableFresh,
                    42,
                    holder.arity,
                    profile,
                ));
            }
        }
    }
}
