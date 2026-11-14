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
    let blind_vec = sample_canonical_gl_vec(b"QSAG.VC.HOLDER_BLIND.V1", ent.expose(), &blind_ctx, 4);
    let mut holder_blind = ZeroizingU64Vec(vec![
        blind_vec[0],
        blind_vec[1],
        blind_vec[2],
        blind_vec[3],
    ]);
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

    // Secret witness layout:
    // - Undisclosed attribute values (arity minus disclosed count).
    // - `holder_blind[0..4]` (`4`)
    // - `pres_blind[0..4]` (`4`)
    // - One Boolean leaf-index bit per Merkle level.
    // - Six sibling limbs per Merkle level.
    let mut secret_vals =
        ZeroizingU64Vec(Vec::with_capacity(MAX_VC_ATTRS + 8 + 7 * VC_ACCUMULATOR_DEPTH));
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
    if profile == ZkSoundnessProfile::Quantum128 {
        inst_bytes.extend_from_slice(b"QSAG.VC.PROFILE.Quantum128:438");
    }
    let statement_digest = cshake256_framed_32(b"QSAG.VC.SD_STMT_DIGEST.V1", &[&inst_bytes]);
    let mut hedged_zk_seed =
        cshake256_framed_32(b"QSAG.VC.SD_ZK_SEED.V1", &[&statement_digest, &ent]);
    let mut tr = InterleavedTranscript::new(b"QSAG.BLIND_VC.SD_ZK.V1", &inst_bytes);
    if profile == ZkSoundnessProfile::Quantum128 {
        tr.absorb(b"VC_SOUNDNESS_PROFILE", b"Quantum128:438");
    }

    struct SdRep {
        commits: [[u8; 32]; 3],
        salts: [[u8; 32]; 3],
        in_shares: [Vec<u64>; 3],
        tape_seeds: [[u8; 32]; 3],
        gate_outs: [Vec<u64>; 3],
        final_outs: [[u64; 3]; VC_FINAL_OUTPUTS],
    }
    impl Drop for SdRep {
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
    let mut round1_bundle = Vec::with_capacity(profile.repetitions() * 480);

    for rep in 0..profile.repetitions() {
        let rep_be = (rep as u32).to_be_bytes();
        let mut share_ctx = [0u8; 36];
        share_ctx[..32].copy_from_slice(&statement_digest);
        share_ctx[32..].copy_from_slice(&rep_be);
        let rand_in = sample_canonical_gl_vec(
            b"QSAG.VC.SD_IN_SH.V1",
            &hedged_zk_seed,
            &share_ctx,
            2 * num_secret_wires,
        );
        let mut in0 = Vec::with_capacity(num_secret_wires);
        let mut in1 = Vec::with_capacity(num_secret_wires);
        let mut in2 = Vec::with_capacity(num_secret_wires);
        let mut sec_wires = Vec::with_capacity(num_secret_wires);
        for (value, random) in secret_vals.iter().zip(rand_in.as_chunks::<2>().0.iter()) {
            let s = split_secret_3(*value, random[0], random[1]);
            sec_wires.push(s);
            in0.push(s[0]);
            in1.push(s[1]);
            in2.push(s[2]);
        }

        let tape_seeds: [[u8; 32]; 3] = core::array::from_fn(|m| {
            cshake256_framed_32(
                b"QSAG.VC.SD_TAPE.V1",
                &[
                    &statement_digest,
                    &hedged_zk_seed,
                    &presentation_nonce,
                    &rep_be,
                    &[m as u8],
                ],
            )
        });
        let salts: [[u8; 32]; 3] = core::array::from_fn(|m| {
            cshake256_framed_32(
                b"QSAG.VC.SD_SALT.V1",
                &[
                    &statement_digest,
                    &hedged_zk_seed,
                    &presentation_nonce,
                    &rep_be,
                    &[m as u8],
                ],
            )
        });

        let mut prover = ZkBooProverTape::new(&tape_seeds, SD_TOTAL_GATES);
        let mut cursor = 0usize;

        // Reassemble `attr_wires[0..6]` from public disclosed constants + secret undisclosed shares!
        let mut attr_wires = [[0u64; 3]; MAX_VC_ATTRS];
        for (i, slot_w) in attr_wires.iter_mut().enumerate() {
            if i >= holder_secret.arity {
                *slot_w = [0; 3];
            } else if let Some(&(_, pub_val)) = disclosed_attrs.iter().find(|&&(idx, _)| idx == i) {
                *slot_w = [pub_val, 0, 0];
            } else {
                *slot_w = sec_wires[cursor];
                cursor += 1;
            }
        }
        let hb_wires: [[u64; 3]; 4] = core::array::from_fn(|_| {
            let v = sec_wires[cursor];
            cursor += 1;
            v
        });
        let pb_wires: [[u64; 3]; 4] = core::array::from_fn(|_| {
            let v = sec_wires[cursor];
            cursor += 1;
            v
        });
        let bit_wires: [[u64; 3]; VC_ACCUMULATOR_DEPTH] = core::array::from_fn(|_| {
            let v = sec_wires[cursor];
            cursor += 1;
            v
        });
        let sib_wires: [[[u64; 3]; 6]; VC_ACCUMULATOR_DEPTH] = core::array::from_fn(|_| {
            core::array::from_fn(|_| {
                let v = sec_wires[cursor];
                cursor += 1;
                v
            })
        });
        debug_assert_eq!(cursor, num_secret_wires);

        // 1. Compute hidden `attr_commit`:
        let mut st_attr: [[u64; 3]; 13] = [
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
            [(cred.schema_id & 0xffff_ffff), 0, 0],
            [
                gl_add(cred.schema_id >> 32, gl_reduce_u64(VC_ATTR_COMMIT_TAG)),
                0,
                0,
            ],
            [holder_secret.arity as u64, 0, 0],
        ];
        prover.perm12(&mut st_attr);
        let mut cur_node: [[u64; 3]; 6] = core::array::from_fn(|j| st_attr[j]);

        // 2. Traverse hidden Merkle path up to `accumulator_root`:
        let mut bool_zeros = [[0u64; 3]; VC_ACCUMULATOR_DEPTH];
        for (lvl, (zero, &b)) in bool_zeros.iter_mut().zip(&bit_wires).enumerate() {
            // `b * (1 - b) == 0`:
            let one_minus_b = [gl_sub(1, b[0]), gl_neg(b[1]), gl_neg(b[2])];
            *zero = prover.mul_gate(b, one_minus_b);

            let mut left = [[0u64; 3]; 6];
            let mut right = [[0u64; 3]; 6];
            for (j, (left_slot, right_slot)) in left.iter_mut().zip(&mut right).enumerate() {
                let sib_j = sib_wires[lvl][j];
                // `diff = sib - cur`; `delta = b * diff`; `left = cur + delta`, `right = sib - delta`:
                let diff: [u64; 3] = core::array::from_fn(|m| gl_sub(sib_j[m], cur_node[j][m]));
                let delta = prover.mul_gate(b, diff);
                *left_slot = core::array::from_fn(|m| gl_add(cur_node[j][m], delta[m]));
                *right_slot = core::array::from_fn(|m| gl_sub(sib_j[m], delta[m]));
            }

            let mut st_mk: [[u64; 3]; 16] = [
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
                [(cred.issuer_epoch & 0xffff_ffff), 0, 0],
                [lvl as u64, 0, 0],
                [gl_reduce_u64(VC_MERKLE_NODE_TAG), 0, 0],
                [
                    gl_add(cred.issuer_epoch >> 32, gl_reduce_u64(POSEIDON2_CONST_IV)),
                    0,
                    0,
                ],
            ];
            prover.perm12(&mut st_mk);
            cur_node = core::array::from_fn(|j| st_mk[j]);
        }

        // 3. Fresh rerandomized `pres_commit`:
        let mut st_pres: [[u64; 3]; 13] = [
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
            [(cred.schema_id & 0xffff_ffff), 0, 0],
            [
                gl_add(cred.schema_id >> 32, gl_reduce_u64(VC_PRES_COMMIT_TAG)),
                0,
                0,
            ],
            [holder_secret.arity as u64, 0, 0],
        ];
        prover.perm12(&mut st_pres);

        // 4. Scope-bound `scope_tag`:
        let mut st_sc: [[u64; 3]; 12] = [
            hb_wires[0],
            hb_wires[1],
            hb_wires[2],
            hb_wires[3],
            [verifier_scope_limbs[0], 0, 0],
            [verifier_scope_limbs[1], 0, 0],
            [verifier_scope_limbs[2], 0, 0],
            [verifier_scope_limbs[3], 0, 0],
            [0, 0, 0],
            [0, 0, 0],
            [(cred.schema_id & 0xffff_ffff), 0, 0],
            [
                gl_add(cred.schema_id >> 32, gl_reduce_u64(VC_SCOPE_TAG_DOM)),
                0,
                0,
            ],
        ];
        prover.perm12(&mut st_sc);
        debug_assert_eq!(prover.gate_cursor, SD_TOTAL_GATES);

        // Six limbs each for root, presentation and scope, plus path-bit constraints.
        let mut final_outs = [[0u64; 3]; VC_FINAL_OUTPUTS];
        final_outs[0..6].copy_from_slice(&cur_node);
        final_outs[6..12].copy_from_slice(&st_pres[0..6]);
        final_outs[12..18].copy_from_slice(&st_sc[0..6]);
        final_outs[18..VC_FINAL_OUTPUTS].copy_from_slice(&bool_zeros);

        let in_shares = [in0, in1, in2];
        let commits: [[u8; 32]; 3] = core::array::from_fn(|m| {
            let f_m: [u64; VC_FINAL_OUTPUTS] = core::array::from_fn(|j| final_outs[j][m]);
            let d = digest_party_view(&in_shares[m], &tape_seeds[m], &prover.out[m], &f_m);
            commit_mpc_broadcast(&presentation_nonce, rep as u32, m as u16, &d, &salts[m])
        });

        for c in &commits {
            round1_bundle.extend_from_slice(c);
        }
        for o16 in &final_outs {
            for &v in o16 {
                round1_bundle.extend_from_slice(&v.to_le_bytes());
            }
        }

        reps.push(SdRep {
            commits,
            salts,
            in_shares,
            tape_seeds,
            gate_outs: core::mem::take(&mut prover.out),
            final_outs,
        });
    }

    tr.absorb(b"VC_SD_R1_COMMITS", &round1_bundle);
    let open_trits = squeeze_ternary_challenges(&mut tr, profile.repetitions());
    ct_zeroize_bytes(&mut hedged_zk_seed);
    ct_zeroize_bytes(&mut ent);
    drop(secret_vals);

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
            num_active_final_outs: VC_FINAL_OUTPUTS,
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

/// Use an explicit verifier-selected soundness budget.
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
    if pres.opened_reps.len() != profile.repetitions()
        || pres.disclosed_attrs.len() > expected_arity
    {
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
    if profile == ZkSoundnessProfile::Quantum128 {
        inst_bytes.extend_from_slice(b"QSAG.VC.PROFILE.Quantum128:438");
    }
    let mut tr = InterleavedTranscript::new(b"QSAG.BLIND_VC.SD_ZK.V1", &inst_bytes);
    if profile == ZkSoundnessProfile::Quantum128 {
        tr.absorb(b"VC_SOUNDNESS_PROFILE", b"Quantum128:438");
    }

    let mut expected_16 = [0u64; VC_FINAL_OUTPUTS];
    expected_16[..6].copy_from_slice(&pres.accumulator_root);
    expected_16[6..12].copy_from_slice(&pres.pres_commit);
    expected_16[12..18].copy_from_slice(&pres.scope_tag);

    let mut round1_bundle = Vec::with_capacity(profile.repetitions() * 480);

    for (rep, o) in pres.opened_reps.iter().enumerate() {
        let e = o.e as usize;
        if e >= 3
            || o.num_active_final_outs != VC_FINAL_OUTPUTS
            || o.in_shares_e.len() != expected_num_secret_wires
            || o.in_shares_e1.len() != expected_num_secret_wires
        {
            return false;
        }
        let e1 = (e + 1) % 3;
        let e2 = (e + 2) % 3;

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
            SD_TOTAL_GATES,
        );

        let mut cursor = 0usize;
        let mut attr_wires = [[0u64; 2]; MAX_VC_ATTRS];
        for (i, slot_w) in attr_wires.iter_mut().enumerate() {
            if i >= expected_arity {
                *slot_w = [0; 2];
            } else if let Some(&(_, pub_val)) =
                pres.disclosed_attrs.iter().find(|&&(idx, _)| idx == i)
            {
                *slot_w = verifier.add_const([0, 0], pub_val);
            } else {
                *slot_w = [o.in_shares_e[cursor], o.in_shares_e1[cursor]];
                cursor += 1;
            }
        }
        let hb_wires: [[u64; 2]; 4] = core::array::from_fn(|_| {
            let v = [o.in_shares_e[cursor], o.in_shares_e1[cursor]];
            cursor += 1;
            v
        });
        let pb_wires: [[u64; 2]; 4] = core::array::from_fn(|_| {
            let v = [o.in_shares_e[cursor], o.in_shares_e1[cursor]];
            cursor += 1;
            v
        });
        let bit_wires: [[u64; 2]; VC_ACCUMULATOR_DEPTH] = core::array::from_fn(|_| {
            let v = [o.in_shares_e[cursor], o.in_shares_e1[cursor]];
            cursor += 1;
            v
        });
        let sib_wires: [[[u64; 2]; 6]; VC_ACCUMULATOR_DEPTH] = core::array::from_fn(|_| {
            core::array::from_fn(|_| {
                let v = [o.in_shares_e[cursor], o.in_shares_e1[cursor]];
                cursor += 1;
                v
            })
        });

        let mut st_attr: [[u64; 2]; 13] = [
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
            verifier.add_const([0, 0], pres.schema_id & 0xffff_ffff),
            verifier.add_const(
                [0, 0],
                gl_add(pres.schema_id >> 32, gl_reduce_u64(VC_ATTR_COMMIT_TAG)),
            ),
            verifier.add_const([0, 0], expected_arity as u64),
        ];
        verifier.perm12(&mut st_attr);
        let mut cur_node: [[u64; 2]; 6] = core::array::from_fn(|j| st_attr[j]);

        let mut bool_zeros = [[0u64; 2]; VC_ACCUMULATOR_DEPTH];
        for (lvl, (zero, &b)) in bool_zeros.iter_mut().zip(&bit_wires).enumerate() {
            let one_wire = verifier.add_const([0, 0], 1);
            let one_minus_b = [gl_sub(one_wire[0], b[0]), gl_sub(one_wire[1], b[1])];
            *zero = verifier.mul_gate(b, one_minus_b);

            let mut left = [[0u64; 2]; 6];
            let mut right = [[0u64; 2]; 6];
            for (j, (left_slot, right_slot)) in left.iter_mut().zip(&mut right).enumerate() {
                let sib_j = sib_wires[lvl][j];
                let diff = [
                    gl_sub(sib_j[0], cur_node[j][0]),
                    gl_sub(sib_j[1], cur_node[j][1]),
                ];
                let delta = verifier.mul_gate(b, diff);
                *left_slot = [
                    gl_add(cur_node[j][0], delta[0]),
                    gl_add(cur_node[j][1], delta[1]),
                ];
                *right_slot = [gl_sub(sib_j[0], delta[0]), gl_sub(sib_j[1], delta[1])];
            }

            let mut st_mk: [[u64; 2]; 16] = [
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
                verifier.add_const([0, 0], pres.issuer_epoch & 0xffff_ffff),
                verifier.add_const([0, 0], lvl as u64),
                verifier.add_const([0, 0], gl_reduce_u64(VC_MERKLE_NODE_TAG)),
                verifier.add_const(
                    [0, 0],
                    gl_add(pres.issuer_epoch >> 32, gl_reduce_u64(POSEIDON2_CONST_IV)),
                ),
            ];
            verifier.perm12(&mut st_mk);
            cur_node = core::array::from_fn(|j| st_mk[j]);
        }

        let mut st_pres: [[u64; 2]; 13] = [
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
            verifier.add_const([0, 0], pres.schema_id & 0xffff_ffff),
            verifier.add_const(
                [0, 0],
                gl_add(pres.schema_id >> 32, gl_reduce_u64(VC_PRES_COMMIT_TAG)),
            ),
            verifier.add_const([0, 0], expected_arity as u64),
        ];
        verifier.perm12(&mut st_pres);

        let mut st_sc: [[u64; 2]; 12] = [
            hb_wires[0],
            hb_wires[1],
            hb_wires[2],
            hb_wires[3],
            verifier.add_const([0, 0], pres.verifier_scope_limbs[0]),
            verifier.add_const([0, 0], pres.verifier_scope_limbs[1]),
            verifier.add_const([0, 0], pres.verifier_scope_limbs[2]),
            verifier.add_const([0, 0], pres.verifier_scope_limbs[3]),
            [0, 0],
            [0, 0],
            verifier.add_const([0, 0], pres.schema_id & 0xffff_ffff),
            verifier.add_const(
                [0, 0],
                gl_add(pres.schema_id >> 32, gl_reduce_u64(VC_SCOPE_TAG_DOM)),
            ),
        ];
        verifier.perm12(&mut st_sc);

        if !verifier.ok || verifier.gate_cursor != SD_TOTAL_GATES {
            return false;
        }

        let mut replayed_16 = [[0u64; 2]; VC_FINAL_OUTPUTS];
        replayed_16[..6].copy_from_slice(&cur_node);
        replayed_16[6..12].copy_from_slice(&st_pres[..6]);
        replayed_16[12..18].copy_from_slice(&st_sc[..6]);
        replayed_16[18..].copy_from_slice(&bool_zeros);

        for (j, replayed) in replayed_16.iter().enumerate() {
            for &s_val in &o.final_outs_all3[j] {
                if !gl_is_canonical(s_val) {
                    return false;
                }
            }
            if replayed[0] != o.final_outs_all3[j][e] || replayed[1] != o.final_outs_all3[j][e1] {
                return false;
            }
            let recon = gl_add(
                o.final_outs_all3[j][0],
                gl_add(o.final_outs_all3[j][1], o.final_outs_all3[j][2]),
            );
            if recon != expected_16[j] {
                return false;
            }
        }

        let f_e: [u64; VC_FINAL_OUTPUTS] = core::array::from_fn(|j| o.final_outs_all3[j][e]);
        let f_e1: [u64; VC_FINAL_OUTPUTS] = core::array::from_fn(|j| o.final_outs_all3[j][e1]);
        let d_e = digest_party_view(&o.in_shares_e, &o.tape_seed_e, &o.gate_outs_e, &f_e);
        let d_e1 = digest_party_view(&o.in_shares_e1, &o.tape_seed_e1, &o.gate_outs_e1, &f_e1);
        let com_e = commit_mpc_broadcast(
            &pres.presentation_nonce,
            rep as u32,
            e as u16,
            &d_e,
            &o.salt_e,
        );
        let com_e1 = commit_mpc_broadcast(
            &pres.presentation_nonce,
            rep as u32,
            e1 as u16,
            &d_e1,
            &o.salt_e1,
        );

        let mut commits = [[0u8; 32]; 3];
        commits[e] = com_e;
        commits[e1] = com_e1;
        commits[e2] = o.unopened_commitment;
        for c in &commits {
            round1_bundle.extend_from_slice(c);
        }
        for o16 in &o.final_outs_all3 {
            for &v in o16 {
                round1_bundle.extend_from_slice(&v.to_le_bytes());
            }
        }
    }

    tr.absorb(b"VC_SD_R1_COMMITS", &round1_bundle);
    let expected_trits = squeeze_ternary_challenges(&mut tr, profile.repetitions());
    for (o, exp_e) in pres.opened_reps.iter().zip(expected_trits) {
        if (o.e as usize) != exp_e {
            return false;
        }
    }
    true
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
        let mode = PresentationMode::UnlinkableFresh;
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

        // Tampering the issuer's attested epoch, signature, or root tag must be rejected!
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

        presentation.opened_reps[0].gate_outs_e[0] =
            gl_add(presentation.opened_reps[0].gate_outs_e[0], 1);
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
        // Intentionally pass the EXACT SAME `presentation_entropy` across two distinct challenges:
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
        // Restoring caller entropy must not allow an identical challenge to
        // produce a second, byte-identical presentation commitment.
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

        // Even when repetition `rep` opens `e = 0` (`in_shares[0], in_shares[1]`) in `pres1` and
        // `e = 1` (`in_shares[1], in_shares[2]`) in `pres2`, combining `pres1`'s share 0 with
        // `pres2`'s shares 1 & 2 MUST NOT reconstruct secret attribute `attrs[1] = 1994`!
        let mut found_cross_trit = false;
        for (r1, r2) in pres1.opened_reps.iter().zip(&pres2.opened_reps) {
            assert_ne!(r1.in_shares_e, r2.in_shares_e);
            assert_ne!(r1.tape_seed_e, r2.tape_seed_e);
            if r1.e == 0 && r2.e == 1 {
                found_cross_trit = true;
                // Under the old unhedged code, `r1.in_shares_e[0] + r2.in_shares_e[0] + r2.in_shares_e1[0]`
                // equaled `holder.attrs[1]` (`1994`) with probability 1!
                let naive_sum = gl_add(
                    r1.in_shares_e[0],
                    gl_add(r2.in_shares_e[0], r2.in_shares_e1[0]),
                );
                assert_ne!(naive_sum, holder.attrs[1]);
                assert_eq!(r1.in_shares_e1[0], r1.in_shares_e1[0]);
                assert_ne!(r1.in_shares_e1[0], r2.in_shares_e[0]);
            }
        }
        assert!(
            found_cross_trit,
            "Repetitions must exercise cross-trit (e=0, e=1) openings"
        );
    }
}
