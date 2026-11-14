//! Wiedemann binary tower hierarchy `T_0 ⊂ T_1 ⊂ ... ⊂ T_8` (`Gf16 = T_2`, `Gf256 = T_3`,
//! `Tower128 = T_7`, `Tower256 = T_8`) via branchless stratified Karatsuba multiplication,
//! Frobenius subfield Booleanity check (`x^2 ⊕ x == 0`), and committed + masked
//! 2-lane `Tower128` BDOZ MAC verification with single-abort key burn.

use crate::keccak::Shake256Sponge;

/// Element of Wiedemann tower `T_2 = GF(2^4)` (canonical lower 4 bits `< 16`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Gf16(pub u8);

/// Element of Wiedemann tower `T_3 = GF(2^8)` (Shamir evaluation & share field).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Gf256(pub u8);

/// Element of Wiedemann tower `T_7 = GF(2^128)` (128-bit BDOZ MAC & triple-sacrifice field).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Tower128(pub u128);

/// Element of Wiedemann tower `T_8 = GF(2^256)` (`lo + hi * X_7`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Tower256 {
    pub lo: u128,
    pub hi: u128,
}

/// Verifier's per-wire record in a committed & masked 2-lane BDOZ batch opening:
/// binds `opened_value` with its non-zero public linear-combination challenge weight `chal_weight`
/// and the verifier's local `key_lanes` (never trusting raw uncommitted peer per-wire MACs).
#[derive(Clone, Copy)]
pub struct BdozWireOpening2Lane {
    pub opened_value: Gf256,
    pub chal_weight: Tower128,
    pub key_lanes: [Tower128; 2],
}

/// Committed and random-mask-blinded peer tag opening for a batch of `BdozWireOpening2Lane`:
/// - `mask_value` & `mask_key_lanes`: one-time authenticated `Tower128` mask blinding the folded
///   linear combination so a failed check leaks zero bits of persistent `alpha_lanes`,
/// - `tag_commitment` & `open_nonce`: pre-open `SHAKE256` commitment binding `(session_id, round_id,
///   masked_sum, peer_masked_mac_lanes, open_nonce)` prior to opening verifier weights/keys.
#[derive(Clone, Copy)]
pub struct BdozCommittedBatchOpening2Lane {
    pub session_id: [u8; 32],
    pub round_id: u64,
    pub mask_value: Tower128,
    pub mask_key_lanes: [Tower128; 2],
    pub peer_masked_mac_lanes: [Tower128; 2],
    pub open_nonce: [u8; 32],
    pub tag_commitment: [u8; 32],
}

/// Stateful BDOZ verifier key handle that permanently burns/zeroes `alpha_lanes` on any abort.
pub struct BdozVerifierSession2Lane {
    alpha_lanes: [Tower128; 2],
    burned: bool,
}

impl BdozVerifierSession2Lane {
    /// Create a fresh verifier session. The caller must provision fresh session keys.
    pub const fn new(alpha_lanes: [Tower128; 2]) -> Self {
        Self { alpha_lanes, burned: false }
    }

    pub const fn is_burned(&self) -> bool {
        self.burned
    }
}

#[inline]
const fn diff_bytes8(a: &[u8; 32], b: &[u8; 32], base: usize) -> u8 {
    ((a[base] ^ b[base]) | (a[base + 1] ^ b[base + 1]))
        | ((a[base + 2] ^ b[base + 2]) | (a[base + 3] ^ b[base + 3]))
        | ((a[base + 4] ^ b[base + 4]) | (a[base + 5] ^ b[base + 5]))
        | ((a[base + 6] ^ b[base + 6]) | (a[base + 7] ^ b[base + 7]))
}

/// Branchless constant-time 32-byte equality check (`0` data-dependent branches).
#[inline]
pub const fn ct_eq_bytes32(a: &[u8; 32], b: &[u8; 32]) -> bool {
    let d = (diff_bytes8(a, b, 0) | diff_bytes8(a, b, 8))
        | (diff_bytes8(a, b, 16) | diff_bytes8(a, b, 24));
    d == 0
}

#[inline]
const fn scale_x_t1(a: u8) -> u8 {
    let lo = a & 1;
    let hi = (a >> 1) & 1;
    hi | ((lo ^ hi) << 1)
}

#[inline]
const fn mul_t1(a: u8, b: u8) -> u8 {
    let a_lo = a & 1;
    let a_hi = (a >> 1) & 1;
    let b_lo = b & 1;
    let b_hi = (b >> 1) & 1;
    let p = a_lo & b_lo;
    let q = a_hi & b_hi;
    let r = (a_lo ^ a_hi) & (b_lo ^ b_hi);
    let lo = p ^ q;
    let hi = r ^ p;
    lo | (hi << 1)
}

#[inline]
const fn scale_x_t2(a: u8) -> u8 {
    let lo = a & 0x3;
    let hi = (a >> 2) & 0x3;
    let s = scale_x_t1(hi);
    hi | ((lo ^ s) << 2)
}

#[inline]
const fn mul_t2(a: u8, b: u8) -> u8 {
    let a_lo = a & 0x3;
    let a_hi = (a >> 2) & 0x3;
    let b_lo = b & 0x3;
    let b_hi = (b >> 2) & 0x3;
    let p = mul_t1(a_lo, b_lo);
    let q = mul_t1(a_hi, b_hi);
    let r = mul_t1(a_lo ^ a_hi, b_lo ^ b_hi);
    let lo = p ^ q;
    let hi = r ^ p ^ q ^ scale_x_t1(q);
    lo | (hi << 2)
}

#[inline]
const fn scale_x_t3(a: u8) -> u8 {
    let lo = a & 0x0F;
    let hi = (a >> 4) & 0x0F;
    let s = scale_x_t2(hi);
    hi | ((lo ^ s) << 4)
}

#[inline]
const fn mul_t3(a: u8, b: u8) -> u8 {
    let a_lo = a & 0x0F;
    let a_hi = (a >> 4) & 0x0F;
    let b_lo = b & 0x0F;
    let b_hi = (b >> 4) & 0x0F;
    let p = mul_t2(a_lo, b_lo);
    let q = mul_t2(a_hi, b_hi);
    let r = mul_t2(a_lo ^ a_hi, b_lo ^ b_hi);
    let lo = p ^ q;
    let hi = r ^ p ^ q ^ scale_x_t2(q);
    lo | (hi << 4)
}

#[inline]
const fn scale_x_t4(a: u16) -> u16 {
    let lo = (a & 0xFF) as u8;
    let hi = ((a >> 8) & 0xFF) as u8;
    let s = scale_x_t3(hi);
    (hi as u16) | (((lo ^ s) as u16) << 8)
}

#[inline]
const fn mul_t4(a: u16, b: u16) -> u16 {
    let a_lo = (a & 0xFF) as u8;
    let a_hi = ((a >> 8) & 0xFF) as u8;
    let b_lo = (b & 0xFF) as u8;
    let b_hi = ((b >> 8) & 0xFF) as u8;
    let p = mul_t3(a_lo, b_lo);
    let q = mul_t3(a_hi, b_hi);
    let r = mul_t3(a_lo ^ a_hi, b_lo ^ b_hi);
    let lo = p ^ q;
    let hi = r ^ p ^ q ^ scale_x_t3(q);
    (lo as u16) | ((hi as u16) << 8)
}

#[inline]
const fn scale_x_t5(a: u32) -> u32 {
    let lo = (a & 0xFFFF) as u16;
    let hi = ((a >> 16) & 0xFFFF) as u16;
    let s = scale_x_t4(hi);
    (hi as u32) | (((lo ^ s) as u32) << 16)
}

#[inline]
const fn mul_t5(a: u32, b: u32) -> u32 {
    let a_lo = (a & 0xFFFF) as u16;
    let a_hi = ((a >> 16) & 0xFFFF) as u16;
    let b_lo = (b & 0xFFFF) as u16;
    let b_hi = ((b >> 16) & 0xFFFF) as u16;
    let p = mul_t4(a_lo, b_lo);
    let q = mul_t4(a_hi, b_hi);
    let r = mul_t4(a_lo ^ a_hi, b_lo ^ b_hi);
    let lo = p ^ q;
    let hi = r ^ p ^ q ^ scale_x_t4(q);
    (lo as u32) | ((hi as u32) << 16)
}

#[inline]
const fn scale_x_t6(a: u64) -> u64 {
    let lo = (a & 0xFFFF_FFFF) as u32;
    let hi = ((a >> 32) & 0xFFFF_FFFF) as u32;
    let s = scale_x_t5(hi);
    (hi as u64) | (((lo ^ s) as u64) << 32)
}

#[inline]
const fn mul_t6(a: u64, b: u64) -> u64 {
    let a_lo = (a & 0xFFFF_FFFF) as u32;
    let a_hi = ((a >> 32) & 0xFFFF_FFFF) as u32;
    let b_lo = (b & 0xFFFF_FFFF) as u32;
    let b_hi = ((b >> 32) & 0xFFFF_FFFF) as u32;
    let p = mul_t5(a_lo, b_lo);
    let q = mul_t5(a_hi, b_hi);
    let r = mul_t5(a_lo ^ a_hi, b_lo ^ b_hi);
    let lo = p ^ q;
    let hi = r ^ p ^ q ^ scale_x_t5(q);
    (lo as u64) | ((hi as u64) << 32)
}

#[inline]
const fn scale_x_t7(a: u128) -> u128 {
    let lo = (a & 0xFFFF_FFFF_FFFF_FFFF) as u64;
    let hi = ((a >> 64) & 0xFFFF_FFFF_FFFF_FFFF) as u64;
    let s = scale_x_t6(hi);
    (hi as u128) | (((lo ^ s) as u128) << 64)
}

/// Branchless addition (XOR) in `Gf16 = T_2`.
#[inline]
pub const fn gf16_add(a: Gf16, b: Gf16) -> Gf16 {
    Gf16((a.0 ^ b.0) & 0x0F)
}

/// Branchless stratified Karatsuba multiplication in `Gf16 = T_2`.
#[inline]
pub const fn gf16_mul(a: Gf16, b: Gf16) -> Gf16 {
    Gf16(mul_t2(a.0 & 0x0F, b.0 & 0x0F))
}

/// Branchless addition (XOR) in `Gf256 = T_3`.
#[inline]
pub const fn gf256_add(a: Gf256, b: Gf256) -> Gf256 {
    Gf256(a.0 ^ b.0)
}

/// Branchless stratified Karatsuba multiplication in `Gf256 = T_3`.
#[inline]
pub const fn gf256_mul(a: Gf256, b: Gf256) -> Gf256 {
    Gf256(mul_t3(a.0, b.0))
}

/// Pure straight-line branchless Fermat inversion `a^254` in `Gf256` (`0` maps to `0`).
/// Executes 13 `gf256_mul` calls: 7 squarings and 6 additional multiplications,
/// with zero secret-dependent control flow in Rust source.
#[inline]
pub const fn gf256_inv_or_zero(a: Gf256) -> Gf256 {
    let a2 = gf256_mul(a, a);
    let a4 = gf256_mul(a2, a2);
    let a6 = gf256_mul(a4, a2);
    let a8 = gf256_mul(a4, a4);
    let a14 = gf256_mul(a8, a6);
    let a16 = gf256_mul(a8, a8);
    let a32 = gf256_mul(a16, a16);
    let a64 = gf256_mul(a32, a32);
    let a128 = gf256_mul(a64, a64);
    let hi = gf256_mul(gf256_mul(a128, a64), gf256_mul(a32, a16));
    gf256_mul(hi, a14)
}

/// Partial multiplicative inverse in `Gf256^*` for public Shamir denominators (`None` iff `a == 0`).
/// Always executes the full straight-line `gf256_inv_or_zero` Fermat chain unconditionally.
#[inline]
pub const fn gf256_inv(a: Gf256) -> Option<Gf256> {
    let inv = gf256_inv_or_zero(a);
    if inv.0 == 0 {
        None
    } else {
        Some(inv)
    }
}

/// Branchless Frobenius Booleanity residual `x^2 ⊕ x` over `Gf256 = T_3`.
/// Vanishes (`Gf256(0)`) if and only if `x` lies in the prime subfield `GF(2) = {0, 1}`.
#[inline]
pub const fn gf256_frobenius_residual(x: Gf256) -> Gf256 {
    gf256_add(gf256_mul(x, x), x)
}

/// Exact subfield Booleanity predicate `x^2 ⊕ x == 0` over `Gf256 = T_3`.
#[inline]
pub const fn gf256_is_boolean_frobenius(x: Gf256) -> bool {
    gf256_frobenius_residual(x).0 == 0
}

/// Subfield embedding `Gf256 = T_3 -> Tower128 = T_7`.
#[inline]
pub const fn embed_gf256_to_tower128(x: Gf256) -> Tower128 {
    Tower128(x.0 as u128)
}

/// Branchless addition (XOR) in `Tower128 = T_7`.
#[inline]
pub const fn tower128_add(a: Tower128, b: Tower128) -> Tower128 {
    Tower128(a.0 ^ b.0)
}

/// Branchless stratified Karatsuba multiplication in `Tower128 = T_7 = GF(2^128)`.
#[inline]
pub const fn tower128_mul(a: Tower128, b: Tower128) -> Tower128 {
    let a_lo = (a.0 & 0xFFFF_FFFF_FFFF_FFFF) as u64;
    let a_hi = ((a.0 >> 64) & 0xFFFF_FFFF_FFFF_FFFF) as u64;
    let b_lo = (b.0 & 0xFFFF_FFFF_FFFF_FFFF) as u64;
    let b_hi = ((b.0 >> 64) & 0xFFFF_FFFF_FFFF_FFFF) as u64;
    let p = mul_t6(a_lo, b_lo);
    let q = mul_t6(a_hi, b_hi);
    let r = mul_t6(a_lo ^ a_hi, b_lo ^ b_hi);
    let lo = p ^ q;
    let hi = r ^ p ^ q ^ scale_x_t6(q);
    Tower128((lo as u128) | ((hi as u128) << 64))
}

/// Branchless addition (XOR) in `Tower256 = T_8`.
#[inline]
pub const fn tower256_add(a: Tower256, b: Tower256) -> Tower256 {
    Tower256 {
        lo: a.lo ^ b.lo,
        hi: a.hi ^ b.hi,
    }
}

/// Branchless stratified Karatsuba multiplication in `Tower256 = T_8 = GF(2^256)`.
#[inline]
pub const fn tower256_mul(a: Tower256, b: Tower256) -> Tower256 {
    let p = tower128_mul(Tower128(a.lo), Tower128(b.lo)).0;
    let q = tower128_mul(Tower128(a.hi), Tower128(b.hi)).0;
    let r = tower128_mul(Tower128(a.lo ^ a.hi), Tower128(b.lo ^ b.hi)).0;
    Tower256 {
        lo: p ^ q,
        hi: r ^ p ^ q ^ scale_x_t7(q),
    }
}

#[inline]
const fn encode_le_u64(v: u64) -> [u8; 8] {
    [
        (v & 0xFF) as u8,
        ((v >> 8) & 0xFF) as u8,
        ((v >> 16) & 0xFF) as u8,
        ((v >> 24) & 0xFF) as u8,
        ((v >> 32) & 0xFF) as u8,
        ((v >> 40) & 0xFF) as u8,
        ((v >> 48) & 0xFF) as u8,
        ((v >> 56) & 0xFF) as u8,
    ]
}

#[inline]
const fn encode_le_u128(v: u128) -> [u8; 16] {
    [
        (v & 0xFF) as u8,
        ((v >> 8) & 0xFF) as u8,
        ((v >> 16) & 0xFF) as u8,
        ((v >> 24) & 0xFF) as u8,
        ((v >> 32) & 0xFF) as u8,
        ((v >> 40) & 0xFF) as u8,
        ((v >> 48) & 0xFF) as u8,
        ((v >> 56) & 0xFF) as u8,
        ((v >> 64) & 0xFF) as u8,
        ((v >> 72) & 0xFF) as u8,
        ((v >> 80) & 0xFF) as u8,
        ((v >> 88) & 0xFF) as u8,
        ((v >> 96) & 0xFF) as u8,
        ((v >> 104) & 0xFF) as u8,
        ((v >> 112) & 0xFF) as u8,
        ((v >> 120) & 0xFF) as u8,
    ]
}

/// Compute the domain-separated `SHAKE256` commitment over a peer's mask-blinded 2-lane BDOZ
/// batch tag opening (`"QSAG.BDOZ.MAC2L\x01"`).
pub fn bdoz_commit_masked_tag(
    session_id: &[u8; 32],
    round_id: u64,
    masked_sum: Tower128,
    peer_masked_mac_lanes: [Tower128; 2],
    open_nonce: &[u8; 32],
) -> [u8; 32] {
    let domain_tag: [u8; 16] = [
        0x51, 0x53, 0x41, 0x47, 0x2E, 0x42, 0x44, 0x4F, // "QSAG.BDO"
        0x5A, 0x2E, 0x4D, 0x41, 0x43, 0x32, 0x4C, 0x01, // "Z.MAC2L\x01"
    ];
    let round_bytes = encode_le_u64(round_id);
    let sum_bytes = encode_le_u128(masked_sum.0);
    let mac0_bytes = encode_le_u128(peer_masked_mac_lanes[0].0);
    let mac1_bytes = encode_le_u128(peer_masked_mac_lanes[1].0);

    let mut sp = Shake256Sponge::new_shake256();
    sp.absorb(&domain_tag);
    sp.absorb(session_id);
    sp.absorb(&round_bytes);
    sp.absorb(&sum_bytes);
    sp.absorb(&mac0_bytes);
    sp.absorb(&mac1_bytes);
    sp.absorb(open_nonce);
    let mut commit = [0u8; 32];
    sp.squeeze(&mut commit);
    commit
}

/// Fold a batch of wire openings against `mask_value` to obtain the public masked linear combination
/// `mask_value ⊕ ∑_i chal_weight_i * embed(opened_value_i)`.
pub fn bdoz_fold_masked_value(
    mask_value: Tower128,
    openings: &[BdozWireOpening2Lane],
) -> Tower128 {
    let mut acc = mask_value;
    let mut i: usize = 0;
    while i < openings.len() {
        let w = openings[i];
        let x_emb = embed_gf256_to_tower128(w.opened_value);
        acc = tower128_add(acc, tower128_mul(w.chal_weight, x_emb));
        i += 1;
    }
    acc
}

/// Verify a non-empty batch of committed, random-mask-blinded 2-lane `Tower128` BDOZ openings:
/// 1. Explicitly rejects empty slices (`&[] -> false`) and any zero linear-combination weight,
/// 2. Folds `(opened_value_i, key_lanes_i)` under `chal_weight_i` into `(mask_value, mask_key_lanes)`
///    so peer tag openings never expose unmasked `K_i ⊕ alpha * x_i` differences on abort,
/// 3. Verifies the pre-open `SHAKE256` `tag_commitment` in constant time (`ct_eq_bytes32`),
/// 4. Checks `peer_masked_mac_lanes[l] == folded_key[l] ⊕ alpha_lanes[l] * masked_sum` across both lanes.
pub fn verify_mac_2lane(
    alpha_lanes: [Tower128; 2],
    batch: &BdozCommittedBatchOpening2Lane,
    openings: &[BdozWireOpening2Lane],
) -> bool {
    if openings.is_empty() {
        return false;
    }
    let mut weight_ok: u8 = 1;
    let mut masked_sum = batch.mask_value;
    let mut folded_key0 = batch.mask_key_lanes[0];
    let mut folded_key1 = batch.mask_key_lanes[1];
    let mut i: usize = 0;
    while i < openings.len() {
        let w = openings[i];
        if w.chal_weight.0 == 0 {
            weight_ok = 0;
        }
        let x_emb = embed_gf256_to_tower128(w.opened_value);
        masked_sum = tower128_add(masked_sum, tower128_mul(w.chal_weight, x_emb));
        folded_key0 = tower128_add(folded_key0, tower128_mul(w.chal_weight, w.key_lanes[0]));
        folded_key1 = tower128_add(folded_key1, tower128_mul(w.chal_weight, w.key_lanes[1]));
        i += 1;
    }
    let expected_commit = bdoz_commit_masked_tag(
        &batch.session_id,
        batch.round_id,
        masked_sum,
        batch.peer_masked_mac_lanes,
        &batch.open_nonce,
    );
    let commit_ok = ct_eq_bytes32(&expected_commit, &batch.tag_commitment);
    let exp0 = tower128_add(folded_key0, tower128_mul(alpha_lanes[0], masked_sum));
    let exp1 = tower128_add(folded_key1, tower128_mul(alpha_lanes[1], masked_sum));
    let diff0 = batch.peer_masked_mac_lanes[0].0 ^ exp0.0;
    let diff1 = batch.peer_masked_mac_lanes[1].0 ^ exp1.0;
    (weight_ok == 1) && commit_ok && ((diff0 | diff1) == 0)
}

/// Stateful BDOZ batch verification with mandatory single-abort key burn:
/// once `session.burned` is set or any `verify_mac_2lane` call fails, `alpha_lanes` are zeroed
/// and the session permanently rejects all subsequent openings.
pub fn verify_mac_2lane_with_burn(
    session: BdozVerifierSession2Lane,
    batch: &BdozCommittedBatchOpening2Lane,
    openings: &[BdozWireOpening2Lane],
) -> (BdozVerifierSession2Lane, bool) {
    if session.burned {
        return (
            BdozVerifierSession2Lane {
                alpha_lanes: [Tower128(0), Tower128(0)],
                burned: true,
            },
            false,
        );
    }
    let ok = verify_mac_2lane(session.alpha_lanes, batch, openings);
    if ok {
        (session, true)
    } else {
        (
            BdozVerifierSession2Lane {
                alpha_lanes: [Tower128(0), Tower128(0)],
                burned: true,
            },
            false,
        )
    }
}

/// One opening attempt for a caller-provisioned session and round. This handle is
/// neither Clone nor Copy; every attempt consumes its keys, including success.
/// Provisioning unique handles and fresh masks remains the caller's obligation.
pub struct BdozOpeningGuard2Lane {
    alpha_lanes: [Tower128; 2],
    session_id: [u8; 32],
    round_id: u64,
    consumed: bool,
}

impl BdozOpeningGuard2Lane {
    pub const fn new(alpha_lanes: [Tower128; 2], session_id: [u8; 32], round_id: u64) -> Self {
        Self { alpha_lanes, session_id, round_id, consumed: false }
    }

    pub const fn is_consumed(&self) -> bool { self.consumed }

    /// Binds the opening to its provisioned context, checks the actual folded
    /// MAC and commitment, and clears keys before returning the decision.
    pub fn verify_once(
        self,
        batch: &BdozCommittedBatchOpening2Lane,
        openings: &[BdozWireOpening2Lane],
    ) -> (Self, bool) {
        let spent = Self {
            alpha_lanes: [Tower128(0), Tower128(0)],
            session_id: self.session_id,
            round_id: self.round_id,
            consumed: true,
        };
        if self.consumed { return (spent, false); }
        if !ct_eq_bytes32(&self.session_id, &batch.session_id) || self.round_id != batch.round_id {
            return (spent, false);
        }
        let accepted = verify_mac_2lane(self.alpha_lanes, batch, openings);
        (spent, accepted)
    }
}
