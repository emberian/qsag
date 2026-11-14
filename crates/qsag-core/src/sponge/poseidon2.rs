//! Width-12 Goldilocks `Poseidon2` permutation (`poseidon2_perm12`) and 256-bit sponge
//! (`poseidon2_hash32`), matching `lean/Qsag/Poseidon2.lean` bit-for-bit.
//!
//! Includes the fixed internal-round ordering (`sbox7(st[0] + rc)` BEFORE `apply_mi`) and
//! nothing-up-my-sleeve Stafford-13 round constants anchored at `POSEIDON2_CONST_IV = "POS2_GL1"`.

use alloc::vec::Vec;

use crate::field::goldilocks::Goldilocks;

/// Bijective 64-bit Stafford-13 avalanching step used exclusively to derive public
/// nothing-up-my-sleeve `Poseidon2` round constants from `POSEIDON2_CONST_IV`.
#[inline]
pub const fn poseidon2_rc_bijection(x: u64) -> u64 {
    let z0 = x.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let z1 = (z0 ^ (z0 >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    let z2 = (z1 ^ (z1 >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z2 ^ (z2 >> 31)
}

/// Domain IV of the round-constant generator, ASCII `"POS2_GL1"` (`poseidon2ConstIV`).
pub const POSEIDON2_CONST_IV: u64 = 0x504F_5332_5F47_4C31;

/// External rounds on each side of the internal rounds ($R_F = 8$ total).
pub const POSEIDON2_HALF_EXTERNAL_ROUNDS: u64 = 4;

/// Internal partial rounds ($R_P = 22$).
pub const POSEIDON2_INTERNAL_ROUNDS: u64 = 22;

/// `poseidon2ConstWord`: `(tag, round, lane)` absorbed into `POSEIDON2_CONST_IV`.
#[inline]
pub const fn poseidon2_const_word(tag: u64, round: u64, lane: u64) -> u64 {
    poseidon2_rc_bijection(
        poseidon2_rc_bijection(poseidon2_rc_bijection(POSEIDON2_CONST_IV ^ tag) ^ round) ^ lane,
    )
}

/// `poseidon2ConstAt`: round constant reduced modulo $p$.
#[inline]
pub const fn poseidon2_const_at(tag: u64, round: u64, lane: u64) -> Goldilocks {
    Goldilocks::from_u64_reduced(poseidon2_const_word(tag, round, lane))
}

/// Width-12 sponge state: lanes `0..8` are the rate, lanes `8..12` are the 256-bit capacity.
pub type Poseidon2State12 = [Goldilocks; 12];

/// Monomial S-box $x \mapsto x^7 \bmod p$ via 4 modular multiplications (`gcd(7, p - 1) = 1`).
#[inline]
pub const fn poseidon2_sbox7(x: Goldilocks) -> Goldilocks {
    let x2 = x.const_mul(x);
    let x3 = x2.const_mul(x);
    let x4 = x2.const_mul(x2);
    x3.const_mul(x4)
}

/// `applyM4`: MDS circulant $\text{circ}(2, 3, 1, 1)$ on one 4-lane block.
#[inline]
fn poseidon2_apply_m4(b: [Goldilocks; 4]) -> [Goldilocks; 4] {
    let s = (b[0] + b[1]) + (b[2] + b[3]);
    [
        s + (b[0] + Goldilocks::TWO * b[1]),
        s + (b[1] + Goldilocks::TWO * b[2]),
        s + (b[2] + Goldilocks::TWO * b[3]),
        s + (b[3] + Goldilocks::TWO * b[0]),
    ]
}

/// External MDS layer $M_E = \text{circ}(2 M_4, M_4, M_4)$.
pub fn poseidon2_apply_me(st: &mut Poseidon2State12) {
    let y0 = poseidon2_apply_m4([st[0], st[1], st[2], st[3]]);
    let y1 = poseidon2_apply_m4([st[4], st[5], st[6], st[7]]);
    let y2 = poseidon2_apply_m4([st[8], st[9], st[10], st[11]]);
    for i in 0..4 {
        let s = (y0[i] + y1[i]) + y2[i];
        st[i] = y0[i] + s;
        st[4 + i] = y1[i] + s;
        st[8 + i] = y2[i] + s;
    }
}

/// Internal diffusion layer $M_I = \mathbf{1}\mathbf{1}^T + \text{diag}(-2, 1, 2, 4, \dots, 1024)$.
pub fn poseidon2_apply_mi(st: &mut Poseidon2State12) {
    let mut s = Goldilocks::ZERO;
    for x in st.iter() {
        s += *x;
    }
    st[0] = (Goldilocks::TWO * st[0]).const_neg() + s;
    st[1] += s;
    let mut d = Goldilocks::TWO;
    for x in st.iter_mut().skip(2) {
        *x = d * *x + s;
        d = d + d;
    }
}

/// External round: add 12 round constants, apply $x^7$ to every lane, then apply $M_E$.
pub fn poseidon2_external_round(tag: u64, round: u64, st: &mut Poseidon2State12) {
    for (lane, x) in st.iter_mut().enumerate() {
        *x = poseidon2_sbox7(*x + poseidon2_const_at(tag, round, lane as u64));
    }
    poseidon2_apply_me(st);
}

/// Internal round: add constant to lane `0`, apply $x^7$ to lane `0` only, then apply $M_I$.
pub fn poseidon2_internal_round(round: u64, st: &mut Poseidon2State12) {
    st[0] = poseidon2_sbox7(st[0] + poseidon2_const_at(1, round, 0));
    poseidon2_apply_mi(st);
}

/// Width-12 `Poseidon2` permutation: initial $M_E$, 4 external rounds (`tag = 0`), 22 internal
/// rounds (`tag = 1`), 4 external rounds (`tag = 2`).
pub fn poseidon2_perm12(st: &mut Poseidon2State12) {
    poseidon2_apply_me(st);
    for r in 0..POSEIDON2_HALF_EXTERNAL_ROUNDS {
        poseidon2_external_round(0, r, st);
    }
    for r in 0..POSEIDON2_INTERNAL_ROUNDS {
        poseidon2_internal_round(r, st);
    }
    for r in 0..POSEIDON2_HALF_EXTERNAL_ROUNDS {
        poseidon2_external_round(2, r, st);
    }
}

/// Pack arbitrary byte slice into `< 2^56` Goldilocks limbs (`0x01` delimiter + zero pad to 7-byte
/// boundary), matching `Qsag.bytesToLimbs56`, with zero heap reallocation and deterministic wipe
/// of temporary byte buffers (`[P1-09]`).
pub fn bytes_to_limbs56(msg: &[u8]) -> Vec<Goldilocks> {
    let num_limbs = (msg.len() + 1).div_ceil(7);
    let mut marked: Vec<u8> = Vec::with_capacity(num_limbs * 7);
    marked.extend_from_slice(msg);
    marked.push(0x01);
    while !marked.len().is_multiple_of(7) {
        marked.push(0x00);
    }
    // Reserve +9 extra limbs so `poseidon2_pad` never reallocates `limbs` on the heap!
    let mut out = Vec::with_capacity(num_limbs + 9);
    for chunk in marked.as_chunks::<7>().0 {
        let v = chunk
            .iter()
            .fold(0u64, |acc, &byte| (acc << 8) | (byte as u64));
        out.push(Goldilocks::from_u64_reduced(v));
    }
    crate::wipe::wipe_bytes(&mut marked);
    out
}

/// Pack a fixed 32-byte digest into **5 canonical 56-bit Goldilocks limbs** (`5 * 7 = 35 >= 33` bytes)
/// on the stack (`0` heap allocations, `0` modulo-$p$ wraparound collisions `[P1-02]`).
#[inline]
pub fn pack_bytes32_to_limbs56_canonical(digest: &[u8; 32]) -> [Goldilocks; 5] {
    let mut buf = [0u8; 35];
    buf[0..32].copy_from_slice(digest);
    buf[32] = 0x01;
    let mut out = [Goldilocks::ZERO; 5];
    for i in 0..5 {
        let mut v = 0u64;
        for b in 0..7 {
            v = (v << 8) | (buf[7 * i + b] as u64);
        }
        out[i] = Goldilocks::from_u64_reduced(v);
    }
    crate::wipe::wipe_bytes(&mut buf);
    out
}

/// Multi-rate `10*1` sponge padding (`rate = 8`), matching `Qsag.poseidon2Pad`.
pub fn poseidon2_pad(limbs: &mut Vec<Goldilocks>) {
    let z = (8 - (limbs.len() + 1) % 8) % 8;
    limbs.reserve_exact(z + 2);
    if z == 0 {
        limbs.push(Goldilocks::from_u64_reduced((1u64 << 56) + 1));
    } else {
        limbs.push(Goldilocks::ONE);
        limbs.extend(core::iter::repeat_n(Goldilocks::ZERO, z - 1));
        limbs.push(Goldilocks::from_u64_reduced(1u64 << 56));
    }
}

/// Domain-separated initial Width-12 sponge state: zero rate, capacity `(8, 4, 32, "POS2_GL1")`.
pub const POSEIDON2_INIT_STATE: Poseidon2State12 = {
    let mut st = [Goldilocks::ZERO; 12];
    st[8] = Goldilocks::from_u64_reduced(8);
    st[9] = Goldilocks::from_u64_reduced(4);
    st[10] = Goldilocks::from_u64_reduced(32);
    st[11] = Goldilocks::from_u64_reduced(POSEIDON2_CONST_IV);
    st
};

/// 256-bit algebraic Goldilocks `Poseidon2` sponge hash matching `Qsag.poseidon2Hash32`,
/// deterministically wiping intermediate rate limbs and sponge state before returning (`[P1-09]`).
pub fn poseidon2_hash32(msg: &[u8]) -> [u8; 32] {
    let mut limbs = bytes_to_limbs56(msg);
    poseidon2_pad(&mut limbs);
    let mut st = POSEIDON2_INIT_STATE;
    for block in limbs.as_chunks::<8>().0 {
        for (lane, limb) in block.iter().enumerate() {
            st[lane] += *limb;
        }
        poseidon2_perm12(&mut st);
    }
    crate::wipe::wipe_goldilocks(&mut limbs);
    let mut out = [0u8; 32];
    for lane in 0..4 {
        out[8 * lane..8 * lane + 8].copy_from_slice(&st[lane].to_be_bytes());
    }
    crate::wipe::wipe_goldilocks(&mut st);
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_poseidon2_padding_injectivity_and_determinism() {
        let mut l1 = bytes_to_limbs56(b"abc\x00");
        let mut l2 = bytes_to_limbs56(b"abc");
        poseidon2_pad(&mut l1);
        poseidon2_pad(&mut l2);
        assert_ne!(l1, l2);
        assert_eq!(l1.len() % 8, 0);
        assert_eq!(l2.len() % 8, 0);

        let d1 = poseidon2_hash32(b"abc\x00");
        let d2 = poseidon2_hash32(b"abc");
        assert_ne!(d1, d2);
        assert_eq!(d2, poseidon2_hash32(b"abc"));
    }
}
