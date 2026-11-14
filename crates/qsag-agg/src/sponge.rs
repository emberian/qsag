//! Sponge primitives (`Keccak-f[1600]`, `SHAKE256`, `cSHAKE256` with compile-time static
//! midstates `CANOPY_MIDSTATE` and 4-way SIMD `keccak_f1600_x4`, Width-12 `Poseidon2` over
//! `Goldilocks` and `GoldilocksExt4`) and compile-time typestate Fenzi
//! instance-bound `FiatShamirTranscript<Phase>`.

use alloc::vec;
use alloc::vec::Vec;
use core::marker::PhantomData;

use crate::field::{Goldilocks, GoldilocksExt4};

// ============================================================================
// 1. Self-Delimiting LEB128 Multi-Field Framing (`encode_multi_frame`)
// ============================================================================

/// Push canonical unsigned LEB128 integer `n` into `out`.
#[inline]
pub fn push_leb128(out: &mut Vec<u8>, mut n: usize) {
    loop {
        if n < 128 {
            out.push(n as u8);
            break;
        } else {
            out.push(0x80 | ((n & 0x7F) as u8));
            n >>= 7;
        }
    }
}

/// Self-delimiting multi-field byte frame `leb128(fields.len()) || leb128(|f_0|) || f_0 || ...`,
/// matching `Qsag.encodeMultiFrame` (`encodeMultiFrame_injective`).
pub fn encode_multi_frame(fields: &[&[u8]]) -> Vec<u8> {
    let total_payload: usize = fields.iter().map(|f| f.len() + 2).sum();
    let mut out = Vec::with_capacity(4 + total_payload);
    push_leb128(&mut out, fields.len());
    for f in fields {
        push_leb128(&mut out, f.len());
        out.extend_from_slice(f);
    }
    out
}

// ============================================================================
// 2. Full 24-Round `Keccak-f[1600]`, `SHAKE256`, and `cSHAKE256`
// ============================================================================

const KECCAK_RC: [u64; 24] = [
    0x0000_0000_0000_0001,
    0x0000_0000_0000_8082,
    0x8000_0000_0000_808A,
    0x8000_0000_8000_8000,
    0x0000_0000_0000_808B,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8009,
    0x0000_0000_0000_008A,
    0x0000_0000_0000_0088,
    0x0000_0000_8000_8009,
    0x0000_0000_8000_000A,
    0x0000_0000_8000_808B,
    0x8000_0000_0000_008B,
    0x8000_0000_0000_8089,
    0x8000_0000_0000_8003,
    0x8000_0000_0000_8002,
    0x8000_0000_0000_0080,
    0x0000_0000_0000_800A,
    0x8000_0000_8000_000A,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8080,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8008,
];

const KECCAK_ROT: [u32; 25] = [
    0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14,
];

const KECCAK_PI: [usize; 25] = [
    0, 6, 12, 18, 24, 3, 9, 10, 16, 22, 1, 7, 13, 19, 20, 4, 5, 11, 17, 23, 2, 8, 14, 15, 21,
];

const SHAKE256_RATE: usize = 136;

/// Full 24-round `Keccak-f[1600]` permutation (usable in both `const` evaluation and runtime).
#[inline(always)]
pub const fn keccak_f1600(state: &mut [u64; 25]) {
    let mut r = 0usize;
    while r < 24 {
        let rc = KECCAK_RC[r];
        let c0 = state[0] ^ state[5] ^ state[10] ^ state[15] ^ state[20];
        let c1 = state[1] ^ state[6] ^ state[11] ^ state[16] ^ state[21];
        let c2 = state[2] ^ state[7] ^ state[12] ^ state[17] ^ state[22];
        let c3 = state[3] ^ state[8] ^ state[13] ^ state[18] ^ state[23];
        let c4 = state[4] ^ state[9] ^ state[14] ^ state[19] ^ state[24];

        let d0 = c4 ^ c1.rotate_left(1);
        let d1 = c0 ^ c2.rotate_left(1);
        let d2 = c1 ^ c3.rotate_left(1);
        let d3 = c2 ^ c4.rotate_left(1);
        let d4 = c3 ^ c0.rotate_left(1);

        let mut y_step = 0usize;
        while y_step < 25 {
            state[y_step] ^= d0;
            state[y_step + 1] ^= d1;
            state[y_step + 2] ^= d2;
            state[y_step + 3] ^= d3;
            state[y_step + 4] ^= d4;
            y_step += 5;
        }

        let mut b = [0u64; 25];
        let mut i = 0usize;
        while i < 25 {
            let src = KECCAK_PI[i];
            b[i] = state[src].rotate_left(KECCAK_ROT[src]);
            i += 1;
        }

        y_step = 0;
        while y_step < 25 {
            state[y_step] = b[y_step] ^ ((!b[y_step + 1]) & b[y_step + 2]);
            state[y_step + 1] = b[y_step + 1] ^ ((!b[y_step + 2]) & b[y_step + 3]);
            state[y_step + 2] = b[y_step + 2] ^ ((!b[y_step + 3]) & b[y_step + 4]);
            state[y_step + 3] = b[y_step + 3] ^ ((!b[y_step + 4]) & b[y_step]);
            state[y_step + 4] = b[y_step + 4] ^ ((!b[y_step]) & b[y_step + 1]);
            y_step += 5;
        }
        state[0] ^= rc;
        r += 1;
    }
}

/// Precompute the post-prefix 1600-bit sponge state for NIST SP 800-185
/// `cSHAKE256("", input, L, customization)` at compile time (`1 <= customization.len() <= 128`),
/// eliminating the redundant static-prefix `keccak_f1600` call across millions of Merkle/transcript
/// hashes while remaining 100% bit-for-bit identical to [`cshake256_into`].
pub const fn cshake256_static_midstate(customization: &[u8]) -> [u64; 25] {
    assert!(
        !customization.is_empty() && customization.len() <= 128,
        "cshake256_static_midstate requires 1..=128 byte customization"
    );
    let mut pad_blk = [0u8; SHAKE256_RATE];
    // `left_encode(136)` = `[1, 136]`, `encode_string("")` = `[1, 0]`
    pad_blk[0] = 1;
    pad_blk[1] = SHAKE256_RATE as u8;
    pad_blk[2] = 1;
    pad_blk[3] = 0;
    let bit_len = (customization.len() as u64) * 8;
    let mut p = 4usize;
    if bit_len < 256 {
        pad_blk[p] = 1;
        pad_blk[p + 1] = bit_len as u8;
        p += 2;
    } else {
        pad_blk[p] = 2;
        pad_blk[p + 1] = (bit_len >> 8) as u8;
        pad_blk[p + 2] = (bit_len & 0xFF) as u8;
        p += 3;
    }
    let mut idx = 0usize;
    while idx < customization.len() {
        pad_blk[p + idx] = customization[idx];
        idx += 1;
    }

    let mut state = [0u64; 25];
    let mut lane = 0usize;
    while lane < 17 {
        let base = 8 * lane;
        state[lane] = u64::from_le_bytes([
            pad_blk[base],
            pad_blk[base + 1],
            pad_blk[base + 2],
            pad_blk[base + 3],
            pad_blk[base + 4],
            pad_blk[base + 5],
            pad_blk[base + 6],
            pad_blk[base + 7],
        ]);
        lane += 1;
    }
    keccak_f1600(&mut state);
    state
}

/// Canonical `cSHAKE256` customization string for `Hem` Merkle-Canopy leaves, nodes, and salts.
pub const CANOPY_CUSTOM: &[u8] = b"QSAG.PCS.CANOPY/v2";
/// Precomputed compile-time `cSHAKE256` midstate for [`CANOPY_CUSTOM`].
pub const CANOPY_MIDSTATE: [u64; 25] = cshake256_static_midstate(CANOPY_CUSTOM);

/// Canonical `cSHAKE256` customization string for WHIR per-stage Proof-of-Work grinding.
pub const POW_CUSTOM: &[u8] = b"QSAG.PCS.POW2/v1";
/// Precomputed compile-time `cSHAKE256` midstate for [`POW_CUSTOM`].
pub const POW_MIDSTATE: [u64; 25] = cshake256_static_midstate(POW_CUSTOM);

#[inline]
fn absorb_and_squeeze_from_state(mut state: [u64; 25], input: &[u8], suffix: u8, out: &mut [u8]) {
    let mut chunks = input.chunks_exact(SHAKE256_RATE);
    for blk in &mut chunks {
        xor_slice_136(&mut state, blk);
        keccak_f1600(&mut state);
    }

    let rem = chunks.remainder();
    let mut block = [0u8; SHAKE256_RATE];
    block[..rem.len()].copy_from_slice(rem);
    block[rem.len()] ^= suffix;
    block[SHAKE256_RATE - 1] ^= 0x80;
    xor_slice_136(&mut state, &block);
    keccak_f1600(&mut state);

    let mut written = 0usize;
    while written < out.len() {
        let rem_out = out.len() - written;
        if rem_out <= 32 {
            for (lane, &lane_val) in state.iter().enumerate().take(4) {
                let start = written + 8 * lane;
                if start >= out.len() {
                    break;
                }
                let lb = lane_val.to_le_bytes();
                let take = (out.len() - start).min(8);
                out[start..start + take].copy_from_slice(&lb[..take]);
            }
            break;
        }
        let mut rate_bytes = [0u8; SHAKE256_RATE];
        for lane in 0..17 {
            rate_bytes[8 * lane..8 * (lane + 1)].copy_from_slice(&state[lane].to_le_bytes());
        }
        let take = rem_out.min(SHAKE256_RATE);
        out[written..written + take].copy_from_slice(&rate_bytes[..take]);
        written += take;
        if written < out.len() {
            keccak_f1600(&mut state);
        }
    }
}

#[inline]
fn absorb_and_squeeze_keccak(prefix_blocks: &[u8], input: &[u8], suffix: u8, out: &mut [u8]) {
    debug_assert_eq!(prefix_blocks.len() % SHAKE256_RATE, 0);
    let mut state = [0u64; 25];
    for blk in prefix_blocks.chunks_exact(SHAKE256_RATE) {
        xor_slice_136(&mut state, blk);
        keccak_f1600(&mut state);
    }
    absorb_and_squeeze_from_state(state, input, suffix, out);
}

/// Evaluate `cSHAKE256("", input, 8 * out.len(), customization)` directly from its precomputed
/// compile-time `midstate` (`cshake256_static_midstate(customization)`).
#[inline]
pub fn cshake256_from_midstate_into(midstate: &[u64; 25], input: &[u8], out: &mut [u8]) {
    absorb_and_squeeze_from_state(*midstate, input, 0x04, out);
}

/// Evaluate 32-byte `cSHAKE256` directly from a precomputed compile-time `midstate`.
#[inline]
pub fn cshake256_from_midstate_32(midstate: &[u64; 25], input: &[u8]) -> [u8; 32] {
    let mut out = [0u8; 32];
    cshake256_from_midstate_into(midstate, input, &mut out);
    out
}

/// Evaluate 4 independent 32-byte `cSHAKE256` digests simultaneously from `midstate`
/// using 4-way SIMD `qsag_asm::keccak_f1600_x4` (`AVX2` / `SHA3-NEON` / portable).
#[inline]
pub fn cshake256_from_midstate_32_x4(midstate: &[u64; 25], inputs: [&[u8]; 4]) -> [[u8; 32]; 4] {
    let len = inputs[0].len();
    if inputs.iter().any(|input| input.len() != len) {
        return inputs.map(|input| cshake256_from_midstate_32(midstate, input));
    }

    let mut st = qsag_asm::KeccakState4x([[0u64; 4]; 25]);
    for (dst_lane, &ms_val) in st.0.iter_mut().zip(midstate.iter()) {
        *dst_lane = [ms_val; 4];
    }

    let mut off = 0usize;
    while off + SHAKE256_RATE <= len {
        for (lane, st_lane) in st.0.iter_mut().enumerate().take(17) {
            let b = off + 8 * lane;
            for (dst, inp) in st_lane.iter_mut().zip(inputs.iter()) {
                let s = &inp[b..b + 8];
                *dst ^= u64::from_le_bytes([s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7]]);
            }
        }
        qsag_asm::keccak_f1600_x4(&mut st);
        off += SHAKE256_RATE;
    }

    let rem = len - off;
    let mut blocks = [[0u8; SHAKE256_RATE]; 4];
    for (blk, inp) in blocks.iter_mut().zip(inputs.iter()) {
        blk[..rem].copy_from_slice(&inp[off..]);
        blk[rem] ^= 0x04;
        blk[SHAKE256_RATE - 1] ^= 0x80;
    }
    for (lane, st_lane) in st.0.iter_mut().enumerate().take(17) {
        let b = 8 * lane;
        for (dst, blk) in st_lane.iter_mut().zip(blocks.iter()) {
            let s = &blk[b..b + 8];
            *dst ^= u64::from_le_bytes([s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7]]);
        }
    }
    qsag_asm::keccak_f1600_x4(&mut st);

    let mut out = [[0u8; 32]; 4];
    for lane in 0..4 {
        for k in 0..4 {
            out[k][8 * lane..8 * (lane + 1)].copy_from_slice(&st.0[lane][k].to_le_bytes());
        }
    }
    out
}

/// Evaluate 4 independent 16-byte `cSHAKE256` digests simultaneously from `midstate`.
#[inline]
pub fn cshake256_from_midstate_16_x4(midstate: &[u64; 25], inputs: [&[u8]; 4]) -> [[u8; 16]; 4] {
    let full = cshake256_from_midstate_32_x4(midstate, inputs);
    let mut out = [[0u8; 16]; 4];
    for k in 0..4 {
        out[k].copy_from_slice(&full[k][..16]);
    }
    out
}

/// Register-only 4-way Proof-of-Work `cSHAKE256(POW_CUSTOM, chal || (base_nonce + k))` (`k in 0..4`),
/// returning the low 64-bit little-endian output word of each of the 4 candidate nonces.
#[inline]
pub fn cshake256_pow_u64_x4(midstate: &[u64; 25], chal: &[u8; 32], base_nonce: u64) -> [u64; 4] {
    let mut st = qsag_asm::KeccakState4x([[0u64; 4]; 25]);
    for (dst_lane, &ms_val) in st.0.iter_mut().zip(midstate.iter()) {
        *dst_lane = [ms_val; 4];
    }
    for lane in 0..4 {
        let s = &chal[8 * lane..8 * (lane + 1)];
        let w = u64::from_le_bytes([s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7]]);
        st.0[lane] = [
            st.0[lane][0] ^ w,
            st.0[lane][1] ^ w,
            st.0[lane][2] ^ w,
            st.0[lane][3] ^ w,
        ];
    }
    st.0[4][0] ^= base_nonce;
    st.0[4][1] ^= base_nonce.wrapping_add(1);
    st.0[4][2] ^= base_nonce.wrapping_add(2);
    st.0[4][3] ^= base_nonce.wrapping_add(3);
    // Byte 40 is byte 0 of lane 5 (`0x04`); byte 135 is byte 7 of lane 16 (`0x80`).
    for k in 0..4 {
        st.0[5][k] ^= 0x04;
        st.0[16][k] ^= 0x8000_0000_0000_0000;
    }
    qsag_asm::keccak_f1600_x4(&mut st);
    st.0[0]
}

/// Single-nonce verifier counterpart to [`cshake256_pow_u64_x4`].
#[inline]
pub fn cshake256_pow_u64_single(midstate: &[u64; 25], chal: &[u8; 32], nonce: u64) -> u64 {
    let mut buf = [0u8; 40];
    buf[0..32].copy_from_slice(chal);
    buf[32..40].copy_from_slice(&nonce.to_le_bytes());
    let mut out = [0u8; 8];
    cshake256_from_midstate_into(midstate, &buf, &mut out);
    u64::from_le_bytes(out)
}

#[inline(always)]
fn xor_slice_136(state: &mut [u64; 25], block: &[u8]) {
    for lane in 0..17 {
        let mut b = [0u8; 8];
        b.copy_from_slice(&block[8 * lane..8 * (lane + 1)]);
        state[lane] ^= u64::from_le_bytes(b);
    }
}

fn sp800_185_left_encode(mut val: u64) -> Vec<u8> {
    if val == 0 {
        return vec![1u8, 0u8];
    }
    let mut rev = Vec::with_capacity(8);
    while val > 0 {
        rev.push((val & 0xFF) as u8);
        val >>= 8;
    }
    rev.reverse();
    let mut out = Vec::with_capacity(1 + rev.len());
    out.push(rev.len() as u8);
    out.extend_from_slice(&rev);
    out
}

fn sp800_185_encode_string(s: &[u8]) -> Vec<u8> {
    let bit_len = (s.len() as u64) * 8;
    let mut out = sp800_185_left_encode(bit_len);
    out.extend_from_slice(s);
    out
}

fn sp800_185_bytepad(data: &[u8], width: usize) -> Vec<u8> {
    let mut out = sp800_185_left_encode(width as u64);
    out.extend_from_slice(data);
    let pad = (width - (out.len() % width)) % width;
    out.resize(out.len() + pad, 0u8);
    out
}

/// NIST FIPS 202 `SHAKE256(input, 8 * out.len())`.
#[inline]
pub fn shake256_into(input: &[u8], out: &mut [u8]) {
    absorb_and_squeeze_keccak(&[], input, 0x1F, out);
}

/// NIST SP 800-185 `cSHAKE256("", input, 8 * out.len(), customization)`.
#[inline]
pub fn cshake256_into(customization: &[u8], input: &[u8], out: &mut [u8]) {
    if customization.is_empty() {
        shake256_into(input, out);
    } else if customization.len() <= 128 {
        // Zero-allocation fast path for short customization strings (`<= 128` bytes fits in 1 rate block):
        let mut pad_blk = [0u8; SHAKE256_RATE];
        // `left_encode(136)` = `[1, 136]`, `encode_string("")` = `[1, 0]`
        pad_blk[0] = 1;
        pad_blk[1] = SHAKE256_RATE as u8;
        pad_blk[2] = 1;
        pad_blk[3] = 0;
        let bit_len = (customization.len() as u64) * 8;
        let mut p = 4usize;
        if bit_len < 256 {
            pad_blk[p] = 1;
            pad_blk[p + 1] = bit_len as u8;
            p += 2;
        } else {
            pad_blk[p] = 2;
            pad_blk[p + 1] = (bit_len >> 8) as u8;
            pad_blk[p + 2] = (bit_len & 0xFF) as u8;
            p += 3;
        }
        pad_blk[p..p + customization.len()].copy_from_slice(customization);
        absorb_and_squeeze_keccak(&pad_blk, input, 0x04, out);
    } else {
        let mut s = sp800_185_encode_string(&[]);
        s.extend_from_slice(&sp800_185_encode_string(customization));
        let prefix = sp800_185_bytepad(&s, SHAKE256_RATE);
        absorb_and_squeeze_keccak(&prefix, input, 0x04, out);
    }
}

/// Canonical 32-byte `cSHAKE256` digest.
#[inline]
pub fn cshake256_32(customization: &[u8], input: &[u8]) -> [u8; 32] {
    let mut out = [0u8; 32];
    cshake256_into(customization, input, &mut out);
    out
}

// ============================================================================
// 3. Width-12 `Poseidon2` over `Goldilocks` and `GoldilocksExt2`
// ============================================================================

/// Domain IV `"POS2_GL1"` (`0x504F_5332_5F47_4C31`), matching `Qsag.poseidon2ConstIV`.
pub const POSEIDON2_CONST_IV: u64 = 0x504F_5332_5F47_4C31;
pub const POSEIDON2_HALF_EXT_ROUNDS: usize = 4;
pub const POSEIDON2_INT_ROUNDS: usize = 22;

#[inline]
pub const fn poseidon2_rc_bijection(x: u64) -> u64 {
    let z0 = x.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let z1 = (z0 ^ (z0 >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    let z2 = (z1 ^ (z1 >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z2 ^ (z2 >> 31)
}

#[inline]
const fn poseidon2_const_compute(tag: u64, round: u64, lane: u64) -> Goldilocks {
    let w = poseidon2_rc_bijection(
        poseidon2_rc_bijection(poseidon2_rc_bijection(POSEIDON2_CONST_IV ^ tag) ^ round) ^ lane,
    );
    Goldilocks::from_u64_reduced(w)
}

const POSEIDON2_RC_EXT0: [[Goldilocks; 12]; POSEIDON2_HALF_EXT_ROUNDS] = {
    let mut tbl = [[Goldilocks::ZERO; 12]; POSEIDON2_HALF_EXT_ROUNDS];
    let mut r = 0;
    while r < POSEIDON2_HALF_EXT_ROUNDS {
        let mut l = 0;
        while l < 12 {
            tbl[r][l] = poseidon2_const_compute(0, r as u64, l as u64);
            l += 1;
        }
        r += 1;
    }
    tbl
};

const POSEIDON2_RC_INT: [Goldilocks; POSEIDON2_INT_ROUNDS] = {
    let mut tbl = [Goldilocks::ZERO; POSEIDON2_INT_ROUNDS];
    let mut r = 0;
    while r < POSEIDON2_INT_ROUNDS {
        tbl[r] = poseidon2_const_compute(1, r as u64, 0);
        r += 1;
    }
    tbl
};

const POSEIDON2_RC_EXT2: [[Goldilocks; 12]; POSEIDON2_HALF_EXT_ROUNDS] = {
    let mut tbl = [[Goldilocks::ZERO; 12]; POSEIDON2_HALF_EXT_ROUNDS];
    let mut r = 0;
    while r < POSEIDON2_HALF_EXT_ROUNDS {
        let mut l = 0;
        while l < 12 {
            tbl[r][l] = poseidon2_const_compute(2, r as u64, l as u64);
            l += 1;
        }
        r += 1;
    }
    tbl
};

#[inline(always)]
pub const fn poseidon2_const_at(tag: u64, round: u64, lane: u64) -> Goldilocks {
    match tag {
        0 if (round as usize) < POSEIDON2_HALF_EXT_ROUNDS && (lane as usize) < 12 => {
            POSEIDON2_RC_EXT0[round as usize][lane as usize]
        }
        1 if (round as usize) < POSEIDON2_INT_ROUNDS && lane == 0 => {
            POSEIDON2_RC_INT[round as usize]
        }
        2 if (round as usize) < POSEIDON2_HALF_EXT_ROUNDS && (lane as usize) < 12 => {
            POSEIDON2_RC_EXT2[round as usize][lane as usize]
        }
        _ => poseidon2_const_compute(tag, round, lane),
    }
}

#[inline(always)]
pub const fn poseidon2_sbox7(x: Goldilocks) -> Goldilocks {
    let x2 = x.const_mul(x);
    let x3 = x2.const_mul(x);
    let x4 = x2.const_mul(x2);
    x3.const_mul(x4)
}

#[inline(always)]
fn apply_m4_base(b: [Goldilocks; 4]) -> [Goldilocks; 4] {
    let s = (b[0] + b[1]) + (b[2] + b[3]);
    [
        s + (b[0] + Goldilocks::TWO * b[1]),
        s + (b[1] + Goldilocks::TWO * b[2]),
        s + (b[2] + Goldilocks::TWO * b[3]),
        s + (b[3] + Goldilocks::TWO * b[0]),
    ]
}

#[inline(always)]
