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

const SHAKE256_RATE: usize = 136;

/// Full 24-round `Keccak-f[1600]` permutation (usable in both `const` evaluation and runtime).
#[inline(always)]
pub const fn keccak_f1600(state: &mut [u64; 25]) {
    let mut s0 = state[0];
    let mut s1 = state[1];
    let mut s2 = state[2];
    let mut s3 = state[3];
    let mut s4 = state[4];
    let mut s5 = state[5];
    let mut s6 = state[6];
    let mut s7 = state[7];
    let mut s8 = state[8];
    let mut s9 = state[9];
    let mut s10 = state[10];
    let mut s11 = state[11];
    let mut s12 = state[12];
    let mut s13 = state[13];
    let mut s14 = state[14];
    let mut s15 = state[15];
    let mut s16 = state[16];
    let mut s17 = state[17];
    let mut s18 = state[18];
    let mut s19 = state[19];
    let mut s20 = state[20];
    let mut s21 = state[21];
    let mut s22 = state[22];
    let mut s23 = state[23];
    let mut s24 = state[24];

    let mut r = 0usize;
    while r < 24 {
        let c0 = s0 ^ s5 ^ s10 ^ s15 ^ s20;
        let c1 = s1 ^ s6 ^ s11 ^ s16 ^ s21;
        let c2 = s2 ^ s7 ^ s12 ^ s17 ^ s22;
        let c3 = s3 ^ s8 ^ s13 ^ s18 ^ s23;
        let c4 = s4 ^ s9 ^ s14 ^ s19 ^ s24;

        let d0 = c4 ^ c1.rotate_left(1);
        let d1 = c0 ^ c2.rotate_left(1);
        let d2 = c1 ^ c3.rotate_left(1);
        let d3 = c2 ^ c4.rotate_left(1);
        let d4 = c3 ^ c0.rotate_left(1);

        s0 ^= d0;
        s5 ^= d0;
        s10 ^= d0;
        s15 ^= d0;
        s20 ^= d0;
        s1 ^= d1;
        s6 ^= d1;
        s11 ^= d1;
        s16 ^= d1;
        s21 ^= d1;
        s2 ^= d2;
        s7 ^= d2;
        s12 ^= d2;
        s17 ^= d2;
        s22 ^= d2;
        s3 ^= d3;
        s8 ^= d3;
        s13 ^= d3;
        s18 ^= d3;
        s23 ^= d3;
        s4 ^= d4;
        s9 ^= d4;
        s14 ^= d4;
        s19 ^= d4;
        s24 ^= d4;

        let b0 = s0;
        let b1 = s6.rotate_left(44);
        let b2 = s12.rotate_left(43);
        let b3 = s18.rotate_left(21);
        let b4 = s24.rotate_left(14);

        let b5 = s3.rotate_left(28);
        let b6 = s9.rotate_left(20);
        let b7 = s10.rotate_left(3);
        let b8 = s16.rotate_left(45);
        let b9 = s22.rotate_left(61);

        let b10 = s1.rotate_left(1);
        let b11 = s7.rotate_left(6);
        let b12 = s13.rotate_left(25);
        let b13 = s19.rotate_left(8);
        let b14 = s20.rotate_left(18);

        let b15 = s4.rotate_left(27);
        let b16 = s5.rotate_left(36);
        let b17 = s11.rotate_left(10);
        let b18 = s17.rotate_left(15);
        let b19 = s23.rotate_left(56);

        let b20 = s2.rotate_left(62);
        let b21 = s8.rotate_left(55);
        let b22 = s14.rotate_left(39);
        let b23 = s15.rotate_left(41);
        let b24 = s21.rotate_left(2);

        s0 = (b0 ^ ((!b1) & b2)) ^ KECCAK_RC[r];
        s1 = b1 ^ ((!b2) & b3);
        s2 = b2 ^ ((!b3) & b4);
        s3 = b3 ^ ((!b4) & b0);
        s4 = b4 ^ ((!b0) & b1);

        s5 = b5 ^ ((!b6) & b7);
        s6 = b6 ^ ((!b7) & b8);
        s7 = b7 ^ ((!b8) & b9);
        s8 = b8 ^ ((!b9) & b5);
        s9 = b9 ^ ((!b5) & b6);

        s10 = b10 ^ ((!b11) & b12);
        s11 = b11 ^ ((!b12) & b13);
        s12 = b12 ^ ((!b13) & b14);
        s13 = b13 ^ ((!b14) & b10);
        s14 = b14 ^ ((!b10) & b11);

        s15 = b15 ^ ((!b16) & b17);
        s16 = b16 ^ ((!b17) & b18);
        s17 = b17 ^ ((!b18) & b19);
        s18 = b18 ^ ((!b19) & b15);
        s19 = b19 ^ ((!b15) & b16);

        s20 = b20 ^ ((!b21) & b22);
        s21 = b21 ^ ((!b22) & b23);
        s22 = b22 ^ ((!b23) & b24);
        s23 = b23 ^ ((!b24) & b20);
        s24 = b24 ^ ((!b20) & b21);

        r += 1;
    }

    state[0] = s0;
    state[1] = s1;
    state[2] = s2;
    state[3] = s3;
    state[4] = s4;
    state[5] = s5;
    state[6] = s6;
    state[7] = s7;
    state[8] = s8;
    state[9] = s9;
    state[10] = s10;
    state[11] = s11;
    state[12] = s12;
    state[13] = s13;
    state[14] = s14;
    state[15] = s15;
    state[16] = s16;
    state[17] = s17;
    state[18] = s18;
    state[19] = s19;
    state[20] = s20;
    state[21] = s21;
    state[22] = s22;
    state[23] = s23;
    state[24] = s24;
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
    let min_len = inputs.iter().map(|s| s.len()).min().unwrap_or(0);
    let same_len = inputs.iter().all(|s| s.len() == min_len);

    let mut st = qsag_asm::KeccakState4x([[0u64; 4]; 25]);
    for (dst_lane, &ms_val) in st.0.iter_mut().zip(midstate.iter()) {
        *dst_lane = [ms_val; 4];
    }

    let mut off = 0usize;
    while off + SHAKE256_RATE <= min_len {
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

    if !same_len {
        let mut out = [[0u8; 32]; 4];
        for (k, inp) in inputs.iter().enumerate() {
            let mut lane_state = [0u64; 25];
            for (lane, st_lane) in st.0.iter().enumerate() {
                lane_state[lane] = st_lane[k];
            }
            absorb_and_squeeze_from_state(lane_state, &inp[off..], 0x04, &mut out[k]);
        }
        return out;
    }

    let rem = min_len - off;
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
    for (lane, st_lane) in st.0.iter().enumerate().take(4) {
        for (dst, &word) in out.iter_mut().zip(st_lane.iter()) {
            dst[8 * lane..8 * (lane + 1)].copy_from_slice(&word.to_le_bytes());
        }
    }
    out
}

/// Evaluate 4 independent 16-byte `cSHAKE256` digests simultaneously from `midstate`.
#[inline]
pub fn cshake256_from_midstate_16_x4(midstate: &[u64; 25], inputs: [&[u8]; 4]) -> [[u8; 16]; 4] {
    let full = cshake256_from_midstate_32_x4(midstate, inputs);
    let mut out = [[0u8; 16]; 4];
    for (dst, src) in out.iter_mut().zip(full.iter()) {
        dst.copy_from_slice(&src[..16]);
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

/// Unrolled 4-lane butterfly for `M_4 = circ(2, 3, 1, 1)` over `Goldilocks` (`9` adds, `0` muls).
#[inline(always)]
fn apply_m4_base(b: [Goldilocks; 4]) -> [Goldilocks; 4] {
    let t01 = b[0] + b[1];
    let t23 = b[2] + b[3];
    let t0123 = t01 + t23;
    let t01123 = t0123 + b[1];
    let t01233 = t0123 + b[3];
    [
        t01123 + t01,
        t01123 + b[2].shl_small::<1>(),
        t01233 + t23,
        t01233 + b[0].shl_small::<1>(),
    ]
}

#[inline(always)]
pub fn poseidon2_apply_me(st: &mut [Goldilocks; 12]) {
    let y0 = apply_m4_base([st[0], st[1], st[2], st[3]]);
    let y1 = apply_m4_base([st[4], st[5], st[6], st[7]]);
    let y2 = apply_m4_base([st[8], st[9], st[10], st[11]]);
    let s0 = (y0[0] + y1[0]) + y2[0];
    let s1 = (y0[1] + y1[1]) + y2[1];
    let s2 = (y0[2] + y1[2]) + y2[2];
    let s3 = (y0[3] + y1[3]) + y2[3];
    st[0] = y0[0] + s0;
    st[1] = y0[1] + s1;
    st[2] = y0[2] + s2;
    st[3] = y0[3] + s3;
    st[4] = y1[0] + s0;
    st[5] = y1[1] + s1;
    st[6] = y1[2] + s2;
    st[7] = y1[3] + s3;
    st[8] = y2[0] + s0;
    st[9] = y2[1] + s1;
    st[10] = y2[2] + s2;
    st[11] = y2[3] + s3;
}

/// Unrolled internal diffusion `M_I = I + diag(-3, 0, 1, 3, ..., 1023) + 1*1^T` (`0` muls:
/// diagonal entries on lanes `0..12` are `-2, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024`).
#[inline(always)]
pub fn poseidon2_apply_mi(st: &mut [Goldilocks; 12]) {
    let s = (((st[0] + st[1]) + (st[2] + st[3])) + ((st[4] + st[5]) + (st[6] + st[7])))
        + ((st[8] + st[9]) + (st[10] + st[11]));
    st[0] = s - st[0].shl_small::<1>();
    st[1] += s;
    st[2] = st[2].shl_small::<1>() + s;
    st[3] = st[3].shl_small::<2>() + s;
    st[4] = st[4].shl_small::<3>() + s;
    st[5] = st[5].shl_small::<4>() + s;
    st[6] = st[6].shl_small::<5>() + s;
    st[7] = st[7].shl_small::<6>() + s;
    st[8] = st[8].shl_small::<7>() + s;
    st[9] = st[9].shl_small::<8>() + s;
    st[10] = st[10].shl_small::<9>() + s;
    st[11] = st[11].shl_small::<10>() + s;
}

#[inline(always)]
pub const fn poseidon2_sbox7_ext4(x: GoldilocksExt4) -> GoldilocksExt4 {
    let x2 = x.square();
    let x3 = x2.const_mul(x);
    let x4 = x2.square();
    x3.const_mul(x4)
}

/// Unrolled 4-lane butterfly for `M_4 = circ(2, 3, 1, 1)` over `GoldilocksExt4` (`0` muls).
#[inline(always)]
fn apply_m4_ext4(b: [GoldilocksExt4; 4]) -> [GoldilocksExt4; 4] {
    let t01 = b[0] + b[1];
    let t23 = b[2] + b[3];
    let t0123 = t01 + t23;
    let t01123 = t0123 + b[1];
    let t01233 = t0123 + b[3];
    [
        t01123 + t01,
        t01123 + b[2].shl_small::<1>(),
        t01233 + t23,
        t01233 + b[0].shl_small::<1>(),
    ]
}

#[inline(always)]
pub fn poseidon2_apply_me_ext4(st: &mut [GoldilocksExt4; 12]) {
    let y0 = apply_m4_ext4([st[0], st[1], st[2], st[3]]);
    let y1 = apply_m4_ext4([st[4], st[5], st[6], st[7]]);
    let y2 = apply_m4_ext4([st[8], st[9], st[10], st[11]]);
    let s0 = (y0[0] + y1[0]) + y2[0];
    let s1 = (y0[1] + y1[1]) + y2[1];
    let s2 = (y0[2] + y1[2]) + y2[2];
    let s3 = (y0[3] + y1[3]) + y2[3];
    st[0] = y0[0] + s0;
    st[1] = y0[1] + s1;
    st[2] = y0[2] + s2;
    st[3] = y0[3] + s3;
    st[4] = y1[0] + s0;
    st[5] = y1[1] + s1;
    st[6] = y1[2] + s2;
    st[7] = y1[3] + s3;
    st[8] = y2[0] + s0;
    st[9] = y2[1] + s1;
    st[10] = y2[2] + s2;
    st[11] = y2[3] + s3;
}

/// Unrolled internal diffusion over `GoldilocksExt4` (`0` muls: shift/add power-of-two diagonal).
#[inline(always)]
pub fn poseidon2_apply_mi_ext4(st: &mut [GoldilocksExt4; 12]) {
    let s = (((st[0] + st[1]) + (st[2] + st[3])) + ((st[4] + st[5]) + (st[6] + st[7])))
        + ((st[8] + st[9]) + (st[10] + st[11]));
    st[0] = s - st[0].shl_small::<1>();
    st[1] += s;
    st[2] = st[2].shl_small::<1>() + s;
    st[3] = st[3].shl_small::<2>() + s;
    st[4] = st[4].shl_small::<3>() + s;
    st[5] = st[5].shl_small::<4>() + s;
    st[6] = st[6].shl_small::<5>() + s;
    st[7] = st[7].shl_small::<6>() + s;
    st[8] = st[8].shl_small::<7>() + s;
    st[9] = st[9].shl_small::<8>() + s;
    st[10] = st[10].shl_small::<9>() + s;
    st[11] = st[11].shl_small::<10>() + s;
}

/// Full 30-round Width-12 `Poseidon2` permutation (`4` ext + `22` int + `4` ext),
/// matching `lean/Qsag/Poseidon2.lean` and `qsag-core` bit-for-bit.
#[inline]
pub fn poseidon2_perm12(st: &mut [Goldilocks; 12]) {
    poseidon2_apply_me(st);
    for round_consts in &POSEIDON2_RC_EXT0 {
        for (x, &rc) in st.iter_mut().zip(round_consts) {
            *x = poseidon2_sbox7(*x + rc);
        }
        poseidon2_apply_me(st);
    }
    for &rc in &POSEIDON2_RC_INT {
        st[0] = poseidon2_sbox7(st[0] + rc);
        poseidon2_apply_mi(st);
    }
    for round_consts in &POSEIDON2_RC_EXT2 {
        for (x, &rc) in st.iter_mut().zip(round_consts) {
            *x = poseidon2_sbox7(*x + rc);
        }
        poseidon2_apply_me(st);
    }
}

/// Zero-allocation streaming 32-byte `Poseidon2` hash (`Qsag.poseidon2Hash32`) with volatile zeroization.
pub fn poseidon2_hash32(msg: &[u8]) -> [u8; 32] {
    let mut st = [Goldilocks::ZERO; 12];
    st[8] = Goldilocks::from_u64_reduced(8);
    st[9] = Goldilocks::from_u64_reduced(4);
    st[10] = Goldilocks::from_u64_reduced(32);
    st[11] = Goldilocks::from_u64_reduced(POSEIDON2_CONST_IV);

    let mut blk = [Goldilocks::ZERO; 8];
    let mut cur_l = 0usize;

    let mut chunks7 = msg.chunks_exact(7);
    for c in &mut chunks7 {
        let v = ((c[0] as u64) << 48)
            | ((c[1] as u64) << 40)
            | ((c[2] as u64) << 32)
            | ((c[3] as u64) << 24)
            | ((c[4] as u64) << 16)
            | ((c[5] as u64) << 8)
            | (c[6] as u64);
        blk[cur_l] = Goldilocks::from_u64_reduced(v);
        cur_l += 1;
        if cur_l == 8 {
            for i in 0..8 {
                st[i] += blk[i];
            }
            poseidon2_perm12(&mut st);
            blk = [Goldilocks::ZERO; 8];
            cur_l = 0;
        }
    }

    let rem = chunks7.remainder();
    let mut last7 = [0u8; 7];
    last7[..rem.len()].copy_from_slice(rem);
    last7[rem.len()] = 0x01;
    let v_last = ((last7[0] as u64) << 48)
        | ((last7[1] as u64) << 40)
        | ((last7[2] as u64) << 32)
        | ((last7[3] as u64) << 24)
        | ((last7[4] as u64) << 16)
        | ((last7[5] as u64) << 8)
        | (last7[6] as u64);
    qsag_asm::volatile_fill(&mut last7, 0);

    blk[cur_l] = Goldilocks::from_u64_reduced(v_last);
    cur_l += 1;
    if cur_l == 8 {
        for i in 0..8 {
            st[i] += blk[i];
        }
        poseidon2_perm12(&mut st);
        blk = [Goldilocks::ZERO; 8];
        cur_l = 0;
    }

    if cur_l == 7 {
        blk[7] = Goldilocks::from_u64_reduced((1u64 << 56) + 1);
    } else {
        blk[cur_l] = Goldilocks::ONE;
        blk[7] = Goldilocks::from_u64_reduced(1u64 << 56);
    }
    for i in 0..8 {
        st[i] += blk[i];
    }
    poseidon2_perm12(&mut st);

    qsag_asm::volatile_fill(&mut blk, Goldilocks::ZERO);

    let mut out = [0u8; 32];
    for (i, limb) in st[..4].iter().enumerate() {
        out[8 * i..8 * (i + 1)].copy_from_slice(&limb.to_canonical_u64().to_be_bytes());
    }
    qsag_asm::volatile_fill(&mut st, Goldilocks::ZERO);
    out
}

/// Algebraic 256-bit (4-limb) compression `H_comp(left4, right4, tweak4) -> [Goldilocks; 4]`:
/// runs `poseidon2_perm12([left4, right4, tweak4])` with Jive/feed-forward `+ left4` so the
/// compression function is non-invertible even though `poseidon2_perm12` is a permutation!
#[inline]
pub fn poseidon2_compress12_ff(
    mut in0: [Goldilocks; 4],
    in1: [Goldilocks; 4],
    tweak: [Goldilocks; 4],
) -> [Goldilocks; 4] {
    let mut st = [
        in0[0], in0[1], in0[2], in0[3], in1[0], in1[1], in1[2], in1[3], tweak[0], tweak[1],
        tweak[2], tweak[3],
    ];
    poseidon2_perm12(&mut st);
    let out = [
        st[0] + in0[0],
        st[1] + in0[1],
        st[2] + in0[2],
        st[3] + in0[3],
    ];
    qsag_asm::volatile_fill(&mut st, Goldilocks::ZERO);
    qsag_asm::volatile_fill(&mut in0, Goldilocks::ZERO);
    out
}

// ============================================================================
// 4. Typestate Fenzi Instance-Bound Fiat–Shamir Transcript
// ============================================================================

/// Transcript phase before binding protocol relation (`squeeze` NOT available).
pub struct Unbound;
/// Transcript phase after binding relation, before binding public instance (`squeeze` NOT available).
pub struct RelationBound;
/// Transcript phase after binding BOTH relation and full public instance (`squeeze` enabled!).
pub struct InstanceBound;

/// Anti-grinding Fiat–Shamir transcript parameterized by compile-time phase `P`.
///
/// Follows Fenzi et al. (`IACR 2025`): challenges cannot be squeezed at compile time until
/// BOTH `.bind_relation(...)` AND `.bind_instance(...)` have been executed on self-delimiting
/// multi-field frames, eliminating weak-Fiat–Shamir last-round grinding attacks.
pub struct FiatShamirTranscript<P> {
    chain_digest: [u8; 32],
    counter: u64,
    _phase: PhantomData<P>,
}

impl<P> Clone for FiatShamirTranscript<P> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            chain_digest: self.chain_digest,
            counter: self.counter,
            _phase: PhantomData,
        }
    }
}

const FS_CUSTOM: &[u8] = b"QSAG.AGG.FS_TRANSCRIPT/v1";
const FS_MIDSTATE: [u64; 25] = cshake256_static_midstate(FS_CUSTOM);

impl FiatShamirTranscript<Unbound> {
    /// Initialize a fresh unbound Fiat–Shamir transcript.
    pub fn new() -> Self {
        let init = cshake256_from_midstate_32(&FS_MIDSTATE, b"INIT");
        Self {
            chain_digest: init,
            counter: 0,
            _phase: PhantomData,
        }
    }

    /// Bind protocol relation identifier & public circuit/WHIR PCS parameters.
    pub fn bind_relation(
        self,
        relation_tag: &[u8],
        params_bytes: &[u8],
        schedule: &crate::pcs::WhirSchedule,
    ) -> FiatShamirTranscript<RelationBound> {
        let mut encoded = schedule.to_bytes();
        encoded.extend_from_slice(&crate::pcs::PCS_POW_BITS.to_le_bytes());
        let frame = encode_multi_frame(&[
            b"BIND_RELATION_HEM_WHIR_EXT4_V5",
            &self.chain_digest,
            relation_tag,
            params_bytes,
            &encoded,
        ]);
        FiatShamirTranscript {
            chain_digest: cshake256_from_midstate_32(&FS_MIDSTATE, &frame),
            counter: 0,
            _phase: PhantomData,
        }
    }
}

impl Default for FiatShamirTranscript<Unbound> {
    fn default() -> Self {
        Self::new()
    }
}

impl FiatShamirTranscript<RelationBound> {
    /// Bind the complete public statement (`committee_root`, `bitmap`, `signing_mode`, `profile`).
    pub fn bind_instance(self, instance_fields: &[&[u8]]) -> FiatShamirTranscript<InstanceBound> {
        let inner = encode_multi_frame(instance_fields);
        let frame = encode_multi_frame(&[b"BIND_INSTANCE", &self.chain_digest, &inner]);
        FiatShamirTranscript {
            chain_digest: cshake256_from_midstate_32(&FS_MIDSTATE, &frame),
            counter: 0,
            _phase: PhantomData,
        }
    }
}

impl FiatShamirTranscript<InstanceBound> {
    /// Absorb a labeled prover message / Merkle-Canopy commitment / polynomial evaluation.
    pub fn absorb(&mut self, label: &[u8], payload: &[u8]) {
        let frame = encode_multi_frame(&[b"ABSORB", &self.chain_digest, label, payload]);
        self.chain_digest = cshake256_from_midstate_32(&FS_MIDSTATE, &frame);
        self.counter = 0;
    }

    /// Absorb an `Ext4` element with canonical 32-byte little-endian framing.
    pub fn absorb_ext4(&mut self, label: &[u8], val: GoldilocksExt4) {
        self.absorb(label, &val.to_le_bytes());
    }

    /// Squeeze an unbiased `Goldilocks` challenge via rejection sampling over 64-bit blocks.
    pub fn squeeze_base(&mut self, label: &[u8]) -> Goldilocks {
        let mut sub_try: u64 = 0;
        loop {
            let ctr_bytes = self.counter.to_le_bytes();
            let try_bytes = sub_try.to_le_bytes();
            let frame = encode_multi_frame(&[
                b"SQUEEZE_F",
                &self.chain_digest,
                label,
                &ctr_bytes,
                &try_bytes,
            ]);
            let mut raw = [0u8; 8];
            cshake256_from_midstate_into(&FS_MIDSTATE, &frame, &mut raw);
            let cand = u64::from_le_bytes(raw);
            if let Some(f) = Goldilocks::from_canonical_u64(cand) {
                self.counter += 1;
                return f;
            }
            sub_try += 1;
        }
    }

    /// Squeeze an unbiased `GoldilocksExt4` challenge ($\ge 255.99$ bits of min-entropy).
    pub fn squeeze_ext4(&mut self, label: &[u8]) -> GoldilocksExt4 {
        let l0 = self.squeeze_base(label);
        let l1 = self.squeeze_base(label);
        let l2 = self.squeeze_base(label);
        let l3 = self.squeeze_base(label);
        GoldilocksExt4::from_limbs([l0, l1, l2, l3])
    }

    /// Squeeze `count` independent `GoldilocksExt4` challenges.
    pub fn squeeze_ext4_vec(&mut self, label: &[u8], count: usize) -> Vec<GoldilocksExt4> {
        (0..count).map(|_| self.squeeze_ext4(label)).collect()
    }

    /// Squeeze `num_queries` uniform indices in `0..half_domain_len` (`half_domain_len` power of 2).
    pub fn squeeze_query_indices(
        &mut self,
        label: &[u8],
        half_domain_len: usize,
        num_queries: usize,
    ) -> Vec<usize> {
        assert!(half_domain_len.is_power_of_two());

        let ctr_bytes = self.counter.to_le_bytes();
        self.counter += 1;
        let frame = encode_multi_frame(&[b"SQUEEZE_IDX", &self.chain_digest, label, &ctr_bytes]);
        let mut raw = vec![0u8; 8 * num_queries];
        cshake256_from_midstate_into(&FS_MIDSTATE, &frame, &mut raw);
        raw.chunks_exact(8)
            .map(|c| {
                let mut b = [0u8; 8];
                b.copy_from_slice(c);
                qsag_whir_verified::canonical_query_group_idx(
                    u64::from_le_bytes(b),
                    half_domain_len as u64,
                )
                .expect("nonempty query domain") as usize
            })
            .collect()
    }

    /// Current transcript binding digest.
    pub fn transcript_digest(&self) -> [u8; 32] {
        self.chain_digest
    }
}

/// The internal diffusion matrix used here is the one whose invertibility and
/// invariant-subspace properties are established by the unit tests of
/// `qsag_accel::poseidon2` (see `POSEIDON2_INTERNAL_DIAG` there). These tests pin that identity.
#[cfg(test)]
mod internal_matrix_tests {
    use super::*;
    use qsag_accel::poseidon2::{POSEIDON2_INTERNAL_DIAG, poseidon2_perm12 as reference_perm12};

    fn expected_entry(row: usize, col: usize) -> u64 {
        let diag = if row == col {
            POSEIDON2_INTERNAL_DIAG[row]
        } else {
            0
        };
        (Goldilocks::ONE + Goldilocks::from_u64_reduced(diag)).to_canonical_u64()
    }

    #[test]
    fn internal_matrix_is_all_ones_plus_the_analysed_diagonal() {
        for col in 0..12 {
            let mut base = [Goldilocks::ZERO; 12];
            base[col] = Goldilocks::ONE;
            poseidon2_apply_mi(&mut base);
            // Both extension-field variants must act as the same matrix on each coordinate.

            let mut ext4 = [GoldilocksExt4::ZERO; 12];
            ext4[col] = GoldilocksExt4::from_limbs([
                Goldilocks::ONE,
                Goldilocks::from_u64_reduced(3),
                Goldilocks::from_u64_reduced(5),
                Goldilocks::from_u64_reduced(11),
            ]);
            poseidon2_apply_mi_ext4(&mut ext4);

            for row in 0..12 {
                let entry = expected_entry(row, col);
                let g_entry = Goldilocks::from_u64_reduced(entry);
                assert_eq!(
                    base[row].to_canonical_u64(),
                    entry,
                    "row {row}, column {col}"
                );
                let limbs = ext4[row].to_limbs();
                assert_eq!(limbs[0], g_entry);
                assert_eq!(limbs[1], g_entry * Goldilocks::from_u64_reduced(3));
                assert_eq!(limbs[2], g_entry * Goldilocks::from_u64_reduced(5));
                assert_eq!(limbs[3], g_entry * Goldilocks::from_u64_reduced(11));
            }
        }
    }

    #[test]
    fn permutation_matches_the_reference_implementation() {
        for seed in [0u64, 1, 0xFFFF_FFFF_0000_0000, 0x1234_5678_9ABC_DEF0] {
            let raw: [u64; 12] =
                core::array::from_fn(|i| seed.wrapping_mul(i as u64 + 1).wrapping_add(i as u64));
            let mut state = raw.map(Goldilocks::from_u64_reduced);
            let mut reference = raw;
            poseidon2_perm12(&mut state);
            reference_perm12(&mut reference);
            assert_eq!(state.map(|x| x.to_canonical_u64()), reference);
        }
    }

    #[test]
    fn unequal_x4_lanes_match_scalar() {
        let data = [0xabu8; 409];
        for lengths in [[0, 17, 136, 205], [409, 272, 135, 1], [136, 0, 137, 271]] {
            let inputs = lengths.map(|len| &data[..len]);
            let expected = inputs.map(|input| cshake256_from_midstate_32(&CANOPY_MIDSTATE, input));
            assert_eq!(
                cshake256_from_midstate_32_x4(&CANOPY_MIDSTATE, inputs),
                expected
            );
            let short = cshake256_from_midstate_16_x4(&CANOPY_MIDSTATE, inputs);
            for lane in 0..4 {
                assert_eq!(short[lane], expected[lane][..16]);
            }
        }
    }

    #[test]
    fn canopy_midstate_and_x4_match_cshake256_bit_for_bit() {
        for len in [0usize, 1, 69, 135, 136, 137, 272, 310] {
            let mut bufs = [
                vec![0u8; len],
                vec![0u8; len],
                vec![0u8; len],
                vec![0u8; len],
            ];
            for (k, b) in bufs.iter_mut().enumerate() {
                for (i, byte) in b.iter_mut().enumerate() {
                    *byte = ((i * 37 + k * 91 + len * 13) & 0xFF) as u8;
                }
            }
            let got_x4 = cshake256_from_midstate_32_x4(
                &CANOPY_MIDSTATE,
                [&bufs[0], &bufs[1], &bufs[2], &bufs[3]],
            );
            for k in 0..4 {
                let exp = cshake256_32(CANOPY_CUSTOM, &bufs[k]);
                let single = cshake256_from_midstate_32(&CANOPY_MIDSTATE, &bufs[k]);
                assert_eq!(single, exp, "midstate single mismatch at len={len}");
                assert_eq!(
                    got_x4[k], exp,
                    "midstate x4 mismatch at len={len}, lane={k}"
                );
            }
        }

        let chal = [0x5Au8; 32];
        let got_pow = cshake256_pow_u64_x4(&POW_MIDSTATE, &chal, 100);
        for k in 0..4u64 {
            let mut raw_in = [0u8; 40];
            raw_in[0..32].copy_from_slice(&chal);
            raw_in[32..40].copy_from_slice(&(100 + k).to_le_bytes());
            let mut ref_out = [0u8; 8];
            cshake256_into(POW_CUSTOM, &raw_in, &mut ref_out);
            let exp_u64 = u64::from_le_bytes(ref_out);
            assert_eq!(got_pow[k as usize], exp_u64);
            assert_eq!(
                cshake256_pow_u64_single(&POW_MIDSTATE, &chal, 100 + k),
                exp_u64
            );
        }
    }
}
