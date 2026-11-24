//! Sponge primitives (`Keccak-f[1600]`, `SHAKE256`, `cSHAKE256` with compile-time static
//! midstates `CANOPY_MIDSTATE` and 4-way SIMD `keccak_f1600_x4`, Width-12 `Poseidon2` over
//! `Goldilocks` width-12 and width-24 `Poseidon2` permutations).

use alloc::vec::Vec;

use crate::field::Goldilocks;

// ============================================================================
// 1. Self-Delimiting LEB128 Multi-Field Framing (`encode_multi_frame`)
// ============================================================================

/// Push canonical unsigned LEB128 integer `n` into `out`.
#[inline]
pub fn push_leb128(out: &mut Vec<u8>, n: usize) {
    out.extend_from_slice(&qsag_core::sponge::leb128(n));
}

/// Self-delimiting multi-field byte frame `leb128(fields.len()) || leb128(|f_0|) || f_0 || ...`,
/// matching `Qsag.encodeMultiFrame` (`encodeMultiFrame_injective`).
pub use qsag_core::sponge::encode_multi_frame;

// ============================================================================
// 2. Full 24-Round `Keccak-f[1600]`, `SHAKE256`, and `cSHAKE256`
// ============================================================================

use qsag_core::sponge::keccak::keccak_p1600_lanes;

const SHAKE256_RATE: usize = 136;

pub use qsag_core::sponge::keccak::{keccak_f1600, keccak_p1600_12};

/// Post-prefix sponge state of `cSHAKE256("", input, L, customization)` for a customization
/// of `1..=128` bytes, evaluated at compile time; bit-identical to [`cshake256_into`].
pub use qsag_core::sponge::keccak::cshake256_static_midstate;

/// Canonical `cSHAKE256` customization string for `Hem` Merkle-Canopy leaves, nodes, and salts.
pub const CANOPY_CUSTOM: &[u8] = b"QSAG.PCS.CANOPY/v2";
/// Precomputed compile-time `cSHAKE256` midstate for [`CANOPY_CUSTOM`].
pub const CANOPY_MIDSTATE: [u64; 25] = cshake256_static_midstate(CANOPY_CUSTOM);

/// Canonical `cSHAKE256` customization string for WHIR per-stage Proof-of-Work grinding.
pub const POW_CUSTOM: &[u8] = b"QSAG.PCS.POW2/v1";
/// Precomputed compile-time `cSHAKE256` midstate for [`POW_CUSTOM`].
pub const POW_MIDSTATE: [u64; 25] = cshake256_static_midstate(POW_CUSTOM);

/// Precompute a compile-time 12-round `TurboSHAKE256` customization midstate (`1..=128` byte customization).
pub const fn turboshake256_static_midstate(custom: &[u8]) -> [u64; 25] {
    assert!(!custom.is_empty() && custom.len() <= 128);
    let mut blk = [0u8; SHAKE256_RATE];
    blk[0] = 1;
    blk[1] = SHAKE256_RATE as u8;
    blk[2] = 1;
    blk[3] = 0;
    let bit_len = (custom.len() as u64) * 8;
    let mut p = 4usize;
    if bit_len < 256 {
        blk[p] = 1;
        blk[p + 1] = bit_len as u8;
        p += 2;
    } else {
        blk[p] = 2;
        blk[p + 1] = (bit_len >> 8) as u8;
        blk[p + 2] = (bit_len & 0xFF) as u8;
        p += 3;
    }
    let mut i = 0;
    while i < custom.len() {
        blk[p + i] = custom[i];
        i += 1;
    }
    let mut state = [0u64; 25];
    let mut lane = 0;
    while lane < 17 {
        let mut word = [0u8; 8];
        let mut b = 0;
        while b < 8 {
            word[b] = blk[8 * lane + b];
            b += 1;
        }
        state[lane] = u64::from_le_bytes(word);
        lane += 1;
    }
    qsag_core::sponge::keccak::keccak_p1600_const::<12>(&mut state);
    state
}

/// RFC 9861 `TurboSHAKE256` domain byte (`0x07` in `0x01..=0x7F`, distinct from SHAKE `0x1F` & cSHAKE `0x04`).
const TURBOSHAKE_SUFFIX: u8 = 0x07;

/// Canonical `TurboSHAKE256` customization string for Role-1 outer WHIR Merkle-Canopy commitments.
pub const TURBOSHAKE_CANOPY_CUSTOM: &[u8] = b"QSAG.PCS.TURBOCANOPY/v1";
/// Precomputed compile-time 12-round `TurboSHAKE256` midstate for [`TURBOSHAKE_CANOPY_CUSTOM`].
pub const TURBOSHAKE_CANOPY_MIDSTATE: [u64; 25] =
    turboshake256_static_midstate(TURBOSHAKE_CANOPY_CUSTOM);

/// Canonical `TurboSHAKE256` customization string for Role-1 WHIR Proof-of-Work grinding.
pub const TURBOSHAKE_POW_CUSTOM: &[u8] = b"QSAG.PCS.TURBOPOW/v1";
/// Precomputed compile-time 12-round `TurboSHAKE256` midstate for [`TURBOSHAKE_POW_CUSTOM`].
pub const TURBOSHAKE_POW_MIDSTATE: [u64; 25] = turboshake256_static_midstate(TURBOSHAKE_POW_CUSTOM);

#[inline]
pub fn turboshake256_from_midstate_into(midstate: &[u64; 25], input: &[u8], out: &mut [u8]) {
    let mut state = *midstate;
    let (chunks, rem) = input.as_chunks::<SHAKE256_RATE>();
    for blk in chunks {
        xor_slice_136(&mut state, blk);
        keccak_p1600_12(&mut state);
    }
    let mut block = [0u8; SHAKE256_RATE];
    block[..rem.len()].copy_from_slice(rem);
    block[rem.len()] ^= TURBOSHAKE_SUFFIX;
    block[SHAKE256_RATE - 1] ^= 0x80;
    xor_slice_136(&mut state, &block);
    keccak_p1600_12(&mut state);

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
            keccak_p1600_12(&mut state);
        }
    }
}

#[inline]
pub fn turboshake256_from_midstate_32(midstate: &[u64; 25], input: &[u8]) -> [u8; 32] {
    let mut out = [0u8; 32];
    turboshake256_from_midstate_into(midstate, input, &mut out);
    out
}

#[inline]
fn turboshake256_from_midstate_32_lanes<const N: usize>(
    midstate: &[u64; 25],
    inputs: [&[u8]; N],
) -> [[u8; 32]; N] {
    let min_len = inputs.iter().map(|s| s.len()).min().unwrap_or(0);
    let same_len = inputs.iter().all(|s| s.len() == min_len);
    let mut st = [[0u64; N]; 25];
    for (dst_lane, &ms_val) in st.iter_mut().zip(midstate.iter()) {
        *dst_lane = [ms_val; N];
    }
    let mut off = 0usize;
    while off + SHAKE256_RATE <= min_len {
        for (lane, st_lane) in st.iter_mut().enumerate().take(17) {
            let b = off + 8 * lane;
            for (dst, inp) in st_lane.iter_mut().zip(inputs.iter()) {
                let s = &inp[b..b + 8];
                *dst ^= u64::from_le_bytes([s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7]]);
            }
        }
        keccak_p1600_lanes::<_, 12>(&mut st);
        off += SHAKE256_RATE;
    }
    if !same_len {
        let mut out = [[0u8; 32]; N];
        for (k, inp) in inputs.iter().enumerate() {
            let mut lane_state = [0u64; 25];
            for (lane, st_lane) in st.iter().enumerate() {
                lane_state[lane] = st_lane[k];
            }
            let (chunks, rem) = inp[off..].as_chunks::<SHAKE256_RATE>();
            for blk in chunks {
                xor_slice_136(&mut lane_state, blk);
                keccak_p1600_12(&mut lane_state);
            }
            let mut block = [0u8; SHAKE256_RATE];
            block[..rem.len()].copy_from_slice(rem);
            block[rem.len()] ^= TURBOSHAKE_SUFFIX;
            block[SHAKE256_RATE - 1] ^= 0x80;
            xor_slice_136(&mut lane_state, &block);
            keccak_p1600_12(&mut lane_state);
            for lane in 0..4 {
                out[k][8 * lane..8 * (lane + 1)].copy_from_slice(&lane_state[lane].to_le_bytes());
            }
        }
        return out;
    }
    let rem = min_len - off;
    let mut blocks = [[0u8; SHAKE256_RATE]; N];
    for (blk, inp) in blocks.iter_mut().zip(inputs.iter()) {
        blk[..rem].copy_from_slice(&inp[off..]);
        blk[rem] ^= TURBOSHAKE_SUFFIX;
        blk[SHAKE256_RATE - 1] ^= 0x80;
    }
    for (lane, st_lane) in st.iter_mut().enumerate().take(17) {
        let b = 8 * lane;
        for (dst, blk) in st_lane.iter_mut().zip(blocks.iter()) {
            let s = &blk[b..b + 8];
            *dst ^= u64::from_le_bytes([s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7]]);
        }
    }
    keccak_p1600_lanes::<_, 12>(&mut st);
    let mut out = [[0u8; 32]; N];
    for (lane, st_lane) in st.iter().enumerate().take(4) {
        for (dst, &word) in out.iter_mut().zip(st_lane.iter()) {
            dst[8 * lane..8 * (lane + 1)].copy_from_slice(&word.to_le_bytes());
        }
    }
    out
}

#[inline]
pub fn turboshake256_from_midstate_32_x4(
    midstate: &[u64; 25],
    inputs: [&[u8]; 4],
) -> [[u8; 32]; 4] {
    #[cfg(any(
        target_pointer_width = "64",
        target_feature = "avx2",
        target_feature = "avx512f"
    ))]
    {
        turboshake256_from_midstate_32_lanes::<4>(midstate, inputs)
    }
    #[cfg(not(any(
        target_pointer_width = "64",
        target_feature = "avx2",
        target_feature = "avx512f"
    )))]
    {
        let lo = turboshake256_from_midstate_32_lanes::<2>(midstate, [inputs[0], inputs[1]]);
        let hi = turboshake256_from_midstate_32_lanes::<2>(midstate, [inputs[2], inputs[3]]);
        [lo[0], lo[1], hi[0], hi[1]]
    }
}

#[inline]
pub fn turboshake256_from_midstate_32_x8(
    midstate: &[u64; 25],
    inputs: [&[u8]; 8],
) -> [[u8; 32]; 8] {
    #[cfg(target_feature = "avx512f")]
    {
        turboshake256_from_midstate_32_lanes::<8>(midstate, inputs)
    }
    #[cfg(not(target_feature = "avx512f"))]
    {
        let lo = turboshake256_from_midstate_32_x4(
            midstate,
            [inputs[0], inputs[1], inputs[2], inputs[3]],
        );
        let hi = turboshake256_from_midstate_32_x4(
            midstate,
            [inputs[4], inputs[5], inputs[6], inputs[7]],
        );
        [lo[0], lo[1], lo[2], lo[3], hi[0], hi[1], hi[2], hi[3]]
    }
}

#[inline]
pub fn turboshake256_from_midstate_16_x4(
    midstate: &[u64; 25],
    inputs: [&[u8]; 4],
) -> [[u8; 16]; 4] {
    let full = turboshake256_from_midstate_32_x4(midstate, inputs);
    let mut out = [[0u8; 16]; 4];
    for (dst, src) in out.iter_mut().zip(full.iter()) {
        dst.copy_from_slice(&src[..16]);
    }
    out
}

#[inline]
pub fn turboshake256_from_midstate_16_x8(
    midstate: &[u64; 25],
    inputs: [&[u8]; 8],
) -> [[u8; 16]; 8] {
    let full = turboshake256_from_midstate_32_x8(midstate, inputs);
    let mut out = [[0u8; 16]; 8];
    for (dst, src) in out.iter_mut().zip(full.iter()) {
        dst.copy_from_slice(&src[..16]);
    }
    out
}

#[inline]
fn turboshake256_pow_lanes<const N: usize>(
    midstate: &[u64; 25],
    chal: &[u8; 32],
    base_nonce: u64,
) -> [u64; N] {
    let mut st = [[0u64; N]; 25];
    for (dst_lane, &ms_val) in st.iter_mut().zip(midstate.iter()) {
        *dst_lane = [ms_val; N];
    }
    for (lane, st_lane) in st.iter_mut().enumerate().take(4) {
        let s = &chal[8 * lane..8 * (lane + 1)];
        let w = u64::from_le_bytes([s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7]]);
        for dst in st_lane.iter_mut() {
            *dst ^= w;
        }
    }
    for (k, dst) in st[4].iter_mut().enumerate() {
        *dst ^= base_nonce.wrapping_add(k as u64);
    }
    for dst in &mut st[5] {
        *dst ^= TURBOSHAKE_SUFFIX as u64;
    }
    for dst in &mut st[16] {
        *dst ^= 0x8000_0000_0000_0000;
    }
    keccak_p1600_lanes::<_, 12>(&mut st);
    st[0]
}

#[inline]
pub fn turboshake256_pow_u64_x8(
    midstate: &[u64; 25],
    chal: &[u8; 32],
    base_nonce: u64,
) -> [u64; 8] {
    #[cfg(target_feature = "avx512f")]
    {
        turboshake256_pow_lanes::<8>(midstate, chal, base_nonce)
    }
    #[cfg(all(
        not(target_feature = "avx512f"),
        any(target_pointer_width = "64", target_feature = "avx2")
    ))]
    {
        let lo = turboshake256_pow_lanes::<4>(midstate, chal, base_nonce);
        let hi = turboshake256_pow_lanes::<4>(midstate, chal, base_nonce.wrapping_add(4));
        [lo[0], lo[1], lo[2], lo[3], hi[0], hi[1], hi[2], hi[3]]
    }
    #[cfg(not(any(
        target_pointer_width = "64",
        target_feature = "avx2",
        target_feature = "avx512f"
    )))]
    {
        let a = turboshake256_pow_lanes::<2>(midstate, chal, base_nonce);
        let b = turboshake256_pow_lanes::<2>(midstate, chal, base_nonce.wrapping_add(2));
        let c = turboshake256_pow_lanes::<2>(midstate, chal, base_nonce.wrapping_add(4));
        let d = turboshake256_pow_lanes::<2>(midstate, chal, base_nonce.wrapping_add(6));
        [a[0], a[1], b[0], b[1], c[0], c[1], d[0], d[1]]
    }
}

#[inline]
pub fn turboshake256_pow_u64_single(midstate: &[u64; 25], chal: &[u8; 32], nonce: u64) -> u64 {
    let mut buf = [0u8; 40];
    buf[0..32].copy_from_slice(chal);
    buf[32..40].copy_from_slice(&nonce.to_le_bytes());
    let mut out = [0u8; 8];
    turboshake256_from_midstate_into(midstate, &buf, &mut out);
    u64::from_le_bytes(out)
}

#[inline]
fn absorb_and_squeeze_from_state(mut state: [u64; 25], input: &[u8], suffix: u8, out: &mut [u8]) {
    let (chunks, rem) = input.as_chunks::<SHAKE256_RATE>();
    for blk in chunks {
        xor_slice_136(&mut state, blk);
        keccak_f1600(&mut state);
    }

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
    for blk in prefix_blocks.as_chunks::<SHAKE256_RATE>().0 {
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

/// Evaluate 8 independent 32-byte `cSHAKE256` digests simultaneously from `midstate`
/// using 8-way SIMD `qsag_asm::keccak_f1600_x8` (`AVX-512` ZMM / `2x AVX2` / `2x SHA3-NEON` / portable).
#[inline]
pub fn cshake256_from_midstate_32_x8(midstate: &[u64; 25], inputs: [&[u8]; 8]) -> [[u8; 32]; 8] {
    let min_len = inputs.iter().map(|s| s.len()).min().unwrap_or(0);
    let same_len = inputs.iter().all(|s| s.len() == min_len);

    let mut st = qsag_asm::KeccakState8x([[0u64; 8]; 25]);
    for (dst_lane, &ms_val) in st.0.iter_mut().zip(midstate.iter()) {
        *dst_lane = [ms_val; 8];
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
        qsag_asm::keccak_f1600_x8(&mut st);
        off += SHAKE256_RATE;
    }

    if !same_len {
        let mut out = [[0u8; 32]; 8];
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
    let mut blocks = [[0u8; SHAKE256_RATE]; 8];
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
    qsag_asm::keccak_f1600_x8(&mut st);

    let mut out = [[0u8; 32]; 8];
    for (lane, st_lane) in st.0.iter().enumerate().take(4) {
        for (dst, &word) in out.iter_mut().zip(st_lane.iter()) {
            dst[8 * lane..8 * (lane + 1)].copy_from_slice(&word.to_le_bytes());
        }
    }
    out
}

/// Evaluate 8 independent 16-byte `cSHAKE256` digests simultaneously from `midstate`.
#[inline]
pub fn cshake256_from_midstate_16_x8(midstate: &[u64; 25], inputs: [&[u8]; 8]) -> [[u8; 16]; 8] {
    let full = cshake256_from_midstate_32_x8(midstate, inputs);
    let mut out = [[0u8; 16]; 8];
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

/// Register-only 8-way Proof-of-Work `cSHAKE256(POW_CUSTOM, chal || (base_nonce + k))` (`k in 0..8`),
/// returning the low 64-bit little-endian output word of each of the 8 candidate nonces.
#[inline]
pub fn cshake256_pow_u64_x8(midstate: &[u64; 25], chal: &[u8; 32], base_nonce: u64) -> [u64; 8] {
    let mut st = qsag_asm::KeccakState8x([[0u64; 8]; 25]);
    for (dst_lane, &ms_val) in st.0.iter_mut().zip(midstate.iter()) {
        *dst_lane = [ms_val; 8];
    }
    for lane in 0..4 {
        let s = &chal[8 * lane..8 * (lane + 1)];
        let w = u64::from_le_bytes([s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7]]);
        for k in 0..8 {
            st.0[lane][k] ^= w;
        }
    }
    for k in 0..8 {
        st.0[4][k] ^= base_nonce.wrapping_add(k as u64);
        // Byte 40 is byte 0 of lane 5 (`0x04`); byte 135 is byte 7 of lane 16 (`0x80`).
        st.0[5][k] ^= 0x04;
        st.0[16][k] ^= 0x8000_0000_0000_0000;
    }
    qsag_asm::keccak_f1600_x8(&mut st);
    st.0[0]
}

/// Four consecutive counter-mode blocks at once: lanes `0..4` of
/// `cSHAKE256(customization, seed || le64(counter + k))` for `k in 0..4`, where `midstate`
/// is `cshake256_static_midstate(customization)` and `seed` is given as its four
/// little-endian words. `out[k]` read as little-endian bytes is exactly
/// `cshake256_from_midstate_32(midstate, seed || le64(counter + k))`; the 40-byte input
/// fits one rate block, so this is one 4-way permutation.
#[inline]
pub fn cshake256_seed_counter_words_x4(
    midstate: &[u64; 25],
    seed: &[u64; 4],
    counter: u64,
) -> [[u64; 4]; 4] {
    let mut st = qsag_asm::KeccakState4x([[0u64; 4]; 25]);
    for (dst_lane, &ms_val) in st.0.iter_mut().zip(midstate.iter()) {
        *dst_lane = [ms_val; 4];
    }
    for (lane, &w) in seed.iter().enumerate() {
        for dst in &mut st.0[lane] {
            *dst ^= w;
        }
    }
    for (k, dst) in st.0[4].iter_mut().enumerate() {
        *dst ^= counter.wrapping_add(k as u64);
    }
    // Byte 40 is byte 0 of lane 5 (`0x04`); byte 135 is byte 7 of lane 16 (`0x80`).
    for k in 0..4 {
        st.0[5][k] ^= 0x04;
        st.0[16][k] ^= 0x8000_0000_0000_0000;
    }
    qsag_asm::keccak_f1600_x4(&mut st);
    let out = core::array::from_fn(|k| core::array::from_fn(|lane| st.0[lane][k]));
    for lane in &mut st.0 {
        qsag_asm::volatile_fill(lane, 0u64);
    }
    out
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
        let prefix = qsag_core::sponge::cshake256_customization_prefix(customization);
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

pub use qsag_core::sponge::{
    POSEIDON2_CONST_IV, poseidon2_apply_me, poseidon2_apply_mi, poseidon2_const_at,
    poseidon2_perm12, poseidon2_rc_bijection, poseidon2_sbox7,
};

pub const POSEIDON2_HALF_EXT_ROUNDS: usize =
    qsag_core::sponge::POSEIDON2_HALF_EXTERNAL_ROUNDS as usize;
pub const POSEIDON2_INT_ROUNDS: usize = qsag_core::sponge::POSEIDON2_INTERNAL_ROUNDS as usize;

#[cfg(test)]
fn poseidon2_perm12_layered(st: &mut [Goldilocks; 12]) {
    use qsag_core::sponge::poseidon2::{poseidon2_external_round, poseidon2_internal_round};
    poseidon2_apply_me(st);
    for r in 0..POSEIDON2_HALF_EXT_ROUNDS {
        poseidon2_external_round(0, r as u64, st);
    }
    for r in 0..POSEIDON2_INT_ROUNDS {
        poseidon2_internal_round(r as u64, st);
    }
    for r in 0..POSEIDON2_HALF_EXT_ROUNDS {
        poseidon2_external_round(2, r as u64, st);
    }
}

/// 256-bit `Poseidon2` sponge hash of a byte string (`Qsag.poseidon2Hash32`).
pub use qsag_core::sponge::poseidon2_hash32;

/// Width-24 Goldilocks `Poseidon2-GL-w24` (`rate = 16, capacity = 8`, 7-limb = 448-bit digest)
/// re-exported from `qsag_core::sponge` (`SECURITY.md §V2.10` resolution).
pub use qsag_core::sponge::{
    POSEIDON2_GL24_CAPACITY, POSEIDON2_GL24_DIGEST_LIMBS, POSEIDON2_GL24_HALF_EXTERNAL_ROUNDS,
    POSEIDON2_GL24_INTERNAL_DIAG, POSEIDON2_GL24_INTERNAL_ROUNDS, POSEIDON2_GL24_IV,
    POSEIDON2_GL24_MERKLE_TAG, POSEIDON2_GL24_RATE, POSEIDON2_GL24_RC, POSEIDON2_GL24_SBOX_COUNT,
    POSEIDON2_GL24_WIDTH, Poseidon2Gl24Sponge, Poseidon2State24, goldilocks_shl_small,
    poseidon2_gl24_apply_me, poseidon2_gl24_apply_mi, poseidon2_gl24_compress_merkle,
    poseidon2_gl24_grain_constants, poseidon2_gl24_hash56, poseidon2_gl24_perm,
};

/// Algebraic 256-bit (4-limb) compression `H_comp(left4, right4, tweak4) -> [Goldilocks; 4]`:
/// runs `poseidon2_perm12([left4, right4, tweak4])` with weighted Jive feed-forward `+ left4 + 2*right4 + 4*tweak4` so the
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
    let out = core::array::from_fn(|i| {
        st[i] + in0[i] + in1[i] * Goldilocks::TWO + tweak[i] * Goldilocks::from_u64_reduced(4)
    });
    qsag_asm::volatile_fill(&mut st, Goldilocks::ZERO);
    qsag_asm::volatile_fill(&mut in0, Goldilocks::ZERO);
    out
}

// ============================================================================
// 3B. Algebraic Width-12 Rate-8 `Poseidon2` Canopy Merkle & Limb Sponge
// ============================================================================

/// Pairwise-disjoint canonical `< p` domain tags separating `Poseidon2` Canopy salt derivation,
/// Round-0 single/batch leaves, 2-to-1 internal nodes, and root binding.
pub const P2_DOMAIN_CANOPY_SALT: u64 = 0x5032_434E_534C_5401; // "P2CNSLT\x01"
pub const P2_DOMAIN_CANOPY_LEAF_R0: u64 = 0x5032_434E_4C46_3001; // "P2CNLF0\x01"
pub const P2_DOMAIN_CANOPY_LEAF_BATCH: u64 = 0x5032_434E_4C46_4201; // "P2CNLFB\x01"
/// High 32 bits `"P2ND"` combined via bitwise OR with `node_idx: u32` (`< p` for every `u32`).
pub const P2_DOMAIN_CANOPY_NODE_HI: u64 = 0x5032_4E44_0000_0000; // "P2ND\0\0\0\0"
pub const P2_DOMAIN_CANOPY_ROOT: u64 = 0x5032_434E_524F_4F54; // "P2CNROOT"

pub const P2_DOMAIN_FS_INIT: u64 = 0x5032_4653_494E_4954; // "P2FSINIT"
pub const P2_DOMAIN_FS_BIND_REL: u64 = 0x5032_4653_4252_454C; // "P2FSBREL"
pub const P2_DOMAIN_FS_BIND_INST: u64 = 0x5032_4653_4249_4E53; // "P2FSBINS"
pub const P2_DOMAIN_FS_ABSORB_BYTES: u64 = 0x5032_4653_4142_5954; // "P2FSABYT"
pub const P2_DOMAIN_FS_ABSORB_LIMBS: u64 = 0x5032_4653_414C_4D42; // "P2FSALMB"
pub const P2_DOMAIN_FS_SQUEEZE_BASE: u64 = 0x5032_4653_5351_4253; // "P2FSSQBS"
pub const P2_DOMAIN_FS_SQUEEZE_IDX: u64 = 0x5032_4653_5351_4958; // "P2FSSQIX"
pub const P2_DOMAIN_FS_POW: u64 = 0x5032_4653_504F_5701; // "P2FSPOW\x01"

/// Poseidon2 Proof-of-Work word of `nonce` against the transcript chain state `chain`
/// (`nonce` enters as its two 32-bit halves, each a canonical limb).
#[inline]
pub fn poseidon2_pow_word(chain: [Goldilocks; 4], nonce: u64) -> u64 {
    poseidon2_sponge_hash_limbs(
        P2_DOMAIN_FS_POW,
        chain,
        &[
            Goldilocks::from_u64_reduced(nonce & 0xFFFF_FFFF),
            Goldilocks::from_u64_reduced(nonce >> 32),
        ],
    )[0]
    .to_canonical_u64()
}

/// Encode 4 canonical `Goldilocks` limbs as 32 little-endian bytes.
#[inline]
pub fn limbs4_to_le_bytes32(limbs: [Goldilocks; 4]) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (i, limb) in limbs.iter().enumerate() {
        out[8 * i..8 * (i + 1)].copy_from_slice(&limb.to_le_bytes());
    }
    out
}

/// Decode 32 little-endian bytes into 4 canonical `Goldilocks` limbs (`None` if any word `>= p`).
#[inline]
pub fn bytes32_to_limbs4_le_canonical(bytes: &[u8; 32]) -> Option<[Goldilocks; 4]> {
    let mut out = [Goldilocks::ZERO; 4];
    for (i, dst) in out.iter_mut().enumerate() {
        let mut word = [0u8; 8];
        word.copy_from_slice(&bytes[8 * i..8 * (i + 1)]);
        *dst = Goldilocks::from_le_bytes_canonical(word).ok()?;
    }
    Some(out)
}

/// Injectively frame an arbitrary byte slice as canonical `< p` `Goldilocks` limbs:
/// `[Goldilocks(bytes.len()), pack_le_u56(chunk_0), pack_le_u56(chunk_1), ...]`.
#[inline]
pub fn push_packed_bytes_7_limbs(out: &mut Vec<Goldilocks>, bytes: &[u8]) {
    out.push(Goldilocks::from_u64_reduced(bytes.len() as u64));
    for chunk in bytes.chunks(7) {
        let mut v = 0u64;
        for (i, &b) in chunk.iter().enumerate() {
            v |= (b as u64) << (8 * i);
        }
        out.push(Goldilocks::from_u64_reduced(v));
    }
}

/// Allocating convenience wrapper around [`push_packed_bytes_7_limbs`].
#[inline]
pub fn pack_bytes_7_limbs(bytes: &[u8]) -> Vec<Goldilocks> {
    let mut out = Vec::with_capacity(1 + bytes.len().div_ceil(7));
    push_packed_bytes_7_limbs(&mut out, bytes);
    out
}

/// Domain-separated, length-framed Width-12 Rate-8 `Poseidon2` sponge over `Goldilocks` limbs.
///
/// Initializes capacity `st[8..12] = init_cap` and absorbs the self-delimiting stream
/// `[Goldilocks(domain_tag), Goldilocks(limbs.len())] ++ limbs` in 8-limb rate blocks (zero-padded
/// in the final block), running `poseidon2_perm12` after each block and returning `st[0..4]`.
pub use qsag_core::sponge::poseidon2::poseidon2_sponge_hash_limbs;

/// Derive the per-tree salted capacity key `tree_key` binding a 256-bit `4`-limb `tree_salt`
/// to `(stage_idx, log_leaves)`.
#[inline]
pub fn poseidon2_canopy_tree_key(
    stage_idx: u8,
    log_leaves: u8,
    tree_salt: [Goldilocks; 4],
) -> [Goldilocks; 4] {
    poseidon2_sponge_hash_limbs(
        P2_DOMAIN_CANOPY_SALT,
        tree_salt,
        &[
            Goldilocks::from_u64_reduced(stage_idx as u64),
            Goldilocks::from_u64_reduced(log_leaves as u64),
        ],
    )
}

/// Domain-separated 2-to-1 `Poseidon2` Jive Canopy internal node compression (`1` permutation),
/// binding the 1-indexed binary tree position `node_idx` and salted `tree_key[0..3]`.
#[inline]
pub fn poseidon2_canopy_internal(
    node_idx: u32,
    tree_key: [Goldilocks; 4],
    left: [Goldilocks; 4],
    right: [Goldilocks; 4],
) -> [Goldilocks; 4] {
    poseidon2_compress12_ff(
        left,
        right,
        [
            Goldilocks::from_u64_reduced(P2_DOMAIN_CANOPY_NODE_HI | (node_idx as u64)),
            tree_key[0],
            tree_key[1],
            tree_key[2],
        ],
    )
}

/// Bind a `Poseidon2` Canopy tree's top node `nodes[1]` to `(stage_idx, log_leaves, tree_salt)`.
#[inline]
pub fn poseidon2_canopy_root(
    stage_idx: u8,
    log_leaves: u8,
    tree_salt: [Goldilocks; 4],
    top_node: [Goldilocks; 4],
) -> [Goldilocks; 4] {
    poseidon2_sponge_hash_limbs(
        P2_DOMAIN_CANOPY_ROOT,
        tree_salt,
        &[
            Goldilocks::from_u64_reduced(stage_idx as u64),
            Goldilocks::from_u64_reduced(log_leaves as u64),
            top_node[0],
            top_node[1],
            top_node[2],
            top_node[3],
        ],
    )
}

/// The internal diffusion matrix used here is the one whose invertibility and
/// invariant-subspace properties are established by the unit tests of
/// `qsag_accel::poseidon2` (see `POSEIDON2_INTERNAL_DIAG` there). These tests pin that identity.
#[cfg(test)]
mod internal_matrix_tests {
    use super::*;
    use alloc::vec;
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
            for (row, actual) in base.iter().enumerate() {
                let entry = expected_entry(row, col);
                assert_eq!(actual.to_canonical_u64(), entry, "row {row}, column {col}");
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
    fn permutation_matches_the_qsag_core_specification() {
        for seed in [0u64, 1, 0xFFFF_FFFF_0000_0000, 0x1234_5678_9ABC_DEF0] {
            let mut state: [Goldilocks; 12] = core::array::from_fn(|i| {
                Goldilocks::from_u64_reduced(seed.wrapping_mul(i as u64 + 1).wrapping_add(i as u64))
            });
            let mut spec = state;
            let mut layered = state;
            poseidon2_perm12(&mut state);
            qsag_core::sponge::poseidon2_perm12(&mut spec);
            poseidon2_perm12_layered(&mut layered);
            assert_eq!(state, spec);
            assert_eq!(state, layered);
        }
    }

    /// The raw-word sponge against the lane-by-lane definition, for every payload length that
    /// changes the block layout (empty, partial first block, exact blocks, partial tail).
    #[test]
    fn limb_sponge_matches_layered_definition() {
        let top = crate::field::GOLDILOCKS_PRIME - 1;
        let cap: [Goldilocks; 4] =
            core::array::from_fn(|i| Goldilocks::from_u64_reduced(top - 3 * i as u64));
        for len in 0..=41usize {
            let limbs: Vec<Goldilocks> = (0..len)
                .map(|i| {
                    let x = (i as u64 + 1).wrapping_mul(0x9E37_79B9_7F4A_7C15);
                    Goldilocks::from_u64_reduced(if i % 5 == 0 { top } else { x })
                })
                .collect();
            for domain in [0u64, P2_DOMAIN_CANOPY_LEAF_R0, u64::MAX] {
                let mut st = [Goldilocks::ZERO; 12];
                st[8..].copy_from_slice(&cap);
                let stream: Vec<Goldilocks> = [
                    Goldilocks::from_u64_reduced(domain),
                    Goldilocks::from_u64_reduced(len as u64),
                ]
                .into_iter()
                .chain(limbs.iter().copied())
                .collect();
                for block in stream.chunks(8) {
                    for (lane, &v) in st.iter_mut().zip(block) {
                        *lane += v;
                    }
                    poseidon2_perm12_layered(&mut st);
                }
                assert_eq!(
                    poseidon2_sponge_hash_limbs(domain, cap, &limbs),
                    [st[0], st[1], st[2], st[3]],
                    "len {len}, domain {domain:#x}"
                );
            }
        }
    }

    /// The compression against `perm.b0 + in0 + 2 in1 + 4 tweak` computed lane by lane.
    #[test]
    fn compression_matches_layered_definition() {
        let top = crate::field::GOLDILOCKS_PRIME - 1;
        for seed in [0u64, 1, top, 0x0123_4567_89AB_CDEF] {
            let st: [Goldilocks; 12] = core::array::from_fn(|i| {
                Goldilocks::from_u64_reduced(seed.wrapping_sub(i as u64).wrapping_mul(i as u64 | 1))
            });
            let mut perm = st;
            poseidon2_perm12_layered(&mut perm);
            let four = Goldilocks::from_u64_reduced(4);
            let expected: [Goldilocks; 4] = core::array::from_fn(|i| {
                perm[i] + st[i] + st[4 + i].const_mul(Goldilocks::TWO) + st[8 + i].const_mul(four)
            });
            let got = poseidon2_compress12_ff(
                st[..4].try_into().unwrap(),
                st[4..8].try_into().unwrap(),
                st[8..].try_into().unwrap(),
            );
            assert_eq!(got, expected);
        }
    }

    /// Lanes at the top of the canonical range and long iteration chains exercise every
    /// carry and borrow path of the raw-word kernel.
    #[test]
    fn permutation_kernel_matches_layers_on_extreme_and_iterated_states() {
        let top = crate::field::GOLDILOCKS_PRIME - 1;
        let mut states: Vec<[Goldilocks; 12]> = vec![
            [Goldilocks::from_u64_reduced(top); 12],
            core::array::from_fn(|i| Goldilocks::from_u64_reduced(top - i as u64)),
            core::array::from_fn(|i| Goldilocks::from_u64_reduced(0xFFFF_FFFF << (i % 2 * 32))),
            core::array::from_fn(|i| Goldilocks::from_u64_reduced(u64::from(i == 0) * top)),
        ];
        let mut chain = [Goldilocks::ZERO; 12];
        for _ in 0..2_000 {
            poseidon2_perm12(&mut chain);
            states.push(chain);
        }
        for mut state in states {
            let mut layered = state;
            poseidon2_perm12(&mut state);
            poseidon2_perm12_layered(&mut layered);
            assert_eq!(state, layered);
        }
    }

    #[test]
    #[ignore = "timing probe: run with --ignored --nocapture"]
    fn bench_poseidon2_perm12() {
        const N: u32 = 1_000_000;
        let init: [Goldilocks; 12] =
            core::array::from_fn(|i| Goldilocks::from_u64_reduced(i as u64 + 1));
        let time = |f: &dyn Fn(&mut [Goldilocks; 12])| {
            let mut st = init;
            let t = std::time::Instant::now();
            for _ in 0..N {
                f(&mut st);
            }
            (t.elapsed().as_nanos() as f64 / f64::from(N), st)
        };
        let (agg_ns, a) = time(&|st| poseidon2_perm12(st));
        let (core_ns, c) = time(&|st| qsag_core::sponge::poseidon2_perm12(st));
        assert_eq!(a, c);
        std::println!("PERM12 agg_ns={agg_ns:.1} core_ns={core_ns:.1}");
    }

    #[test]
    fn linear_layers_match_the_qsag_core_specification() {
        let mut state: [Goldilocks; 12] = core::array::from_fn(|i| {
            Goldilocks::from_u64_reduced(0xFFFF_FFFF_0000_0000u64.wrapping_sub(977 * i as u64))
        });
        for _ in 0..8 {
            let (mut me, mut mi) = (state, state);
            let (mut spec_me, mut spec_mi) = (state, state);
            poseidon2_apply_me(&mut me);
            poseidon2_apply_mi(&mut mi);
            qsag_core::sponge::poseidon2_apply_me(&mut spec_me);
            qsag_core::sponge::poseidon2_apply_mi(&mut spec_mi);
            assert_eq!(me, spec_me);
            assert_eq!(mi, spec_mi);
            state = core::array::from_fn(|i| me[i] + mi[(i + 5) % 12]);
        }
    }

    #[test]
    fn keccak_kernel_matches_the_qsag_core_permutation() {
        let mut state: [u64; 25] =
            core::array::from_fn(|i| 0x9E37_79B9_7F4A_7C15u64.wrapping_mul(i as u64 + 1));
        for _ in 0..16 {
            let mut spec = state;
            keccak_f1600(&mut state);
            qsag_core::sponge::keccak_f1600(&mut spec);
            assert_eq!(state, spec);
        }
        assert_eq!(
            cshake256_32(&[b'x'; 200], b"long customization"),
            qsag_core::sponge::cshake256_32(&[b'x'; 200], b"long customization")
        );
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

    #[test]
    fn turboshake256_x1_x4_x8_and_pow_match_bit_for_bit() {
        for len in [0usize, 1, 37, 69, 135, 136, 137, 272, 534] {
            let bufs: [Vec<u8>; 8] = core::array::from_fn(|k| {
                (0..len)
                    .map(|i| ((i * 53 + k * 97 + len * 19) & 0xFF) as u8)
                    .collect()
            });
            let got_x8 = turboshake256_from_midstate_32_x8(
                &TURBOSHAKE_CANOPY_MIDSTATE,
                bufs.each_ref().map(Vec::as_slice),
            );
            let got_x4_lo = turboshake256_from_midstate_32_x4(
                &TURBOSHAKE_CANOPY_MIDSTATE,
                [&bufs[0], &bufs[1], &bufs[2], &bufs[3]],
            );
            let got_x4_hi = turboshake256_from_midstate_32_x4(
                &TURBOSHAKE_CANOPY_MIDSTATE,
                [&bufs[4], &bufs[5], &bufs[6], &bufs[7]],
            );
            let got_16_x8 = turboshake256_from_midstate_16_x8(
                &TURBOSHAKE_CANOPY_MIDSTATE,
                bufs.each_ref().map(Vec::as_slice),
            );
            for k in 0..8 {
                let single = turboshake256_from_midstate_32(&TURBOSHAKE_CANOPY_MIDSTATE, &bufs[k]);
                assert_eq!(got_x8[k], single, "x8 mismatch len={len} lane={k}");
                assert_eq!(got_16_x8[k], single[..16]);
                if k < 4 {
                    assert_eq!(got_x4_lo[k], single);
                } else {
                    assert_eq!(got_x4_hi[k - 4], single);
                }
                assert_ne!(
                    single,
                    cshake256_from_midstate_32(&CANOPY_MIDSTATE, &bufs[k])
                );
            }
        }
        let chal = [0xA5u8; 32];
        let pow8 = turboshake256_pow_u64_x8(&TURBOSHAKE_POW_MIDSTATE, &chal, 1_000);
        for (k, &word) in pow8.iter().enumerate() {
            assert_eq!(
                word,
                turboshake256_pow_u64_single(&TURBOSHAKE_POW_MIDSTATE, &chal, 1_000 + k as u64)
            );
        }
    }
}

#[cfg(test)]
mod canonical_compression_tests {
    use super::*;
    #[test]
    fn weighted_jive_kat() {
        let st: [Goldilocks; 12] = core::array::from_fn(|i| Goldilocks::from_u64_reduced(i as u64));
        let out = poseidon2_compress12_ff(
            st[..4].try_into().unwrap(),
            st[4..8].try_into().unwrap(),
            st[8..].try_into().unwrap(),
        );
        assert_eq!(
            out.map(|x| x.to_canonical_u64()),
            [
                13782584570844608185,
                13136387643152332218,
                7171133015474200873,
                7643370872200861755
            ]
        );
    }
    #[test]
    fn external_layer_matches_dense_kronecker_matrix_in_base() {
        let m4 = [[2, 3, 1, 1], [1, 2, 3, 1], [1, 1, 2, 3], [3, 1, 1, 2]];
        for j in 0..12 {
            let mut st = [Goldilocks::ZERO; 12];
            st[j] = Goldilocks::ONE;
            poseidon2_apply_me(&mut st);
            for i in 0..12 {
                let entry = Goldilocks::from_u64_reduced(
                    m4[i / 3][j / 3] * if i % 3 == j % 3 { 2 } else { 1 },
                );
                assert_eq!(st[i], entry);
            }
        }
    }
    #[test]
    fn seed_counter_words_x4_matches_single_block_cshake256() {
        let midstate = cshake256_static_midstate(b"QSAG.ZKHEM2.COINS/v1");
        let seed_bytes: [u8; 32] = core::array::from_fn(|i| (0xA5u8).wrapping_add(i as u8 * 7));
        let seed_words: [u64; 4] = core::array::from_fn(|lane| {
            u64::from_le_bytes(core::array::from_fn(|b| seed_bytes[8 * lane + b]))
        });
        for base_ctr in [0u64, 1, 17, u64::MAX - 2] {
            let quad = cshake256_seed_counter_words_x4(&midstate, &seed_words, base_ctr);
            for (k, got) in quad.iter().enumerate() {
                let mut input = [0u8; 40];
                input[..32].copy_from_slice(&seed_bytes);
                input[32..].copy_from_slice(&base_ctr.wrapping_add(k as u64).to_le_bytes());
                let want = cshake256_from_midstate_32(&midstate, &input);
                for (lane, &w) in got.iter().enumerate() {
                    assert_eq!(&w.to_le_bytes()[..], &want[8 * lane..8 * (lane + 1)]);
                }
            }
        }
    }
}
