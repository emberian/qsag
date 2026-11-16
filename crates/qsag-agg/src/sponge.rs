//! Sponge primitives (`Keccak-f[1600]`, `SHAKE256`, `cSHAKE256` with compile-time static
//! midstates `CANOPY_MIDSTATE` and 4-way SIMD `keccak_f1600_x4`, Width-12 `Poseidon2` over
//! `Goldilocks` and `GoldilocksExt4`) and compile-time typestate Fenzi
//! instance-bound `FiatShamirTranscript<Phase>`.

use alloc::vec;
use alloc::vec::Vec;
use core::marker::PhantomData;

use crate::field::{Goldilocks, GoldilocksExt4, GoldilocksOps as _};

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

use qsag_core::sponge::KECCAK_ROUND_CONSTANTS as KECCAK_RC;

const SHAKE256_RATE: usize = 136;

/// Full 24-round `Keccak-f[1600]` permutation (usable in both `const` evaluation and runtime).
/// This is the unrolled kernel behind the Merkle and transcript hashing of the prover;
/// `qsag_core::sponge::keccak_f1600` is the specification it is tested against.
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

/// RFC 9861 12-round `Keccak-p[1600, 12]` permutation (rounds `12..24` of `KECCAK_RC`).
/// Preserves 256-bit preimage, 128-bit collision, and 128-bit Grover QROM security for Role-1
/// outer WHIR commitments and PoW grinding (zero AIR constraints) at 2x throughput.
#[inline(always)]
pub const fn keccak_p1600_12(state: &mut [u64; 25]) {
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

    let mut r = 12usize;
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

/// Vectorized `N`-way (`N = 4` AVX2/NEON or `N = 8` AVX-512 ZMM) 12-round `Keccak-p[1600, 12]`.
#[inline(always)]
fn keccak_p1600_12_lanes<const N: usize>(st: &mut [[u64; N]; 25]) {
    #[inline(always)]
    fn xor<const N: usize>(a: [u64; N], b: [u64; N]) -> [u64; N] {
        core::array::from_fn(|k| a[k] ^ b[k])
    }
    #[inline(always)]
    fn xor5<const N: usize>(
        a: [u64; N],
        b: [u64; N],
        c: [u64; N],
        d: [u64; N],
        e: [u64; N],
    ) -> [u64; N] {
        core::array::from_fn(|k| a[k] ^ b[k] ^ c[k] ^ d[k] ^ e[k])
    }
    #[inline(always)]
    fn rol<const N: usize, const R: u32>(a: [u64; N]) -> [u64; N] {
        core::array::from_fn(|k| a[k].rotate_left(R))
    }
    #[inline(always)]
    fn chi<const N: usize>(a: [u64; N], b: [u64; N], c: [u64; N]) -> [u64; N] {
        core::array::from_fn(|k| a[k] ^ ((!b[k]) & c[k]))
    }

    for &rc in &KECCAK_RC[12..24] {
        let c0 = xor5(st[0], st[5], st[10], st[15], st[20]);
        let c1 = xor5(st[1], st[6], st[11], st[16], st[21]);
        let c2 = xor5(st[2], st[7], st[12], st[17], st[22]);
        let c3 = xor5(st[3], st[8], st[13], st[18], st[23]);
        let c4 = xor5(st[4], st[9], st[14], st[19], st[24]);

        let d0 = xor(c4, rol::<N, 1>(c1));
        let d1 = xor(c0, rol::<N, 1>(c2));
        let d2 = xor(c1, rol::<N, 1>(c3));
        let d3 = xor(c2, rol::<N, 1>(c4));
        let d4 = xor(c3, rol::<N, 1>(c0));

        for row in [0, 5, 10, 15, 20] {
            st[row] = xor(st[row], d0);
        }
        for row in [1, 6, 11, 16, 21] {
            st[row] = xor(st[row], d1);
        }
        for row in [2, 7, 12, 17, 22] {
            st[row] = xor(st[row], d2);
        }
        for row in [3, 8, 13, 18, 23] {
            st[row] = xor(st[row], d3);
        }
        for row in [4, 9, 14, 19, 24] {
            st[row] = xor(st[row], d4);
        }

        let b0 = st[0];
        let b1 = rol::<N, 44>(st[6]);
        let b2 = rol::<N, 43>(st[12]);
        let b3 = rol::<N, 21>(st[18]);
        let b4 = rol::<N, 14>(st[24]);
        let b5 = rol::<N, 28>(st[3]);
        let b6 = rol::<N, 20>(st[9]);
        let b7 = rol::<N, 3>(st[10]);
        let b8 = rol::<N, 45>(st[16]);
        let b9 = rol::<N, 61>(st[22]);
        let b10 = rol::<N, 1>(st[1]);
        let b11 = rol::<N, 6>(st[7]);
        let b12 = rol::<N, 25>(st[13]);
        let b13 = rol::<N, 8>(st[19]);
        let b14 = rol::<N, 18>(st[20]);
        let b15 = rol::<N, 27>(st[4]);
        let b16 = rol::<N, 36>(st[5]);
        let b17 = rol::<N, 10>(st[11]);
        let b18 = rol::<N, 15>(st[17]);
        let b19 = rol::<N, 56>(st[23]);
        let b20 = rol::<N, 62>(st[2]);
        let b21 = rol::<N, 55>(st[8]);
        let b22 = rol::<N, 39>(st[14]);
        let b23 = rol::<N, 41>(st[15]);
        let b24 = rol::<N, 2>(st[21]);

        let s0 = chi(b0, b1, b2);
        st[0] = core::array::from_fn(|k| s0[k] ^ rc);
        st[1] = chi(b1, b2, b3);
        st[2] = chi(b2, b3, b4);
        st[3] = chi(b3, b4, b0);
        st[4] = chi(b4, b0, b1);
        st[5] = chi(b5, b6, b7);
        st[6] = chi(b6, b7, b8);
        st[7] = chi(b7, b8, b9);
        st[8] = chi(b8, b9, b5);
        st[9] = chi(b9, b5, b6);
        st[10] = chi(b10, b11, b12);
        st[11] = chi(b11, b12, b13);
        st[12] = chi(b12, b13, b14);
        st[13] = chi(b13, b14, b10);
        st[14] = chi(b14, b10, b11);
        st[15] = chi(b15, b16, b17);
        st[16] = chi(b16, b17, b18);
        st[17] = chi(b17, b18, b19);
        st[18] = chi(b18, b19, b15);
        st[19] = chi(b19, b15, b16);
        st[20] = chi(b20, b21, b22);
        st[21] = chi(b21, b22, b23);
        st[22] = chi(b22, b23, b24);
        st[23] = chi(b23, b24, b20);
        st[24] = chi(b24, b20, b21);
    }
}

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
    keccak_p1600_12(&mut state);
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
        keccak_p1600_12_lanes(&mut st);
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
    keccak_p1600_12_lanes(&mut st);
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
    #[cfg(any(target_feature = "avx2", target_feature = "avx512f"))]
    {
        turboshake256_from_midstate_32_lanes::<4>(midstate, inputs)
    }
    #[cfg(not(any(target_feature = "avx2", target_feature = "avx512f")))]
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
    keccak_p1600_12_lanes(&mut st);
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
    #[cfg(all(not(target_feature = "avx512f"), target_feature = "avx2"))]
    {
        let lo = turboshake256_pow_lanes::<4>(midstate, chal, base_nonce);
        let hi = turboshake256_pow_lanes::<4>(midstate, chal, base_nonce.wrapping_add(4));
        [lo[0], lo[1], lo[2], lo[3], hi[0], hi[1], hi[2], hi[3]]
    }
    #[cfg(not(any(target_feature = "avx2", target_feature = "avx512f")))]
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

use qsag_core::sponge::poseidon2_const_at as poseidon2_const_compute;
pub use qsag_core::sponge::{POSEIDON2_CONST_IV, poseidon2_rc_bijection, poseidon2_sbox7};

pub const POSEIDON2_HALF_EXT_ROUNDS: usize = 4;
pub const POSEIDON2_INT_ROUNDS: usize = 22;
const _: () = assert!(
    POSEIDON2_HALF_EXT_ROUNDS as u64 == qsag_core::sponge::POSEIDON2_HALF_EXTERNAL_ROUNDS
        && POSEIDON2_INT_ROUNDS as u64 == qsag_core::sponge::POSEIDON2_INTERNAL_ROUNDS
);

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
    // M4 tensor P3: transpose lanes, apply P3 tensor M4, transpose back.
    *st = [
        st[0], st[3], st[6], st[9], st[1], st[4], st[7], st[10], st[2], st[5], st[8], st[11],
    ];
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
    *st = [
        st[0], st[4], st[8], st[1], st[5], st[9], st[2], st[6], st[10], st[3], st[7], st[11],
    ];
}

/// Unrolled internal diffusion `M_I = I + diag(-3, 0, 1, 3, ..., 1023) + 1*1^T` (`0` muls:
/// diagonal entries on lanes `0..12` are `-64, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024`).
#[inline(always)]
pub fn poseidon2_apply_mi(st: &mut [Goldilocks; 12]) {
    let s = (((st[0] + st[1]) + (st[2] + st[3])) + ((st[4] + st[5]) + (st[6] + st[7])))
        + ((st[8] + st[9]) + (st[10] + st[11]));
    st[0] = s - st[0].shl_small::<6>();
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
    // M4 tensor P3: transpose lanes, apply P3 tensor M4, transpose back.
    *st = [
        st[0], st[3], st[6], st[9], st[1], st[4], st[7], st[10], st[2], st[5], st[8], st[11],
    ];
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
    *st = [
        st[0], st[4], st[8], st[1], st[5], st[9], st[2], st[6], st[10], st[3], st[7], st[11],
    ];
}

/// Unrolled internal diffusion over `GoldilocksExt4` (`0` muls: shift/add power-of-two diagonal).
#[inline(always)]
pub fn poseidon2_apply_mi_ext4(st: &mut [GoldilocksExt4; 12]) {
    let s = (((st[0] + st[1]) + (st[2] + st[3])) + ((st[4] + st[5]) + (st[6] + st[7])))
        + ((st[8] + st[9]) + (st[10] + st[11]));
    st[0] = s - st[0].shl_small::<6>();
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

/// Raw-word kernel of [`poseidon2_perm12`].
///
/// Between layers a lane is any `u64` representative modulo `p`. Each linear layer is
/// accumulated exactly in `u128` (every accumulator stays below `2^75`) together with the next
/// round constants and reduced once per lane; only the final state is canonicalized. The
/// layer-by-layer functions above remain the readable definition, and the tests compare this
/// kernel against them and against the `qsag-core` specification.
mod perm_kernel {
    use super::{POSEIDON2_RC_EXT0, POSEIDON2_RC_EXT2, POSEIDON2_RC_INT};
    use crate::field::GOLDILOCKS_PRIME;

    const EPS: u64 = 0xFFFF_FFFF;
    const ZERO_RC: [u64; 12] = [0; 12];

    const fn words(rc: &[crate::field::Goldilocks; 12]) -> [u64; 12] {
        let mut out = [0u64; 12];
        let mut i = 0;
        while i < 12 {
            out[i] = rc[i].to_canonical_u64();
            i += 1;
        }
        out
    }

    const RC_EXT0: [[u64; 12]; 4] = [
        words(&POSEIDON2_RC_EXT0[0]),
        words(&POSEIDON2_RC_EXT0[1]),
        words(&POSEIDON2_RC_EXT0[2]),
        words(&POSEIDON2_RC_EXT0[3]),
    ];
    const RC_EXT2: [[u64; 12]; 4] = [
        words(&POSEIDON2_RC_EXT2[0]),
        words(&POSEIDON2_RC_EXT2[1]),
        words(&POSEIDON2_RC_EXT2[2]),
        words(&POSEIDON2_RC_EXT2[3]),
    ];
    const RC_INT: [u64; 22] = {
        let mut out = [0u64; 22];
        let mut i = 0;
        while i < 22 {
            out[i] = POSEIDON2_RC_INT[i].to_canonical_u64();
            i += 1;
        }
        out
    };

    /// `x mod p` as some `u64` representative, for `x < 2^96`
    /// (`2^64 = 2^32 - 1 (mod p)`; a carry out of the fold leaves room for one more `EPS`).
    #[inline(always)]
    pub(super) const fn reduce_wide(x: u128) -> u64 {
        let lo = x as u64;
        let hi = (x >> 64) as u64;
        debug_assert!(hi <= EPS);
        let (s, carry) = lo.overflowing_add(hi * EPS);
        s.wrapping_add(EPS & 0u64.wrapping_sub(carry as u64))
    }

    /// `a * b mod p` as some `u64` representative, for arbitrary `u64` representatives
    /// (`2^96 = -1 (mod p)`).
    #[inline(always)]
    const fn mul(a: u64, b: u64) -> u64 {
        let x = (a as u128) * (b as u128);
        let lo = x as u64;
        let hi = (x >> 64) as u64;
        let (t0, borrow) = lo.overflowing_sub(hi >> 32);
        let t0 = t0.wrapping_sub(EPS & 0u64.wrapping_sub(borrow as u64));
        let (r, carry) = t0.overflowing_add((hi & EPS) * EPS);
        r.wrapping_add(EPS & 0u64.wrapping_sub(carry as u64))
    }

    #[inline(always)]
    const fn sbox7(x: u64) -> u64 {
        let x2 = mul(x, x);
        let x3 = mul(x2, x);
        let x4 = mul(x2, x2);
        mul(x3, x4)
    }

    /// `circ(2, 3, 1, 1)` on one block, exact in `u128` (coefficient sum 7).
    #[inline(always)]
    const fn m4(b0: u64, b1: u64, b2: u64, b3: u64) -> [u128; 4] {
        let (b0, b1, b2, b3) = (b0 as u128, b1 as u128, b2 as u128, b3 as u128);
        let t01 = b0 + b1;
        let t23 = b2 + b3;
        let t0123 = t01 + t23;
        let t01123 = t0123 + b1;
        let t01233 = t0123 + b3;
        [
            t01123 + t01,
            t01123 + (b2 << 1),
            t01233 + t23,
            t01233 + (b0 << 1),
        ]
    }

    /// `M_E = M_4 (x) P_3` in the flattened lane order, plus `rc` (coefficient sum 28).
    #[inline(always)]
    const fn external_layer(st: &[u64; 12], rc: &[u64; 12]) -> [u64; 12] {
        let y0 = m4(st[0], st[3], st[6], st[9]);
        let y1 = m4(st[1], st[4], st[7], st[10]);
        let y2 = m4(st[2], st[5], st[8], st[11]);
        let mut out = [0u64; 12];
        let mut i = 0;
        while i < 4 {
            let s = y0[i] + y1[i] + y2[i];
            out[3 * i] = reduce_wide(y0[i] + s + rc[3 * i] as u128);
            out[3 * i + 1] = reduce_wide(y1[i] + s + rc[3 * i + 1] as u128);
            out[3 * i + 2] = reduce_wide(y2[i] + s + rc[3 * i + 2] as u128);
            i += 1;
        }
        out
    }

    /// `M_I = J + diag(-64, 1, 2, 4, ..., 1024)`, plus `rc0` on lane 0.
    #[inline(always)]
    const fn internal_layer(st: &[u64; 12], rc0: u64) -> [u64; 12] {
        let mut s = 0u128;
        let mut i = 0;
        while i < 12 {
            s += st[i] as u128;
            i += 1;
        }
        let mut out = [0u64; 12];
        // `-64 x = 64 (2p - x) (mod p)`, and `x <= 2^64 - 1 < 2p`.
        let neg = ((2 * GOLDILOCKS_PRIME as u128) - st[0] as u128) << 6;
        out[0] = reduce_wide(s + neg + rc0 as u128);
        out[1] = reduce_wide(s + st[1] as u128);
        let mut i = 2;
        while i < 12 {
            out[i] = reduce_wide(s + ((st[i] as u128) << (i - 1)));
            i += 1;
        }
        out
    }

    #[inline(always)]
    pub(super) const fn permute(input: &[u64; 12]) -> [u64; 12] {
        let mut st = external_layer(input, &RC_EXT0[0]);
        let mut r = 0;
        while r < 4 {
            let mut i = 0;
            while i < 12 {
                st[i] = sbox7(st[i]);
                i += 1;
            }
            st = if r < 3 {
                external_layer(&st, &RC_EXT0[r + 1])
            } else {
                let mut rc = ZERO_RC;
                rc[0] = RC_INT[0];
                external_layer(&st, &rc)
            };
            r += 1;
        }
        let mut r = 0;
        while r < 22 {
            st[0] = sbox7(st[0]);
            if r < 21 {
                st = internal_layer(&st, RC_INT[r + 1]);
            } else {
                st = internal_layer(&st, 0);
                let mut i = 0;
                while i < 12 {
                    st[i] = reduce_wide(st[i] as u128 + RC_EXT2[0][i] as u128);
                    i += 1;
                }
            }
            r += 1;
        }
        let mut r = 0;
        while r < 4 {
            let mut i = 0;
            while i < 12 {
                st[i] = sbox7(st[i]);
                i += 1;
            }
            st = external_layer(&st, if r < 3 { &RC_EXT2[r + 1] } else { &ZERO_RC });
            r += 1;
        }
        st
    }
}

/// Full 30-round Width-12 `Poseidon2` permutation (`4` ext + `22` int + `4` ext),
/// matching `lean/Qsag/Poseidon2.lean` and `qsag-core` bit-for-bit.
#[inline]
pub fn poseidon2_perm12(st: &mut [Goldilocks; 12]) {
    let out = perm_kernel::permute(&st.map(Goldilocks::to_canonical_u64));
    *st = out.map(Goldilocks::from_u64_reduced);
}

/// The same permutation composed from the individual layers; the reference for the kernel.
#[cfg(test)]
fn poseidon2_perm12_layered(st: &mut [Goldilocks; 12]) {
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

/// 256-bit `Poseidon2` sponge hash of a byte string (`Qsag.poseidon2Hash32`).
pub use qsag_core::sponge::poseidon2_hash32;

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
    let mut perm = perm_kernel::permute(&st.map(Goldilocks::to_canonical_u64));
    // `perm.b0 + in0 + 2 in1 + 4 tweak`, exact in `u128` (below `2^67`) and reduced once.
    let out: [Goldilocks; 4] = core::array::from_fn(|i| {
        Goldilocks::from_u64_reduced(perm_kernel::reduce_wide(
            perm[i] as u128
                + in0[i].to_canonical_u64() as u128
                + ((in1[i].to_canonical_u64() as u128) << 1)
                + ((tweak[i].to_canonical_u64() as u128) << 2),
        ))
    });
    qsag_asm::volatile_fill(&mut perm, 0u64);
    qsag_asm::volatile_fill(&mut st, Goldilocks::ZERO);
    qsag_asm::volatile_fill(&mut in0, Goldilocks::ZERO);
    out
}

// ============================================================================
// 3B. Algebraic Width-12 Rate-8 `Poseidon2` Canopy Merkle & Limb Sponge
// ============================================================================

/// Pairwise-disjoint canonical `< p` domain tags separating `Poseidon2` Canopy salt derivation,
/// Round-0 single/batch leaves, Stage-`k` `Ext4` leaves, 2-to-1 internal nodes, root binding,
/// and algebraic Fiat–Shamir transcript phases/operations.
pub const P2_DOMAIN_CANOPY_SALT: u64 = 0x5032_434E_534C_5401; // "P2CNSLT\x01"
pub const P2_DOMAIN_CANOPY_LEAF_R0: u64 = 0x5032_434E_4C46_3001; // "P2CNLF0\x01"
pub const P2_DOMAIN_CANOPY_LEAF_BATCH: u64 = 0x5032_434E_4C46_4201; // "P2CNLFB\x01"
pub const P2_DOMAIN_CANOPY_LEAF_EXT4: u64 = 0x5032_434E_4C46_4501; // "P2CNLFE\x01"
/// High 32 bits `"P2ND"` combined via bitwise OR with `node_idx: u32` (`< p` for every `u32`).
pub const P2_DOMAIN_CANOPY_NODE_HI: u64 = 0x5032_4E44_0000_0000; // "P2ND\0\0\0\0"
pub const P2_DOMAIN_CANOPY_ROOT: u64 = 0x5032_434E_524F_4F54; // "P2CNROOT"

pub const P2_DOMAIN_FS_INIT: u64 = 0x5032_4653_494E_4954; // "P2FSINIT"
pub const P2_DOMAIN_FS_BIND_REL: u64 = 0x5032_4653_4252_454C; // "P2FSBREL"
pub const P2_DOMAIN_FS_BIND_INST: u64 = 0x5032_4653_4249_4E53; // "P2FSBINS"
pub const P2_DOMAIN_FS_ABSORB_BYTES: u64 = 0x5032_4653_4142_5954; // "P2FSABYT"
pub const P2_DOMAIN_FS_ABSORB_LIMBS: u64 = 0x5032_4653_414C_4D42; // "P2FSALMB"
pub const P2_DOMAIN_FS_SQUEEZE_BASE: u64 = 0x5032_4653_5351_4253; // "P2FSSQBS"
pub const P2_DOMAIN_FS_SQUEEZE_EXT4: u64 = 0x5032_4653_5351_4534; // "P2FSSQE4"
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
#[inline]
pub fn poseidon2_sponge_hash_limbs(
    domain_tag: u64,
    init_cap: [Goldilocks; 4],
    limbs: &[Goldilocks],
) -> [Goldilocks; 4] {
    // Raw-word sponge: lanes stay arbitrary `u64` representatives between blocks and are
    // canonicalized once at the end.
    let mut st = [0u64; 12];
    for (dst, cap) in st[8..].iter_mut().zip(init_cap) {
        *dst = cap.to_canonical_u64();
    }
    let absorb = |st: &mut [u64; 12], block: &[u64; 8]| {
        for (lane, &val) in st[..8].iter_mut().zip(block) {
            *lane = perm_kernel::reduce_wide(*lane as u128 + val as u128);
        }
        *st = perm_kernel::permute(st);
    };

    // First block: the two-limb frame header followed by up to six payload limbs.
    let mut block = [0u64; 8];
    block[0] = Goldilocks::from_u64_reduced(domain_tag).to_canonical_u64();
    block[1] = Goldilocks::from_u64_reduced(limbs.len() as u64).to_canonical_u64();
    let head = limbs.len().min(6);
    for (dst, limb) in block[2..2 + head].iter_mut().zip(limbs) {
        *dst = limb.to_canonical_u64();
    }
    absorb(&mut st, &block);

    let (full, tail) = limbs[head..].as_chunks::<8>();
    for chunk in full {
        absorb(&mut st, &chunk.map(Goldilocks::to_canonical_u64));
    }
    if !tail.is_empty() {
        let mut block = [0u64; 8];
        for (dst, limb) in block.iter_mut().zip(tail) {
            *dst = limb.to_canonical_u64();
        }
        absorb(&mut st, &block);
    }
    core::array::from_fn(|i| Goldilocks::from_u64_reduced(st[i]))
}

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

// ============================================================================
// 4. Typestate Fenzi Instance-Bound Fiat–Shamir Transcript
// ============================================================================

// The phase markers are the sealed `qsag-core` typestate: `Unbound` (nothing bound),
// `RelationBound` (relation bound, instance pending) and `InstanceBound` (both bound; only this
// phase can absorb prover messages and squeeze challenges).
pub use qsag_core::sponge::{InstanceBound, RelationBound, TranscriptPhase, Unbound};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TranscriptBackend {
    Cshake256,
    Poseidon2 { p2_chain: [Goldilocks; 4] },
}

/// Anti-grinding Fiat–Shamir transcript parameterized by compile-time phase `P`.
///
/// Follows Fenzi et al. (`IACR 2025`): challenges cannot be squeezed at compile time until
/// BOTH `.bind_relation(...)` AND `.bind_instance(...)` have been executed on self-delimiting
/// multi-field frames, eliminating weak-Fiat–Shamir last-round grinding attacks.
///
/// Supports both `cSHAKE256` (default, bit-identical for byte-hash WHIR regimes) and algebraic
/// Width-12 Rate-8 `Poseidon2` (selected automatically by `bind_relation` when
/// `schedule.regime.uses_poseidon2_canopy()` is `true`, enabling native in-circuit verification).
pub struct FiatShamirTranscript<P: TranscriptPhase> {
    chain_digest: [u8; 32],
    backend: TranscriptBackend,
    turboshake_pow: bool,
    pow_bits: u32,
    counter: u64,
    _phase: PhantomData<P>,
}

impl<P: TranscriptPhase> Clone for FiatShamirTranscript<P> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            chain_digest: self.chain_digest,
            backend: self.backend,
            turboshake_pow: self.turboshake_pow,
            pow_bits: self.pow_bits,
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
            backend: TranscriptBackend::Cshake256,
            turboshake_pow: false,
            pow_bits: crate::pcs::PCS_POW_BITS,
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
        let pow_bits = schedule.regime.pow_bits();
        let turboshake_pow = schedule.regime.uses_turboshake_canopy();
        let sched_bytes = schedule.to_bytes();
        if schedule.regime.uses_poseidon2_canopy() {
            let mut limbs = Vec::with_capacity(
                4 + relation_tag.len().div_ceil(7)
                    + params_bytes.len().div_ceil(7)
                    + sched_bytes.len().div_ceil(7),
            );
            push_packed_bytes_7_limbs(&mut limbs, relation_tag);
            push_packed_bytes_7_limbs(&mut limbs, params_bytes);
            push_packed_bytes_7_limbs(&mut limbs, &sched_bytes);
            limbs.push(Goldilocks::from_u64_reduced(pow_bits as u64));
            let init_cap = [
                Goldilocks::from_u64_reduced(P2_DOMAIN_FS_INIT),
                Goldilocks::ZERO,
                Goldilocks::ZERO,
                Goldilocks::from_u64_reduced(POSEIDON2_CONST_IV),
            ];
            let p2_chain = poseidon2_sponge_hash_limbs(P2_DOMAIN_FS_BIND_REL, init_cap, &limbs);
            return FiatShamirTranscript {
                chain_digest: limbs4_to_le_bytes32(p2_chain),
                backend: TranscriptBackend::Poseidon2 { p2_chain },
                turboshake_pow,
                pow_bits,
                counter: 0,
                _phase: PhantomData,
            };
        }

        let mut encoded = sched_bytes;
        encoded.extend_from_slice(&pow_bits.to_le_bytes());
        let frame = encode_multi_frame(&[
            b"BIND_RELATION_HEM_WHIR_EXT4_V5",
            &self.chain_digest,
            relation_tag,
            params_bytes,
            &encoded,
        ]);
        FiatShamirTranscript {
            chain_digest: cshake256_from_midstate_32(&FS_MIDSTATE, &frame),
            backend: TranscriptBackend::Cshake256,
            turboshake_pow,
            pow_bits,
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
    /// Algebraic `Poseidon2` relation chain state (`Some` iff `schedule.regime.uses_poseidon2_canopy()`).
    #[inline]
    pub fn poseidon2_chain(&self) -> Option<[Goldilocks; 4]> {
        match self.backend {
            TranscriptBackend::Cshake256 => None,
            TranscriptBackend::Poseidon2 { p2_chain } => Some(p2_chain),
        }
    }

    /// Bind the complete public statement (`committee_root`, `bitmap`, `signing_mode`, `profile`).
    pub fn bind_instance(self, instance_fields: &[&[u8]]) -> FiatShamirTranscript<InstanceBound> {
        match self.backend {
            TranscriptBackend::Poseidon2 { p2_chain } => {
                let cap_hint: usize = instance_fields
                    .iter()
                    .map(|f| 1 + f.len().div_ceil(7))
                    .sum();
                let mut limbs = Vec::with_capacity(1 + cap_hint);
                limbs.push(Goldilocks::from_u64_reduced(instance_fields.len() as u64));
                for f in instance_fields {
                    push_packed_bytes_7_limbs(&mut limbs, f);
                }
                let next_chain =
                    poseidon2_sponge_hash_limbs(P2_DOMAIN_FS_BIND_INST, p2_chain, &limbs);
                FiatShamirTranscript {
                    chain_digest: limbs4_to_le_bytes32(next_chain),
                    backend: TranscriptBackend::Poseidon2 {
                        p2_chain: next_chain,
                    },
                    turboshake_pow: self.turboshake_pow,
                    pow_bits: self.pow_bits,
                    counter: 0,
                    _phase: PhantomData,
                }
            }
            TranscriptBackend::Cshake256 => {
                let inner = encode_multi_frame(instance_fields);
                let frame = encode_multi_frame(&[b"BIND_INSTANCE", &self.chain_digest, &inner]);
                FiatShamirTranscript {
                    chain_digest: cshake256_from_midstate_32(&FS_MIDSTATE, &frame),
                    backend: TranscriptBackend::Cshake256,
                    turboshake_pow: self.turboshake_pow,
                    pow_bits: self.pow_bits,
                    counter: 0,
                    _phase: PhantomData,
                }
            }
        }
    }
}

impl FiatShamirTranscript<InstanceBound> {
    /// Per-stage Proof-of-Work grinding bits bound into this transcript's relation (`0` or `16`).
    #[inline]
    pub fn pow_bits(&self) -> u32 {
        self.pow_bits
    }

    /// Whether Proof-of-Work grinding uses 12-round `TurboSHAKE256` (`TURBOSHAKE_POW_MIDSTATE`).
    #[inline]
    pub fn uses_turboshake_pow(&self) -> bool {
        self.turboshake_pow
    }

    /// Whether this transcript operates in algebraic `Poseidon2` mode.
    #[inline]
    pub fn uses_poseidon2(&self) -> bool {
        matches!(self.backend, TranscriptBackend::Poseidon2 { .. })
    }

    /// Current algebraic `Poseidon2` chain state (`Some` iff `uses_poseidon2()`).
    #[inline]
    pub fn poseidon2_chain(&self) -> Option<[Goldilocks; 4]> {
        match self.backend {
            TranscriptBackend::Cshake256 => None,
            TranscriptBackend::Poseidon2 { p2_chain } => Some(p2_chain),
        }
    }

    /// Absorb canonical `Goldilocks` limbs directly in `Poseidon2` mode (or their canonical LE
    /// byte encoding in `cSHAKE256` mode).
    pub fn absorb_limbs(&mut self, label: &[u8], payload_limbs: &[Goldilocks]) {
        match &mut self.backend {
            TranscriptBackend::Poseidon2 { p2_chain } => {
                let mut limbs =
                    Vec::with_capacity(1 + label.len().div_ceil(7) + payload_limbs.len());
                push_packed_bytes_7_limbs(&mut limbs, label);
                limbs.extend_from_slice(payload_limbs);
                let next =
                    poseidon2_sponge_hash_limbs(P2_DOMAIN_FS_ABSORB_LIMBS, *p2_chain, &limbs);
                *p2_chain = next;
                self.chain_digest = limbs4_to_le_bytes32(next);
                self.counter = 0;
            }
            TranscriptBackend::Cshake256 => {
                let mut bytes = Vec::with_capacity(8 * payload_limbs.len());
                for &limb in payload_limbs {
                    bytes.extend_from_slice(&limb.to_le_bytes());
                }
                self.absorb(label, &bytes);
            }
        }
    }

    /// Absorb a labeled prover message / byte frame.
    pub fn absorb(&mut self, label: &[u8], payload: &[u8]) {
        match &mut self.backend {
            TranscriptBackend::Poseidon2 { p2_chain } => {
                let mut limbs =
                    Vec::with_capacity(2 + label.len().div_ceil(7) + payload.len().div_ceil(7));
                push_packed_bytes_7_limbs(&mut limbs, label);
                push_packed_bytes_7_limbs(&mut limbs, payload);
                let next =
                    poseidon2_sponge_hash_limbs(P2_DOMAIN_FS_ABSORB_BYTES, *p2_chain, &limbs);
                *p2_chain = next;
                self.chain_digest = limbs4_to_le_bytes32(next);
                self.counter = 0;
            }
            TranscriptBackend::Cshake256 => {
                let frame = encode_multi_frame(&[b"ABSORB", &self.chain_digest, label, payload]);
                self.chain_digest = cshake256_from_midstate_32(&FS_MIDSTATE, &frame);
                self.counter = 0;
            }
        }
    }

    /// Absorb an `Ext4` element (`4` native `Goldilocks` limbs in `Poseidon2` mode; canonical 32B LE in `cSHAKE256`).
    pub fn absorb_ext4(&mut self, label: &[u8], val: GoldilocksExt4) {
        match self.backend {
            TranscriptBackend::Poseidon2 { .. } => self.absorb_limbs(label, &val.to_limbs()),
            TranscriptBackend::Cshake256 => self.absorb(label, &val.to_le_bytes()),
        }
    }

    /// Absorb a slice of `Ext4` elements (`4 * vals.len()` native `Goldilocks` limbs in `Poseidon2` mode;
    /// bit-identical `32 * vals.len()` LE byte slice in `cSHAKE256` mode).
    pub fn absorb_ext4_slice(&mut self, label: &[u8], vals: &[GoldilocksExt4]) {
        match self.backend {
            TranscriptBackend::Poseidon2 { .. } => {
                let mut limbs = Vec::with_capacity(4 * vals.len());
                for v in vals {
                    limbs.extend_from_slice(&v.to_limbs());
                }
                self.absorb_limbs(label, &limbs);
            }
            TranscriptBackend::Cshake256 => {
                let mut bytes = Vec::with_capacity(32 * vals.len());
                for v in vals {
                    bytes.extend_from_slice(&v.to_le_bytes());
                }
                self.absorb(label, &bytes);
            }
        }
    }

    /// Absorb a `CanopyCommitment` (`[root_limbs[0..4], log_leaves]` in `Poseidon2` mode; 33B wire in `cSHAKE256`).
    /// Returns `false` in `Poseidon2` mode if `comm.root` does not decode to 4 canonical `< p` limbs.
    pub fn absorb_canopy_commitment(
        &mut self,
        label: &[u8],
        comm: &crate::pcs::CanopyCommitment,
    ) -> bool {
        match self.backend {
            TranscriptBackend::Poseidon2 { .. } => {
                let Some(r4) = bytes32_to_limbs4_le_canonical(&comm.root) else {
                    return false;
                };
                self.absorb_limbs(
                    label,
                    &[
                        r4[0],
                        r4[1],
                        r4[2],
                        r4[3],
                        Goldilocks::from_u64_reduced(comm.log_leaves as u64),
                    ],
                );
                true
            }
            TranscriptBackend::Cshake256 => {
                self.absorb(label, &comm.to_bytes());
                true
            }
        }
    }

    /// Absorb a `u32` scalar (`1` `Goldilocks` limb in `Poseidon2` mode; 4B LE in `cSHAKE256`).
    pub fn absorb_u32(&mut self, label: &[u8], val: u32) {
        match self.backend {
            TranscriptBackend::Poseidon2 { .. } => {
                self.absorb_limbs(label, &[Goldilocks::from_u64_reduced(val as u64)]);
            }
            TranscriptBackend::Cshake256 => self.absorb(label, &val.to_le_bytes()),
        }
    }

    /// Absorb a `u64` scalar (`[lo32, hi32]` canonical `Goldilocks` limbs in `Poseidon2` mode; 8B LE in `cSHAKE256`).
    pub fn absorb_u64(&mut self, label: &[u8], val: u64) {
        match self.backend {
            TranscriptBackend::Poseidon2 { .. } => {
                self.absorb_limbs(
                    label,
                    &[
                        Goldilocks::from_u64_reduced(val & 0xFFFF_FFFF),
                        Goldilocks::from_u64_reduced(val >> 32),
                    ],
                );
            }
            TranscriptBackend::Cshake256 => self.absorb(label, &val.to_le_bytes()),
        }
    }

    /// Squeeze an unbiased `Goldilocks` challenge.
    pub fn squeeze_base(&mut self, label: &[u8]) -> Goldilocks {
        if let TranscriptBackend::Poseidon2 { p2_chain } = self.backend {
            let mut limbs = Vec::with_capacity(2 + label.len().div_ceil(7));
            push_packed_bytes_7_limbs(&mut limbs, label);
            limbs.push(Goldilocks::from_u64_reduced(self.counter));
            self.counter += 1;
            return poseidon2_sponge_hash_limbs(P2_DOMAIN_FS_SQUEEZE_BASE, p2_chain, &limbs)[0];
        }

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
        if let TranscriptBackend::Poseidon2 { p2_chain } = self.backend {
            let mut limbs = Vec::with_capacity(2 + label.len().div_ceil(7));
            push_packed_bytes_7_limbs(&mut limbs, label);
            limbs.push(Goldilocks::from_u64_reduced(self.counter));
            self.counter += 1;
            let out4 = poseidon2_sponge_hash_limbs(P2_DOMAIN_FS_SQUEEZE_EXT4, p2_chain, &limbs);
            return GoldilocksExt4::from_limbs(out4);
        }

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

        if let TranscriptBackend::Poseidon2 { p2_chain } = self.backend {
            assert!(half_domain_len <= (1usize << 28));
            let mask = (half_domain_len - 1) as u64;
            let call_ctr = self.counter;
            self.counter += 1;
            let mut label_prefix = Vec::with_capacity(3 + label.len().div_ceil(7));
            push_packed_bytes_7_limbs(&mut label_prefix, label);
            label_prefix.push(Goldilocks::from_u64_reduced(call_ctr));
            label_prefix.push(Goldilocks::ZERO);
            let sub_slot = label_prefix.len() - 1;

            let mut out = Vec::with_capacity(num_queries);
            let mut sub_idx: u64 = 0;
            while out.len() < num_queries {
                label_prefix[sub_slot] = Goldilocks::from_u64_reduced(sub_idx);
                sub_idx += 1;
                let h4 =
                    poseidon2_sponge_hash_limbs(P2_DOMAIN_FS_SQUEEZE_IDX, p2_chain, &label_prefix);
                for limb in h4 {
                    if out.len() == num_queries {
                        break;
                    }
                    let u = limb.to_canonical_u64();
                    // Goldilocks p - 1 = 2^32 * (2^32 - 1) is divisible by 2^L for every L <= 32,
                    // so rejecting the single point u == p - 1 yields an exact uniform distribution!
                    if u < crate::field::GOLDILOCKS_PRIME - 1 {
                        out.push((u & mask) as usize);
                    }
                }
            }
            return out;
        }

        let ctr_bytes = self.counter.to_le_bytes();
        self.counter += 1;
        let frame = encode_multi_frame(&[b"SQUEEZE_IDX", &self.chain_digest, label, &ctr_bytes]);
        let mut raw = vec![0u8; 8 * num_queries];
        cshake256_from_midstate_into(&FS_MIDSTATE, &frame, &mut raw);
        raw.as_chunks::<8>()
            .0
            .iter()
            .map(|&b| {
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
    fn external_layer_matches_dense_kronecker_matrix_in_base_and_ext4() {
        let m4 = [[2, 3, 1, 1], [1, 2, 3, 1], [1, 1, 2, 3], [3, 1, 1, 2]];
        for j in 0..12 {
            let mut st = [Goldilocks::ZERO; 12];
            st[j] = Goldilocks::ONE;
            let mut ext = [GoldilocksExt4::ZERO; 12];
            ext[j] = GoldilocksExt4::from_limbs([Goldilocks::ONE; 4]);
            poseidon2_apply_me(&mut st);
            poseidon2_apply_me_ext4(&mut ext);
            for i in 0..12 {
                let entry = Goldilocks::from_u64_reduced(
                    m4[i / 3][j / 3] * if i % 3 == j % 3 { 2 } else { 1 },
                );
                assert_eq!(st[i], entry);
                assert_eq!(ext[i].to_limbs(), [entry; 4]);
            }
        }
    }
}
