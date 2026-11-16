//! Backend-dispatched cSHAKE and 12-round TurboSHAKE256 commitments. Secret states are wiped on drop.
use crate::{secret::Secret, secret::SecretVec, zk_engine::PartyView};
use alloc::vec::Vec;
use qsag_accel::{
    AcceleratorBackend,
    ct::{ct_zeroize_bytes, ct_zeroize_u64s},
    keccak::KECCAK_RC,
};

pub(crate) const COZK_VIEW_MAGIC_V4: [u8; 8] = *b"COZKVW04";
pub(crate) const COZK_VIEW_MAGIC_V5: [u8; 8] = *b"COZKVW05";
pub(crate) const COZK_TREE_LEAVES: usize = 8;
pub(crate) const TURBOSHAKE_RATE_BYTES: usize = 136;
/// RFC 9861 KangarooTwelve / TurboSHAKE leaf hop domain byte (`0x0B` in `0x01..=0x7F`).
pub(crate) const TURBOSHAKE_LEAF_SUFFIX: u8 = 0x0B;
/// RFC 9861 TurboSHAKE256 root domain byte (`0x07` in `0x01..=0x7F`, distinct from `0x0B`, `0x04`, `0x1F`).
pub(crate) const TURBOSHAKE_ROOT_SUFFIX: u8 = 0x07;

/// RFC 9861 12-round `Keccak-p[1600, 12]` permutation (rounds `12..24` of `KECCAK_RC`).
#[inline(always)]
pub(crate) const fn keccak_p1600_12(state: &mut [u64; 25]) {
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

/// Vectorized `N`-way (`N = 8` AVX-512 ZMM / `2x` AVX2 YMM) 12-round `Keccak-p[1600, 12]`.
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

/// Compile-time 12-round `TurboSHAKE256` customization midstate (`1..=128` bytes).
pub(crate) const fn turboshake256_static_midstate(custom: &[u8]) -> [u64; 25] {
    assert!(!custom.is_empty() && custom.len() <= 128);
    let mut blk = [0u8; TURBOSHAKE_RATE_BYTES];
    blk[0] = 1;
    blk[1] = TURBOSHAKE_RATE_BYTES as u8;
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

/// Precomputed 12-round `TurboSHAKE256` midstate for collaborative view commitments.
pub(crate) const TURBOSHAKE_VIEW_MIDSTATE: [u64; 25] =
    turboshake256_static_midstate(b"QSAG.MIGRATE.VIEW.V3");

/// Deterministic byte slice of `products` assigned to Kangaroo leaf `leaf` (`0..COZK_TREE_LEAVES`).
#[inline]
pub(crate) fn cozk_product_leaf_range(products_len: usize, leaf: usize) -> (usize, usize) {
    let block_stride =
        products_len.div_ceil(COZK_TREE_LEAVES * TURBOSHAKE_RATE_BYTES) * TURBOSHAKE_RATE_BYTES;
    let start = (leaf * block_stride).min(products_len);
    let end = ((leaf + 1) * block_stride).min(products_len);
    (start, end)
}

#[cfg(test)]
pub(crate) fn turboshake256_slices_32(
    midstate: &[u64; 25],
    suffix: u8,
    pieces: &[&[u8]],
) -> [u8; 32] {
    let mut state = Secret(*midstate);
    let mut block = Secret([0u8; TURBOSHAKE_RATE_BYTES]);
    let mut pos = 0usize;
    for &piece in pieces {
        let mut rem = piece;
        while !rem.is_empty() {
            if pos == 0 && rem.len() >= TURBOSHAKE_RATE_BYTES {
                for (w, bytes) in state
                    .iter_mut()
                    .zip(rem[..TURBOSHAKE_RATE_BYTES].chunks_exact(8))
                {
                    *w ^= u64::from_le_bytes(bytes.try_into().unwrap());
                }
                keccak_p1600_12(&mut state);
                rem = &rem[TURBOSHAKE_RATE_BYTES..];
            } else {
                let take = (TURBOSHAKE_RATE_BYTES - pos).min(rem.len());
                block[pos..pos + take].copy_from_slice(&rem[..take]);
                pos += take;
                rem = &rem[take..];
                if pos == TURBOSHAKE_RATE_BYTES {
                    for (w, bytes) in state.iter_mut().zip(block.chunks_exact(8)) {
                        *w ^= u64::from_le_bytes(bytes.try_into().unwrap());
                    }
                    ct_zeroize_bytes(&mut *block);
                    keccak_p1600_12(&mut state);
                    pos = 0;
                }
            }
        }
    }
    block[pos] ^= suffix;
    block[TURBOSHAKE_RATE_BYTES - 1] ^= 0x80;
    for (w, bytes) in state.iter_mut().zip(block.chunks_exact(8)) {
        *w ^= u64::from_le_bytes(bytes.try_into().unwrap());
    }
    keccak_p1600_12(&mut state);
    let mut out = [0u8; 32];
    for (chunk, &w) in out.chunks_exact_mut(8).zip(state.iter().take(4)) {
        chunk.copy_from_slice(&w.to_le_bytes());
    }
    out
}

/// Compute all 8 parallel leaf digests `L_0..L_7` of `products` simultaneously in one
/// 8-lane SIMD `keccak_p1600_12_lanes::<8>` pass, then hash the length-framed root tuple.
pub(crate) fn commit_cozk_v4_one(
    rep: usize, head: usize, subseeds: &[[u8; 32]], head_inputs: &[u8], products: &[u8], outputs: &[u8],
) -> [u8; 32] {
    commit_cozk_tree_one(&COZK_VIEW_MAGIC_V4, rep, head, subseeds, head_inputs, products, outputs)
}

/// V5 commits to seed commitments and a seed-masked view. Binding follows from
/// binding of the ordered seed commitments and tree hash: fixed seeds determine
/// a unique mask, hence a unique plaintext for each masked view. The mask XOF is
/// domain-separated from the inner proof tapes.
#[allow(clippy::too_many_arguments)]
pub(crate) fn commit_cozk_tree_one(
    magic: &[u8; 8], rep: usize, head: usize, subseeds: &[[u8; 32]], head_inputs: &[u8], products: &[u8], outputs: &[u8],
) -> [u8; 32] {
    let mut st8 = Secret(TURBOSHAKE_VIEW_MIDSTATE.map(|w| [w; COZK_TREE_LEAVES]));
    let ranges: [(usize, usize); COZK_TREE_LEAVES] =
        core::array::from_fn(|k| cozk_product_leaf_range(products.len(), k));
    let mut cursors = [0usize; COZK_TREE_LEAVES];
    let mut header_done = [false; COZK_TREE_LEAVES];
    let mut finished = [false; COZK_TREE_LEAVES];
    let mut extracted = [false; COZK_TREE_LEAVES];
    let mut leaf_digests = Secret([[0u8; 32]; COZK_TREE_LEAVES]);
    let mut blk = Secret([0u8; TURBOSHAKE_RATE_BYTES]);

    while extracted.iter().any(|&done| !done) {
        for k in 0..COZK_TREE_LEAVES {
            if finished[k] {
                continue;
            }
            ct_zeroize_bytes(&mut *blk);
            let mut filled = 0usize;
            let (start, end) = ranges[k];
            let slice = &products[start..end];
            if !header_done[k] {
                blk[0..8].copy_from_slice(&(k as u64).to_le_bytes());
                blk[8..16].copy_from_slice(&(slice.len() as u64).to_le_bytes());
                filled = 16;
                header_done[k] = true;
            }
            let rem = &slice[cursors[k]..];
            let take = (TURBOSHAKE_RATE_BYTES - filled).min(rem.len());
            blk[filled..filled + take].copy_from_slice(&rem[..take]);
            filled += take;
            cursors[k] += take;
            if filled < TURBOSHAKE_RATE_BYTES {
                blk[filled] ^= TURBOSHAKE_LEAF_SUFFIX;
                blk[TURBOSHAKE_RATE_BYTES - 1] ^= 0x80;
                finished[k] = true;
            }
            for (lane_idx, bytes) in blk.chunks_exact(8).enumerate() {
                st8[lane_idx][k] ^= u64::from_le_bytes(bytes.try_into().unwrap());
            }
        }
        keccak_p1600_12_lanes(&mut st8);
        for k in 0..COZK_TREE_LEAVES {
            if finished[k] && !extracted[k] {
                for w_idx in 0..4 {
                    leaf_digests[k][8 * w_idx..8 * (w_idx + 1)]
                        .copy_from_slice(&st8[w_idx][k].to_le_bytes());
                }
                extracted[k] = true;
            }
        }
    }
    ct_zeroize_u64s(st8.as_flattened_mut());

    // Root TurboSHAKE256 (`TURBOSHAKE_ROOT_SUFFIX = 0x07`) over the injective length-framed tuple.
    let mut root_state = Secret(TURBOSHAKE_VIEW_MIDSTATE);
    ct_zeroize_bytes(&mut *blk);
    let mut pos = 0usize;
    let mut absorb_root = |mut input: &[u8]| {
        while !input.is_empty() {
            let take = (TURBOSHAKE_RATE_BYTES - pos).min(input.len());
            blk[pos..pos + take].copy_from_slice(&input[..take]);
            pos += take;
            input = &input[take..];
            if pos == TURBOSHAKE_RATE_BYTES {
                for (w, bytes) in root_state.iter_mut().zip(blk.chunks_exact(8)) {
                    *w ^= u64::from_le_bytes(bytes.try_into().unwrap());
                }
                ct_zeroize_bytes(&mut *blk);
                keccak_p1600_12(&mut root_state);
                pos = 0;
            }
        }
    };
    absorb_root(magic);
    absorb_root(&(rep as u64).to_le_bytes());
    absorb_root(&[head as u8]);
    absorb_root(&(subseeds.len() as u64).to_le_bytes());
    for s in subseeds {
        absorb_root(s);
    }
    absorb_root(&(head_inputs.len() as u64).to_le_bytes());
    absorb_root(head_inputs);
    absorb_root(&(products.len() as u64).to_le_bytes());
    for l in leaf_digests.iter() {
        absorb_root(l);
    }
    absorb_root(&(outputs.len() as u64).to_le_bytes());
    absorb_root(outputs);

    blk[pos] ^= TURBOSHAKE_ROOT_SUFFIX;
    blk[TURBOSHAKE_RATE_BYTES - 1] ^= 0x80;
    for (w, bytes) in root_state.iter_mut().zip(blk.chunks_exact(8)) {
        *w ^= u64::from_le_bytes(bytes.try_into().unwrap());
    }
    keccak_p1600_12(&mut root_state);
    let mut out = [0u8; 32];
    for (chunk, &w) in out.chunks_exact_mut(8).zip(root_state.iter().take(4)) {
        chunk.copy_from_slice(&w.to_le_bytes());
    }
    out
}

pub(crate) fn cozk_seed_commit(rep: usize, head: usize, position: usize, seed: &[u8; 32]) -> [u8; 32] {
    qsag_accel::keccak::cshake256_framed_32(b"QSAG.COZK.SEED.COMMIT.V5", &[&(rep as u64).to_le_bytes(), &(head as u64).to_le_bytes(), &(position as u64).to_le_bytes(), seed])
}

pub(crate) fn view_mask_stream(seed: &[u8; 32], rep: usize, head: usize) -> qsag_core::sponge::keccak::Cshake256WordStream4 {
    const MIDSTATE: [u64; 25] = qsag_core::sponge::keccak::cshake256_static_midstate(b"QSAG.COZK.VIEW.MASK.V5");
    let mut input = Secret([0u8; 41]);
    input[..32].copy_from_slice(seed);
    input[32..40].copy_from_slice(&(rep as u64).to_le_bytes());
    input[40] = head as u8;
    qsag_core::sponge::keccak::Cshake256WordStream4::new(&MIDSTATE, &input[..])
}

fn commit_cozk_v5_one(v: &CozkIndexedView<'_>) -> [u8; 32] {
    let mut masked: SecretVec<u8> = v.head_inputs.iter().chain(v.products).chain(v.outputs).copied().collect();
    let seed_commits: Vec<_> = v.subseeds.iter().enumerate().map(|(i, s)| cozk_seed_commit(v.rep, v.head, i, s)).collect();
    for seed in &v.subseeds {
        let mut mask = view_mask_stream(seed, v.rep, v.head);
        let mut words = Secret([0u64; 4]);
        for chunk in masked.chunks_mut(32) {
            mask.fill_words(&mut words[..]);
            for (i, byte) in chunk.iter_mut().enumerate() { *byte ^= (words[i / 8] >> (8 * (i % 8))) as u8; }
        }
    }
    let a = v.head_inputs.len();
    let b = a + v.products.len();
    commit_cozk_tree_one(&COZK_VIEW_MAGIC_V5, v.rep, v.head, &seed_commits, &masked[..a], &masked[a..b], &masked[b..])
}

pub(crate) fn commit_cozk_v5_indexed(views: &[CozkIndexedView<'_>]) -> Vec<[u8; 32]> {
    crate::parallel::map(views.len(), |i| commit_cozk_v5_one(&views[i]))
}

pub(crate) struct CozkIndexedView<'a> {
    pub rep: usize,
    pub head: usize,
    pub subseeds: Vec<[u8; 32]>,
    pub head_inputs: &'a [u8],
    pub products: &'a [u8],
    pub outputs: &'a [u8],
}
impl Drop for CozkIndexedView<'_> {
    fn drop(&mut self) {
        for s in &mut self.subseeds {
            ct_zeroize_bytes(s);
        }
    }
}

pub(crate) fn commit_cozk_v4_indexed(views: &[CozkIndexedView<'_>]) -> Vec<[u8; 32]> {
    crate::parallel::map(views.len(), |i| {
        let v = &views[i];
        commit_cozk_v4_one(
            v.rep,
            v.head,
            &v.subseeds,
            v.head_inputs,
            v.products,
            v.outputs,
        )
    })
}

/// Hash independent framed messages in lockstep, including unequal lengths and
/// exact rate boundaries. Only public message lengths control scheduling.
fn framed<B: AcceleratorBackend>(accel: &B, custom: &[u8], frames: &[Vec<&[u8]>]) -> Vec<[u8; 32]> {
    let prefix = if custom.is_empty() {
        Vec::new()
    } else {
        qsag_core::sponge::keccak::cshake256_customization_prefix(custom)
    };
    // Keep payloads borrowed. Only the small framing headers are owned.
    let headers: Vec<Vec<[u8; 8]>> = frames
        .iter()
        .map(|f| {
            core::iter::once((f.len() as u64).to_le_bytes())
                .chain(f.iter().map(|frame| (frame.len() as u64).to_le_bytes()))
                .collect()
        })
        .collect();
    let mut streams: Vec<_> = frames
        .iter()
        .zip(&headers)
        .map(|(f, h)| {
            let pieces: Vec<&[u8]> = core::iter::once(prefix.as_slice())
                .chain(core::iter::once(h[0].as_slice()))
                .chain(
                    f.iter()
                        .zip(&h[1..])
                        .flat_map(|(frame, len)| [len.as_slice(), *frame]),
                )
                .collect();
            (pieces, 0usize, 0usize)
        })
        .collect();
    let mut states: SecretVec<[u64; 25]> = (0..frames.len()).map(|_| [0; 25]).collect();
    let mut active: Vec<_> = (0..frames.len()).collect();
    let mut result = alloc::vec![[0; 32]; frames.len()];
    let mut finished = Vec::new();
    while !active.is_empty() {
        finished.clear();
        for (i, &index) in active.iter().enumerate() {
            let (pieces, piece, offset) = &mut streams[index];
            let mut block = [0u8; 136];
            let mut filled = 0;
            while filled < block.len() && *piece < pieces.len() {
                let input = &pieces[*piece][*offset..];
                let take = input.len().min(block.len() - filled);
                block[filled..filled + take].copy_from_slice(&input[..take]);
                filled += take;
                *offset += take;
                if *offset == pieces[*piece].len() {
                    *piece += 1;
                    *offset = 0;
                }
            }
            if filled < block.len() {
                block[filled] = if custom.is_empty() { 0x1f } else { 0x04 };
                block[135] |= 0x80;
                finished.push(i);
            }
            for (word, bytes) in states[i].iter_mut().zip(block.chunks_exact(8)) {
                *word ^= u64::from_le_bytes(bytes.try_into().unwrap());
            }
            qsag_accel::ct::ct_zeroize_bytes(&mut block);
        }
        accel.batch_keccak_f1600(&mut states);
        for &i in finished.iter().rev() {
            for (out, word) in result[active[i]].chunks_exact_mut(8).zip(&states[i]) {
                out.copy_from_slice(&word.to_le_bytes());
            }
            let last = states.len() - 1;
            states.swap(i, last);
            states.truncate(last);
            active.swap_remove(i);
        }
    }
    result
}

pub(crate) fn commit_views<B: AcceleratorBackend>(
    accel: &B,
    views: &[[PartyView; 3]],
) -> Vec<[u8; 32]> {
    let indexed: Vec<_> = views
        .iter()
        .enumerate()
        .flat_map(|(r, v)| v.iter().enumerate().map(move |(p, v)| (r, p, v)))
        .collect();
    commit_indexed(accel, &indexed)
}

pub(crate) fn commit_indexed<B: AcceleratorBackend>(
    accel: &B,
    views: &[(usize, usize, &PartyView)],
) -> Vec<[u8; 32]> {
    let reps: Vec<_> = views
        .iter()
        .map(|(r, _, _)| (*r as u64).to_le_bytes())
        .collect();
    let parties: Vec<_> = views.iter().map(|(_, p, _)| [*p as u8]).collect();
    let frames: Vec<_> = views
        .iter()
        .enumerate()
        .map(|(i, (_, _, v))| {
            alloc::vec![
                reps[i].as_slice(),
                parties[i].as_slice(),
                &v.seed,
                &v.inputs,
                &v.products,
                &v.outputs,
            ]
        })
        .collect();
    framed(accel, b"QSAG.MIGRATE.VIEW.V3", &frames)
}

#[cfg(test)]
mod tests {
    use super::*;
    use qsag_accel::{CpuReferenceBackend, keccak::cshake256_framed_32};

    fn exercise<B: AcceleratorBackend>(backend: &B) {
        let messages: Vec<Vec<u8>> = [0, 1, 119, 120, 121, 135, 136, 137, 272, 4096]
            .into_iter()
            .map(|len| (0..len).map(|i| i as u8).collect())
            .collect();
        let mut frames: Vec<_> = messages.iter().map(|m| alloc::vec![m.as_slice()]).collect();
        frames.push(alloc::vec![]);
        frames.push(alloc::vec![&[], &[], &[]]);
        for m in &messages {
            for split in 0..=m.len().min(136) {
                frames.push(alloc::vec![&m[..split], &[], &m[split..]]);
            }
        }
        for custom in [b"".as_slice(), b"QSAG.MIGRATE.VIEW.V3", &[42; 200]] {
            let actual = framed(backend, custom, &frames);
            let expected: Vec<_> = frames
                .iter()
                .map(|f| cshake256_framed_32(custom, f))
                .collect();
            assert_eq!(actual, expected);
        }
    }

    #[test]
    fn batch_sponge_matches_scalar_at_rate_boundaries() {
        exercise(&CpuReferenceBackend);
    }

    #[test]
    fn cozk_v4_turboshake_tree_matches_scalar_reference_at_rate_boundaries() {
        let subseeds = [[0x11u8; 32], [0x22u8; 32], [0x33u8; 32]];
        for prod_len in [0usize, 1, 119, 120, 121, 135, 136, 137, 960, 1088, 1089, 5000] {
            let products: Vec<u8> = (0..prod_len).map(|i| (i * 37 + 13) as u8).collect();
            let head_inputs: Vec<u8> = (0..41).map(|i| (i ^ 0x5a) as u8).collect();
            let outputs: Vec<u8> = (0..19).map(|i| (i + 7) as u8).collect();
            let actual = commit_cozk_v4_one(17, 2, &subseeds, &head_inputs, &products, &outputs);

            let mut expected_leaves = [[0u8; 32]; COZK_TREE_LEAVES];
            for (k, slot) in expected_leaves.iter_mut().enumerate() {
                let (s, e) = cozk_product_leaf_range(products.len(), k);
                let slice = &products[s..e];
                let k_le = (k as u64).to_le_bytes();
                let len_le = (slice.len() as u64).to_le_bytes();
                *slot = turboshake256_slices_32(
                    &TURBOSHAKE_VIEW_MIDSTATE,
                    TURBOSHAKE_LEAF_SUFFIX,
                    &[&k_le, &len_le, slice],
                );
            }
            let rep_le = 17u64.to_le_bytes();
            let head_b = [2u8];
            let m_le = (subseeds.len() as u64).to_le_bytes();
            let in_le = (head_inputs.len() as u64).to_le_bytes();
            let pr_le = (products.len() as u64).to_le_bytes();
            let out_le = (outputs.len() as u64).to_le_bytes();
            let leaves_flat: Vec<u8> = expected_leaves.iter().flatten().copied().collect();
            let expected = turboshake256_slices_32(
                &TURBOSHAKE_VIEW_MIDSTATE,
                TURBOSHAKE_ROOT_SUFFIX,
                &[
                    &COZK_VIEW_MAGIC_V4,
                    &rep_le,
                    &head_b,
                    &m_le,
                    &subseeds[0],
                    &subseeds[1],
                    &subseeds[2],
                    &in_le,
                    &head_inputs,
                    &pr_le,
                    &leaves_flat,
                    &out_le,
                    &outputs,
                ],
            );
            assert_eq!(actual, expected, "mismatch at prod_len={prod_len}");
        }
    }

    #[test]
    #[cfg(feature = "vulkan")]
    fn vulkan_batch_sponge_matches_cpu() {
        let gpu = qsag_accel::VulkanSpirvBackend::try_new()
            .expect("opt-in Vulkan test requires a supported device");
        std::eprintln!("GPU: {}", gpu.device_name());
        let before = gpu.cpu_fallback_count();
        exercise(&gpu);
        assert_eq!(
            gpu.cpu_fallback_count(),
            before,
            "GPU test must not fall back to CPU"
        );
    }
}
