//! BLAKE2b and BLAKE2s (RFC 7693) with the personalization parameter Zcash uses, and the
//! BLAKE2b gadget over the zk-Hem constraint system.
//!
//! Only the sequential, unkeyed mode with a 16-byte (BLAKE2b) or 8-byte (BLAKE2s)
//! personalization and no salt is implemented; that is every use in the Zcash protocol
//! specification (`PRF^expand`, ZIP 32, F4Jumble, hash-to-curve, RedDSA, group hashes).
//!
//! # Gadget cost
//!
//! One BLAKE2b `G` function is four modular additions and four 64-bit XORs: 524 rows. A
//! compression is 96 `G` plus the feed-forward, about 51,000 rows. A BLAKE2s compression
//! is 80 `G` on 32-bit words, about 21,000 rows.

use alloc::vec::Vec;

use qsag_agg::zk_hem::relation::{ConstraintSystem, Lc};

use crate::hem::hash::{Word, add_mod, xor2, xor3};

const IV_B: [u64; 8] = [
    0x6a09_e667_f3bc_c908,
    0xbb67_ae85_84ca_a73b,
    0x3c6e_f372_fe94_f82b,
    0xa54f_f53a_5f1d_36f1,
    0x510e_527f_ade6_82d1,
    0x9b05_688c_2b3e_6c1f,
    0x1f83_d9ab_fb41_bd6b,
    0x5be0_cd19_137e_2179,
];

const IV_S: [u32; 8] = [
    0x6a09_e667,
    0xbb67_ae85,
    0x3c6e_f372,
    0xa54f_f53a,
    0x510e_527f,
    0x9b05_688c,
    0x1f83_d9ab,
    0x5be0_cd19,
];

const SIGMA: [[usize; 16]; 10] = [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0],
];

/// The eight column and diagonal index quadruples of one round.
const QUARTERS: [[usize; 4]; 8] = [
    [0, 4, 8, 12],
    [1, 5, 9, 13],
    [2, 6, 10, 14],
    [3, 7, 11, 15],
    [0, 5, 10, 15],
    [1, 6, 11, 12],
    [2, 7, 8, 13],
    [3, 4, 9, 14],
];

fn wipe<T: Copy + Default>(buf: &mut [T]) {
    qsag_asm::volatile_fill(buf, T::default());
}

// ============================================================================
// BLAKE2b
// ============================================================================

/// Initial chaining value of unkeyed BLAKE2b with digest length `out_len` and a
/// personalization.
pub fn blake2b_iv(out_len: usize, personal: &[u8; 16]) -> [u64; 8] {
    assert!(
        (1..=64).contains(&out_len),
        "BLAKE2b digest length is 1..=64"
    );
    let mut h = IV_B;
    h[0] ^= 0x0101_0000 ^ out_len as u64;
    h[6] ^= u64::from_le_bytes(personal[..8].try_into().unwrap());
    h[7] ^= u64::from_le_bytes(personal[8..].try_into().unwrap());
    h
}

fn compress_b(h: &mut [u64; 8], block: &[u8; 128], t: u128, last: bool) {
    let mut m = [0u64; 16];
    for (w, c) in m.iter_mut().zip(block.chunks_exact(8)) {
        *w = u64::from_le_bytes(c.try_into().unwrap());
    }
    let mut v = [0u64; 16];
    v[..8].copy_from_slice(h);
    v[8..].copy_from_slice(&IV_B);
    v[12] ^= t as u64;
    v[13] ^= (t >> 64) as u64;
    if last {
        v[14] = !v[14];
    }
    for round in 0..12 {
        let s = &SIGMA[round % 10];
        for (i, q) in QUARTERS.iter().enumerate() {
            let (a, b, c, d) = (q[0], q[1], q[2], q[3]);
            v[a] = v[a].wrapping_add(v[b]).wrapping_add(m[s[2 * i]]);
            v[d] = (v[d] ^ v[a]).rotate_right(32);
            v[c] = v[c].wrapping_add(v[d]);
            v[b] = (v[b] ^ v[c]).rotate_right(24);
            v[a] = v[a].wrapping_add(v[b]).wrapping_add(m[s[2 * i + 1]]);
            v[d] = (v[d] ^ v[a]).rotate_right(16);
            v[c] = v[c].wrapping_add(v[d]);
            v[b] = (v[b] ^ v[c]).rotate_right(63);
        }
    }
    for i in 0..8 {
        h[i] ^= v[i] ^ v[i + 8];
    }
    wipe(&mut m);
    wipe(&mut v);
}

/// Incremental unkeyed BLAKE2b. Erased on drop.
pub struct Blake2b {
    h: [u64; 8],
    buf: [u8; 128],
    buf_len: usize,
    total: u128,
    out_len: usize,
}

impl Drop for Blake2b {
    fn drop(&mut self) {
        wipe(&mut self.h);
        wipe(&mut self.buf);
    }
}

impl Blake2b {
    pub fn new(out_len: usize, personal: &[u8; 16]) -> Self {
        Self {
            h: blake2b_iv(out_len, personal),
            buf: [0; 128],
            buf_len: 0,
            total: 0,
            out_len,
        }
    }

    pub fn update(&mut self, mut data: &[u8]) -> &mut Self {
        while !data.is_empty() {
            // A full buffer is compressed only when more input follows: the last block
            // (even a full one) must be compressed with the finalization flag.
            if self.buf_len == 128 {
                self.total += 128;
                compress_b(&mut self.h, &self.buf, self.total, false);
                self.buf_len = 0;
            }
            let take = (128 - self.buf_len).min(data.len());
            self.buf[self.buf_len..self.buf_len + take].copy_from_slice(&data[..take]);
            self.buf_len += take;
            data = &data[take..];
        }
        self
    }

    /// The digest in the first `out_len` bytes; the rest is zero.
    pub fn finalize(mut self) -> [u8; 64] {
        self.total += self.buf_len as u128;
        self.buf[self.buf_len..].fill(0);
        compress_b(&mut self.h, &self.buf, self.total, true);
        let mut out = [0u8; 64];
        for (o, w) in out.chunks_exact_mut(8).zip(&self.h) {
            o.copy_from_slice(&w.to_le_bytes());
        }
        out[self.out_len..].fill(0);
        out
    }
}

/// BLAKE2b-512 of the concatenation of `parts` under a personalization.
pub fn blake2b_512(personal: &[u8; 16], parts: &[&[u8]]) -> [u8; 64] {
    let mut st = Blake2b::new(64, personal);
    for p in parts {
        st.update(p);
    }
    st.finalize()
}

/// BLAKE2b-256 of the concatenation of `parts` under a personalization.
pub fn blake2b_256(personal: &[u8; 16], parts: &[&[u8]]) -> [u8; 32] {
    let mut st = Blake2b::new(32, personal);
    for p in parts {
        st.update(p);
    }
    let full = st.finalize();
    full[..32].try_into().unwrap()
}

/// BLAKE2b with digest length `out.len()` (1 to 64 bytes).
pub fn blake2b_var(personal: &[u8; 16], parts: &[&[u8]], out: &mut [u8]) {
    let mut st = Blake2b::new(out.len(), personal);
    for p in parts {
        st.update(p);
    }
    let full = st.finalize();
    out.copy_from_slice(&full[..out.len()]);
}

// ============================================================================
// BLAKE2s
// ============================================================================

fn compress_s(h: &mut [u32; 8], block: &[u8; 64], t: u64, last: bool) {
    let mut m = [0u32; 16];
    for (w, c) in m.iter_mut().zip(block.chunks_exact(4)) {
        *w = u32::from_le_bytes(c.try_into().unwrap());
    }
    let mut v = [0u32; 16];
    v[..8].copy_from_slice(h);
    v[8..].copy_from_slice(&IV_S);
    v[12] ^= t as u32;
    v[13] ^= (t >> 32) as u32;
    if last {
        v[14] = !v[14];
    }
    for s in &SIGMA {
        for (i, q) in QUARTERS.iter().enumerate() {
            let (a, b, c, d) = (q[0], q[1], q[2], q[3]);
            v[a] = v[a].wrapping_add(v[b]).wrapping_add(m[s[2 * i]]);
            v[d] = (v[d] ^ v[a]).rotate_right(16);
            v[c] = v[c].wrapping_add(v[d]);
            v[b] = (v[b] ^ v[c]).rotate_right(12);
            v[a] = v[a].wrapping_add(v[b]).wrapping_add(m[s[2 * i + 1]]);
            v[d] = (v[d] ^ v[a]).rotate_right(8);
            v[c] = v[c].wrapping_add(v[d]);
            v[b] = (v[b] ^ v[c]).rotate_right(7);
        }
    }
    for i in 0..8 {
        h[i] ^= v[i] ^ v[i + 8];
    }
    wipe(&mut m);
    wipe(&mut v);
}

/// Incremental unkeyed BLAKE2s. Erased on drop.
pub struct Blake2s {
    h: [u32; 8],
    buf: [u8; 64],
    buf_len: usize,
    total: u64,
    out_len: usize,
}

impl Drop for Blake2s {
    fn drop(&mut self) {
        wipe(&mut self.h);
        wipe(&mut self.buf);
    }
}

impl Blake2s {
    pub fn new(out_len: usize, personal: &[u8; 8]) -> Self {
        assert!(
            (1..=32).contains(&out_len),
            "BLAKE2s digest length is 1..=32"
        );
        let mut h = IV_S;
        h[0] ^= 0x0101_0000 ^ out_len as u32;
        h[6] ^= u32::from_le_bytes(personal[..4].try_into().unwrap());
        h[7] ^= u32::from_le_bytes(personal[4..].try_into().unwrap());
        Self {
            h,
            buf: [0; 64],
            buf_len: 0,
            total: 0,
            out_len,
        }
    }

    pub fn update(&mut self, mut data: &[u8]) -> &mut Self {
        while !data.is_empty() {
            if self.buf_len == 64 {
                self.total += 64;
                compress_s(&mut self.h, &self.buf, self.total, false);
                self.buf_len = 0;
            }
            let take = (64 - self.buf_len).min(data.len());
            self.buf[self.buf_len..self.buf_len + take].copy_from_slice(&data[..take]);
            self.buf_len += take;
            data = &data[take..];
        }
        self
    }

    /// The digest in the first `out_len` bytes; the rest is zero.
    pub fn finalize(mut self) -> [u8; 32] {
        self.total += self.buf_len as u64;
        self.buf[self.buf_len..].fill(0);
        compress_s(&mut self.h, &self.buf, self.total, true);
        let mut out = [0u8; 32];
        for (o, w) in out.chunks_exact_mut(4).zip(&self.h) {
            o.copy_from_slice(&w.to_le_bytes());
        }
        out[self.out_len..].fill(0);
        out
    }
}

/// BLAKE2s-256 of the concatenation of `parts` under a personalization.
pub fn blake2s_256(personal: &[u8; 8], parts: &[&[u8]]) -> [u8; 32] {
    let mut st = Blake2s::new(32, personal);
    for p in parts {
        st.update(p);
    }
    st.finalize()
}

// ============================================================================
// BLAKE2b gadget
// ============================================================================

pub(super) fn xor_words(cs: &mut ConstraintSystem, a: &Word, b: &Word) -> Word {
    Word::from_bits(
        a.bits()
            .iter()
            .zip(b.bits())
            .map(|(x, y)| xor2(cs, x, y))
            .collect(),
    )
}

/// One BLAKE2b compression. `t` is the byte counter after this block and `last` the
/// finalization flag; both are public.
pub fn blake2b_compress(
    cs: &mut ConstraintSystem,
    h: &[Word; 8],
    m: &[Word; 16],
    t: u128,
    last: bool,
) -> [Word; 8] {
    let mut v: Vec<Word> = h.to_vec();
    for (i, iv) in IV_B.iter().enumerate() {
        let k = match i {
            4 => iv ^ t as u64,
            5 => iv ^ (t >> 64) as u64,
            6 if last => !iv,
            _ => *iv,
        };
        v.push(Word::constant(k, 64));
    }
    for round in 0..12 {
        let s = &SIGMA[round % 10];
        for (i, q) in QUARTERS.iter().enumerate() {
            let (a, b, c, d) = (q[0], q[1], q[2], q[3]);
            v[a] = add_mod(cs, &[&v[a], &v[b], &m[s[2 * i]]], &[]);
            v[d] = xor_words(cs, &v[d], &v[a]).rotr(32);
            v[c] = add_mod(cs, &[&v[c], &v[d]], &[]);
            v[b] = xor_words(cs, &v[b], &v[c]).rotr(24);
            v[a] = add_mod(cs, &[&v[a], &v[b], &m[s[2 * i + 1]]], &[]);
            v[d] = xor_words(cs, &v[d], &v[a]).rotr(16);
            v[c] = add_mod(cs, &[&v[c], &v[d]], &[]);
            v[b] = xor_words(cs, &v[b], &v[c]).rotr(63);
        }
    }
    core::array::from_fn(|i| {
        Word::from_bits(
            (0..64)
                .map(|k| xor3(cs, &h[i].bits()[k], &v[i].bits()[k], &v[i + 8].bits()[k]))
                .collect(),
        )
    })
}

/// BLAKE2b-512 of a byte string (bits, least significant first within each byte) of public
/// length under a personalization. Returns the 512 digest bits in the same layout.
pub fn blake2b_512_gadget(
    cs: &mut ConstraintSystem,
    personal: &[u8; 16],
    message: &[Lc],
) -> Vec<Lc> {
    assert!(message.len() % 8 == 0, "byte strings hold whole bytes");
    let len = message.len() / 8;
    let blocks = len.div_ceil(128).max(1);
    let mut h: [Word; 8] = blake2b_iv(64, personal).map(|w| Word::constant(w, 64));
    for b in 0..blocks {
        let m: [Word; 16] = core::array::from_fn(|w| {
            Word::from_bits(
                (0..64)
                    .map(|k| {
                        message
                            .get(8 * 128 * b + 64 * w + k)
                            .cloned()
                            .unwrap_or_else(Lc::zero)
                    })
                    .collect(),
            )
        });
        let last = b + 1 == blocks;
        let t = if last { len } else { 128 * (b + 1) } as u128;
        h = blake2b_compress(cs, &h, &m, t, last);
    }
    h.into_iter().flat_map(Word::into_bits).collect()
}

/// The quarter-round of BLAKE2s and BLAKE3 on 32-bit words (rotations 16, 12, 8, 7).
pub(super) fn g32(cs: &mut ConstraintSystem, v: &mut [Word], q: &[usize; 4], x: &Word, y: &Word) {
    let (a, b, c, d) = (q[0], q[1], q[2], q[3]);
    v[a] = add_mod(cs, &[&v[a], &v[b], x], &[]);
    v[d] = xor_words(cs, &v[d], &v[a]).rotr(16);
    v[c] = add_mod(cs, &[&v[c], &v[d]], &[]);
    v[b] = xor_words(cs, &v[b], &v[c]).rotr(12);
    v[a] = add_mod(cs, &[&v[a], &v[b], y], &[]);
    v[d] = xor_words(cs, &v[d], &v[a]).rotr(8);
    v[c] = add_mod(cs, &[&v[c], &v[d]], &[]);
    v[b] = xor_words(cs, &v[b], &v[c]).rotr(7);
}

/// Initial chaining value of unkeyed BLAKE2s-256 with a personalization.
pub fn blake2s_256_iv(personal: &[u8; 8]) -> [u32; 8] {
    let mut h = IV_S;
    h[0] ^= 0x0101_0000 ^ 32;
    h[6] ^= u32::from_le_bytes(personal[..4].try_into().unwrap());
    h[7] ^= u32::from_le_bytes(personal[4..].try_into().unwrap());
    h
}

/// BLAKE2s-256 of exactly one 64-byte block (512 bits, least significant bit first within
/// each byte) under a personalization: one compression, about 21,000 rows.
pub fn blake2s_256_block_gadget(
    cs: &mut ConstraintSystem,
    personal: &[u8; 8],
    block: &[Lc],
) -> Vec<Lc> {
    assert_eq!(block.len(), 512, "one 64-byte block");
    let h: Vec<Word> = blake2s_256_iv(personal)
        .iter()
        .map(|&w| Word::constant(w as u64, 32))
        .collect();
    let m: Vec<Word> = block
        .chunks(32)
        .map(|w| Word::from_bits(w.to_vec()))
        .collect();
    let mut v = h.clone();
    for (i, iv) in IV_S.iter().enumerate() {
        let k = match i {
            4 => iv ^ 64,
            6 => !iv,
            _ => *iv,
        };
        v.push(Word::constant(k as u64, 32));
    }
    for s in &SIGMA {
        for (i, q) in QUARTERS.iter().enumerate() {
            g32(cs, &mut v, q, &m[s[2 * i]], &m[s[2 * i + 1]]);
        }
    }
    (0..8)
        .flat_map(|i| {
            (0..32)
                .map(|k| xor3(cs, &h[i].bits()[k], &v[i].bits()[k], &v[i + 8].bits()[k]))
                .collect::<Vec<_>>()
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hem::hash::{alloc_bits, bits_to_bytes};

    fn hex(s: &str) -> Vec<u8> {
        (0..s.len() / 2)
            .map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap())
            .collect()
    }

    #[test]
    fn blake2b_rfc7693_abc() {
        // RFC 7693 appendix A: BLAKE2b-512("abc"), no personalization.
        let got = blake2b_512(&[0; 16], &[b"abc"]);
        let want = hex(
            "ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d1\
             7d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923",
        );
        assert_eq!(got.to_vec(), want);
    }

    #[test]
    fn blake2s_rfc7693_abc() {
        // RFC 7693 appendix B: BLAKE2s-256("abc").
        let got = blake2s_256(&[0; 8], &[b"abc"]);
        let want = hex("508c5e8c327c14e2e1a72ba34eeb452f37458b209ed63a294d999b4c86675982");
        assert_eq!(got.to_vec(), want);
    }

    #[test]
    fn blake2b_block_boundaries_match_one_shot() {
        // Splitting the input anywhere, including at exact block multiples, must not change
        // the digest; a full final block is compressed with the finalization flag.
        let data: Vec<u8> = (0..400u32).map(|i| (i * 7 + 3) as u8).collect();
        for len in [0, 1, 127, 128, 129, 255, 256, 257, 384, 400] {
            let whole = blake2b_512(b"Zcash_ExpandSeed", &[&data[..len]]);
            for cut in [0, 1, 64, 128, 200] {
                let cut = cut.min(len);
                let split = blake2b_512(b"Zcash_ExpandSeed", &[&data[..cut], &data[cut..len]]);
                assert_eq!(whole, split, "len {len} cut {cut}");
            }
        }
        assert_ne!(
            blake2b_512(b"Zcash_ExpandSeed", &[&data[..128]]),
            blake2b_512(b"Zcash_ExpandSeee", &[&data[..128]])
        );
    }

    #[test]
    fn blake2s_block_gadget_matches_native() {
        let data: Vec<u8> = (0..64u32).map(|i| (i * 11 + 9) as u8).collect();
        for personal in [b"QsIwTre\x00", b"QsIwTre\xff"] {
            let mut cs = ConstraintSystem::new();
            let bits = alloc_bits(&mut cs, &data);
            let rows0 = cs.num_rows();
            let out = blake2s_256_block_gadget(&mut cs, personal, &bits);
            std::println!("BLAKE2s block: {} rows", cs.num_rows() - rows0);
            assert_eq!(
                bits_to_bytes(&cs, &out),
                blake2s_256(personal, &[&data]).to_vec()
            );
            let var = out[0].terms().last().expect("a variable").0 as usize;
            let (shape, z) = cs.finish();
            assert!(shape.is_satisfied(&z));
            let mut bad = z.clone();
            bad[var] += qsag_agg::field::Goldilocks::ONE;
            assert!(!shape.is_satisfied(&bad));
        }
    }

    #[test]
    fn blake2b_gadget_matches_native() {
        for len in [0usize, 1, 33, 128, 129, 169] {
            let data: Vec<u8> = (0..len as u32).map(|i| (i * 31 + 5) as u8).collect();
            let mut cs = ConstraintSystem::new();
            let bits = alloc_bits(&mut cs, &data);
            let rows0 = cs.num_rows();
            let out = blake2b_512_gadget(&mut cs, b"Zcash_ExpandSeed", &bits);
            let rows = cs.num_rows() - rows0;
            assert_eq!(
                bits_to_bytes(&cs, &out),
                blake2b_512(b"Zcash_ExpandSeed", &[&data]).to_vec(),
                "len {len}"
            );
            let blocks = len.div_ceil(128).max(1);
            assert!(rows <= 52_000 * blocks, "len {len}: {rows} rows");
            let digest_var = out[0].terms().last().expect("a variable").0 as usize;
            let (shape, z) = cs.finish();
            assert!(shape.is_satisfied(&z));
            // A changed digest bit violates the feed-forward row that defines it.
            let mut bad = z.clone();
            bad[digest_var] += qsag_agg::field::Goldilocks::ONE;
            assert!(!shape.is_satisfied(&bad));
        }
    }
}
