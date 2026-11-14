//! Zero-dependency FIPS 180-4 `SHA-256`, `SHA-512`, RFC 2104 `HMAC-SHA512`, and `RIPEMD-160`
//! (`HASH160`) with `write_volatile` zeroization on drop.

use crate::ct::{ct_zeroize_bytes, ct_zeroize_u32s, ct_zeroize_u64s};

const SHA256_K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

fn sha256_compress(state: &mut [u32; 8], block: &[u8; 64]) {
    let mut w = [0u32; 64];
    for (slot, chunk) in w.iter_mut().take(16).zip(block.chunks_exact(4)) {
        *slot = u32::from_be_bytes([chunk[0], chunk[1], chunk[2], chunk[3]]);
    }
    for i in 16..64 {
        let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
        let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
        w[i] = w[i - 16]
            .wrapping_add(s0)
            .wrapping_add(w[i - 7])
            .wrapping_add(s1);
    }
    let mut a = state[0];
    let mut b = state[1];
    let mut c = state[2];
    let mut d = state[3];
    let mut e = state[4];
    let mut f = state[5];
    let mut g = state[6];
    let mut h = state[7];

    for (&k, &word) in SHA256_K.iter().zip(&w) {
        let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
        let ch = (e & f) ^ ((!e) & g);
        let temp1 = h
            .wrapping_add(s1)
            .wrapping_add(ch)
            .wrapping_add(k)
            .wrapping_add(word);
        let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
        let maj = (a & b) ^ (a & c) ^ (b & c);
        let temp2 = s0.wrapping_add(maj);

        h = g;
        g = f;
        f = e;
        e = d.wrapping_add(temp1);
        d = c;
        c = b;
        b = a;
        a = temp1.wrapping_add(temp2);
    }

    state[0] = state[0].wrapping_add(a);
    state[1] = state[1].wrapping_add(b);
    state[2] = state[2].wrapping_add(c);
    state[3] = state[3].wrapping_add(d);
    state[4] = state[4].wrapping_add(e);
    state[5] = state[5].wrapping_add(f);
    state[6] = state[6].wrapping_add(g);
    state[7] = state[7].wrapping_add(h);
    ct_zeroize_u32s(&mut w);
}

/// Streaming zeroizing `SHA-256` hasher.
pub struct Sha256Hasher {
    state: [u32; 8],
    buf: [u8; 64],
    buf_len: usize,
    total_len: u64,
}

impl Default for Sha256Hasher {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for Sha256Hasher {
    fn drop(&mut self) {
        ct_zeroize_u32s(&mut self.state);
        ct_zeroize_bytes(&mut self.buf);
    }
}

impl Sha256Hasher {
    pub const fn new() -> Self {
        Self {
            state: [
                0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
                0x5be0cd19,
            ],
            buf: [0u8; 64],
            buf_len: 0,
            total_len: 0,
        }
    }

    pub fn update(&mut self, mut data: &[u8]) {
        self.total_len = self.total_len.wrapping_add(data.len() as u64);
        while !data.is_empty() {
            let take = (64 - self.buf_len).min(data.len());
            self.buf[self.buf_len..self.buf_len + take].copy_from_slice(&data[..take]);
            self.buf_len += take;
            data = &data[take..];
            if self.buf_len == 64 {
                sha256_compress(&mut self.state, &self.buf);
                self.buf_len = 0;
            }
        }
    }

    pub fn finalize(mut self) -> [u8; 32] {
        let bit_len = self.total_len.wrapping_mul(8);
        self.buf[self.buf_len] = 0x80;
        self.buf_len += 1;
        if self.buf_len > 56 {
            for slot in &mut self.buf[self.buf_len..64] {
                *slot = 0;
            }
            sha256_compress(&mut self.state, &self.buf);
            self.buf_len = 0;
        }
        for slot in &mut self.buf[self.buf_len..56] {
            *slot = 0;
        }
        self.buf[56..64].copy_from_slice(&bit_len.to_be_bytes());
        sha256_compress(&mut self.state, &self.buf);

        let mut out = [0u8; 32];
        for (chunk, word) in out.chunks_exact_mut(4).zip(&self.state) {
            chunk.copy_from_slice(&word.to_be_bytes());
        }
        out
    }
}

/// One-shot `SHA-256`.
pub fn sha256(data: &[u8]) -> [u8; 32] {
    let mut h = Sha256Hasher::new();
    h.update(data);
    h.finalize()
}

/// BIP-340 / BIP-341 tagged `SHA-256`: `SHA256(SHA256(tag) || SHA256(tag) || msg)`.
pub fn sha256_tagged(tag: &[u8], msg: &[u8]) -> [u8; 32] {
    let tag_hash = sha256(tag);
    let mut h = Sha256Hasher::new();
    h.update(&tag_hash);
    h.update(&tag_hash);
    h.update(msg);
    h.finalize()
}

const SHA512_K: [u64; 80] = [
    0x428a2f98d728ae22,
    0x7137449123ef65cd,
    0xb5c0fbcfec4d3b2f,
    0xe9b5dba58189dbbc,
    0x3956c25bf348b538,
    0x59f111f1b605d019,
    0x923f82a4af194f9b,
    0xab1c5ed5da6d8118,
    0xd807aa98a3030242,
    0x12835b0145706fbe,
    0x243185be4ee4b28c,
    0x550c7dc3d5ffb4e2,
    0x72be5d74f27b896f,
    0x80deb1fe3b1696b1,
    0x9bdc06a725c71235,
    0xc19bf174cf692694,
    0xe49b69c19ef14ad2,
    0xefbe4786384f25e3,
    0x0fc19dc68b8cd5b5,
    0x240ca1cc77ac9c65,
    0x2de92c6f592b0275,
    0x4a7484aa6ea6e483,
    0x5cb0a9dcbd41fbd4,
    0x76f988da831153b5,
    0x983e5152ee66dfab,
    0xa831c66d2db43210,
    0xb00327c898fb213f,
    0xbf597fc7beef0ee4,
    0xc6e00bf33da88fc2,
    0xd5a79147930aa725,
    0x06ca6351e003826f,
    0x142929670a0e6e70,
    0x27b70a8546d22ffc,
    0x2e1b21385c26c926,
    0x4d2c6dfc5ac42aed,
    0x53380d139d95b3df,
    0x650a73548baf63de,
    0x766a0abb3c77b2a8,
    0x81c2c92e47edaee6,
    0x92722c851482353b,
    0xa2bfe8a14cf10364,
    0xa81a664bbc423001,
    0xc24b8b70d0f89791,
    0xc76c51a30654be30,
    0xd192e819d6ef5218,
    0xd69906245565a910,
    0xf40e35855771202a,
    0x106aa07032bbd1b8,
    0x19a4c116b8d2d0c8,
    0x1e376c085141ab53,
    0x2748774cdf8eeb99,
    0x34b0bcb5e19b48a8,
    0x391c0cb3c5c95a63,
    0x4ed8aa4ae3418acb,
    0x5b9cca4f7763e373,
    0x682e6ff3d6b2b8a3,
    0x748f82ee5defb2fc,
    0x78a5636f43172f60,
    0x84c87814a1f0ab72,
    0x8cc702081a6439ec,
    0x90befffa23631e28,
    0xa4506cebde82bde9,
    0xbef9a3f7b2c67915,
    0xc67178f2e372532b,
    0xca273eceea26619c,
    0xd186b8c721c0c207,
    0xeada7dd6cde0eb1e,
    0xf57d4f7fee6ed178,
    0x06f067aa72176fba,
    0x0a637dc5a2c898a6,
    0x113f9804bef90dae,
    0x1b710b35131c471b,
    0x28db77f523047d84,
    0x32caab7b40c72493,
    0x3c9ebe0a15c9bebc,
    0x431d67c49c100d4c,
    0x4cc5d4becb3e42b6,
    0x597f299cfc657e2a,
    0x5fcb6fab3ad6faec,
    0x6c44198c4a475817,
];

fn sha512_compress(state: &mut [u64; 8], block: &[u8; 128]) {
    let mut w = [0u64; 80];
    for (slot, chunk) in w.iter_mut().take(16).zip(block.chunks_exact(8)) {
        *slot = u64::from_be_bytes([
            chunk[0], chunk[1], chunk[2], chunk[3], chunk[4], chunk[5], chunk[6], chunk[7],
        ]);
    }
    for i in 16..80 {
        let s0 = w[i - 15].rotate_right(1) ^ w[i - 15].rotate_right(8) ^ (w[i - 15] >> 7);
        let s1 = w[i - 2].rotate_right(19) ^ w[i - 2].rotate_right(61) ^ (w[i - 2] >> 6);
        w[i] = w[i - 16]
            .wrapping_add(s0)
            .wrapping_add(w[i - 7])
            .wrapping_add(s1);
    }
    let mut a = state[0];
    let mut b = state[1];
    let mut c = state[2];
    let mut d = state[3];
    let mut e = state[4];
    let mut f = state[5];
    let mut g = state[6];
    let mut h = state[7];

    for (&k, &word) in SHA512_K.iter().zip(&w) {
        let s1 = e.rotate_right(14) ^ e.rotate_right(18) ^ e.rotate_right(41);
        let ch = (e & f) ^ ((!e) & g);
        let temp1 = h
            .wrapping_add(s1)
            .wrapping_add(ch)
            .wrapping_add(k)
            .wrapping_add(word);
        let s0 = a.rotate_right(28) ^ a.rotate_right(34) ^ a.rotate_right(39);
        let maj = (a & b) ^ (a & c) ^ (b & c);
        let temp2 = s0.wrapping_add(maj);

        h = g;
        g = f;
        f = e;
        e = d.wrapping_add(temp1);
        d = c;
        c = b;
        b = a;
        a = temp1.wrapping_add(temp2);
    }

    state[0] = state[0].wrapping_add(a);
    state[1] = state[1].wrapping_add(b);
    state[2] = state[2].wrapping_add(c);
    state[3] = state[3].wrapping_add(d);
    state[4] = state[4].wrapping_add(e);
    state[5] = state[5].wrapping_add(f);
    state[6] = state[6].wrapping_add(g);
    state[7] = state[7].wrapping_add(h);
    ct_zeroize_u64s(&mut w);
}

/// Streaming zeroizing `SHA-512` hasher.
pub struct Sha512Hasher {
    state: [u64; 8],
    buf: [u8; 128],
    buf_len: usize,
    total_len: u128,
}

impl Default for Sha512Hasher {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for Sha512Hasher {
    fn drop(&mut self) {
        ct_zeroize_u64s(&mut self.state);
        ct_zeroize_bytes(&mut self.buf);
    }
}

impl Sha512Hasher {
    pub const fn new() -> Self {
        Self {
            state: [
                0x6a09e667f3bcc908,
                0xbb67ae8584caa73b,
                0x3c6ef372fe94f82b,
                0xa54ff53a5f1d36f1,
                0x510e527fade682d1,
                0x9b05688c2b3e6c1f,
                0x1f83d9abfb41bd6b,
                0x5be0cd19137e2179,
            ],
            buf: [0u8; 128],
            buf_len: 0,
            total_len: 0,
        }
    }

    pub fn update(&mut self, mut data: &[u8]) {
        self.total_len = self.total_len.wrapping_add(data.len() as u128);
        while !data.is_empty() {
            let take = (128 - self.buf_len).min(data.len());
            self.buf[self.buf_len..self.buf_len + take].copy_from_slice(&data[..take]);
            self.buf_len += take;
            data = &data[take..];
            if self.buf_len == 128 {
                sha512_compress(&mut self.state, &self.buf);
                self.buf_len = 0;
            }
        }
    }

    pub fn finalize(mut self) -> [u8; 64] {
        let bit_len = self.total_len.wrapping_mul(8);
        self.buf[self.buf_len] = 0x80;
        self.buf_len += 1;
        if self.buf_len > 112 {
            for slot in &mut self.buf[self.buf_len..128] {
                *slot = 0;
            }
            sha512_compress(&mut self.state, &self.buf);
            self.buf_len = 0;
        }
        for slot in &mut self.buf[self.buf_len..112] {
            *slot = 0;
        }
        self.buf[112..128].copy_from_slice(&bit_len.to_be_bytes());
        sha512_compress(&mut self.state, &self.buf);

        let mut out = [0u8; 64];
        for (chunk, word) in out.chunks_exact_mut(8).zip(&self.state) {
            chunk.copy_from_slice(&word.to_be_bytes());
        }
        out
    }
}

/// One-shot `SHA-512`.
pub fn sha512(data: &[u8]) -> [u8; 64] {
    let mut h = Sha512Hasher::new();
    h.update(data);
    h.finalize()
}

/// RFC 2104 `HMAC-SHA512` (zeroizes key pads and inner digest via `write_volatile`).
pub fn hmac_sha512(key: &[u8], data: &[u8]) -> [u8; 64] {
    let mut k_block = [0u8; 128];
    if key.len() > 128 {
        let mut hk = sha512(key);
        k_block[..64].copy_from_slice(&hk);
        ct_zeroize_bytes(&mut hk);
    } else {
        k_block[..key.len()].copy_from_slice(key);
    }
    let mut ipad = [0x36u8; 128];
    let mut opad = [0x5cu8; 128];
    for ((inner, outer), &key_byte) in ipad.iter_mut().zip(&mut opad).zip(&k_block) {
        *inner ^= key_byte;
        *outer ^= key_byte;
    }

    let mut inner = Sha512Hasher::new();
    inner.update(&ipad);
    inner.update(data);
    let mut inner_digest = inner.finalize();

    let mut outer = Sha512Hasher::new();
    outer.update(&opad);
    outer.update(&inner_digest);
    let out = outer.finalize();

    ct_zeroize_bytes(&mut k_block);
    ct_zeroize_bytes(&mut ipad);
    ct_zeroize_bytes(&mut opad);
    ct_zeroize_bytes(&mut inner_digest);
    out
}

// ============================================================================
// RIPEMD-160 & Bitcoin HASH160 = RIPEMD160(SHA256(data))
// ============================================================================

const RMD_RL: [usize; 80] = [
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5,
    2, 14, 11, 8, 3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12, 1, 9, 11, 10, 0, 8, 12, 4,
    13, 3, 7, 15, 14, 5, 6, 2, 4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13,
];

const RMD_RR: [usize; 80] = [
    5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12, 6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12,
    4, 9, 1, 2, 15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13, 8, 6, 4, 1, 3, 11, 15, 0, 5,
    12, 2, 13, 9, 7, 10, 14, 12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11,
];

const RMD_SL: [u32; 80] = [
    11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8, 7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15,
    9, 11, 7, 13, 12, 11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5, 11, 12, 14, 15, 14,
    15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12, 9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6,
];

const RMD_SR: [u32; 80] = [
    8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6, 9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12,
    7, 6, 15, 13, 11, 9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5, 15, 5, 8, 11, 14, 14,
    6, 14, 6, 9, 12, 9, 12, 5, 15, 8, 8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11,
];

#[inline]
fn rmd_f(round: usize, x: u32, y: u32, z: u32) -> u32 {
    match round / 16 {
        0 => x ^ y ^ z,
        1 => (x & y) | ((!x) & z),
        2 => (x | (!y)) ^ z,
        3 => (x & z) | (y & (!z)),
        _ => x ^ (y | (!z)),
    }
}

#[inline]
fn rmd_kl(round: usize) -> u32 {
    match round / 16 {
        0 => 0x0000_0000,
        1 => 0x5a82_7999,
        2 => 0x6ed9_eba1,
        3 => 0x8f1b_bcdc,
        _ => 0xa953_fd4e,
    }
}

#[inline]
fn rmd_kr(round: usize) -> u32 {
    match round / 16 {
        0 => 0x50a2_8be6,
        1 => 0x5c4d_d124,
        2 => 0x6d70_3ef3,
        3 => 0x7a6d_76e9,
        _ => 0x0000_0000,
    }
}

fn ripemd160_compress(state: &mut [u32; 5], block: &[u8; 64]) {
    let mut x = [0u32; 16];
    for (slot, chunk) in x.iter_mut().zip(block.chunks_exact(4)) {
        *slot = u32::from_le_bytes([chunk[0], chunk[1], chunk[2], chunk[3]]);
    }

    let (mut al, mut bl, mut cl, mut dl, mut el) =
        (state[0], state[1], state[2], state[3], state[4]);
    let (mut ar, mut br, mut cr, mut dr, mut er) =
        (state[0], state[1], state[2], state[3], state[4]);

    for j in 0..80 {
        let tl = al
            .wrapping_add(rmd_f(j, bl, cl, dl))
            .wrapping_add(x[RMD_RL[j]])
            .wrapping_add(rmd_kl(j))
            .rotate_left(RMD_SL[j])
            .wrapping_add(el);
        al = el;
        el = dl;
        dl = cl.rotate_left(10);
        cl = bl;
        bl = tl;

        let tr = ar
            .wrapping_add(rmd_f(79 - j, br, cr, dr))
            .wrapping_add(x[RMD_RR[j]])
            .wrapping_add(rmd_kr(j))
            .rotate_left(RMD_SR[j])
            .wrapping_add(er);
        ar = er;
        er = dr;
        dr = cr.rotate_left(10);
        cr = br;
        br = tr;
    }

    let t = state[1].wrapping_add(cl).wrapping_add(dr);
    state[1] = state[2].wrapping_add(dl).wrapping_add(er);
    state[2] = state[3].wrapping_add(el).wrapping_add(ar);
    state[3] = state[4].wrapping_add(al).wrapping_add(br);
    state[4] = state[0].wrapping_add(bl).wrapping_add(cr);
    state[0] = t;
    ct_zeroize_u32s(&mut x);
}

/// One-shot `RIPEMD-160` (`20 B` output).
pub fn ripemd160(mut data: &[u8]) -> [u8; 20] {
    let total_len = data.len() as u64;
    let mut state: [u32; 5] = [0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0];
    let mut buf = [0u8; 64];
    while data.len() >= 64 {
        buf.copy_from_slice(&data[..64]);
        ripemd160_compress(&mut state, &buf);
        data = &data[64..];
    }
    let rem = data.len();
    buf.fill(0);
    buf[..rem].copy_from_slice(data);
    buf[rem] = 0x80;
    if rem >= 56 {
        ripemd160_compress(&mut state, &buf);
        buf.fill(0);
    }
    buf[56..64].copy_from_slice(&(total_len.wrapping_mul(8)).to_le_bytes());
    ripemd160_compress(&mut state, &buf);

    let mut out = [0u8; 20];
    for (chunk, word) in out.chunks_exact_mut(4).zip(&state) {
        chunk.copy_from_slice(&word.to_le_bytes());
    }
    ct_zeroize_u32s(&mut state);
    ct_zeroize_bytes(&mut buf);
    out
}

/// Bitcoin P2PKH / P2WPKH `HASH160(data) = RIPEMD160(SHA256(data))` (wiping intermediate SHA-256).
pub fn hash160(data: &[u8]) -> [u8; 20] {
    let mut sha = sha256(data);
    let out = ripemd160(&sha);
    ct_zeroize_bytes(&mut sha);
    out
}
