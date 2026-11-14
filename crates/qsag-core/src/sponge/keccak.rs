//! NIST FIPS 202 `Keccak-f[1600]` & `SHAKE256`, NIST SP 800-185 `cSHAKE256`, self-delimiting
//! LEB128 `encode_multi_frame`, and compile-time typestate `FiatShamirTranscript<Phase>`.
//!
//! Matches `lean/Qsag/Keccak.lean` bit-for-bit across all rate boundaries, customization prefixes,
//! and official FIPS 202 conformance vectors.

use alloc::vec;
use alloc::vec::Vec;
use core::marker::PhantomData;

/// Runtime-selected batched Keccak permutation, including four-way SIMD.
pub use qsag_asm::keccak_f1600_batch;

use crate::field::goldilocks::{Goldilocks, GoldilocksExt2};
use crate::wipe::{wipe_bytes, wipe_bytes32, wipe_u64s};

/// Sponge rate of `SHAKE256` and `cSHAKE256` in bytes ($1088 / 8 = 136$).
pub const SHAKE256_RATE_BYTES: usize = 136;

/// Number of 64-bit lanes in the `SHAKE256` / `cSHAKE256` rate ($136 / 8 = 17$).
pub const SHAKE256_RATE_LANES: usize = 17;

/// Standard 24 FIPS 202 `Keccak-f[1600]` round constants.
pub const KECCAK_ROUND_CONSTANTS: [u64; 24] = [
    0x0000_0000_0000_0001,
    0x0000_0000_0000_8082,
    0x8000_0000_0000_808a,
    0x8000_0000_8000_8000,
    0x0000_0000_0000_808b,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8009,
    0x0000_0000_0000_008a,
    0x0000_0000_0000_0088,
    0x0000_0000_8000_8009,
    0x0000_0000_8000_000a,
    0x0000_0000_8000_808b,
    0x8000_0000_0000_008b,
    0x8000_0000_0000_8089,
    0x8000_0000_0000_8003,
    0x8000_0000_0000_8002,
    0x8000_0000_0000_0080,
    0x0000_0000_0000_800a,
    0x8000_0000_8000_000a,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8080,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8008,
];

/// FIPS 202 $\rho$ rotation offsets indexed by `x + 5 * y`.
pub const KECCAK_ROTATION_OFFSETS: [u32; 25] = [
    0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14,
];

/// Domain customization tags for `FiatShamirTranscript`.
pub const FS_SEED_CUSTOMIZATION: &[u8] = b"QSAG.CRYPTO.FS.SEED/v1";
pub const FS_BIND_CUSTOMIZATION: &[u8] = b"QSAG.CRYPTO.FS.BIND/v1";
pub const FS_INSTANCE_CUSTOMIZATION: &[u8] = b"QSAG.CRYPTO.FS.INSTANCE/v1";
pub const FS_ABSORB_CUSTOMIZATION: &[u8] = b"QSAG.CRYPTO.FS.ABSORB/v1";
pub const FS_SQUEEZE_CUSTOMIZATION: &[u8] = b"QSAG.CRYPTO.FS.SQUEEZE/v1";
pub const FS_RATCHET_CUSTOMIZATION: &[u8] = b"QSAG.CRYPTO.FS.RATCHET/v1";

const KECCAK_PI_SOURCE_FOR_TARGET: [(usize, u32); 25] = {
    let mut out = [(0usize, 0u32); 25];
    let mut src = 0usize;
    while src < 25 {
        let x = src % 5;
        let y = src / 5;
        let dst = y + 5 * ((2 * x + 3 * y) % 5);
        out[dst] = (src, KECCAK_ROTATION_OFFSETS[src]);
        src += 1;
    }
    out
};

/// Exact 24-round `Keccak-f[1600]` permutation over 25 little-endian 64-bit lanes.
#[inline]
pub const fn keccak_f1600(state: &mut [u64; 25]) {
    let mut a = *state;
    let mut round = 0;
    while round < 24 {
        let rc = KECCAK_ROUND_CONSTANTS[round];
        round += 1;
        // Theta
        let c0 = a[0] ^ a[5] ^ a[10] ^ a[15] ^ a[20];
        let c1 = a[1] ^ a[6] ^ a[11] ^ a[16] ^ a[21];
        let c2 = a[2] ^ a[7] ^ a[12] ^ a[17] ^ a[22];
        let c3 = a[3] ^ a[8] ^ a[13] ^ a[18] ^ a[23];
        let c4 = a[4] ^ a[9] ^ a[14] ^ a[19] ^ a[24];

        let d0 = c4 ^ c1.rotate_left(1);
        let d1 = c0 ^ c2.rotate_left(1);
        let d2 = c1 ^ c3.rotate_left(1);
        let d3 = c2 ^ c4.rotate_left(1);
        let d4 = c3 ^ c0.rotate_left(1);

        let mut y = 0usize;
        while y < 25 {
            a[y] ^= d0;
            a[y + 1] ^= d1;
            a[y + 2] ^= d2;
            a[y + 3] ^= d3;
            a[y + 4] ^= d4;
            y += 5;
        }

        // Rho + Pi (register-promoted, 0 `% 5` / `/ 5` divisions)
        let mut b = [0u64; 25];
        let mut dst = 0usize;
        while dst < 25 {
            let (src, rot) = KECCAK_PI_SOURCE_FOR_TARGET[dst];
            b[dst] = a[src].rotate_left(rot);
            dst += 1;
        }

        // Chi
        let mut row = 0usize;
        while row < 25 {
            let b0 = b[row];
            let b1 = b[row + 1];
            let b2 = b[row + 2];
            let b3 = b[row + 3];
            let b4 = b[row + 4];
            a[row] = b0 ^ ((!b1) & b2);
            a[row + 1] = b1 ^ ((!b2) & b3);
            a[row + 2] = b2 ^ ((!b3) & b4);
            a[row + 3] = b3 ^ ((!b4) & b0);
            a[row + 4] = b4 ^ ((!b0) & b1);
            row += 5;
        }

        // Iota
        a[0] ^= rc;
    }
    *state = a;
}

/// Public midstate for a nonempty static customization fitting in one rate block.
/// Panics at compile time for empty tags or tags longer than 128 bytes.
/// This is bytepad(left_encode(136) || encode_string("") || encode_string(tag), 136).
pub const fn cshake256_static_midstate(tag: &[u8]) -> [u64; 25] {
    assert!(!tag.is_empty() && tag.len() <= 128);
    let mut block = [0u8; SHAKE256_RATE_BYTES];
    block[0] = 1;
    block[1] = 136;
    block[2] = 1;
    let bits = tag.len() * 8;
    let offset = if bits < 256 {
        block[4] = 1;
        block[5] = bits as u8;
        6
    } else {
        block[4] = 2;
        block[5] = (bits >> 8) as u8;
        block[6] = bits as u8;
        7
    };
    let mut i = 0;
    while i < tag.len() {
        block[offset + i] = tag[i];
        i += 1;
    }
    let mut state = [0u64; 25];
    i = 0;
    while i < SHAKE256_RATE_BYTES {
        state[i / 8] |= (block[i] as u64) << (8 * (i % 8));
        i += 1;
    }
    keccak_f1600(&mut state);
    state
}

fn cached_customization_midstate(tag: &[u8]) -> Option<[u64; 25]> {
    macro_rules! cached {
        ($($tag:literal),* $(,)?) => {
            match tag {
                $($tag => Some(const { cshake256_static_midstate($tag) }),)*
                _ => None,
            }
        };
    }
    cached!(
        b"QSAG.CRYPTO.FS.SEED/v1",
        b"QSAG.CRYPTO.FS.BIND/v1",
        b"QSAG.CRYPTO.FS.INSTANCE/v1",
        b"QSAG.CRYPTO.FS.ABSORB/v1",
        b"QSAG.CRYPTO.FS.SQUEEZE/v1",
        b"QSAG.CRYPTO.FS.RATCHET/v1",
        b"QSAG.RSS.U64.OPEN.COM/v1",
        b"QSAG.RSS.TRIPLE.PRG/v1",
        b"QSAG.RSS.CHI.MASK/v2",
        b"QSAG.RSS.DZK.RHOS.POLY/v2",
        b"QSAG.RSS.DZK.ZPRG.POLY/v2",
        b"QSAG.TH.PRF/v1",
        b"QSAG.TH.TWEAK/v1",
    )
}

/// SP 800-185 minimal non-empty big-endian byte representation (`[0]` for `0`) over `u64`.
pub fn nat_bytes_be_u64(mut value: u64) -> Vec<u8> {
    if value == 0 {
        return vec![0u8];
    }
    let mut le = Vec::with_capacity(8);
    while value > 0 {
        le.push((value & 0xFF) as u8);
        value >>= 8;
    }
    le.reverse();
    le
}

/// SP 800-185 minimal non-empty big-endian byte representation (`[0]` for `0`).
pub fn nat_bytes_be(value: usize) -> Vec<u8> {
    nat_bytes_be_u64(value as u64)
}

/// SP 800-185 `left_encode` over `u64` (overflow-free on 32-bit targets).
pub fn sp800_185_left_encode_u64(value: u64) -> Vec<u8> {
    let bytes = nat_bytes_be_u64(value);
    let mut out = Vec::with_capacity(1 + bytes.len());
    out.push(bytes.len() as u8);
    out.extend_from_slice(&bytes);
    out
}

/// SP 800-185 `left_encode`, matching `Qsag.leftEncode`.
pub fn sp800_185_left_encode(value: usize) -> Vec<u8> {
    sp800_185_left_encode_u64(value as u64)
}

/// SP 800-185 `encode_string`, matching `Qsag.encodeString` without 32-bit `8 * len` overflow.
pub fn sp800_185_encode_string(bytes: &[u8]) -> Vec<u8> {
    let bit_len = (bytes.len() as u64) * 8;
    let mut out = sp800_185_left_encode_u64(bit_len);
    out.extend_from_slice(bytes);
    out
}

/// SP 800-185 `bytepad`, matching `Qsag.bytepad`.
pub fn sp800_185_bytepad(bytes: &[u8], width: usize) -> Vec<u8> {
    if width == 0 {
        return Vec::new();
    }
    let mut out = sp800_185_left_encode(width);
    out.extend_from_slice(bytes);
    let rem = out.len() % width;
    if rem != 0 {
        out.resize(out.len() + (width - rem), 0u8);
    }
    out
}

/// SP 800-185 `cSHAKE256` customization prefix for empty function-name `N = ""` and caller `S`.
pub fn cshake256_customization_prefix(customization: &[u8]) -> Vec<u8> {
    let mut inner = sp800_185_encode_string(&[]);
    inner.extend_from_slice(&sp800_185_encode_string(customization));
    sp800_185_bytepad(&inner, SHAKE256_RATE_BYTES)
}

#[inline]
fn xor_rate_block(state: &mut [u64; 25], block: &[u8; SHAKE256_RATE_BYTES]) {
    let mut lane_idx = 0;
    while lane_idx < SHAKE256_RATE_LANES {
        let off = 8 * lane_idx;
        let lane = u64::from_le_bytes([
            block[off],
            block[off + 1],
            block[off + 2],
            block[off + 3],
            block[off + 4],
            block[off + 5],
            block[off + 6],
            block[off + 7],
        ]);
        state[lane_idx] ^= lane;
        lane_idx += 1;
    }
}

/// Streaming SP 800-185 `cSHAKE256` / FIPS 202 `SHAKE256` XOF sponge (`Drop`-zeroized).
pub struct Cshake256Xof {
    state: [u64; 25],
    buf: [u8; SHAKE256_RATE_BYTES],
    buf_len: usize,
    suffix: u8,
    squeezing: bool,
    squeeze_offset: usize,
}

/// Type alias for uncustomized FIPS 202 `SHAKE256` streaming XOF.
pub type Shake256Xof = Cshake256Xof;

impl Drop for Cshake256Xof {
    fn drop(&mut self) {
        wipe_u64s(&mut self.state);
        wipe_bytes(&mut self.buf);
    }
}

impl Cshake256Xof {
    /// Initialize `cSHAKE256` with empty function-name `N = ""` and customization `S`.
    /// Per NIST SP 800-185 §3.3, empty `S` falls back identically to `SHAKE256` (`suffix = 0x1F`).
    pub fn new(customization: &[u8]) -> Self {
        let mut xof = Self {
            state: [0u64; 25],
            buf: [0u8; SHAKE256_RATE_BYTES],
            buf_len: 0,
            suffix: if customization.is_empty() { 0x1f } else { 0x04 },
            squeezing: false,
            squeeze_offset: 0,
        };
        if !customization.is_empty() {
            if let Some(state) = cached_customization_midstate(customization) {
                xof.state = state;
            } else {
                let prefix = cshake256_customization_prefix(customization);
                xof.absorb(&prefix);
            }
        }
        xof
    }

    /// Initialize uncustomized NIST FIPS 202 `SHAKE256` (`suffix = 0x1F`).
    #[inline]
    pub fn new_shake256() -> Self {
        Self::new(&[])
    }

    /// Absorb arbitrary bytes into the sponge prior to squeezing.
    pub fn absorb(&mut self, mut data: &[u8]) {
        assert!(
            !self.squeezing,
            "cannot absorb into Cshake256Xof after squeezing began"
        );
        while !data.is_empty() {
            let space = SHAKE256_RATE_BYTES - self.buf_len;
            let take = space.min(data.len());
            self.buf[self.buf_len..self.buf_len + take].copy_from_slice(&data[..take]);
            self.buf_len += take;
            data = &data[take..];
            if self.buf_len == SHAKE256_RATE_BYTES {
                xor_rate_block(&mut self.state, &self.buf);
                keccak_f1600(&mut self.state);
                self.buf_len = 0;
            }
        }
    }

    fn finalize_to_squeeze(&mut self) {
        if self.squeezing {
            return;
        }
        for b in &mut self.buf[self.buf_len..] {
            *b = 0;
        }
        self.buf[self.buf_len] ^= self.suffix;
        self.buf[SHAKE256_RATE_BYTES - 1] ^= 0x80;
        xor_rate_block(&mut self.state, &self.buf);
        keccak_f1600(&mut self.state);
        self.squeezing = true;
        self.squeeze_offset = 0;
    }

    /// Squeeze arbitrary output bytes from the finalized sponge.
    pub fn squeeze(&mut self, out: &mut [u8]) {
        self.finalize_to_squeeze();
        let mut written = 0usize;
        while written < out.len() {
            if self.squeeze_offset == SHAKE256_RATE_BYTES {
                keccak_f1600(&mut self.state);
                self.squeeze_offset = 0;
            }
            let lane_idx = self.squeeze_offset / 8;
            let byte_in_lane = self.squeeze_offset % 8;
            let b = ((self.state[lane_idx] >> (8 * byte_in_lane)) & 0xFF) as u8;
            out[written] = b;
            written += 1;
            self.squeeze_offset += 1;
        }
    }
}

/// Four independent single-block SHAKE256 hashes, returning the first 32 bytes.
/// Rejects inputs needing a second block, rather than silently truncating them.
pub(crate) fn shake256_4x_32(inputs: [&[u8]; 4]) -> Option<[[u8; 32]; 4]> {
    if inputs
        .iter()
        .any(|input| input.len() >= SHAKE256_RATE_BYTES)
    {
        return None;
    }
    let mut states = qsag_asm::KeccakState4x::default();
    for (i, input) in inputs.iter().enumerate() {
        for (j, byte) in input.iter().copied().enumerate() {
            states.0[j / 8][i] ^= u64::from(byte) << (8 * (j % 8));
        }
        let end = input.len();
        states.0[end / 8][i] ^= 0x1f << (8 * (end % 8));
        states.0[16][i] ^= 1 << 63;
    }
    qsag_asm::keccak_f1600_x4(&mut states);
    let mut out = [[0u8; 32]; 4];
    for (i, output) in out.iter_mut().enumerate() {
        for (j, word) in output.as_chunks_mut::<8>().0.iter_mut().enumerate() {
            word.copy_from_slice(&states.0[j][i].to_le_bytes());
        }
    }
    qsag_asm::volatile_fill(&mut states.0, [0; 4]);
    Some(out)
}

/// Four interleaved `cSHAKE256` output streams produced by the four-state permutation.
///
/// Stream `i in 0..4` is exactly `cSHAKE256(seed || [i], S)` for the customization `S` whose
/// absorbed-prefix state is `midstate`; output word `w` is lane `(w / 4) % 17` of stream `w % 4`,
/// read in successive rate blocks. One permutation call yields 68 words (`Drop`-zeroized).
pub struct Cshake256WordStream4 {
    states: qsag_asm::KeccakState4x,
    next: usize,
}

impl Drop for Cshake256WordStream4 {
    fn drop(&mut self) {
        qsag_asm::volatile_fill(&mut self.states.0, [0; 4]);
    }
}

impl Cshake256WordStream4 {
    /// Words available per permutation: four streams of [`SHAKE256_RATE_LANES`] lanes.
    pub const WORDS_PER_BLOCK: usize = 4 * SHAKE256_RATE_LANES;

    /// `midstate` must come from [`cshake256_static_midstate`]; `seed` plus the stream index
    /// must fit in one rate block with its padding (`seed.len() <= 134`).
    pub fn new(midstate: &[u64; 25], seed: &[u8]) -> Self {
        assert!(seed.len() + 2 <= SHAKE256_RATE_BYTES);
        let mut states = qsag_asm::KeccakState4x::default();
        for (lane, row) in states.0.iter_mut().enumerate() {
            *row = [midstate[lane]; 4];
        }
        for i in 0..4 {
            for (j, byte) in seed.iter().copied().enumerate() {
                states.0[j / 8][i] ^= u64::from(byte) << (8 * (j % 8));
            }
            let idx = seed.len();
            states.0[idx / 8][i] ^= (i as u64) << (8 * (idx % 8));
            let end = idx + 1;
            states.0[end / 8][i] ^= 0x04 << (8 * (end % 8));
            states.0[SHAKE256_RATE_LANES - 1][i] ^= 1 << 63;
        }
        qsag_asm::keccak_f1600_x4(&mut states);
        Self { states, next: 0 }
    }

    /// Fill `out` with the next stream words.
    pub fn fill_words(&mut self, out: &mut [u64]) {
        let mut written = 0usize;
        while written < out.len() {
            if self.next == Self::WORDS_PER_BLOCK {
                qsag_asm::keccak_f1600_x4(&mut self.states);
                self.next = 0;
            }
            let take = (Self::WORDS_PER_BLOCK - self.next).min(out.len() - written);
            let rate = self.states.0[..SHAKE256_RATE_LANES].as_flattened();
            out[written..written + take].copy_from_slice(&rate[self.next..self.next + take]);
            self.next += take;
            written += take;
        }
    }
}

/// Exact `out_len`-byte `SHAKE256` XOF matching `Qsag.shake256Xof` bit-for-bit.
pub fn shake256_xof(out_len: usize, input: &[u8]) -> Vec<u8> {
    let mut xof = Cshake256Xof::new_shake256();
    xof.absorb(input);
    let mut out = vec![0u8; out_len];
    xof.squeeze(&mut out);
    out
}

/// Exact `out_len`-byte `cSHAKE256` XOF matching `Qsag.cshake256Xof` bit-for-bit.
pub fn cshake256_xof(out_len: usize, customization: &[u8], input: &[u8]) -> Vec<u8> {
    let mut xof = Cshake256Xof::new(customization);
    xof.absorb(input);
    let mut out = vec![0u8; out_len];
    xof.squeeze(&mut out);
    out
}

/// Exact 32-byte `cSHAKE256` evaluation matching `Qsag.cshake256Bytes`.
pub fn cshake256_32(customization: &[u8], input: &[u8]) -> [u8; 32] {
    let mut xof = Cshake256Xof::new(customization);
    xof.absorb(input);
    let mut out = [0u8; 32];
    xof.squeeze(&mut out);
    out
}

/// Exact 32-byte `SHAKE256` evaluation.
#[inline]
pub fn shake256_32(input: &[u8]) -> [u8; 32] {
    cshake256_32(&[], input)
}

// ============================================================================
// Self-Delimiting LEB128 Framing (Matching `Qsag.encodeMultiFrame`)
// ============================================================================

/// Canonical self-delimiting unsigned LEB128 encoding matching `Qsag.leb128`.
pub fn leb128(mut n: usize) -> Vec<u8> {
    let mut out = Vec::with_capacity(4);
    loop {
        if n < 128 {
            out.push(n as u8);
            break;
        }
        out.push(0x80 | ((n & 0x7F) as u8));
        n >>= 7;
    }
    out
}

/// `leb128` for `u64` step counters and epochs.
pub fn leb128_u64(mut n: u64) -> Vec<u8> {
    let mut out = Vec::with_capacity(5);
    loop {
        if n < 128 {
            out.push(n as u8);
            break;
        }
        out.push(0x80 | ((n & 0x7F) as u8));
        n >>= 7;
    }
    out
}

/// Length-prefixed byte field `leb128(xs.len()) || xs`, matching `Qsag.encodeListField`.
pub fn encode_list_field(xs: &[u8]) -> Vec<u8> {
    let mut out = leb128(xs.len());
    out.extend_from_slice(xs);
    out
}

/// Self-delimiting multi-field byte frame `leb128(fields.len()) || encode_list_field(f0) || ...`,
/// matching `Qsag.encodeMultiFrame` (proved unconditionally injective in `Keccak.lean`).
pub fn encode_multi_frame(fields: &[&[u8]]) -> Vec<u8> {
    let total: usize = 5 + fields.iter().map(|f| 5 + f.len()).sum::<usize>();
    let mut out = Vec::with_capacity(total);
    out.extend_from_slice(&leb128(fields.len()));
    for f in fields {
        out.extend_from_slice(&leb128(f.len()));
        out.extend_from_slice(f);
    }
    out
}

#[inline]
fn absorb_leb128_stack(xof: &mut Cshake256Xof, mut n: usize) {
    let mut buf = [0u8; 10];
    let mut len = 0usize;
    loop {
        if n < 128 {
            buf[len] = n as u8;
            len += 1;
            break;
        }
        buf[len] = 0x80 | ((n & 0x7F) as u8);
        len += 1;
        n >>= 7;
    }
    xof.absorb(&buf[..len]);
}

/// Stream `encode_multi_frame(fields)` directly into `xof` without heap allocations or
/// secret-bearing intermediate `Vec<u8>` copies (`Drop` on [`Cshake256Xof`] volatile-wipes state).
pub fn absorb_multi_frame(xof: &mut Cshake256Xof, fields: &[&[u8]]) {
    absorb_leb128_stack(xof, fields.len());
    for f in fields {
        absorb_leb128_stack(xof, f.len());
        xof.absorb(f);
    }
}

/// Zero-heap-copy 32-byte `cSHAKE256` over `encode_multi_frame(fields)` for secret-bearing frames.
pub fn cshake256_32_multi_frame(customization: &[u8], fields: &[&[u8]]) -> [u8; 32] {
    let mut xof = Cshake256Xof::new(customization);
    absorb_multi_frame(&mut xof, fields);
    let mut out = [0u8; 32];
    xof.squeeze(&mut out);
    out
}

/// Zero-heap-copy `out_len`-byte `cSHAKE256` XOF over `encode_multi_frame(fields)` for secret-bearing frames.
pub fn cshake256_xof_multi_frame(
    out_len: usize,
    customization: &[u8],
    fields: &[&[u8]],
) -> Vec<u8> {
    let mut xof = Cshake256Xof::new(customization);
    absorb_multi_frame(&mut xof, fields);
    let mut out = vec![0u8; out_len];
    xof.squeeze(&mut out);
    out
}

/// Injectively framed 3-field payload `encode_list_field(a) || encode_list_field(b) || encode_list_field(c)`.
pub fn encode_frame(a: &[u8], b: &[u8], c: &[u8]) -> Vec<u8> {
    let mut out = encode_list_field(a);
    out.extend_from_slice(&encode_list_field(b));
    out.extend_from_slice(&encode_list_field(c));
    out
}

/// Encode a UTF-8 string via LEB128 Unicode scalar values.
pub fn encode_string_codepoints(s: &str) -> Vec<u8> {
    let mut out = Vec::with_capacity(s.len());
    for ch in s.chars() {
        out.extend_from_slice(&leb128(ch as usize));
    }
    out
}

// ============================================================================
// Compile-Time Typestate `FiatShamirTranscript<Phase>`
// ============================================================================

mod sealed {
    pub trait Sealed {}
}

/// Sealed marker trait for compile-time Fiat–Shamir transcript phases.
pub trait TranscriptPhase: sealed::Sealed + Clone + Copy {}

/// Initial phase: context seed absorbed; relation and statement instance not yet bound.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Unbound;
impl sealed::Sealed for Unbound {}
impl TranscriptPhase for Unbound {}

/// Second phase: `(protocol_id, vk_digest, circuit_desc)` bound; awaiting instance binding.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RelationBound;
impl sealed::Sealed for RelationBound {}
impl TranscriptPhase for RelationBound {}

/// Active phase: both relation and statement instance are bound; challenges may be squeezed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InstanceBound;
impl sealed::Sealed for InstanceBound {}
impl TranscriptPhase for InstanceBound {}

/// Compile-time typestate Fiat–Shamir sponge transcript backed by 256-bit `cSHAKE256`.
///
/// Attempting to squeeze any challenge before calling both `bind_relation` and `bind_instance`
/// is rejected at compile time.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiatShamirTranscript<Phase: TranscriptPhase> {
    state: [u8; 32],
    step_count: u64,
    relation_digest: [u8; 32],
    instance_digest: [u8; 32],
    _phase: PhantomData<Phase>,
}

impl<Phase: TranscriptPhase> Drop for FiatShamirTranscript<Phase> {
    fn drop(&mut self) {
        wipe_bytes32(&mut self.state);
    }
}

impl<Phase: TranscriptPhase> FiatShamirTranscript<Phase> {
    #[inline]
    pub const fn state(&self) -> &[u8; 32] {
        &self.state
    }

    #[inline]
    pub const fn step_count(&self) -> u64 {
        self.step_count
    }

    #[inline]
    pub const fn relation_digest(&self) -> &[u8; 32] {
        &self.relation_digest
    }

    #[inline]
    pub const fn instance_digest(&self) -> &[u8; 32] {
        &self.instance_digest
    }
}

impl FiatShamirTranscript<Unbound> {
    /// Construct a fresh `Unbound` transcript from a session/context seed.
    pub fn new(context_seed: &[u8]) -> Self {
        let state = cshake256_32(FS_SEED_CUSTOMIZATION, context_seed);
        Self {
            state,
            step_count: 0,
            relation_digest: [0u8; 32],
            instance_digest: [0u8; 32],
            _phase: PhantomData,
        }
    }

    /// Injectively bind `(protocol_id, vk_digest, circuit_desc)` to transition to `RelationBound`.
    pub fn bind_relation(
        self,
        protocol_id: &str,
        vk_digest: &[u8; 32],
        circuit_desc: &[u8],
    ) -> FiatShamirTranscript<RelationBound> {
        let mut proto_bytes = encode_string_codepoints(protocol_id);
        let mut rel_frame = encode_frame(&proto_bytes, vk_digest, circuit_desc);
        let state_field = encode_list_field(&self.state);
        let mut preimage = Vec::with_capacity(state_field.len() + rel_frame.len());
        preimage.extend_from_slice(&state_field);
        preimage.extend_from_slice(&rel_frame);
        let next_state = cshake256_32(FS_BIND_CUSTOMIZATION, &preimage);
        wipe_bytes(&mut proto_bytes);
        wipe_bytes(&mut rel_frame);
        wipe_bytes(&mut preimage);
        FiatShamirTranscript {
            state: next_state,
            step_count: 1,
            relation_digest: next_state,
            instance_digest: [0u8; 32],
            _phase: PhantomData,
        }
    }
}

impl FiatShamirTranscript<RelationBound> {
    /// Injectively bind `(comm_bytes, claimed_sum, point)` to transition to `InstanceBound`.
    pub fn bind_instance(
        self,
        comm_bytes: &[u8],
        claimed_sum: GoldilocksExt2,
        point: &[GoldilocksExt2],
    ) -> FiatShamirTranscript<InstanceBound> {
        let sum_bytes = claimed_sum.to_be_bytes();
        let len_hdr = leb128(point.len());
        let mut pt_bytes = Vec::with_capacity(len_hdr.len() + 16 * point.len());
        pt_bytes.extend_from_slice(&len_hdr);
        for coord in point {
            pt_bytes.extend_from_slice(&coord.to_be_bytes());
        }
        let mut inst_frame = encode_frame(comm_bytes, &sum_bytes, &pt_bytes);
        let state_field = encode_list_field(&self.state);
        let step_hdr = leb128_u64(self.step_count);
        let mut preimage =
            Vec::with_capacity(state_field.len() + step_hdr.len() + inst_frame.len());
        preimage.extend_from_slice(&state_field);
        preimage.extend_from_slice(&step_hdr);
        preimage.extend_from_slice(&inst_frame);
        let next_state = cshake256_32(FS_INSTANCE_CUSTOMIZATION, &preimage);
        wipe_bytes(&mut pt_bytes);
        wipe_bytes(&mut inst_frame);
        wipe_bytes(&mut preimage);
        FiatShamirTranscript {
            state: next_state,
            step_count: self.step_count + 1,
            relation_digest: self.relation_digest,
            instance_digest: next_state,
            _phase: PhantomData,
        }
    }
}

impl FiatShamirTranscript<InstanceBound> {
    /// Absorb a labeled message into an `InstanceBound` transcript (`0` heap reallocation).
    pub fn absorb(&mut self, label: &[u8], msg_bytes: &[u8]) {
        let step_hdr = leb128_u64(self.step_count);
        let mut step_and_msg = Vec::with_capacity(step_hdr.len() + msg_bytes.len());
        step_and_msg.extend_from_slice(&step_hdr);
        step_and_msg.extend_from_slice(msg_bytes);
        let mut frame = encode_frame(&self.state, label, &step_and_msg);
        self.state = cshake256_32(FS_ABSORB_CUSTOMIZATION, &frame);
        wipe_bytes(&mut step_and_msg);
        wipe_bytes(&mut frame);
        self.step_count += 1;
    }

    #[inline]
    pub fn absorb_field(&mut self, label: &[u8], val: Goldilocks) {
        let mut b = val.to_be_bytes();
        self.absorb(label, &b);
        wipe_bytes(&mut b);
    }

    #[inline]
    pub fn absorb_ext2(&mut self, label: &[u8], val: GoldilocksExt2) {
        let mut b = val.to_be_bytes();
        self.absorb(label, &b);
        wipe_bytes(&mut b);
    }

    /// Squeeze a full 32-byte (256-bit) challenge and ratchet the transcript state forward.
    pub fn squeeze_challenge_256(&mut self) -> [u8; 32] {
        let state_field = encode_list_field(&self.state);
        let step_hdr = leb128_u64(self.step_count);
        let mut payload = Vec::with_capacity(state_field.len() + step_hdr.len());
        payload.extend_from_slice(&state_field);
        payload.extend_from_slice(&step_hdr);
        let out_bytes = cshake256_32(FS_SQUEEZE_CUSTOMIZATION, &payload);
        wipe_bytes(&mut payload);

        let out_field = encode_list_field(&out_bytes);
        let mut ratchet_in = Vec::with_capacity(state_field.len() + out_field.len());
        ratchet_in.extend_from_slice(&state_field);
        ratchet_in.extend_from_slice(&out_field);
        self.state = cshake256_32(FS_RATCHET_CUSTOMIZATION, &ratchet_in);
        wipe_bytes(&mut ratchet_in);
        self.step_count += 1;
        out_bytes
    }

    /// Squeeze a 128-bit challenge in `GoldilocksExt2` ($\mathbb{F}_{p^2}$) from two independent
    /// 128-bit halves of `squeeze_challenge_256`.
    pub fn squeeze_ext2(&mut self) -> GoldilocksExt2 {
        let bytes = self.squeeze_challenge_256();
        let mut lo_arr = [0u8; 16];
        let mut hi_arr = [0u8; 16];
        lo_arr.copy_from_slice(&bytes[0..16]);
        hi_arr.copy_from_slice(&bytes[16..32]);
        GoldilocksExt2::new(
            Goldilocks::from_u128_reduced(u128::from_be_bytes(lo_arr)),
            Goldilocks::from_u128_reduced(u128::from_be_bytes(hi_arr)),
        )
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn rss_four_shakes_match_scalar_and_reject_multiblock_inputs() {
        let inputs = [vec![], vec![0x8f], vec![0x42; 80], vec![0xa3; 135]];
        let refs = core::array::from_fn(|i| inputs[i].as_slice());
        let output = shake256_4x_32(refs).unwrap();
        for (input, actual) in inputs.iter().zip(output) {
            assert_eq!(actual, shake256_32(input));
        }
        for len in [136, 137, 272] {
            let too_long = vec![0; len];
            assert!(shake256_4x_32([&[], &too_long, &[], &[]]).is_none());
        }
    }

    #[test]
    fn word_stream4_matches_scalar_cshake_per_stream_across_blocks() {
        let tag = b"QSAG.TEST.WORDSTREAM/v1";
        let mid = cshake256_static_midstate(tag);
        for seed_len in [0usize, 1, 72, 133, 134] {
            let seed: Vec<u8> = (0..seed_len).map(|i| (i * 7 + 3) as u8).collect();
            let mut stream = Cshake256WordStream4::new(&mid, &seed);
            // Uneven chunks exercise block boundaries.
            let mut words = vec![0u64; 3 * Cshake256WordStream4::WORDS_PER_BLOCK + 5];
            let (head, tail) = words.split_at_mut(7);
            stream.fill_words(head);
            stream.fill_words(tail);
            for i in 0..4usize {
                let mut input = seed.clone();
                input.push(i as u8);
                let reference = cshake256_xof(8 * SHAKE256_RATE_LANES * 4, tag, &input);
                for (w, word) in words.iter().enumerate().filter(|(w, _)| w % 4 == i) {
                    let block = w / Cshake256WordStream4::WORDS_PER_BLOCK;
                    let lane = (w % Cshake256WordStream4::WORDS_PER_BLOCK) / 4;
                    let off = 8 * (block * SHAKE256_RATE_LANES + lane);
                    let expected = u64::from_le_bytes(reference[off..off + 8].try_into().unwrap());
                    assert_eq!(*word, expected, "stream {i} word {w}");
                }
            }
        }
    }

    #[test]
    fn static_midstates_match_generic_prefix_and_keep_domains_distinct() {
        for tag in [
            b"QSAG.RSS.U64.OPEN.COM/v1".as_slice(),
            b"QSAG.RSS.CHI.MASK/v2",
            b"QSAG.TH.PRF/v1",
            &[0x61; 31],
            &[0x62; 32],
            &[0x63; 128],
        ] {
            let mut expected = [0u64; 25];
            let prefix = cshake256_customization_prefix(tag);
            for block in prefix.as_chunks::<SHAKE256_RATE_BYTES>().0 {
                xor_rate_block(&mut expected, block);
                keccak_f1600(&mut expected);
            }
            assert_eq!(cshake256_static_midstate(tag), expected);
            let mut generic = Cshake256Xof::new_shake256();
            generic.suffix = 4;
            generic.absorb(&prefix);
            let input = [0x81; 273];
            generic.absorb(&input);
            let mut reference = [0u8; 300];
            generic.squeeze(&mut reference);
            assert_eq!(cshake256_xof(300, tag, &input), reference);
            assert_ne!(
                cshake256_xof(300, tag, &input),
                cshake256_xof(300, b"other", &input)
            );
        }
    }

    #[test]
    #[should_panic]
    fn static_midstate_rejects_empty_shake_domain() {
        cshake256_static_midstate(&[]);
    }

    #[test]
    #[should_panic]
    fn static_midstate_rejects_multiblock_tag() {
        cshake256_static_midstate(&[0; 129]);
    }
    use super::*;

    #[test]
    fn test_fips202_shake256_official_vectors() {
        let empty = shake256_32(&[]);
        assert_eq!(
            empty,
            [
                0x46, 0xb9, 0xdd, 0x2b, 0x0b, 0xa8, 0x8d, 0x13, 0x23, 0x3b, 0x3f, 0xeb, 0x74, 0x3e,
                0xeb, 0x24, 0x3f, 0xcd, 0x52, 0xea, 0x62, 0xb8, 0x1b, 0x82, 0xb5, 0x0c, 0x27, 0x64,
                0x6e, 0xd5, 0x76, 0x2f
            ]
        );
        let abc = shake256_32(b"abc");
        assert_eq!(
            abc,
            [
                0x48, 0x33, 0x66, 0x60, 0x13, 0x60, 0xa8, 0x77, 0x1c, 0x68, 0x63, 0x08, 0x0c, 0xc4,
                0x11, 0x4d, 0x8d, 0xb4, 0x45, 0x30, 0xf8, 0xf1, 0xe1, 0xee, 0x4f, 0x94, 0xea, 0x37,
                0xe7, 0x8b, 0x57, 0x39
            ]
        );
    }

    #[test]
    fn test_cshake256_multi_block_and_domain_separation() {
        let msg = [0xA5u8; 300]; // spans 3 rate blocks (300 > 272 = 2 * 136)
        let d1 = cshake256_32(b"DOMAIN.A", &msg);
        let d2 = cshake256_32(b"DOMAIN.B", &msg);
        assert_ne!(d1, d2);

        let xof_long = cshake256_xof(300, b"DOMAIN.A", &msg);
        assert_eq!(&xof_long[..32], &d1);
    }

    #[test]
    fn test_multi_frame_collision_resistance() {
        let f1 = encode_multi_frame(&[b"ab", b"c"]);
        let f2 = encode_multi_frame(&[b"a", b"bc"]);
        assert_ne!(f1, f2);
    }

    #[test]
    fn test_streaming_multi_frame_matches_encode_multi_frame() {
        let big = [0x5Au8; 409];
        let cases: &[&[&[u8]]] = &[
            &[],
            &[b""],
            &[b"seed32_material", b"ctx", &big],
            &[&big, b"short", &[0xFFu8; 136], b""],
        ];
        for &fields in cases {
            let framed = encode_multi_frame(fields);
            assert_eq!(
                cshake256_32_multi_frame(b"QSAG.TEST.STREAM", fields),
                cshake256_32(b"QSAG.TEST.STREAM", &framed)
            );
            assert_eq!(
                cshake256_32_multi_frame(&[], fields),
                cshake256_32(&[], &framed)
            );
            assert_eq!(
                cshake256_xof_multi_frame(200, b"QSAG.TEST.STREAM", fields),
                cshake256_xof(200, b"QSAG.TEST.STREAM", &framed)
            );
        }
    }
}
