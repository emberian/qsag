//! Zero-dependency `Keccak-f[1600]`, `SHAKE128`, `SHAKE256`, `cSHAKE256`, `SHA3-256`,
//! `Keccak256` (0x01 pad), injective length-framed tuple hashing, and interleaved Fiat-Shamir
//! transcript sponge with `write_volatile` state zeroization on drop.

use crate::ct::{ct_zeroize_bytes, ct_zeroize_u64s};

/// Standard 24-round `Keccak-f[1600]` iota round constants (FIPS 202).
pub const KECCAK_RC: [u64; 24] = [
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

const KECCAK_RHO: [u32; 24] = [
    1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14, 27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44,
];

const KECCAK_PI: [usize; 24] = [
    10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4, 15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1,
];

/// In-place 24-round `Keccak-f[1600]` permutation (100% branchless, LUT-free).
pub fn keccak_f1600(state: &mut [u64; 25]) {
    let mut bc = [0u64; 5];
    for &rc in &KECCAK_RC {
        // Theta
        for (i, value) in bc.iter_mut().enumerate() {
            *value = state[i] ^ state[i + 5] ^ state[i + 10] ^ state[i + 15] ^ state[i + 20];
        }
        for i in 0..5 {
            let t = bc[(i + 4) % 5] ^ bc[(i + 1) % 5].rotate_left(1);
            state[i] ^= t;
            state[i + 5] ^= t;
            state[i + 10] ^= t;
            state[i + 15] ^= t;
            state[i + 20] ^= t;
        }
        // Rho + Pi
        let mut t = state[1];
        for (&j, &rotation) in KECCAK_PI.iter().zip(&KECCAK_RHO) {
            let next = state[j];
            state[j] = t.rotate_left(rotation);
            t = next;
        }
        // Chi
        for row in (0..25).step_by(5) {
            bc[0] = state[row];
            bc[1] = state[row + 1];
            bc[2] = state[row + 2];
            bc[3] = state[row + 3];
            bc[4] = state[row + 4];
            for i in 0..5 {
                state[row + i] = bc[i] ^ ((!bc[(i + 1) % 5]) & bc[(i + 2) % 5]);
            }
        }
        // Iota
        state[0] ^= rc;
    }
    ct_zeroize_u64s(&mut bc);
}

/// Generic stack-allocated Keccak sponge with volatile zeroization on `Drop`.
#[derive(Clone)]
pub struct KeccakSponge<const RATE: usize> {
    state: [u64; 25],
    pos: usize,
    squeezing: bool,
}

impl<const RATE: usize> Default for KeccakSponge<RATE> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const RATE: usize> Drop for KeccakSponge<RATE> {
    fn drop(&mut self) {
        ct_zeroize_u64s(&mut self.state);
        self.pos = 0;
    }
}

impl<const RATE: usize> KeccakSponge<RATE> {
    /// Rejects an invalid `RATE` when the sponge type is instantiated (a build error, not a
    /// runtime panic).
    const RATE_IS_VALID: () = assert!(RATE > 0 && RATE < 200 && RATE % 8 == 0);

    pub const fn new() -> Self {
        let () = Self::RATE_IS_VALID;
        Self {
            state: [0u64; 25],
            pos: 0,
            squeezing: false,
        }
    }

    #[inline]
    fn xor_byte(&mut self, offset: usize, byte: u8) {
        let lane = offset / 8;
        let shift = (offset % 8) * 8;
        self.state[lane] ^= (byte as u64) << shift;
    }

    #[inline]
    fn read_byte(&self, offset: usize) -> u8 {
        let lane = offset / 8;
        let shift = (offset % 8) * 8;
        ((self.state[lane] >> shift) & 0xFF) as u8
    }

    pub fn absorb(&mut self, mut input: &[u8]) {
        assert!(!self.squeezing, "cannot absorb after squeezing");
        while !input.is_empty() {
            if self.pos == 0 && input.len() >= RATE {
                for (lane, bytes) in self.state.iter_mut().zip(input[..RATE].chunks_exact(8)) {
                    let mut chunk = [0u8; 8];
                    chunk.copy_from_slice(bytes);
                    *lane ^= u64::from_le_bytes(chunk);
                    ct_zeroize_bytes(&mut chunk);
                }
                keccak_f1600(&mut self.state);
                input = &input[RATE..];
            } else {
                let take = (RATE - self.pos).min(input.len());
                for (i, &b) in input.iter().enumerate().take(take) {
                    self.xor_byte(self.pos + i, b);
                }
                self.pos += take;
                input = &input[take..];
                if self.pos == RATE {
                    keccak_f1600(&mut self.state);
                    self.pos = 0;
                }
            }
        }
    }

    pub fn finalize(&mut self, domain_pad: u8) {
        assert!(!self.squeezing, "already finalized");
        self.xor_byte(self.pos, domain_pad);
        self.xor_byte(RATE - 1, 0x80);
        keccak_f1600(&mut self.state);
        self.pos = 0;
        self.squeezing = true;
    }

    pub fn squeeze(&mut self, mut out: &mut [u8]) {
        assert!(self.squeezing, "must finalize before squeezing");
        while !out.is_empty() {
            if self.pos == RATE {
                keccak_f1600(&mut self.state);
                self.pos = 0;
            }
            let take = (RATE - self.pos).min(out.len());
            for (i, slot) in out.iter_mut().enumerate().take(take) {
                *slot = self.read_byte(self.pos + i);
            }
            self.pos += take;
            out = &mut out[take..];
        }
    }
}

/// `SHAKE128` (`rate = 168`, `pad = 0x1F`) streaming XOF.
pub type Shake128 = KeccakSponge<168>;
/// `SHAKE256` (`rate = 136`, `pad = 0x1F`) streaming XOF.
pub type Shake256 = KeccakSponge<136>;

/// One-shot `SHAKE256` XOF into `out`.
pub fn shake256_xof(input: &[u8], out: &mut [u8]) {
    let mut sp = Shake256::new();
    sp.absorb(input);
    sp.finalize(0x1F);
    sp.squeeze(out);
}

/// One-shot `SHA3-256` (`rate = 136`, `pad = 0x06`).
pub fn sha3_256(input: &[u8]) -> [u8; 32] {
    let mut sp = KeccakSponge::<136>::new();
    sp.absorb(input);
    sp.finalize(0x06);
    let mut out = [0u8; 32];
    sp.squeeze(&mut out);
    out
}

/// One-shot original `Keccak-256` (`rate = 136`, `pad = 0x01`) for legacy EVM address commitments.
pub fn keccak256(input: &[u8]) -> [u8; 32] {
    let mut sp = KeccakSponge::<136>::new();
    sp.absorb(input);
    sp.finalize(0x01);
    let mut out = [0u8; 32];
    sp.squeeze(&mut out);
    out
}

/// NIST SP 800-185 `left_encode(x)` into stack buffer `(buf, len)`.
///
/// Takes a `u128` so the bit length of any addressable byte slice (`len * 8`) is representable.
#[inline]
fn left_encode_u128(mut x: u128) -> ([u8; 17], usize) {
    let mut out = [0u8; 17];
    if x == 0 {
        out[0] = 1;
        return (out, 2);
    }
    let mut tmp = [0u8; 16];
    let mut n = 0usize;
    while x > 0 {
        tmp[n] = (x & 0xFF) as u8;
        x >>= 8;
        n += 1;
    }
    out[0] = n as u8;
    for i in 0..n {
        out[1 + i] = tmp[n - 1 - i];
    }
    (out, n + 1)
}

/// Streaming NIST SP 800-185 `cSHAKE256` XOF (`rate = 136`).
pub fn init_cshake256(function_name: &[u8], customization: &[u8]) -> Shake256 {
    let mut sp = Shake256::new();
    if function_name.is_empty() && customization.is_empty() {
        return sp;
    }
    // bytepad(encode_string(N) || encode_string(S), 136)
    let (w_enc, w_len) = left_encode_u128(136);
    let (n_enc, n_len) = left_encode_u128((function_name.len() as u128) * 8);
    let (s_enc, s_len) = left_encode_u128((customization.len() as u128) * 8);

    sp.absorb(&w_enc[..w_len]);
    sp.absorb(&n_enc[..n_len]);
    sp.absorb(function_name);
    sp.absorb(&s_enc[..s_len]);
    sp.absorb(customization);

    let rem = (w_len + n_len + s_len + function_name.len() % 136 + customization.len() % 136) % 136;
    if rem != 0 {
        let zeros = [0u8; 136];
        sp.absorb(&zeros[..(136 - rem)]);
    }
    sp
}

/// Finalize a `cSHAKE256` sponge initialized via [`init_cshake256`].
#[inline]
pub fn finalize_cshake256(sp: &mut Shake256, has_customization: bool) {
    sp.finalize(if has_customization { 0x04 } else { 0x1F });
}

/// Domain-separated `cSHAKE256` over an array/slice of length-framed byte slices (`0` boundary ambiguity).
///
/// Preimage framing: `u64_le(frames.len()) || (u64_le(frame_i.len()) || frame_i)*`,
/// guaranteeing strict tuple injectivity with zero heap allocation!
pub fn cshake256_framed_xof(customization: &[u8], frames: &[&[u8]], out: &mut [u8]) {
    let has_cust = !customization.is_empty();
    let mut sp = init_cshake256(b"", customization);
    sp.absorb(&(frames.len() as u64).to_le_bytes());
    for frame in frames {
        sp.absorb(&(frame.len() as u64).to_le_bytes());
        sp.absorb(frame);
    }
    finalize_cshake256(&mut sp, has_cust);
    sp.squeeze(out);
}

/// 32-byte domain-separated injective length-framed `cSHAKE256`.
#[inline]
pub fn cshake256_framed_32(customization: &[u8], frames: &[&[u8]]) -> [u8; 32] {
    let mut out = [0u8; 32];
    cshake256_framed_xof(customization, frames, &mut out);
    out
}

/// 64-byte domain-separated injective length-framed `cSHAKE256`.
#[inline]
pub fn cshake256_framed_64(customization: &[u8], frames: &[&[u8]]) -> [u8; 64] {
    let mut out = [0u8; 64];
    cshake256_framed_xof(customization, frames, &mut out);
    out
}

/// Canonical commit-then-open commitment `H("QSAG.COMMIT.V1", [sid, &round_le, &party_le, payload, salt32])`.
pub fn commit_mpc_broadcast(
    sid: &[u8; 32],
    round: u32,
    party_id: u16,
    payload: &[u8],
    salt32: &[u8; 32],
) -> [u8; 32] {
    let r_bytes = round.to_le_bytes();
    let p_bytes = party_id.to_le_bytes();
    cshake256_framed_32(
        b"QSAG.COMMIT.V1",
        &[sid, &r_bytes, &p_bytes, payload, salt32],
    )
}

/// Interleaved Fiat-Shamir transcript enforcing round-by-round absorb-before-squeeze discipline
/// (structurally preventing non-interleaved challenge reuse).
#[derive(Clone)]
pub struct InterleavedTranscript {
    chain_key: [u8; 32],
    round_counter: u64,
    absorbed_since_last_squeeze: bool,
}

impl Drop for InterleavedTranscript {
    fn drop(&mut self) {
        ct_zeroize_bytes(&mut self.chain_key);
    }
}

impl InterleavedTranscript {
    pub fn new(protocol_label: &[u8], instance_bytes: &[u8]) -> Self {
        let chain_key = cshake256_framed_32(b"QSAG.FS.INIT.V1", &[protocol_label, instance_bytes]);
        Self {
            chain_key,
            round_counter: 0,
            absorbed_since_last_squeeze: true,
        }
    }

    /// Absorb a labeled prover message / Merkle root into the transcript chain state.
    pub fn absorb(&mut self, label: &[u8], payload: &[u8]) {
        let rc = self.round_counter.to_le_bytes();
        self.chain_key = cshake256_framed_32(
            b"QSAG.FS.ABSORB.V1",
            &[&self.chain_key, &rc, label, payload],
        );
        self.absorbed_since_last_squeeze = true;
    }

    /// Squeeze challenge bytes AFTER at least one new absorption since the previous squeeze
    /// (advancing `round_counter` monotonically).
    pub fn squeeze_bytes(&mut self, label: &[u8], out: &mut [u8]) {
        assert!(
            self.absorbed_since_last_squeeze,
            "Fiat-Shamir violation: must absorb current round commitment before squeezing challenge"
        );
        let rc = self.round_counter.to_le_bytes();
        cshake256_framed_xof(b"QSAG.FS.SQUEEZE.V1", &[&self.chain_key, &rc, label], out);
        self.chain_key = cshake256_framed_32(b"QSAG.FS.RATCHET.V1", &[&self.chain_key, &rc, label]);
        self.round_counter += 1;
        self.absorbed_since_last_squeeze = false;
    }

    /// Squeeze two canonical Goldilocks challenges by 192-bit reduction.
    /// Each coordinate has TV distance (p-1)/(p * 2^192) < 2^-192;
    /// the pair has TV distance at most twice that bound.
    pub fn squeeze_ext2(&mut self, label: &[u8]) -> [u64; 2] {
        let mut raw = [0u8; 48];
        self.squeeze_bytes(label, &mut raw);
        let mut half = [0u8; 24];
        half.copy_from_slice(&raw[..24]);
        let c0 = reduce_192_zero_bias(&half);
        half.copy_from_slice(&raw[24..]);
        let c1 = reduce_192_zero_bias(&half);
        ct_zeroize_bytes(&mut half);
        ct_zeroize_bytes(&mut raw);
        [c0, c1]
    }

    pub const fn current_anchor(&self) -> [u8; 32] {
        self.chain_key
    }
}

/// Wide reduction of a 24-byte draw modulo Goldilocks p.
/// The historical function name is retained for compatibility; bias is nonzero.
/// Exact TV distance from uniform is (p-1)/(p * 2^192), strictly below 2^-192.
/// Since $2^{96} \equiv -1 \pmod p$, $2^{192} \equiv 1 \pmod p$, so $p \mid (2^{192} - 1)$!
/// Note: only the single point `2^192 - 1` makes `[0, 2^192)` have residue `0` once extra (`2^{-192}`).
#[inline]
pub fn reduce_192_zero_bias(bytes24: &[u8; 24]) -> u64 {
    use crate::goldilocks::{gl_reduce128, gl_sub};
    let mut lo16 = [0u8; 16];
    let mut hi8 = [0u8; 8];
    lo16.copy_from_slice(&bytes24[0..16]);
    hi8.copy_from_slice(&bytes24[16..24]);
    let lo128 = u128::from_le_bytes(lo16);
    let hi64 = u64::from_le_bytes(hi8);
    // 2^{128} = 2^{32} * 2^{96} == -2^{32} (mod p)
    let r_lo = gl_reduce128(lo128);
    let r_hi = gl_reduce128((hi64 as u128) << 32);
    ct_zeroize_bytes(&mut lo16);
    ct_zeroize_bytes(&mut hi8);
    gl_sub(r_lo, r_hi)
}
