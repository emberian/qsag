//! Zero-dependency `Keccak-f[1600]`, `SHAKE128`, `SHAKE256`, `cSHAKE256`, `SHA3-256`,
//! `Keccak256` (0x01 pad), injective length-framed tuple hashing, and interleaved Fiat-Shamir
//! transcript sponge with `write_volatile` state zeroization on drop.

use crate::ct::{ct_zeroize_bytes, ct_zeroize_u64s};

/// Standard 24-round `Keccak-f[1600]` iota round constants (FIPS 202).
pub const KECCAK_RC: [u64; 24] = qsag_asm::KECCAK_ROUND_CONSTANTS;

pub use qsag_verified::keccak::keccak_f1600;
use qsag_verified::keccak::keccak_f1600_round;

/// `Keccak-p[1600,12]` uses the last twelve rounds of Keccak-f.
pub fn keccak_p1600_12(state: &mut [u64; 25]) {
    let mut i = 12;
    while i < KECCAK_RC.len() {
        keccak_f1600_round(state, KECCAK_RC[i]);
        i += 1;
    }
}

/// Portable interleaved Keccak-p, specialized to 4/8 lanes for batch hashing.
/// A single state also supports constant evaluation of public customization midstates.
#[inline(always)]
pub const fn keccak_p1600_lanes<const N: usize, const START: usize>(st: &mut [[u64; N]; 25]) {
    #[inline(always)]
    const fn xor<const N: usize>(a: [u64; N], b: [u64; N]) -> [u64; N] {
        let mut out = [0; N];
        let mut k = 0;
        while k < N {
            out[k] = a[k] ^ b[k];
            k += 1;
        }
        out
    }
    #[inline(always)]
    const fn xor5<const N: usize>(
        a: [u64; N],
        b: [u64; N],
        c: [u64; N],
        d: [u64; N],
        e: [u64; N],
    ) -> [u64; N] {
        let mut out = [0; N];
        let mut k = 0;
        while k < N {
            out[k] = a[k] ^ b[k] ^ c[k] ^ d[k] ^ e[k];
            k += 1;
        }
        out
    }
    #[inline(always)]
    const fn rol<const N: usize, const R: u32>(a: [u64; N]) -> [u64; N] {
        let mut out = [0; N];
        let mut k = 0;
        while k < N {
            out[k] = a[k].rotate_left(R);
            k += 1;
        }
        out
    }
    #[inline(always)]
    const fn chi<const N: usize>(a: [u64; N], b: [u64; N], c: [u64; N]) -> [u64; N] {
        let mut out = [0; N];
        let mut k = 0;
        while k < N {
            out[k] = a[k] ^ ((!b[k]) & c[k]);
            k += 1;
        }
        out
    }

    const { assert!(START <= 24) };
    let mut round = START;
    while round < 24 {
        let rc = KECCAK_RC[round];
        round += 1;
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

        let mut row = 0;
        while row < 25 {
            st[row] = xor(st[row], d0);
            st[row + 1] = xor(st[row + 1], d1);
            st[row + 2] = xor(st[row + 2], d2);
            st[row + 3] = xor(st[row + 3], d3);
            st[row + 4] = xor(st[row + 4], d4);
            row += 5;
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
        st[0] = xor(s0, [rc; N]);
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

/// Const-evaluation adapter for public initial states. Ordinary scalar hashes use
/// the extracted Keccak permutation above.
pub const fn keccak_p1600_const<const START: usize>(state: &mut [u64; 25]) {
    let (lanes, _) = state.as_chunks_mut::<1>();
    keccak_p1600_lanes::<1, START>(lanes.first_chunk_mut::<25>().unwrap());
}

/// Generic stack-allocated Keccak sponge with volatile zeroization on `Drop`.
/// (`Clone` is required for public cSHAKE256 customization-prefix `OnceLock` caching.)
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
    const RATE_IS_VALID: () = assert!(RATE > 0 && RATE < 200 && RATE.is_multiple_of(8));

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
                let (chunks, _) = input[..RATE].as_chunks::<8>();
                for (lane, bytes) in self.state.iter_mut().zip(chunks) {
                    let mut chunk = *bytes;
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
            if self.pos == 0 && out.len() >= RATE {
                let (chunks, _) = out[..RATE].as_chunks_mut::<8>();
                for (slot, &lane) in chunks.iter_mut().zip(self.state.iter()) {
                    *slot = lane.to_le_bytes();
                }
                self.pos = RATE;
                out = &mut out[RATE..];
            } else {
                let take = (RATE - self.pos).min(out.len());
                for (i, slot) in out.iter_mut().enumerate().take(take) {
                    *slot = self.read_byte(self.pos + i);
                }
                self.pos += take;
                out = &mut out[take..];
            }
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
        let c0 = reduce_192_mod_p(&half);
        half.copy_from_slice(&raw[24..]);
        let c1 = reduce_192_mod_p(&half);
        ct_zeroize_bytes(&mut half);
        ct_zeroize_bytes(&mut raw);
        [c0, c1]
    }

    pub const fn current_anchor(&self) -> [u8; 32] {
        self.chain_key
    }
}

/// Wide reduction of a 24-byte draw modulo Goldilocks p.
/// Bias is nonzero and negligible.
/// Exact TV distance from uniform is (p-1)/(p * 2^192), strictly below 2^-192.
/// Since $2^{96} \equiv -1 \pmod p$, $2^{192} \equiv 1 \pmod p$, so $p \mid (2^{192} - 1)$!
/// Note: only the single point `2^192 - 1` makes `[0, 2^192)` have residue `0` once extra (`2^{-192}`).
#[inline]
pub fn reduce_192_mod_p(bytes24: &[u8; 24]) -> u64 {
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

#[cfg(test)]
mod permutation_tests {
    use super::*;

    #[test]
    fn const_midstate_kernel_matches_extracted_rounds() {
        for i in 0..25 {
            let mut input = [0u64; 25];
            input[i] = u64::MAX;
            let mut scalar = input;
            let mut midstate = input;
            keccak_f1600(&mut scalar);
            keccak_p1600_const::<0>(&mut midstate);
            assert_eq!(midstate, scalar);
            let mut scalar = input;
            let mut midstate = input;
            keccak_p1600_12(&mut scalar);
            keccak_p1600_const::<12>(&mut midstate);
            assert_eq!(midstate, scalar);
        }
    }
}
