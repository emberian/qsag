//! Replicated mixed-domain evaluation with active 1-of-3 malicious multiplication
//! verification over authenticated confidential pairwise channels.
use crate::circuit::{Domain, Value};
use alloc::{boxed::Box, vec, vec::Vec};
use qsag_accel::{
    ct::{ct_eq_bytes_mask, ct_zeroize_bytes, ct_zeroize_u64s},
    goldilocks::{GOLDILOCKS_PRIME as GOLDILOCKS_P, gl_add, gl_mul, gl_sub},
    keccak::{KECCAK_RC, cshake256_framed_32, init_cshake256, keccak_f1600, reduce_192_zero_bias},
};
use qsag_asm::{
    BitPlane256, SimdBackend, detect_backend, gf2_128_mul_acc_batch_with_backend,
    transpose64x256_with_backend,
};

const MAX_PENDING_BITS: usize = 262_144;
const D0_BITS: usize = 16;
const SUPER_BLOCKS: usize = 8;
const SUPER_BITS: usize = D0_BITS * SUPER_BLOCKS;
const QUAD_BLOCKS: usize = 4;
const QUAD_BITS: usize = D0_BITS * QUAD_BLOCKS;
const STEP0_PLANES: usize = 2 * D0_BITS;
const STEP0_SLOTS: usize = STEP0_PLANES - 2;
const STEP0_CHUNK: usize = 64;
const STEP2_QUAD_CHUNK: usize = 16;
const MAX_PENDING_FIELD_WORDS: usize = 1_024;
const CONVERT_CHUNK_WORDS: usize = 512;

#[derive(Clone, Copy, Default)]
pub(crate) struct Bit(pub [u64; 2]);
impl core::ops::BitXor for Bit {
    type Output = Self;
    fn bitxor(self, rhs: Self) -> Self {
        Self([self.0[0] ^ rhs.0[0], self.0[1] ^ rhs.0[1]])
    }
}
pub(crate) type Word = Vec<Bit>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    InvalidConfiguration,
    Transport,
    Authentication(usize),
    Disagreement(usize),
    MultiplicationCheck,
    InvalidTape,
    InvalidProof,
}

/// Authenticated envelopes also require confidential delivery. Implementations
/// must deliver each envelope only to its recipient; broadcasting is unsafe.
/// Returned entries are ordered [previous custodian, next custodian].
pub trait Transport: Send {
    /// Optional independent authenticated streams, requested in batch order.
    /// Every custodian must provide all `MIT_REPETITIONS.div_ceil(64)` streams
    /// or none. With the `std` feature these streams allow the independent
    /// repetition batches to run concurrently. Each stream receives a distinct
    /// session/mask domain.
    fn fork(&mut self, _batch: usize) -> Option<Self>
    where
        Self: Sized,
    {
        None
    }

    #[cfg(test)]
    fn audit_transcript(&self) -> Option<(u64, u64)> {
        None
    }
    #[cfg(test)]
    fn audit_candidates(&self, _candidates: Vec<[u8; 32]>) {}
    #[cfg(test)]
    fn audit_private_state(
        &self,
        _party: usize,
        _session: &[u8; 32],
        _witness: &[u8; 32],
        _entropy: &[u8; 32],
        _keys: &[[u8; 32]; 2],
        _statement: &crate::zk_engine::MigrationStatement,
    ) {
    }
    #[cfg(test)]
    fn test_fault_raw(&self) -> Option<[usize; 4]> {
        None
    }
    #[cfg(test)]
    fn on_public_or_view_open(&self) {}
    fn exchange(&mut self, outgoing: [Envelope; 2]) -> Result<[Envelope; 2], Error>;
}

/// Wire envelope. Authentication binds the session, identities and sequence.
pub struct Envelope {
    pub sender: usize,
    pub recipient: usize,
    pub sequence: u64,
    pub payload: Vec<u64>,
    pub tag: [u8; 32],
}
impl Drop for Envelope {
    fn drop(&mut self) {
        ct_zeroize_u64s(&mut self.payload);
    }
}

/// High-throughput rate-136 (`17` `u64` lanes) Keccak sponge operating on native
/// 64-bit words with zero heap allocations and volatile state zeroization on drop.
#[derive(Clone)]
struct WordSponge136 {
    state: [u64; 25],
    pos: usize,
    squeezing: bool,
}
impl Drop for WordSponge136 {
    fn drop(&mut self) {
        ct_zeroize_u64s(&mut self.state);
        self.pos = 0;
    }
}
impl WordSponge136 {
    const RATE_BYTES: usize = 136;
    const RATE_LANES: usize = 17;

    const fn new() -> Self {
        Self {
            state: [0u64; 25],
            pos: 0,
            squeezing: false,
        }
    }

    fn from_shake_seed(seed: &[u8; 32]) -> Self {
        let mut s = Self::new();
        for (lane, chunk) in s.state[..4].iter_mut().zip(seed.chunks_exact(8)) {
            let mut buf = [0u8; 8];
            buf.copy_from_slice(chunk);
            *lane = u64::from_le_bytes(buf);
            ct_zeroize_bytes(&mut buf);
        }
        s.state[4] ^= 0x1f;
        s.state[16] ^= 0x8000_0000_0000_0000;
        keccak_f1600(&mut s.state);
        s.pos = 0;
        s.squeezing = true;
        s
    }

    fn absorb_u64(&mut self, word: u64) {
        debug_assert!(!self.squeezing && self.pos % 8 == 0);
        let lane = self.pos / 8;
        self.state[lane] ^= word;
        self.pos += 8;
        if self.pos == Self::RATE_BYTES {
            keccak_f1600(&mut self.state);
            self.pos = 0;
        }
    }

    fn absorb_bytes32(&mut self, bytes: &[u8; 32]) {
        for chunk in bytes.chunks_exact(8) {
            let mut buf = [0u8; 8];
            buf.copy_from_slice(chunk);
            self.absorb_u64(u64::from_le_bytes(buf));
        }
    }

    fn digest_clone(&self) -> [u8; 32] {
        debug_assert!(!self.squeezing && self.pos % 8 == 0);
        let mut st = self.state;
        let lane = self.pos / 8;
        st[lane] ^= 0x1f;
        st[16] ^= 0x8000_0000_0000_0000;
        keccak_f1600(&mut st);
        let mut out = [0u8; 32];
        for (chunk, &w) in out.chunks_exact_mut(8).zip(&st[..4]) {
            chunk.copy_from_slice(&w.to_le_bytes());
        }
        ct_zeroize_u64s(&mut st);
        out
    }

    fn squeeze_u64s(&mut self, mut out: &mut [u64]) {
        debug_assert!(self.squeezing && self.pos % 8 == 0);
        let mut lane = self.pos / 8;
        while !out.is_empty() {
            if lane == Self::RATE_LANES {
                keccak_f1600(&mut self.state);
                lane = 0;
            }
            let take = (Self::RATE_LANES - lane).min(out.len());
            out[..take].copy_from_slice(&self.state[lane..lane + take]);
            lane += take;
            out = &mut out[take..];
        }
        self.pos = lane * 8;
    }

    fn squeeze_u64(&mut self) -> u64 {
        let mut w = [0u64; 1];
        self.squeeze_u64s(&mut w);
        w[0]
    }

    fn squeeze_u128(&mut self) -> u128 {
        let mut w = [0u64; 2];
        self.squeeze_u64s(&mut w);
        (w[0] as u128) | ((w[1] as u128) << 64)
    }

    fn squeeze_nonzero_u128(&mut self) -> u128 {
        loop {
            let v = self.squeeze_u128();
            if v != 0 {
                return v;
            }
        }
    }

    fn squeeze_bytes32(&mut self) -> [u8; 32] {
        let mut words = [0u64; 4];
        self.squeeze_u64s(&mut words);
        let mut out = [0u8; 32];
        for (chunk, &w) in out.chunks_exact_mut(8).zip(&words) {
            chunk.copy_from_slice(&w.to_le_bytes());
        }
        ct_zeroize_u64s(&mut words);
        out
    }
}

/// Build the pre-absorbed 25-lane state for `cshake256_framed_32("QSAG.OUTER.MESSAGE.V1", ...)`
/// after absorbing the 136-byte cSHAKE customization block, frame count `5`, `key` (`32`B),
/// and `session` (`32`B) (`88` bytes = `11` lanes in block 1).
fn build_mac_prefix(key: &[u8; 32], session: &[u8; 32]) -> [u64; 25] {
    // NIST SP 800-185 bytepad(encode_string("") || encode_string("QSAG.OUTER.MESSAGE.V1"), 136)
    let custom = b"QSAG.OUTER.MESSAGE.V1";
    let mut block = [0u8; 136];
    block[0] = 1;
    block[1] = 136;
    block[2] = 1;
    block[3] = 0;
    block[4] = 1;
    block[5] = (custom.len() * 8) as u8;
    block[6..6 + custom.len()].copy_from_slice(custom);

    let mut state = [0u64; 25];
    for (lane, chunk) in state[..17].iter_mut().zip(block.chunks_exact(8)) {
        let mut buf = [0u8; 8];
        buf.copy_from_slice(chunk);
        *lane = u64::from_le_bytes(buf);
    }
    keccak_f1600(&mut state);

    state[0] ^= 5u64;
    state[1] ^= 32u64;
    for (lane, chunk) in state[2..6].iter_mut().zip(key.chunks_exact(8)) {
        let mut buf = [0u8; 8];
        buf.copy_from_slice(chunk);
        *lane ^= u64::from_le_bytes(buf);
        ct_zeroize_bytes(&mut buf);
    }
    state[6] ^= 32u64;
    for (lane, chunk) in state[7..11].iter_mut().zip(session.chunks_exact(8)) {
        let mut buf = [0u8; 8];
        buf.copy_from_slice(chunk);
        *lane ^= u64::from_le_bytes(buf);
        ct_zeroize_bytes(&mut buf);
    }
    state
}

// ============================================================================
// Polynomial-Basis GF(2^128) = GF(2)[x]/(x^128 + x^7 + x^2 + x + 1) & Bitslice
// ============================================================================

type Gf128 = [u64; 2];
type Gf128Lanes = [Gf128; 64];
type RepGf128Lanes = [Gf128Lanes; 2];
type Bs128 = [u64; 128];
type Bs256 = [BitPlane256; 128];

#[inline(always)]
const fn u128_to_gf128(v: u128) -> Gf128 {
    [v as u64, (v >> 64) as u64]
}

#[inline(always)]
const fn gf128_to_u128(a: Gf128) -> u128 {
    (a[0] as u128) | ((a[1] as u128) << 64)
}

#[inline(always)]
const fn xor_gf128(a: Gf128, b: Gf128) -> Gf128 {
    [a[0] ^ b[0], a[1] ^ b[1]]
}

/// Branch-free multiplication by `x` in `GF(2)[x]/(x^128 + x^7 + x^2 + x + 1)`.
#[inline(always)]
const fn poly128_mul_x(c: u128) -> u128 {
    let carry = 0u128.wrapping_sub(c >> 127);
    (c << 1) ^ (carry & 0x87)
}

/// Exact branch-free multiplication by `x^16` in `GF(2)[x]/(x^128 + x^7 + x^2 + x + 1)`.
/// Since `deg(h) <= 15`, `deg(h * (x^7 + x^2 + x + 1)) <= 22 < 128`, requiring a single step.
#[cfg(test)]
#[inline(always)]
const fn poly128_mul_x16(c: u128) -> u128 {
    let h = c >> 112;
    (c << 16) ^ h ^ (h << 1) ^ (h << 2) ^ (h << 7)
}

/// Constant-time 8x8 bit-matrix transpose (`out[r]` bit `u == (cols[u] >> r) & 1`).
#[inline(always)]
fn transpose_8x8(cols: [u8; 8]) -> [u8; 8] {
    let mut x = u64::from_le_bytes(cols);
    let t1 = (x ^ (x >> 7)) & 0x00aa_00aa_00aa_00aa;
    x = x ^ t1 ^ (t1 << 7);
    let t2 = (x ^ (x >> 14)) & 0x0000_cccc_0000_cccc;
    x = x ^ t2 ^ (t2 << 14);
    let t3 = (x ^ (x >> 28)) & 0x0000_0000_f0f0_f0f0;
    x = x ^ t3 ^ (t3 << 28);
    x.to_le_bytes()
}

/// Constant-time 16-column (`[u128; 16]`) to 128-row (`[u16; 128]`) bit transpose.
#[inline]
fn transpose_cols16_to_u16(cols: &[u128; 16]) -> [u16; 128] {
    let mut out = [0u16; 128];
    for r_blk in 0..16 {
        let shift = r_blk * 8;
        let mut sub_lo = [0u8; 8];
        let mut sub_hi = [0u8; 8];
        for u in 0..8 {
            sub_lo[u] = (cols[u] >> shift) as u8;
            sub_hi[u] = (cols[8 + u] >> shift) as u8;
        }
        let tr_lo = transpose_8x8(sub_lo);
        let tr_hi = transpose_8x8(sub_hi);
        for bit in 0..8 {
            out[shift + bit] = (tr_lo[bit] as u16) | ((tr_hi[bit] as u16) << 8);
        }
    }
    out
}

#[inline(always)]
const fn xor_plane256(a: BitPlane256, b: BitPlane256) -> BitPlane256 {
    [a[0] ^ b[0], a[1] ^ b[1], a[2] ^ b[2], a[3] ^ b[3]]
}

/// (`11` `BitPlane256` XORs, zero branches, zero secret-dependent indices).
/// Build subset sums in public order. Table entries contain shares, but every
/// lookup index used by evaluation is derived exclusively from a public challenge.
#[inline]
fn build_byte_tabs_bs256(words16: &[BitPlane256; 16], tabs: &mut [[BitPlane256; 256]; 2]) {
    for (byte, tab) in tabs.iter_mut().enumerate() {
        tab[0] = [0; 4];
        for bit in 0..8 {
            let base = 1 << bit;
            tab[base] = words16[8 * byte + bit];
            for i in 1..base {
                tab[base + i] = xor_plane256(tab[i], tab[base]);
            }
        }
    }
}

/// Evaluate a public `128 x 16` bit-matrix across four groups of 64 lanes.
#[inline(always)]
fn eval_public_matrix_128x16_bs256(
    row_masks: &[u16; 128],
    tabs: &[[BitPlane256; 256]; 2],
    out: &mut Bs256,
) {
    for (dst, &mask) in out.iter_mut().zip(row_masks) {
        *dst = xor_plane256(
            tabs[0][(mask & 0xff) as usize],
            tabs[1][(mask >> 8) as usize],
        );
    }
}

/// Accumulate a public `128 x 16` bit-matrix across all 256 lanes.
#[inline(always)]
fn xor_public_matrix_128x16_bs256(
    row_masks: &[u16; 128],
    tabs: &[[BitPlane256; 256]; 2],
    out: &mut Bs256,
) {
    for (dst, &mask) in out.iter_mut().zip(row_masks) {
        let prod = xor_plane256(
            tabs[0][(mask & 0xff) as usize],
            tabs[1][(mask >> 8) as usize],
        );
        *dst = xor_plane256(*dst, prod);
    }
}

/// Precompute the eight `128 x 16` public multiplication sub-matrices for constant `c in GF(2^128)`.
#[inline]
fn build_public_mul_masks_bs256(c: Gf128) -> [[u16; 128]; 8] {
    let mut cur = gf128_to_u128(c);
    let mut out = [[0u16; 128]; 8];
    for dst in &mut out {
        let mut cols = [0u128; 16];
        for col in &mut cols {
            *col = cur;
            cur = poly128_mul_x(cur);
        }
        *dst = transpose_cols16_to_u16(&cols);
    }
    out
}

/// Constant-time bitsliced accumulation `acc ^= c * src` across all 256 `GF(2^128)` lanes in `src`
/// using 8-bit byte tables indexed strictly by public `masks8`.
#[inline]
fn xor_mul_bs256_by_public(
    src: &Bs256,
    masks8: &[[u16; 128]; 8],
    tabs8: &mut [[BitPlane256; 256]; 2],
    acc: &mut Bs256,
) {
    for (chunk_idx, row_masks) in masks8.iter().enumerate() {
        let slice16: &[BitPlane256; 16] = src[chunk_idx * 16..chunk_idx * 16 + 16]
            .try_into()
            .expect("16-row slice");
        build_byte_tabs_bs256(slice16, tabs8);
        xor_public_matrix_128x16_bs256(row_masks, tabs8, acc);
    }
}

/// Multiply one column by `x^(16 * blocks)`, for public `blocks` in `0..8`.
/// Overflow degree is at most 111, so reduction by `x^7 + x^2 + x + 1`
/// has degree at most 118 and needs only one pass.
#[inline]
fn bs256_col_mul_x_pow16(bs: &mut Bs256, sub: usize, blocks: usize) {
    debug_assert!(blocks < 8);
    let shift = 16 * blocks;
    if shift == 0 {
        return;
    }
    let mut hi = [0u64; 112];
    for (r, dst) in hi[..shift].iter_mut().enumerate() {
        *dst = bs[128 - shift + r][sub];
    }
    for r in (shift..128).rev() {
        bs[r][sub] = bs[r - shift][sub];
    }
    for row in &mut bs[..shift] {
        row[sub] = 0;
    }
    for (r, &h) in hi[..shift].iter().enumerate() {
        bs[r][sub] ^= h;
        bs[r + 1][sub] ^= h;
        bs[r + 2][sub] ^= h;
        bs[r + 7][sub] ^= h;
    }
    ct_zeroize_u64s(&mut hi);
}

/// Dispatch `GF(2^128)` dot products directly to hardware `VPCLMULQDQ`/`PCLMULQDQ`/`PMULL`
/// (`cpuid::probe_capabilities()` is cached in an `AtomicU32`).
#[inline(always)]
fn gf128_dot_acc(acc: &mut Gf128, a: &[Gf128], b: &[Gf128], backend: SimdBackend) {
    gf2_128_mul_acc_batch_with_backend(acc, a, b, backend);
}

/// Hardware-accelerated single `GF(2^128)` multiplication via `PCLMULQDQ`/`PMULL`.
#[inline(always)]
fn gf128_mul_hw(a: Gf128, b: Gf128, backend: SimdBackend) -> Gf128 {
    let mut acc = [0u64; 2];
    gf2_128_mul_acc_batch_with_backend(&mut acc, &[a], &[b], backend);
    acc
}

/// Convert two 64-lane bitsliced 128-bit planes into two 64-element `Gf128` arrays via
/// hardware-accelerated 64x256 butterfly transpose using caller-owned wiped `rows`.
#[inline]
fn transpose_pair_bs128_to_lanes(
    plane_a: &Bs128,
    plane_b: &Bs128,
    out_a: &mut Gf128Lanes,
    out_b: &mut Gf128Lanes,
    rows: &mut [BitPlane256; 64],
    backend: SimdBackend,
) {
    for (r, row) in rows.iter_mut().enumerate() {
        *row = [plane_a[r], plane_a[64 + r], plane_b[r], plane_b[64 + r]];
    }
    transpose64x256_with_backend(rows, backend);
    for (lane, row) in rows.iter().enumerate() {
        out_a[lane] = [row[0], row[1]];
        out_b[lane] = [row[2], row[3]];
    }
}

/// Convert a 256-way bitsliced 128-bit plane (`4` groups x `64` lanes) into four 64-element
/// `Gf128Lanes` arrays via two hardware-accelerated 64x256 butterfly transposes.
#[inline]
fn transpose_bs256_to_quad_lanes(
    plane: &Bs256,
    out: &mut [Gf128Lanes; 4],
    rows: &mut [BitPlane256; 64],
    backend: SimdBackend,
) {
    rows.copy_from_slice(&plane[..64]);
    transpose64x256_with_backend(rows, backend);
    for (lane, row) in rows.iter().enumerate() {
        out[0][lane][0] = row[0];
        out[1][lane][0] = row[1];
        out[2][lane][0] = row[2];
        out[3][lane][0] = row[3];
    }
    rows.copy_from_slice(&plane[64..]);
    transpose64x256_with_backend(rows, backend);
    for (lane, row) in rows.iter().enumerate() {
        out[0][lane][1] = row[0];
        out[1][lane][1] = row[1];
        out[2][lane][1] = row[2];
        out[3][lane][1] = row[3];
    }
}

/// Inverse 64x256 butterfly transpose from two 64-element `Gf128` lane arrays into
/// two 64-lane bitsliced 128-bit planes using caller-owned wiped `rows`.
#[cfg(test)]
#[inline]
fn transpose_pair_lanes_to_bs128(
    in_a: &Gf128Lanes,
    in_b: &Gf128Lanes,
    plane_a: &mut Bs128,
    plane_b: &mut Bs128,
    rows: &mut [BitPlane256; 64],
    backend: SimdBackend,
) {
    for (lane, row) in rows.iter_mut().enumerate() {
        *row = [in_a[lane][0], in_a[lane][1], in_b[lane][0], in_b[lane][1]];
    }
    transpose64x256_with_backend(rows, backend);
    for (r, row) in rows.iter().enumerate() {
        plane_a[r] = row[0];
        plane_a[64 + r] = row[1];
        plane_b[r] = row[2];
        plane_b[64 + r] = row[3];
    }
}

#[inline]
fn zeroize_gf128_slice(slice: &mut [Gf128]) {
    for item in slice {
        ct_zeroize_u64s(item);
    }
}

#[inline]
fn zeroize_bs256_vec_hwm(vec_buf: &mut Vec<Bs256>, hwm: usize) {
    let target = hwm.min(vec_buf.capacity());
    if vec_buf.len() < target {
        vec_buf.resize(target, [[0u64; 4]; 128]);
    }
    for quad in vec_buf.iter_mut() {
        for row in quad.iter_mut() {
            ct_zeroize_u64s(row);
        }
    }
    vec_buf.clear();
}

struct ZeroizeRepGf128LanesVec(Vec<RepGf128Lanes>);
impl Drop for ZeroizeRepGf128LanesVec {
    fn drop(&mut self) {
        for item in &mut self.0 {
            zeroize_gf128_slice(&mut item[0]);
            zeroize_gf128_slice(&mut item[1]);
        }
    }
}

struct ZeroizeBitVec(Vec<Bit>);
impl Drop for ZeroizeBitVec {
    fn drop(&mut self) {
        for b in &mut self.0 {
            ct_zeroize_u64s(&mut b.0);
        }
    }
}

struct BitCheckScratch {
    planes: Box<[Bs128; STEP0_PLANES]>,
    tr_rows: Box<[BitPlane256; 64]>,
    step0_buf: Vec<Gf128>,
    hwm_step0: usize,
    step0_acc: Box<[Gf128Lanes; STEP0_PLANES]>,
    h0_flat: Vec<Gf128Lanes>,
    a_bs: [[Vec<Bs256>; 2]; 2],
    b_bs: [[Vec<Bs256>; 2]; 2],
    hwm_bs: usize,
    step2_lanes: Box<[[[Gf128; STEP2_QUAD_CHUNK * 4]; 64]; 8]>,
    tabs8: Box<[[BitPlane256; 256]; 2]>,
    bs256_buf: Box<Bs256>,
    h_fold: Box<[Gf128Lanes; 4]>,
    c_claim: [RepGf128Lanes; 2],
    a_fin: [RepGf128Lanes; 2],
    b_fin: [RepGf128Lanes; 2],
    u_mask: [RepGf128Lanes; 2],
    v_mask: [RepGf128Lanes; 2],
    base_locals: [Gf128Lanes; 4],
}
impl BitCheckScratch {
    fn new_boxed() -> Box<Self> {
        let z_lanes = [[0u64; 2]; 64];
        Box::new(Self {
            planes: Box::new([[0u64; 128]; STEP0_PLANES]),
            tr_rows: Box::new([[0u64; 4]; 64]),
            step0_buf: vec![[0u64; 2]; STEP0_PLANES * 64 * STEP0_CHUNK],
            hwm_step0: 0,
            step0_acc: Box::new([z_lanes; STEP0_PLANES]),
            h0_flat: Vec::with_capacity(STEP0_SLOTS),
            a_bs: [[Vec::new(), Vec::new()], [Vec::new(), Vec::new()]],
            b_bs: [[Vec::new(), Vec::new()], [Vec::new(), Vec::new()]],
            hwm_bs: 0,
            step2_lanes: Box::new([[[[0u64; 2]; STEP2_QUAD_CHUNK * 4]; 64]; 8]),
            tabs8: Box::new([[[0u64; 4]; 256]; 2]),
            bs256_buf: Box::new([[0u64; 4]; 128]),
            h_fold: Box::new([z_lanes; 4]),
            c_claim: [[z_lanes; 2]; 2],
            a_fin: [[z_lanes; 2]; 2],
            b_fin: [[z_lanes; 2]; 2],
            u_mask: [[z_lanes; 2]; 2],
            v_mask: [[z_lanes; 2]; 2],
            base_locals: [z_lanes; 4],
        })
    }

    fn prepare(&mut self, num_quads: usize) {
        let reserve_quads = num_quads + (num_quads & 1);
        if reserve_quads > self.hwm_bs {
            self.hwm_bs = reserve_quads;
        }
        for t in 0..2 {
            for side in 0..2 {
                self.a_bs[t][side].clear();
                self.a_bs[t][side].resize(num_quads, [[0u64; 4]; 128]);
                self.b_bs[t][side].clear();
                self.b_bs[t][side].resize(num_quads, [[0u64; 4]; 128]);
            }
        }
        let z_lanes = [[0u64; 2]; 64];
        self.step0_acc.fill(z_lanes);
        self.h0_flat.clear();
    }

    fn wipe_all(&mut self) {
        for plane in self.planes.iter_mut() {
            ct_zeroize_u64s(plane);
        }
        for row in self.tr_rows.iter_mut() {
            ct_zeroize_u64s(row);
        }
        let step0_used = self.hwm_step0.min(self.step0_buf.len());
        zeroize_gf128_slice(&mut self.step0_buf[..step0_used]);
        self.hwm_step0 = 0;
        for plane in self.step0_acc.iter_mut() {
            zeroize_gf128_slice(plane);
        }
        for h in &mut self.h0_flat {
            zeroize_gf128_slice(h);
        }
        self.h0_flat.clear();
        for t in 0..2 {
            for side in 0..2 {
                zeroize_bs256_vec_hwm(&mut self.a_bs[t][side], self.hwm_bs);
                zeroize_bs256_vec_hwm(&mut self.b_bs[t][side], self.hwm_bs);
            }
        }
        self.hwm_bs = 0;
        for arr in self.step2_lanes.iter_mut() {
            for lane_slice in arr.iter_mut() {
                zeroize_gf128_slice(lane_slice);
            }
        }
        for tab in self.tabs8.iter_mut() {
            for entry in tab.iter_mut() {
                ct_zeroize_u64s(entry);
            }
        }
        for row in self.bs256_buf.iter_mut() {
            ct_zeroize_u64s(row);
        }
        for h in self.h_fold.iter_mut() {
            zeroize_gf128_slice(h);
        }
        for pair in [
            &mut self.c_claim,
            &mut self.a_fin,
            &mut self.b_fin,
            &mut self.u_mask,
            &mut self.v_mask,
        ] {
            for r in pair {
                zeroize_gf128_slice(&mut r[0]);
                zeroize_gf128_slice(&mut r[1]);
            }
        }
        for b in &mut self.base_locals {
            zeroize_gf128_slice(b);
        }
    }
}
impl Drop for BitCheckScratch {
    fn drop(&mut self) {
        self.wipe_all();
    }
}

// ============================================================================
// Cubic Goldilocks Extension Field GF(p)[u] / (u^3 - 7), |F| = p^3 > 2^191.99
// ============================================================================

type GoldExt3 = [u64; 3];
type RepGoldExt3 = [GoldExt3; 2];

#[inline]
fn g3_add(a: GoldExt3, b: GoldExt3) -> GoldExt3 {
    [gl_add(a[0], b[0]), gl_add(a[1], b[1]), gl_add(a[2], b[2])]
}

#[inline]
fn g3_sub(a: GoldExt3, b: GoldExt3) -> GoldExt3 {
    [gl_sub(a[0], b[0]), gl_sub(a[1], b[1]), gl_sub(a[2], b[2])]
}

#[inline]
fn g3_mul(a: GoldExt3, b: GoldExt3) -> GoldExt3 {
    let a0b0 = gl_mul(a[0], b[0]);
    let a1b1 = gl_mul(a[1], b[1]);
    let a2b2 = gl_mul(a[2], b[2]);
    let t_0 = gl_add(gl_mul(a[1], b[2]), gl_mul(a[2], b[1]));
    let c0 = gl_add(a0b0, gl_mul(7, t_0));
    let c1 = gl_add(
        gl_add(gl_mul(a[0], b[1]), gl_mul(a[1], b[0])),
        gl_mul(7, a2b2),
    );
    let c2 = gl_add(gl_add(gl_mul(a[0], b[2]), a1b1), gl_mul(a[2], b[0]));
    [c0, c1, c2]
}

#[inline]
fn g3_canonical(a: GoldExt3) -> bool {
    a[0] < GOLDILOCKS_P && a[1] < GOLDILOCKS_P && a[2] < GOLDILOCKS_P
}

#[inline]
fn squeeze_g3_challenge(xof: &mut WordSponge136) -> GoldExt3 {
    let mut words = [0u64; 9];
    xof.squeeze_u64s(&mut words);
    let mut raw = [0u8; 72];
    for (chunk, &w) in raw.chunks_exact_mut(8).zip(&words) {
        chunk.copy_from_slice(&w.to_le_bytes());
    }
    let mut out = [0u64; 3];
    for (dst, slice24) in out.iter_mut().zip(raw.chunks_exact(24)) {
        let mut arr = [0u8; 24];
        arr.copy_from_slice(slice24);
        *dst = reduce_192_zero_bias(&arr);
    }
    out
}

#[inline]
fn squeeze_fp_challenge(xof: &mut WordSponge136, d: Domain) -> Value {
    loop {
        let b = xof.squeeze_bytes32();
        let mut v = crate::scalar::decode(&b);
        if d == Domain::Ed {
            v[3] &= 0x7fff_ffff_ffff_ffff;
        }
        if d.canonical(v) {
            return v;
        }
    }
}

// ============================================================================
// Replicated Mixed-Domain Active Engine
// ============================================================================

/// Replicated additive field shares, with one entry per repetition lane.
pub(crate) type FieldWord = Vec<[Value; 2]>;
type PendingFieldTriple = (FieldWord, FieldWord, FieldWord);

#[cfg(test)]
#[derive(Clone, Copy)]
pub(crate) enum FaultInjection {
    BitAnd {
        call_countdown: usize,
        gate: usize,
        lane: usize,
    },
    FieldMul {
        domain: Domain,
        call_countdown: usize,
        lane: usize,
    },
}

#[cfg(test)]
impl FaultInjection {
    pub(crate) fn to_raw(self) -> [usize; 4] {
        match self {
            Self::BitAnd {
                call_countdown,
                gate,
                lane,
            } => [0, call_countdown, gate, lane],
            Self::FieldMul {
                domain,
                call_countdown,
                lane,
            } => {
                let tag = match domain {
                    Domain::Gold => 1,
                    Domain::Secp => 2,
                    Domain::Ed => 3,
                    Domain::Bit => 0,
                };
                [tag, call_countdown, lane, 0]
            }
        }
    }
    fn from_raw([tag, a, b, c]: [usize; 4]) -> Self {
        match tag {
            0 => Self::BitAnd {
                call_countdown: a,
                gate: b,
                lane: c,
            },
            1 => Self::FieldMul {
                domain: Domain::Gold,
                call_countdown: a,
                lane: b,
            },
            2 => Self::FieldMul {
                domain: Domain::Secp,
                call_countdown: a,
                lane: b,
            },
            _ => Self::FieldMul {
                domain: Domain::Ed,
                call_countdown: a,
                lane: b,
            },
        }
    }
}

pub(crate) struct Engine<T> {
    pub party: usize,
    session: [u8; 32],
    keys: [[u8; 32]; 2],
    mac_prefix: [[u64; 25]; 2],
    pads: [WordSponge136; 2],
    edge_sponges: [WordSponge136; 2],
    coin_rng: WordSponge136,
    sequence: u64,
    poisoned: bool,
    pending_bits_raw: Vec<u64>,
    pending_secp: Vec<PendingFieldTriple>,
    pending_ed: Vec<PendingFieldTriple>,
    pending_gold: Vec<PendingFieldTriple>,
    scratch_r: Vec<u64>,
    scratch_s: Vec<u64>,
    bit_scratch: Option<Box<BitCheckScratch>>,
    #[cfg(test)]
    pub(crate) fault: Option<FaultInjection>,
    pub transport: T,
}

impl<T> Drop for Engine<T> {
    fn drop(&mut self) {
        for key in &mut self.keys {
            ct_zeroize_bytes(key);
        }
        for pref in &mut self.mac_prefix {
            ct_zeroize_u64s(pref);
        }
        ct_zeroize_u64s(&mut self.scratch_r);
        ct_zeroize_u64s(&mut self.scratch_s);
        ct_zeroize_u64s(&mut self.pending_bits_raw);
        for list in [
            &mut self.pending_secp,
            &mut self.pending_ed,
            &mut self.pending_gold,
        ] {
            for (a, b, c) in list {
                for fw in [a, b, c] {
                    for pair in fw {
                        ct_zeroize_u64s(&mut pair[0]);
                        ct_zeroize_u64s(&mut pair[1]);
                    }
                }
            }
        }
    }
}

impl<T: Transport> Engine<T> {
    pub fn new(
        party: usize,
        session: [u8; 32],
        keys: [[u8; 32]; 2],
        transport: T,
    ) -> Result<Self, Error> {
        if party >= 3 {
            return Err(Error::InvalidConfiguration);
        }
        let mac_prefix = [
            build_mac_prefix(&keys[0], &session),
            build_mac_prefix(&keys[1], &session),
        ];
        let pads = keys.map(|key| {
            let mut seed = cshake256_framed_32(b"QSAG.OUTER.PADS.V1", &[&key, &session]);
            let sp = WordSponge136::from_shake_seed(&seed);
            ct_zeroize_bytes(&mut seed);
            sp
        });
        let prev = (party + 2) % 3;
        let next = (party + 1) % 3;
        let init_edge = |u: usize, v: usize| {
            let mut s = WordSponge136::new();
            s.absorb_u64(0x4544_4745_5f56_3100); // "EDGE_V1"
            s.absorb_bytes32(&session);
            s.absorb_u64((u as u64) | ((v as u64) << 8));
            s
        };
        let edge_sponges = [init_edge(prev, party), init_edge(party, next)];
        let mut coin_seed = cshake256_framed_32(
            b"QSAG.OUTER.COIN.RNG.V1",
            &[&session, &[party as u8], &keys[0], &keys[1]],
        );
        let coin_rng = WordSponge136::from_shake_seed(&coin_seed);
        ct_zeroize_bytes(&mut coin_seed);
        #[cfg(test)]
        let fault = transport.test_fault_raw().map(FaultInjection::from_raw);
        Ok(Self {
            party,
            session,
            keys,
            mac_prefix,
            pads,
            edge_sponges,
            coin_rng,
            sequence: 0,
            poisoned: false,
            pending_bits_raw: Vec::new(),
            pending_secp: Vec::new(),
            pending_ed: Vec::new(),
            pending_gold: Vec::new(),
            scratch_r: Vec::new(),
            scratch_s: Vec::new(),
            bit_scratch: None,
            #[cfg(test)]
            fault,
            transport,
        })
    }

    /// Hedge local coin-flipping randomness with custodian-private ceremony entropy.
    pub fn mix_entropy(&mut self, entropy: &[u8; 32]) {
        let current = self.coin_rng.squeeze_bytes32();
        let mut next_seed = cshake256_framed_32(
            b"QSAG.OUTER.COIN.HEDGE.V1",
            &[&current, entropy, &self.session],
        );
        self.coin_rng = WordSponge136::from_shake_seed(&next_seed);
        ct_zeroize_bytes(&mut next_seed);
    }

    #[inline]
    pub fn constant(&self, x: u64) -> Bit {
        Bit([
            if self.party == 0 { x } else { 0 },
            if (self.party + 1) % 3 == 0 { x } else { 0 },
        ])
    }

    fn tag(
        &self,
        peer: usize,
        sender: usize,
        recipient: usize,
        seq: u64,
        payload: &[u64],
    ) -> [u8; 32] {
        let mut state = self.mac_prefix[peer];
        let sr = (sender as u64 & 0xff) | ((recipient as u64 & 0xff) << 8);
        let byte_len = (payload.len() as u64) * 8;
        state[11] ^= 2u64;
        state[12] ^= sr | (8u64 << 16);
        state[13] ^= seq << 16;
        state[14] ^= (seq >> 48) | (byte_len << 16);
        let mut carry16 = byte_len >> 48;
        let mut lane = 15usize;
        for &w in payload {
            state[lane] ^= carry16 | (w << 16);
            carry16 = w >> 48;
            lane += 1;
            if lane == 17 {
                keccak_f1600(&mut state);
                lane = 0;
            }
        }
        state[lane] ^= carry16 | (0x04u64 << 16);
        state[16] ^= 0x8000_0000_0000_0000;
        keccak_f1600(&mut state);
        let mut out = [0u8; 32];
        for (chunk, &w) in out.chunks_exact_mut(8).zip(&state[..4]) {
            chunk.copy_from_slice(&w.to_le_bytes());
        }
        ct_zeroize_u64s(&mut state);
        out
    }

    fn raw_exchange(&mut self, payloads: [Vec<u64>; 2]) -> Result<[Vec<u64>; 2], Error> {
        if self.poisoned {
            return Err(Error::MultiplicationCheck);
        }
        let peers = [(self.party + 2) % 3, (self.party + 1) % 3];
        let seq = self.sequence;
        let [p0, p1] = payloads;
        let out_tag_0 = self.tag(0, self.party, peers[0], seq, &p0);
        let out_tag_1 = self.tag(1, self.party, peers[1], seq, &p1);
        let outgoing = [
            Envelope {
                tag: out_tag_0,
                sender: self.party,
                recipient: peers[0],
                sequence: seq,
                payload: p0,
            },
            Envelope {
                tag: out_tag_1,
                sender: self.party,
                recipient: peers[1],
                sequence: seq,
                payload: p1,
            },
        ];
        let mut incoming = self.transport.exchange(outgoing)?;
        for (i, message) in incoming.iter().enumerate() {
            let expected = self.tag(i, peers[i], self.party, seq, &message.payload);
            if message.sender != peers[i]
                || message.recipient != self.party
                || message.sequence != seq
                || ct_eq_bytes_mask(&expected, &message.tag) != u64::MAX
            {
                self.poisoned = true;
                return Err(Error::Authentication(peers[i]));
            }
        }
        // Record canonical directed-edge tags: edge 0 is `prev -> self`, edge 1 is `self -> next`.
        self.edge_sponges[0].absorb_u64(seq);
        self.edge_sponges[0].absorb_bytes32(&incoming[0].tag);
        self.edge_sponges[0].absorb_bytes32(&out_tag_0);
        self.edge_sponges[1].absorb_u64(seq);
        self.edge_sponges[1].absorb_bytes32(&out_tag_1);
        self.edge_sponges[1].absorb_bytes32(&incoming[1].tag);

        self.sequence = seq.checked_add(1).ok_or(Error::InvalidConfiguration)?;
        Ok(incoming.each_mut().map(|m| core::mem::take(&mut m.payload)))
    }

    fn raw_share_owned(&mut self, own: Vec<u64>) -> Result<(Vec<u64>, Vec<u64>), Error> {
        let len = own.len();
        let mut own_copy = Vec::with_capacity(len);
        own_copy.extend_from_slice(&own);
        let incoming = self.raw_exchange([own, Vec::new()])?;
        if incoming[1].len() != len || !incoming[0].is_empty() {
            ct_zeroize_u64s(&mut own_copy);
            self.poisoned = true;
            return Err(Error::InvalidConfiguration);
        }
        let [_, next_share] = incoming;
        Ok((own_copy, next_share))
    }

    pub fn share(&mut self, own: &[u64]) -> Result<Word, Error> {
        let (mut mine, mut next) = self.raw_share_owned(own.to_vec())?;
        let out = mine.iter().zip(&next).map(|(&a, &b)| Bit([a, b])).collect();
        ct_zeroize_u64s(&mut mine);
        ct_zeroize_u64s(&mut next);
        Ok(out)
    }

    /// Share secret bits while enforcing that every custodian supplies uniform
    /// 64-lane masks (`0` or `u64::MAX`), preventing cross-repetition witness splitting.
    pub fn share_uniform_lanes(&mut self, own: &[u64]) -> Result<Word, Error> {
        if own.iter().any(|&w| w != 0 && w != u64::MAX) {
            return Err(Error::InvalidConfiguration);
        }
        let (mut mine, mut next) = self.raw_share_owned(own.to_vec())?;
        if next.iter().any(|&w| w != 0 && w != u64::MAX) {
            ct_zeroize_u64s(&mut mine);
            ct_zeroize_u64s(&mut next);
            self.poisoned = true;
            return Err(Error::Disagreement((self.party + 1) % 3));
        }
        let out = mine.iter().zip(&next).map(|(&a, &b)| Bit([a, b])).collect();
        ct_zeroize_u64s(&mut mine);
        ct_zeroize_u64s(&mut next);
        Ok(out)
    }

    /// Two-round commit-then-open coin-flipping bound to the full three-edge
    /// authenticated transcript up to `self.sequence`.
    fn coin_flip(&mut self, domain: &[u8]) -> Result<[u8; 32], Error> {
        let flip_seq = self.sequence;
        let td_own = [
            self.edge_sponges[0].digest_clone(),
            self.edge_sponges[1].digest_clone(),
        ];
        let mut r_own = self.coin_rng.squeeze_bytes32();
        let session = self.session;
        let commit_for = |party: usize, td: &[[u8; 32]; 2], r: &[u8; 32]| {
            cshake256_framed_32(
                b"QSAG.OUTER.COIN.COMMIT.V1",
                &[
                    &session,
                    &flip_seq.to_le_bytes(),
                    &(party as u64).to_le_bytes(),
                    domain,
                    &td[0],
                    &td[1],
                    r,
                ],
            )
        };
        let c_own = commit_for(self.party, &td_own, &r_own);
        let to_words4 = |b: &[u8; 32]| -> [u64; 4] {
            core::array::from_fn(|i| {
                let mut buf = [0u8; 8];
                buf.copy_from_slice(&b[8 * i..8 * i + 8]);
                u64::from_le_bytes(buf)
            })
        };
        let from_words4 = |w: &[u64]| -> [u8; 32] {
            let mut out = [0u8; 32];
            for (chunk, &val) in out.chunks_exact_mut(8).zip(&w[..4]) {
                chunk.copy_from_slice(&val.to_le_bytes());
            }
            out
        };

        let c_vec = to_words4(&c_own).to_vec();
        let in_commits = self.raw_exchange([c_vec.clone(), c_vec])?;
        if in_commits[0].len() != 4 || in_commits[1].len() != 4 {
            ct_zeroize_bytes(&mut r_own);
            self.poisoned = true;
            return Err(Error::MultiplicationCheck);
        }
        let prev = (self.party + 2) % 3;
        let next = (self.party + 1) % 3;
        let mut commits = [[0u8; 32]; 3];
        commits[self.party] = c_own;
        commits[prev] = from_words4(&in_commits[0]);
        commits[next] = from_words4(&in_commits[1]);

        let mut open_words = Vec::with_capacity(24);
        open_words.extend_from_slice(&to_words4(&r_own));
        open_words.extend_from_slice(&to_words4(&td_own[0]));
        open_words.extend_from_slice(&to_words4(&td_own[1]));
        for c in &commits {
            open_words.extend_from_slice(&to_words4(c));
        }
        let in_opens = self.raw_exchange([open_words.clone(), open_words])?;
        if in_opens[0].len() != 24 || in_opens[1].len() != 24 {
            ct_zeroize_bytes(&mut r_own);
            self.poisoned = true;
            return Err(Error::MultiplicationCheck);
        }

        let mut r_prev = from_words4(&in_opens[0][0..4]);
        let td_prev = [
            from_words4(&in_opens[0][4..8]),
            from_words4(&in_opens[0][8..12]),
        ];
        let mut r_next = from_words4(&in_opens[1][0..4]);
        let td_next = [
            from_words4(&in_opens[1][4..8]),
            from_words4(&in_opens[1][8..12]),
        ];

        // Verify echoed commitments match across all three parties, pairwise edge
        // transcripts match on all three links, and both peer commitments open validly.
        let mut valid_mask = ct_eq_bytes_mask(&td_prev[1], &td_own[0])
            & ct_eq_bytes_mask(&td_next[0], &td_own[1])
            & ct_eq_bytes_mask(&td_prev[0], &td_next[1]);
        for (idx, expected_c) in commits.iter().enumerate() {
            let echo_prev = from_words4(&in_opens[0][12 + 4 * idx..16 + 4 * idx]);
            let echo_next = from_words4(&in_opens[1][12 + 4 * idx..16 + 4 * idx]);
            valid_mask &= ct_eq_bytes_mask(&echo_prev, expected_c);
            valid_mask &= ct_eq_bytes_mask(&echo_next, expected_c);
        }
        let expected_prev = commit_for(prev, &td_prev, &r_prev);
        let expected_next = commit_for(next, &td_next, &r_next);
        valid_mask &= ct_eq_bytes_mask(&expected_prev, &commits[prev]);
        valid_mask &= ct_eq_bytes_mask(&expected_next, &commits[next]);

        if valid_mask != u64::MAX {
            ct_zeroize_bytes(&mut r_own);
            ct_zeroize_bytes(&mut r_prev);
            ct_zeroize_bytes(&mut r_next);
            self.poisoned = true;
            return Err(Error::MultiplicationCheck);
        }

        let mut r_xor = [0u8; 32];
        for (i, dst) in r_xor.iter_mut().enumerate() {
            *dst = r_own[i] ^ r_prev[i] ^ r_next[i];
        }
        let mut edges_by_party = [[0u8; 32]; 3];
        edges_by_party[self.party] = td_own[0];
        edges_by_party[prev] = td_prev[0];
        edges_by_party[next] = td_next[0];

        let out = cshake256_framed_32(
            b"QSAG.OUTER.COIN.DERIVE.V1",
            &[
                &self.session,
                &flip_seq.to_le_bytes(),
                domain,
                &edges_by_party[0],
                &edges_by_party[1],
                &edges_by_party[2],
                &commits[0],
                &commits[1],
                &commits[2],
                &r_xor,
            ],
        );
        ct_zeroize_bytes(&mut r_own);
        ct_zeroize_bytes(&mut r_prev);
        ct_zeroize_bytes(&mut r_next);
        ct_zeroize_bytes(&mut r_xor);
        Ok(out)
    }

    fn open_raw_bits(&mut self, bits: &[Bit]) -> Result<Vec<u64>, Error> {
        let mut own = Vec::with_capacity(bits.len() * 2);
        for b in bits {
            own.push(b.0[0]);
            own.push(b.0[1]);
        }
        let incoming = self.raw_exchange([own.clone(), own])?;
        if incoming.iter().any(|v| v.len() != bits.len() * 2) {
            self.poisoned = true;
            return Err(Error::InvalidConfiguration);
        }
        let mut out = Vec::with_capacity(bits.len());
        for (i, b) in bits.iter().enumerate() {
            if incoming[0][2 * i + 1] != b.0[0] {
                self.poisoned = true;
                return Err(Error::Disagreement((self.party + 2) % 3));
            }
            if incoming[1][2 * i] != b.0[1] || incoming[0][2 * i] != incoming[1][2 * i + 1] {
                self.poisoned = true;
                return Err(Error::Disagreement((self.party + 1) % 3));
            }
            out.push(b.0[0] ^ b.0[1] ^ incoming[0][2 * i]);
        }
        Ok(out)
    }

    fn reshare_gf128_lanes_many(
        &mut self,
        locals: &[Gf128Lanes],
    ) -> Result<Vec<RepGf128Lanes>, Error> {
        let total_u64 = locals.len() * 128;
        self.scratch_r.resize(total_u64, 0);
        self.scratch_s.resize(total_u64, 0);
        self.pads[0].squeeze_u64s(&mut self.scratch_r);
        self.pads[1].squeeze_u64s(&mut self.scratch_s);
        let mut own = Vec::with_capacity(total_u64);
        for (item_idx, local) in locals.iter().enumerate() {
            let base = item_idx * 128;
            for (lane_idx, &[w0, w1]) in local.iter().enumerate() {
                let off = base + 2 * lane_idx;
                own.push(w0 ^ self.scratch_r[off] ^ self.scratch_s[off]);
                own.push(w1 ^ self.scratch_r[off + 1] ^ self.scratch_s[off + 1]);
            }
        }
        let (mut mine, mut next) = self.raw_share_owned(own)?;
        let mut out = Vec::with_capacity(locals.len());
        for idx in 0..locals.len() {
            let base = idx * 128;
            let a: Gf128Lanes =
                core::array::from_fn(|lane| [mine[base + 2 * lane], mine[base + 2 * lane + 1]]);
            let b: Gf128Lanes =
                core::array::from_fn(|lane| [next[base + 2 * lane], next[base + 2 * lane + 1]]);
            out.push([a, b]);
        }
        ct_zeroize_u64s(&mut mine);
        ct_zeroize_u64s(&mut next);
        Ok(out)
    }

    fn prss_gf128_lanes(&mut self) -> RepGf128Lanes {
        let mut raw0 = [0u64; 128];
        let mut raw1 = [0u64; 128];
        self.pads[0].squeeze_u64s(&mut raw0);
        self.pads[1].squeeze_u64s(&mut raw1);
        let s0: Gf128Lanes = core::array::from_fn(|lane| [raw0[2 * lane], raw0[2 * lane + 1]]);
        let s1: Gf128Lanes = core::array::from_fn(|lane| [raw1[2 * lane], raw1[2 * lane + 1]]);
        ct_zeroize_u64s(&mut raw0);
        ct_zeroize_u64s(&mut raw1);
        [s0, s1]
    }

    /// Batch-verify up to `MAX_PENDING_BITS` (`262,144`) 64-lane Boolean `AND` triples over
    /// `GF(2^128) = GF(2)[x]/(x^128 + x^7 + x^2 + x + 1)` via a uniform `GF(2^128)` super-block
    /// combiner + two independent lockstep Arity-2 BBCGGI19 inner-product instances +
    /// randomized base-case sacrifice (`< 2^-128 + (60 / (2^128 - 1))^2 < 2^-127.99 << 2^-126`).
    fn verify_pending_bits_slice(&mut self, triples_raw: &[u64]) -> Result<(), Error> {
        debug_assert_eq!(triples_raw.len() % 6, 0);
        let n = triples_raw.len() / 6;
        if n == 0 {
            return Ok(());
        }
        let backend = detect_backend();
        let m = n.div_ceil(D0_BITS);
        let num_super = m.div_ceil(SUPER_BLOCKS);
        let num_quads = m.div_ceil(QUAD_BLOCKS);

        let seed0 = self.coin_flip(b"QSAG.OUTER.MULCHECK.BITS.INIT.V1")?;
        let mut xof0 = WordSponge136::from_shake_seed(&seed0);
        let gammas: Vec<Gf128> = (0..num_super)
            .map(|_| u128_to_gf128(xof0.squeeze_u128()))
            .collect();

        // `scratch` implements `Drop` (calling `wipe_all` via `ct_zeroize_u64s`), ensuring
        // deterministic zeroization on EVERY `Err` early return and when `Engine` drops.
        let mut scratch = self
            .bit_scratch
            .take()
            .unwrap_or_else(BitCheckScratch::new_boxed);
        scratch.prepare(num_quads);

        // Step 0 + Round 0: pack eight 16-gate blocks (`128` gates) per super-block
        // into 32 bit-planes (`z_s0`, `z_s1`, and 30 off-diagonal `R^s` slots), transpose via
        // hardware AVX2 butterfly, and accumulate against `gammas` via `PCLMULQDQ`.
        let mut x0_blk = [0u64; D0_BITS];
        let mut x1_blk = [0u64; D0_BITS];
        let mut y01_blk = [0u64; D0_BITS];
        let mut y0_blk = [0u64; D0_BITS];
        let mut lanes_a = [[0u64; 2]; 64];
        let mut lanes_b = [[0u64; 2]; 64];

        for q0 in (0..num_super).step_by(STEP0_CHUNK) {
            let q1 = (q0 + STEP0_CHUNK).min(num_super);
            let chunk_len = q1 - q0;
            let used_step0 = STEP0_PLANES * 64 * chunk_len;
            if used_step0 > scratch.hwm_step0 {
                scratch.hwm_step0 = used_step0;
            }
            for q_rel in 0..chunk_len {
                let q = q0 + q_rel;
                let super_start = q * SUPER_BITS * 6;
                let super_end = (super_start + SUPER_BITS * 6).min(triples_raw.len());
                let super_chunk = &triples_raw[super_start..super_end];
                scratch.planes.fill([0u64; 128]);

                for (b, blk_raw) in super_chunk.chunks(D0_BITS * 6).enumerate() {
                    let base = b * D0_BITS;
                    let blk_gates = blk_raw.len() / 6;
                    for (u, g) in blk_raw.chunks_exact(6).enumerate() {
                        x0_blk[u] = g[0];
                        x1_blk[u] = g[1];
                        y01_blk[u] = g[2] ^ g[3];
                        y0_blk[u] = g[2];
                        scratch.planes[0][base + u] = g[4];
                        scratch.planes[1][base + u] = g[5];
                    }
                    for s in 0..(2 * D0_BITS - 1) {
                        if s == D0_BITS - 1 {
                            continue;
                        }
                        let slot = if s < D0_BITS - 1 { s } else { s - 1 };
                        let plane = &mut scratch.planes[2 + slot];
                        let u_min = s.saturating_sub(D0_BITS - 1);
                        let u_max = (blk_gates + s).saturating_sub(D0_BITS - 1).min(blk_gates);
                        if u_min < u_max {
                            let len = u_max - u_min;
                            let v_min = u_min + (D0_BITS - 1) - s;
                            let dst = &mut plane[base + u_min..base + u_min + len];
                            let x0s = &x0_blk[u_min..u_min + len];
                            let x1s = &x1_blk[u_min..u_min + len];
                            let y01s = &y01_blk[v_min..v_min + len];
                            let y0s = &y0_blk[v_min..v_min + len];
                            for i in 0..len {
                                dst[i] = (x0s[i] & y01s[i]) ^ (x1s[i] & y0s[i]);
                            }
                        }
                    }
                }

                let sp = &mut *scratch;
                for pair_idx in 0..(STEP0_PLANES / 2) {
                    transpose_pair_bs128_to_lanes(
                        &sp.planes[2 * pair_idx],
                        &sp.planes[2 * pair_idx + 1],
                        &mut lanes_a,
                        &mut lanes_b,
                        &mut sp.tr_rows,
                        backend,
                    );
                    for (lane, (&la, &lb)) in lanes_a.iter().zip(&lanes_b).enumerate() {
                        sp.step0_buf[((2 * pair_idx) * 64 + lane) * chunk_len + q_rel] = la;
                        sp.step0_buf[((2 * pair_idx + 1) * 64 + lane) * chunk_len + q_rel] = lb;
                    }
                }
            }

            let sp = &mut *scratch;
            let gammas_slice = &gammas[q0..q1];
            for p in 0..STEP0_PLANES {
                for lane in 0..64 {
                    let base = (p * 64 + lane) * chunk_len;
                    let src = &sp.step0_buf[base..base + chunk_len];
                    gf128_dot_acc(&mut sp.step0_acc[p][lane], src, gammas_slice, backend);
                }
            }
        }
        ct_zeroize_u64s(&mut x0_blk);
        ct_zeroize_u64s(&mut x1_blk);
        ct_zeroize_u64s(&mut y01_blk);
        ct_zeroize_u64s(&mut y0_blk);
        zeroize_gf128_slice(&mut lanes_a);
        zeroize_gf128_slice(&mut lanes_b);

        for slot in 0..STEP0_SLOTS {
            scratch.h0_flat.push(scratch.step0_acc[2 + slot]);
        }
        let reshared_h0 = ZeroizeRepGf128LanesVec(self.reshare_gf128_lanes_many(&scratch.h0_flat)?);

        let seed_r0 = self.coin_flip(b"QSAG.OUTER.MULCHECK.BITS.R0.V1")?;
        let mut xof_r0 = WordSponge136::from_shake_seed(&seed_r0);
        let r0 = [
            u128_to_gf128(xof_r0.squeeze_u128()),
            u128_to_gf128(xof_r0.squeeze_u128()),
        ];

        // Evaluate `H_0(r_0^(t))` at both independent challenges and precompute
        // one `128 x 16` public projection matrix per challenge for `A`.
        const DEG_R0: usize = 2 * D0_BITS - 1;
        const HALF_R0: usize = D0_BITS - 1;
        let mut pows_r0 = [[[0u64; 2]; DEG_R0]; 2];
        let mut masks_a = [[0u16; 128]; 2];
        let mut eval_r0 = [[0u64; 2]; DEG_R0];

        for t in 0..2 {
            pows_r0[t][0] = [1, 0];
            for s in 1..DEG_R0 {
                pows_r0[t][s] = gf128_mul_hw(pows_r0[t][s - 1], r0[t], backend);
            }
            for side in 0..2 {
                for lane in 0..64 {
                    for (s, dst) in eval_r0[..HALF_R0].iter_mut().enumerate() {
                        *dst = reshared_h0.0[s][side][lane];
                    }
                    eval_r0[HALF_R0] = scratch.step0_acc[side][lane];
                    for (slot_hi, dst) in eval_r0[HALF_R0 + 1..].iter_mut().enumerate() {
                        *dst = reshared_h0.0[HALF_R0 + slot_hi][side][lane];
                    }
                    let mut acc = [0u64; 2];
                    gf128_dot_acc(&mut acc, &eval_r0, &pows_r0[t], backend);
                    scratch.c_claim[t][side][lane] = acc;
                }
            }

            let xr0 = u128_to_gf128(poly128_mul_x(gf128_to_u128(r0[t])));
            let mut cur_xr = [1u64, 0u64];
            let mut cols = [0u128; 16];
            for col in &mut cols {
                *col = gf128_to_u128(cur_xr);
                cur_xr = gf128_mul_hw(cur_xr, xr0, backend);
            }
            masks_a[t] = transpose_cols16_to_u16(&cols);
        }
        zeroize_gf128_slice(&mut eval_r0);
        drop(reshared_h0);

        // Step 1: each quad holds four 16-gate blocks. Two quads share a
        // super-block challenge; block b contributes the public factor x^(16*b).
        let mut x_rows = [[[0u64; 4]; 16]; 2];
        let mut y_rows = [[[0u64; 4]; 16]; 2];
        let mut masks_b = [[0u16; 128]; 2];
        for (q_quad, quad_chunk) in triples_raw.chunks(QUAD_BITS * 6).enumerate() {
            let b_count = quad_chunk.len().div_ceil(D0_BITS * 6);
            x_rows.fill([[0; 4]; 16]);
            y_rows.fill([[0; 4]; 16]);
            for (sub, block) in quad_chunk.chunks(D0_BITS * 6).enumerate() {
                for (u, g) in block.chunks_exact(6).enumerate() {
                    x_rows[0][u][sub] = g[0];
                    x_rows[1][u][sub] = g[1];
                    y_rows[0][u][sub] = g[2];
                    y_rows[1][u][sub] = g[3];
                }
            }
            // Reuse the projection masks for both halves of a super-block.
            if q_quad % 2 == 0 {
                for (t, mask) in masks_b.iter_mut().enumerate() {
                    let cols = core::array::from_fn(|v| {
                        gf128_to_u128(gf128_mul_hw(
                            gammas[q_quad / 2],
                            pows_r0[t][HALF_R0 - v],
                            backend,
                        ))
                    });
                    *mask = transpose_cols16_to_u16(&cols);
                }
            }
            let sp = &mut *scratch;
            for side in 0..2 {
                build_byte_tabs_bs256(&x_rows[side], &mut sp.tabs8);
                for (t, mask) in masks_a.iter().enumerate() {
                    eval_public_matrix_128x16_bs256(mask, &sp.tabs8, &mut sp.a_bs[t][side][q_quad]);
                }
                build_byte_tabs_bs256(&y_rows[side], &mut sp.tabs8);
                for (t, mask) in masks_b.iter().enumerate() {
                    let dst = &mut sp.b_bs[t][side][q_quad];
                    eval_public_matrix_128x16_bs256(mask, &sp.tabs8, dst);
                    for sub in 0..b_count {
                        bs256_col_mul_x_pow16(dst, sub, 4 * (q_quad % 2) + sub);
                    }
                }
            }
        }
        for planes in [&mut x_rows, &mut y_rows] {
            for side in planes {
                for row in side {
                    ct_zeroize_u64s(row);
                }
            }
        }

        // Step 2: In-place Arity-2 half-split BBCGGI19 inner-product folding on `Bs256` quads
        // (`cur_quads -> ceil(cur_quads / 2) -> ... -> 1`), streaming cross-terms in L2-sized
        // chunks into contiguous `PCLMULQDQ` dot products and folding vectors via 8-bit byte
        // public matrix evaluation (`0` `a_next`/`b_next` buffers).
        let mut cur_quads = num_quads;
        let mut quad_tmp = [[[0u64; 2]; 64]; 4];

        while cur_quads > 1 {
            if cur_quads % 2 == 1 {
                let padded = cur_quads + 1;
                if padded > scratch.hwm_bs {
                    scratch.hwm_bs = padded;
                }
                for t in 0..2 {
                    for side in 0..2 {
                        scratch.a_bs[t][side].push([[0u64; 4]; 128]);
                        scratch.b_bs[t][side].push([[0u64; 4]; 128]);
                    }
                }
                cur_quads = padded;
            }
            let half_q = cur_quads / 2;
            scratch.h_fold.fill([[0u64; 2]; 64]);

            for c0 in (0..half_q).step_by(STEP2_QUAD_CHUNK) {
                let chunk_q = (half_q - c0).min(STEP2_QUAD_CHUNK);
                let len = chunk_q * 4;
                let sp = &mut *scratch;
                for t in 0..2 {
                    for q_rel in 0..chunk_q {
                        let q_lo = c0 + q_rel;
                        let q_hi = half_q + q_lo;
                        let dst_off = q_rel * 4;

                        // Transpose the 6 direct planes + 2 XORed `b_sum` planes into contiguous
                        // per-lane slices (`step2_lanes[0..8][lane][dst_off..dst_off + 4]`).
                        let direct: [(&Bs256, usize); 6] = [
                            (&sp.a_bs[t][0][q_lo], 0),
                            (&sp.a_bs[t][1][q_lo], 1),
                            (&sp.a_bs[t][0][q_hi], 2),
                            (&sp.a_bs[t][1][q_hi], 3),
                            (&sp.b_bs[t][0][q_lo], 4),
                            (&sp.b_bs[t][0][q_hi], 6),
                        ];
                        for (src_bs, slot_idx) in direct {
                            transpose_bs256_to_quad_lanes(
                                src_bs,
                                &mut quad_tmp,
                                &mut sp.tr_rows,
                                backend,
                            );
                            for (lane, lane_dst) in sp.step2_lanes[slot_idx].iter_mut().enumerate()
                            {
                                lane_dst[dst_off] = quad_tmp[0][lane];
                                lane_dst[dst_off + 1] = quad_tmp[1][lane];
                                lane_dst[dst_off + 2] = quad_tmp[2][lane];
                                lane_dst[dst_off + 3] = quad_tmp[3][lane];
                            }
                        }

                        for (q_src, slot_idx) in [(q_lo, 5usize), (q_hi, 7usize)] {
                            for ((dst_r, &r0), &r1) in sp
                                .bs256_buf
                                .iter_mut()
                                .zip(&sp.b_bs[t][0][q_src])
                                .zip(&sp.b_bs[t][1][q_src])
                            {
                                *dst_r = xor_plane256(r0, r1);
                            }
                            transpose_bs256_to_quad_lanes(
                                &sp.bs256_buf,
                                &mut quad_tmp,
                                &mut sp.tr_rows,
                                backend,
                            );
                            for (lane, lane_dst) in sp.step2_lanes[slot_idx].iter_mut().enumerate()
                            {
                                lane_dst[dst_off] = quad_tmp[0][lane];
                                lane_dst[dst_off + 1] = quad_tmp[1][lane];
                                lane_dst[dst_off + 2] = quad_tmp[2][lane];
                                lane_dst[dst_off + 3] = quad_tmp[3][lane];
                            }
                        }
                    }

                    for lane in 0..64 {
                        gf128_dot_acc(
                            &mut sp.h_fold[2 * t][lane],
                            &sp.step2_lanes[0][lane][..len],
                            &sp.step2_lanes[7][lane][..len],
                            backend,
                        );
                        gf128_dot_acc(
                            &mut sp.h_fold[2 * t][lane],
                            &sp.step2_lanes[1][lane][..len],
                            &sp.step2_lanes[6][lane][..len],
                            backend,
                        );
                        gf128_dot_acc(
                            &mut sp.h_fold[2 * t + 1][lane],
                            &sp.step2_lanes[2][lane][..len],
                            &sp.step2_lanes[5][lane][..len],
                            backend,
                        );
                        gf128_dot_acc(
                            &mut sp.h_fold[2 * t + 1][lane],
                            &sp.step2_lanes[3][lane][..len],
                            &sp.step2_lanes[4][lane][..len],
                            backend,
                        );
                    }
                }
            }

            let reshared =
                ZeroizeRepGf128LanesVec(self.reshare_gf128_lanes_many(&scratch.h_fold[..])?);
            let seed_rk = self.coin_flip(b"QSAG.OUTER.MULCHECK.BITS.FOLD.V1")?;
            let mut xof_rk = WordSponge136::from_shake_seed(&seed_rk);
            let rk = [
                u128_to_gf128(xof_rk.squeeze_u128()),
                u128_to_gf128(xof_rk.squeeze_u128()),
            ];
            let rk_sq = [
                gf128_mul_hw(rk[0], rk[0], backend),
                gf128_mul_hw(rk[1], rk[1], backend),
            ];
            let rk_masks = [
                build_public_mul_masks_bs256(rk[0]),
                build_public_mul_masks_bs256(rk[1]),
            ];

            let sp = &mut *scratch;
            for t in 0..2 {
                let pows2 = [rk[t], rk_sq[t]];
                for side in 0..2 {
                    for lane in 0..64 {
                        let mut acc = reshared.0[2 * t][side][lane];
                        let rhs2 = [sp.c_claim[t][side][lane], reshared.0[2 * t + 1][side][lane]];
                        gf128_dot_acc(&mut acc, &rhs2, &pows2, backend);
                        sp.c_claim[t][side][lane] = acc;
                    }

                    let (lo_a, hi_a) = sp.a_bs[t][side].split_at_mut(half_q);
                    for (dst_a, src_a) in lo_a.iter_mut().zip(&*hi_a) {
                        xor_mul_bs256_by_public(src_a, &rk_masks[t], &mut sp.tabs8, dst_a);
                    }
                    sp.a_bs[t][side].truncate(half_q);

                    let (lo_b, hi_b) = sp.b_bs[t][side].split_at_mut(half_q);
                    for (dst_b, src_b) in lo_b.iter_mut().zip(&*hi_b) {
                        *sp.bs256_buf = *src_b;
                        xor_mul_bs256_by_public(
                            dst_b,
                            &rk_masks[t],
                            &mut sp.tabs8,
                            &mut sp.bs256_buf,
                        );
                        *dst_b = *sp.bs256_buf;
                    }
                    sp.b_bs[t][side].truncate(half_q);
                }
            }
            drop(reshared);
            cur_quads = half_q;
        }
        for ql in &mut quad_tmp {
            zeroize_gf128_slice(ql);
        }

        // Transpose the single remaining `Bs256` quad (`4` blocks x `64` lanes) and complete
        // the final `4 -> 2 -> 1` Arity-2 steps when `m > 1`.
        let mut a4 = [[[[[0u64; 2]; 64]; 4]; 2]; 2];
        let mut b4 = [[[[[0u64; 2]; 64]; 4]; 2]; 2];
        for t in 0..2 {
            for side in 0..2 {
                transpose_bs256_to_quad_lanes(
                    &scratch.a_bs[t][side][0],
                    &mut a4[t][side],
                    &mut scratch.tr_rows,
                    backend,
                );
                transpose_bs256_to_quad_lanes(
                    &scratch.b_bs[t][side][0],
                    &mut b4[t][side],
                    &mut scratch.tr_rows,
                    backend,
                );
            }
        }

        if m > 1 {
            let mut len4 = 4usize;
            while len4 > 1 {
                let half4 = len4 / 2;
                scratch.h_fold.fill([[0u64; 2]; 64]);
                for t in 0..2 {
                    for k in 0..half4 {
                        for lane in 0..64 {
                            let a_lo = [a4[t][0][k][lane], a4[t][1][k][lane]];
                            let a_hi = [a4[t][0][half4 + k][lane], a4[t][1][half4 + k][lane]];
                            let b0_lo = b4[t][0][k][lane];
                            let bsum_lo = xor_gf128(b0_lo, b4[t][1][k][lane]);
                            let b0_hi = b4[t][0][half4 + k][lane];
                            let bsum_hi = xor_gf128(b0_hi, b4[t][1][half4 + k][lane]);
                            gf128_dot_acc(
                                &mut scratch.h_fold[2 * t][lane],
                                &a_lo,
                                &[bsum_hi, b0_hi],
                                backend,
                            );
                            gf128_dot_acc(
                                &mut scratch.h_fold[2 * t + 1][lane],
                                &a_hi,
                                &[bsum_lo, b0_lo],
                                backend,
                            );
                        }
                    }
                }
                let reshared = match self.reshare_gf128_lanes_many(&scratch.h_fold[..]) {
                    Ok(v) => ZeroizeRepGf128LanesVec(v),
                    Err(e) => {
                        for arr in [&mut a4, &mut b4] {
                            for t_arr in arr {
                                for s_arr in t_arr {
                                    for sub_arr in s_arr {
                                        zeroize_gf128_slice(sub_arr);
                                    }
                                }
                            }
                        }
                        return Err(e);
                    }
                };
                let seed_rk = match self.coin_flip(b"QSAG.OUTER.MULCHECK.BITS.FOLD.V1") {
                    Ok(s) => s,
                    Err(e) => {
                        for arr in [&mut a4, &mut b4] {
                            for t_arr in arr {
                                for s_arr in t_arr {
                                    for sub_arr in s_arr {
                                        zeroize_gf128_slice(sub_arr);
                                    }
                                }
                            }
                        }
                        return Err(e);
                    }
                };
                let mut xof_rk = WordSponge136::from_shake_seed(&seed_rk);
                let rk = [
                    u128_to_gf128(xof_rk.squeeze_u128()),
                    u128_to_gf128(xof_rk.squeeze_u128()),
                ];
                let rk_sq = [
                    gf128_mul_hw(rk[0], rk[0], backend),
                    gf128_mul_hw(rk[1], rk[1], backend),
                ];
                for t in 0..2 {
                    let pows2 = [rk[t], rk_sq[t]];
                    for side in 0..2 {
                        for lane in 0..64 {
                            let mut acc = reshared.0[2 * t][side][lane];
                            let rhs2 = [
                                scratch.c_claim[t][side][lane],
                                reshared.0[2 * t + 1][side][lane],
                            ];
                            gf128_dot_acc(&mut acc, &rhs2, &pows2, backend);
                            scratch.c_claim[t][side][lane] = acc;
                        }
                        for k in 0..half4 {
                            for lane in 0..64 {
                                a4[t][side][k][lane] = xor_gf128(
                                    a4[t][side][k][lane],
                                    gf128_mul_hw(a4[t][side][half4 + k][lane], rk[t], backend),
                                );
                                b4[t][side][k][lane] = xor_gf128(
                                    gf128_mul_hw(b4[t][side][k][lane], rk[t], backend),
                                    b4[t][side][half4 + k][lane],
                                );
                            }
                        }
                    }
                }
                drop(reshared);
                len4 = half4;
            }
        }
        for t in 0..2 {
            for side in 0..2 {
                scratch.a_fin[t][side] = a4[t][side][0];
                scratch.b_fin[t][side] = b4[t][side][0];
                for sub_arr in &mut a4[t][side] {
                    zeroize_gf128_slice(sub_arr);
                }
                for sub_arr in &mut b4[t][side] {
                    zeroize_gf128_slice(sub_arr);
                }
            }
        }

        // Zero-knowledge randomized base-case sacrifice at `len == 1`.
        scratch.u_mask = [self.prss_gf128_lanes(), self.prss_gf128_lanes()];
        scratch.v_mask = [self.prss_gf128_lanes(), self.prss_gf128_lanes()];
        for t in 0..2 {
            for lane in 0..64 {
                let a0 = scratch.a_fin[t][0][lane];
                let a1 = scratch.a_fin[t][1][lane];
                let b0 = scratch.b_fin[t][0][lane];
                let b1 = scratch.b_fin[t][1][lane];
                let u0 = scratch.u_mask[t][0][lane];
                let u1 = scratch.u_mask[t][1][lane];
                let v0 = scratch.v_mask[t][0][lane];
                let v1 = scratch.v_mask[t][1][lane];
                let v_sum = xor_gf128(v0, v1);
                let b_sum = xor_gf128(b0, b1);

                let mut d1 = [0u64; 2];
                let mut lhs4 = [a0, a1, u0, u1];
                let mut rhs4 = [v_sum, v0, b_sum, b0];
                gf128_dot_acc(&mut d1, &lhs4, &rhs4, backend);
                zeroize_gf128_slice(&mut lhs4);
                zeroize_gf128_slice(&mut rhs4);

                let mut d2 = [0u64; 2];
                let mut lhs2 = [u0, u1];
                let mut rhs2 = [v_sum, v0];
                gf128_dot_acc(&mut d2, &lhs2, &rhs2, backend);
                zeroize_gf128_slice(&mut lhs2);
                zeroize_gf128_slice(&mut rhs2);

                scratch.base_locals[2 * t][lane] = d1;
                scratch.base_locals[2 * t + 1][lane] = d2;
            }
        }

        let d_sh = ZeroizeRepGf128LanesVec(self.reshare_gf128_lanes_many(&scratch.base_locals)?);
        let seed_base = self.coin_flip(b"QSAG.OUTER.MULCHECK.BITS.BASE.V1")?;
        let mut xof_base = WordSponge136::from_shake_seed(&seed_base);
        let rb = [
            u128_to_gf128(xof_base.squeeze_nonzero_u128()),
            u128_to_gf128(xof_base.squeeze_nonzero_u128()),
        ];
        let rb_sq = [
            gf128_mul_hw(rb[0], rb[0], backend),
            gf128_mul_hw(rb[1], rb[1], backend),
        ];

        let mut to_open = ZeroizeBitVec(Vec::with_capacity(6 * 128));
        for t in 0..2 {
            let pows2 = [rb[t], rb_sq[t]];
            for lane in 0..64 {
                let mut alpha_sh = [[0u64; 2]; 2];
                let mut beta_sh = [[0u64; 2]; 2];
                let mut gamma_sh = [[0u64; 2]; 2];
                for side in 0..2 {
                    alpha_sh[side] = xor_gf128(
                        scratch.a_fin[t][side][lane],
                        gf128_mul_hw(scratch.u_mask[t][side][lane], rb[t], backend),
                    );
                    beta_sh[side] = xor_gf128(
                        scratch.b_fin[t][side][lane],
                        gf128_mul_hw(scratch.v_mask[t][side][lane], rb[t], backend),
                    );
                    let mut g_val = scratch.c_claim[t][side][lane];
                    let d_arr = [d_sh.0[2 * t][side][lane], d_sh.0[2 * t + 1][side][lane]];
                    gf128_dot_acc(&mut g_val, &d_arr, &pows2, backend);
                    gamma_sh[side] = g_val;
                }
                for item in [&alpha_sh, &beta_sh, &gamma_sh] {
                    to_open.0.push(Bit([item[0][0], item[1][0]]));
                    to_open.0.push(Bit([item[0][1], item[1][1]]));
                }
                zeroize_gf128_slice(&mut alpha_sh);
                zeroize_gf128_slice(&mut beta_sh);
                zeroize_gf128_slice(&mut gamma_sh);
            }
        }
        drop(d_sh);

        let mut opened = self.open_raw_bits(&to_open.0).map_err(|err| match err {
            Error::Disagreement(_) => Error::MultiplicationCheck,
            other => other,
        })?;
        drop(to_open);

        let mut diff_acc = 0u64;
        for t in 0..2 {
            for lane in 0..64 {
                let base = (t * 64 + lane) * 6;
                let alpha = [opened[base], opened[base + 1]];
                let beta = [opened[base + 2], opened[base + 3]];
                let gamma = [opened[base + 4], opened[base + 5]];
                let expected = gf128_mul_hw(alpha, beta, backend);
                diff_acc |= (gamma[0] ^ expected[0]) | (gamma[1] ^ expected[1]);
            }
        }
        ct_zeroize_u64s(&mut opened);
        if diff_acc != 0 {
            self.poisoned = true;
            return Err(Error::MultiplicationCheck);
        }
        // Return `scratch` to `self.bit_scratch` for reuse across flushes; `Drop` on
        // `BitCheckScratch` deterministically wipes up to `hwm_*` when `Engine` drops.
        self.bit_scratch = Some(scratch);
        Ok(())
    }

    fn flush_pending_bits(&mut self) -> Result<(), Error> {
        if self.pending_bits_raw.is_empty() {
            return Ok(());
        }
        let mut batch = core::mem::take(&mut self.pending_bits_raw);
        for chunk in batch.chunks(MAX_PENDING_BITS * 6) {
            if let Err(err) = self.verify_pending_bits_slice(chunk) {
                ct_zeroize_u64s(&mut batch);
                return Err(err);
            }
        }
        ct_zeroize_u64s(&mut batch);
        batch.clear();
        self.pending_bits_raw = batch;
        Ok(())
    }

    fn reshare_fp_scalars(
        &mut self,
        locals: &[Value],
        d: Domain,
    ) -> Result<Vec<[Value; 2]>, Error> {
        let mut own = Vec::with_capacity(locals.len() * 4);
        let mut mine_vals = Vec::with_capacity(locals.len());
        for &lv in locals {
            let r0 = Self::field_pad(&mut self.pads[0], d);
            let r1 = Self::field_pad(&mut self.pads[1], d);
            let masked = d.add(lv, d.sub(r0, r1));
            mine_vals.push(masked);
            own.extend_from_slice(&masked);
        }
        let (_, next_raw) = self.raw_share_owned(own)?;
        let mut out = Vec::with_capacity(locals.len());
        for (mv, chunk) in mine_vals.into_iter().zip(next_raw.chunks_exact(4)) {
            let nv: Value = [chunk[0], chunk[1], chunk[2], chunk[3]];
            if !d.canonical(nv) {
                self.poisoned = true;
                return Err(Error::MultiplicationCheck);
            }
            out.push([mv, nv]);
        }
        Ok(out)
    }

    fn open_raw_fp_scalars(
        &mut self,
        shares: &[[Value; 2]],
        d: Domain,
    ) -> Result<Vec<Value>, Error> {
        let mut payload = Vec::with_capacity(shares.len() * 8);
        for pair in shares {
            payload.extend_from_slice(&pair[0]);
            payload.extend_from_slice(&pair[1]);
        }
        let received = self.raw_exchange([payload.clone(), payload])?;
        if received.iter().any(|v| v.len() != shares.len() * 8) {
            self.poisoned = true;
            return Err(Error::InvalidConfiguration);
        }
        let mut out = Vec::with_capacity(shares.len());
        for (i, a) in shares.iter().enumerate() {
            let prev: [Value; 2] = core::array::from_fn(|j| {
                let s = &received[0][8 * i + 4 * j..8 * i + 4 * j + 4];
                [s[0], s[1], s[2], s[3]]
            });
            let next: [Value; 2] = core::array::from_fn(|j| {
                let s = &received[1][8 * i + 4 * j..8 * i + 4 * j + 4];
                [s[0], s[1], s[2], s[3]]
            });
            if prev[1] != a[0] {
                self.poisoned = true;
                return Err(Error::Disagreement((self.party + 2) % 3));
            }
            if next[0] != a[1] || prev[0] != next[1] || !d.canonical(prev[0]) {
                self.poisoned = true;
                return Err(Error::Disagreement((self.party + 1) % 3));
            }
            out.push(d.add(d.add(a[0], a[1]), prev[0]));
        }
        Ok(out)
    }

    /// Batch-verify large-prime (`Secp256k1` / `Ed25519`, `p > 2^254.99`) multiplications
    /// via replicated BBCGGI19 inner-product folding + zero-knowledge base-case sacrifice
    /// (cheating probability `< 30 / p < 2^-249 << 2^-128`).
    fn verify_pending_large_prime_slice(
        &mut self,
        triples: &[PendingFieldTriple],
        d: Domain,
    ) -> Result<(), Error> {
        if triples.is_empty() {
            return Ok(());
        }
        let total = triples.len() * 64;
        let seed0 = self.coin_flip(b"QSAG.OUTER.MULCHECK.FP.INIT.V1")?;
        let mut xof0 = WordSponge136::from_shake_seed(&seed0);

        struct FpScratch {
            a_vec: Vec<[Value; 2]>,
            b_vec: Vec<[Value; 2]>,
            cap: usize,
            c_claim: [Value; 2],
            u_sh: [Value; 2],
            v_sh: [Value; 2],
            d_loc: [Value; 2],
        }
        impl Drop for FpScratch {
            fn drop(&mut self) {
                for vec_buf in [&mut self.a_vec, &mut self.b_vec] {
                    if vec_buf.len() < self.cap && vec_buf.capacity() >= self.cap {
                        vec_buf.resize(self.cap, [[0; 4]; 2]);
                    }
                    for pair in vec_buf.iter_mut() {
                        ct_zeroize_u64s(&mut pair[0]);
                        ct_zeroize_u64s(&mut pair[1]);
                    }
                }
                for pair in [
                    &mut self.c_claim,
                    &mut self.u_sh,
                    &mut self.v_sh,
                    &mut self.d_loc,
                ] {
                    ct_zeroize_u64s(&mut pair[0]);
                    ct_zeroize_u64s(&mut pair[1]);
                }
            }
        }

        let mut sc = FpScratch {
            a_vec: Vec::with_capacity(total + 1),
            b_vec: Vec::with_capacity(total + 1),
            cap: total + 1,
            c_claim: [[0; 4]; 2],
            u_sh: [[0; 4]; 2],
            v_sh: [[0; 4]; 2],
            d_loc: [[0; 4]; 2],
        };

        for (x_fw, y_fw, z_fw) in triples {
            for ((x, y), z) in x_fw.iter().zip(y_fw).zip(z_fw) {
                let chi = squeeze_fp_challenge(&mut xof0, d);
                sc.a_vec.push([d.mul(chi, x[0]), d.mul(chi, x[1])]);
                sc.b_vec.push(*y);
                sc.c_claim[0] = d.add(sc.c_claim[0], d.mul(chi, z[0]));
                sc.c_claim[1] = d.add(sc.c_claim[1], d.mul(chi, z[1]));
            }
        }

        let rep_local_mul = |x: &[Value; 2], y: &[Value; 2]| -> Value {
            d.add(d.mul(x[0], d.add(y[0], y[1])), d.mul(x[1], y[0]))
        };

        while sc.a_vec.len() > 1 {
            if sc.a_vec.len() % 2 == 1 {
                sc.a_vec.push([[0; 4]; 2]);
                sc.b_vec.push([[0; 4]; 2]);
            }
            let half = sc.a_vec.len() / 2;
            sc.d_loc = [[0u64; 4]; 2];
            for k in 0..half {
                sc.d_loc[0] = d.add(
                    sc.d_loc[0],
                    rep_local_mul(&sc.a_vec[2 * k], &sc.b_vec[2 * k + 1]),
                );
                sc.d_loc[1] = d.add(
                    sc.d_loc[1],
                    rep_local_mul(&sc.a_vec[2 * k + 1], &sc.b_vec[2 * k]),
                );
            }
            let mut reshared = self.reshare_fp_scalars(&sc.d_loc, d)?;
            let seed_rk = match self.coin_flip(b"QSAG.OUTER.MULCHECK.FP.FOLD.V1") {
                Ok(s) => s,
                Err(e) => {
                    for r in &mut reshared {
                        ct_zeroize_u64s(&mut r[0]);
                        ct_zeroize_u64s(&mut r[1]);
                    }
                    return Err(e);
                }
            };
            let mut xof_rk = WordSponge136::from_shake_seed(&seed_rk);
            let rk = squeeze_fp_challenge(&mut xof_rk, d);
            let rk_sq = d.mul(rk, rk);

            sc.c_claim = [
                d.add(
                    reshared[0][0],
                    d.add(d.mul(rk, sc.c_claim[0]), d.mul(rk_sq, reshared[1][0])),
                ),
                d.add(
                    reshared[0][1],
                    d.add(d.mul(rk, sc.c_claim[1]), d.mul(rk_sq, reshared[1][1])),
                ),
            ];
            for r in &mut reshared {
                ct_zeroize_u64s(&mut r[0]);
                ct_zeroize_u64s(&mut r[1]);
            }
            for k in 0..half {
                let na = [
                    d.add(sc.a_vec[2 * k][0], d.mul(rk, sc.a_vec[2 * k + 1][0])),
                    d.add(sc.a_vec[2 * k][1], d.mul(rk, sc.a_vec[2 * k + 1][1])),
                ];
                let nb = [
                    d.add(d.mul(rk, sc.b_vec[2 * k][0]), sc.b_vec[2 * k + 1][0]),
                    d.add(d.mul(rk, sc.b_vec[2 * k][1]), sc.b_vec[2 * k + 1][1]),
                ];
                sc.a_vec[k] = na;
                sc.b_vec[k] = nb;
            }
            sc.a_vec.truncate(half);
            sc.b_vec.truncate(half);
        }

        let a0 = sc.a_vec[0];
        let b0 = sc.b_vec[0];
        sc.u_sh = [
            Self::field_pad(&mut self.pads[0], d),
            Self::field_pad(&mut self.pads[1], d),
        ];
        sc.v_sh = [
            Self::field_pad(&mut self.pads[0], d),
            Self::field_pad(&mut self.pads[1], d),
        ];
        sc.d_loc = [
            d.add(rep_local_mul(&a0, &sc.v_sh), rep_local_mul(&sc.u_sh, &b0)),
            rep_local_mul(&sc.u_sh, &sc.v_sh),
        ];
        let mut d_sh = self.reshare_fp_scalars(&sc.d_loc, d)?;

        let seed_base = match self.coin_flip(b"QSAG.OUTER.MULCHECK.FP.BASE.V1") {
            Ok(s) => s,
            Err(e) => {
                for r in &mut d_sh {
                    ct_zeroize_u64s(&mut r[0]);
                    ct_zeroize_u64s(&mut r[1]);
                }
                return Err(e);
            }
        };
        let mut xof_base = WordSponge136::from_shake_seed(&seed_base);
        let rb = loop {
            let cand = squeeze_fp_challenge(&mut xof_base, d);
            if cand != [0; 4] {
                break cand;
            }
        };
        let rb_sq = d.mul(rb, rb);

        let alpha_sh = [
            d.add(a0[0], d.mul(rb, sc.u_sh[0])),
            d.add(a0[1], d.mul(rb, sc.u_sh[1])),
        ];
        let beta_sh = [
            d.add(b0[0], d.mul(rb, sc.v_sh[0])),
            d.add(b0[1], d.mul(rb, sc.v_sh[1])),
        ];
        let gamma_sh = [
            d.add(
                sc.c_claim[0],
                d.add(d.mul(rb, d_sh[0][0]), d.mul(rb_sq, d_sh[1][0])),
            ),
            d.add(
                sc.c_claim[1],
                d.add(d.mul(rb, d_sh[0][1]), d.mul(rb_sq, d_sh[1][1])),
            ),
        ];
        for r in &mut d_sh {
            ct_zeroize_u64s(&mut r[0]);
            ct_zeroize_u64s(&mut r[1]);
        }
        let mut to_open = [alpha_sh, beta_sh, gamma_sh];
        let opened_res = self.open_raw_fp_scalars(&to_open, d);
        for item in &mut to_open {
            ct_zeroize_u64s(&mut item[0]);
            ct_zeroize_u64s(&mut item[1]);
        }
        let opened = opened_res.map_err(|err| match err {
            Error::Disagreement(_) => Error::MultiplicationCheck,
            other => other,
        })?;
        if opened[2] != d.mul(opened[0], opened[1]) {
            self.poisoned = true;
            return Err(Error::MultiplicationCheck);
        }
        Ok(())
    }

    fn prss_g3(&mut self) -> RepGoldExt3 {
        let sample = |sp: &mut WordSponge136| -> GoldExt3 {
            core::array::from_fn(|_| {
                loop {
                    let w = sp.squeeze_u64();
                    if w < GOLDILOCKS_P {
                        return w;
                    }
                }
            })
        };
        [sample(&mut self.pads[0]), sample(&mut self.pads[1])]
    }

    fn reshare_g3_many(&mut self, locals: &[GoldExt3]) -> Result<Vec<RepGoldExt3>, Error> {
        let mut own = Vec::with_capacity(locals.len() * 3);
        let mut mine_vals = Vec::with_capacity(locals.len());
        for &lv in locals {
            let r = self.prss_g3();
            let masked = g3_add(lv, g3_sub(r[0], r[1]));
            mine_vals.push(masked);
            own.extend_from_slice(&masked);
        }
        let (_, next_raw) = self.raw_share_owned(own)?;
        let mut out = Vec::with_capacity(locals.len());
        for (mv, chunk) in mine_vals.into_iter().zip(next_raw.chunks_exact(3)) {
            let nv: GoldExt3 = [chunk[0], chunk[1], chunk[2]];
            if !g3_canonical(nv) {
                self.poisoned = true;
                return Err(Error::MultiplicationCheck);
            }
            out.push([mv, nv]);
        }
        Ok(out)
    }

    fn open_raw_g3(&mut self, shares: &[RepGoldExt3]) -> Result<Vec<GoldExt3>, Error> {
        let mut payload = Vec::with_capacity(shares.len() * 6);
        for pair in shares {
            payload.extend_from_slice(&pair[0]);
            payload.extend_from_slice(&pair[1]);
        }
        let received = self.raw_exchange([payload.clone(), payload])?;
        if received.iter().any(|v| v.len() != shares.len() * 6) {
            self.poisoned = true;
            return Err(Error::InvalidConfiguration);
        }
        let mut out = Vec::with_capacity(shares.len());
        for (i, a) in shares.iter().enumerate() {
            let prev: RepGoldExt3 = core::array::from_fn(|j| {
                let s = &received[0][6 * i + 3 * j..6 * i + 3 * j + 3];
                [s[0], s[1], s[2]]
            });
            let next: RepGoldExt3 = core::array::from_fn(|j| {
                let s = &received[1][6 * i + 3 * j..6 * i + 3 * j + 3];
                [s[0], s[1], s[2]]
            });
            if prev[1] != a[0] {
                self.poisoned = true;
                return Err(Error::Disagreement((self.party + 2) % 3));
            }
            if next[0] != a[1] || prev[0] != next[1] || !g3_canonical(prev[0]) {
                self.poisoned = true;
                return Err(Error::Disagreement((self.party + 1) % 3));
            }
            out.push(g3_add(g3_add(a[0], a[1]), prev[0]));
        }
        Ok(out)
    }

    /// Batch-verify Goldilocks (`p = 2^64 - 2^32 + 1`) multiplications lifted into the
    /// irreducible cubic extension `GF(p)[u] / (u^3 - 7)` (`p^3 > 2^191.99`,
    /// cheating probability `< 30 / p^3 < 2^-186 << 2^-128`).
    fn verify_pending_gold_slice(&mut self, triples: &[PendingFieldTriple]) -> Result<(), Error> {
        if triples.is_empty() {
            return Ok(());
        }
        let total = triples.len() * 64;
        let seed0 = self.coin_flip(b"QSAG.OUTER.MULCHECK.GOLD.INIT.V1")?;
        let mut xof0 = WordSponge136::from_shake_seed(&seed0);

        struct GoldScratch {
            a_vec: Vec<RepGoldExt3>,
            b_vec: Vec<RepGoldExt3>,
            cap: usize,
            c_claim: RepGoldExt3,
            u_sh: RepGoldExt3,
            v_sh: RepGoldExt3,
            d_loc: [GoldExt3; 2],
        }
        impl Drop for GoldScratch {
            fn drop(&mut self) {
                for vec_buf in [&mut self.a_vec, &mut self.b_vec] {
                    if vec_buf.len() < self.cap && vec_buf.capacity() >= self.cap {
                        vec_buf.resize(self.cap, [[0; 3]; 2]);
                    }
                    for pair in vec_buf.iter_mut() {
                        ct_zeroize_u64s(&mut pair[0]);
                        ct_zeroize_u64s(&mut pair[1]);
                    }
                }
                for pair in [
                    &mut self.c_claim,
                    &mut self.u_sh,
                    &mut self.v_sh,
                    &mut self.d_loc,
                ] {
                    ct_zeroize_u64s(&mut pair[0]);
                    ct_zeroize_u64s(&mut pair[1]);
                }
            }
        }

        let mut sc = GoldScratch {
            a_vec: Vec::with_capacity(total + 1),
            b_vec: Vec::with_capacity(total + 1),
            cap: total + 1,
            c_claim: [[0; 3]; 2],
            u_sh: [[0; 3]; 2],
            v_sh: [[0; 3]; 2],
            d_loc: [[0; 3]; 2],
        };

        for (x_fw, y_fw, z_fw) in triples {
            for ((x, y), z) in x_fw.iter().zip(y_fw).zip(z_fw) {
                let chi = squeeze_g3_challenge(&mut xof0);
                let scale_base = |c: GoldExt3, v: u64| -> GoldExt3 {
                    [gl_mul(c[0], v), gl_mul(c[1], v), gl_mul(c[2], v)]
                };
                sc.a_vec
                    .push([scale_base(chi, x[0][0]), scale_base(chi, x[1][0])]);
                sc.b_vec.push([[y[0][0], 0, 0], [y[1][0], 0, 0]]);
                sc.c_claim[0] = g3_add(sc.c_claim[0], scale_base(chi, z[0][0]));
                sc.c_claim[1] = g3_add(sc.c_claim[1], scale_base(chi, z[1][0]));
            }
        }

        let rep_local_mul = |x: &RepGoldExt3, y: &RepGoldExt3| -> GoldExt3 {
            g3_add(g3_mul(x[0], g3_add(y[0], y[1])), g3_mul(x[1], y[0]))
        };

        while sc.a_vec.len() > 1 {
            if sc.a_vec.len() % 2 == 1 {
                sc.a_vec.push([[0; 3]; 2]);
                sc.b_vec.push([[0; 3]; 2]);
            }
            let half = sc.a_vec.len() / 2;
            sc.d_loc = [[0u64; 3]; 2];
            for k in 0..half {
                sc.d_loc[0] = g3_add(
                    sc.d_loc[0],
                    rep_local_mul(&sc.a_vec[2 * k], &sc.b_vec[2 * k + 1]),
                );
                sc.d_loc[1] = g3_add(
                    sc.d_loc[1],
                    rep_local_mul(&sc.a_vec[2 * k + 1], &sc.b_vec[2 * k]),
                );
            }
            let mut reshared = self.reshare_g3_many(&sc.d_loc)?;
            let seed_rk = match self.coin_flip(b"QSAG.OUTER.MULCHECK.GOLD.FOLD.V1") {
                Ok(s) => s,
                Err(e) => {
                    for r in &mut reshared {
                        ct_zeroize_u64s(&mut r[0]);
                        ct_zeroize_u64s(&mut r[1]);
                    }
                    return Err(e);
                }
            };
            let mut xof_rk = WordSponge136::from_shake_seed(&seed_rk);
            let rk = squeeze_g3_challenge(&mut xof_rk);
            let rk_sq = g3_mul(rk, rk);

            sc.c_claim = [
                g3_add(
                    reshared[0][0],
                    g3_add(g3_mul(rk, sc.c_claim[0]), g3_mul(rk_sq, reshared[1][0])),
                ),
                g3_add(
                    reshared[0][1],
                    g3_add(g3_mul(rk, sc.c_claim[1]), g3_mul(rk_sq, reshared[1][1])),
                ),
            ];
            for r in &mut reshared {
                ct_zeroize_u64s(&mut r[0]);
                ct_zeroize_u64s(&mut r[1]);
            }
            for k in 0..half {
                let na = [
                    g3_add(sc.a_vec[2 * k][0], g3_mul(rk, sc.a_vec[2 * k + 1][0])),
                    g3_add(sc.a_vec[2 * k][1], g3_mul(rk, sc.a_vec[2 * k + 1][1])),
                ];
                let nb = [
                    g3_add(g3_mul(rk, sc.b_vec[2 * k][0]), sc.b_vec[2 * k + 1][0]),
                    g3_add(g3_mul(rk, sc.b_vec[2 * k][1]), sc.b_vec[2 * k + 1][1]),
                ];
                sc.a_vec[k] = na;
                sc.b_vec[k] = nb;
            }
            sc.a_vec.truncate(half);
            sc.b_vec.truncate(half);
        }

        let a0 = sc.a_vec[0];
        let b0 = sc.b_vec[0];
        sc.u_sh = self.prss_g3();
        sc.v_sh = self.prss_g3();
        sc.d_loc = [
            g3_add(rep_local_mul(&a0, &sc.v_sh), rep_local_mul(&sc.u_sh, &b0)),
            rep_local_mul(&sc.u_sh, &sc.v_sh),
        ];
        let mut d_sh = self.reshare_g3_many(&sc.d_loc)?;

        let seed_base = match self.coin_flip(b"QSAG.OUTER.MULCHECK.GOLD.BASE.V1") {
            Ok(s) => s,
            Err(e) => {
                for r in &mut d_sh {
                    ct_zeroize_u64s(&mut r[0]);
                    ct_zeroize_u64s(&mut r[1]);
                }
                return Err(e);
            }
        };
        let mut xof_base = WordSponge136::from_shake_seed(&seed_base);
        let rb = loop {
            let cand = squeeze_g3_challenge(&mut xof_base);
            if cand != [0; 3] {
                break cand;
            }
        };
        let rb_sq = g3_mul(rb, rb);

        let alpha_sh = [
            g3_add(a0[0], g3_mul(rb, sc.u_sh[0])),
            g3_add(a0[1], g3_mul(rb, sc.u_sh[1])),
        ];
        let beta_sh = [
            g3_add(b0[0], g3_mul(rb, sc.v_sh[0])),
            g3_add(b0[1], g3_mul(rb, sc.v_sh[1])),
        ];
        let gamma_sh = [
            g3_add(
                sc.c_claim[0],
                g3_add(g3_mul(rb, d_sh[0][0]), g3_mul(rb_sq, d_sh[1][0])),
            ),
            g3_add(
                sc.c_claim[1],
                g3_add(g3_mul(rb, d_sh[0][1]), g3_mul(rb_sq, d_sh[1][1])),
            ),
        ];
        for r in &mut d_sh {
            ct_zeroize_u64s(&mut r[0]);
            ct_zeroize_u64s(&mut r[1]);
        }
        let mut to_open = [alpha_sh, beta_sh, gamma_sh];
        let opened_res = self.open_raw_g3(&to_open);
        for item in &mut to_open {
            ct_zeroize_u64s(&mut item[0]);
            ct_zeroize_u64s(&mut item[1]);
        }
        let opened = opened_res.map_err(|err| match err {
            Error::Disagreement(_) => Error::MultiplicationCheck,
            other => other,
        })?;
        if opened[2] != g3_mul(opened[0], opened[1]) {
            self.poisoned = true;
            return Err(Error::MultiplicationCheck);
        }
        Ok(())
    }

    fn flush_pending_domain(&mut self, d: Domain) -> Result<(), Error> {
        let mut batch = match d {
            Domain::Secp => core::mem::take(&mut self.pending_secp),
            Domain::Ed => core::mem::take(&mut self.pending_ed),
            Domain::Gold => core::mem::take(&mut self.pending_gold),
            Domain::Bit => return self.flush_pending_bits(),
        };
        if batch.is_empty() {
            return Ok(());
        }
        let wipe = |items: &mut [PendingFieldTriple]| {
            for (a, b, c) in items {
                for fw in [a, b, c] {
                    for pair in fw {
                        ct_zeroize_u64s(&mut pair[0]);
                        ct_zeroize_u64s(&mut pair[1]);
                    }
                }
            }
        };
        for chunk in batch.chunks(MAX_PENDING_FIELD_WORDS) {
            let res = if d == Domain::Gold {
                self.verify_pending_gold_slice(chunk)
            } else {
                self.verify_pending_large_prime_slice(chunk, d)
            };
            if let Err(err) = res {
                wipe(&mut batch);
                return Err(err);
            }
        }
        wipe(&mut batch);
        Ok(())
    }

    /// Mandatory pre-open active multiplication verification barrier across all
    /// Boolean and prime-field domains. Zero secret-dependent wire values may open
    /// unless this barrier succeeds.
    pub fn verify_all_pending(&mut self) -> Result<(), Error> {
        if self.poisoned {
            return Err(Error::MultiplicationCheck);
        }
        self.flush_pending_bits()?;
        self.flush_pending_domain(Domain::Secp)?;
        self.flush_pending_domain(Domain::Ed)?;
        self.flush_pending_domain(Domain::Gold)?;
        Ok(())
    }

    pub fn and(&mut self, pairs: &[(Bit, Bit)]) -> Result<Word, Error> {
        if self.poisoned {
            return Err(Error::MultiplicationCheck);
        }
        if pairs.is_empty() {
            return Ok(Vec::new());
        }
        self.scratch_r.resize(pairs.len(), 0);
        self.scratch_s.resize(pairs.len(), 0);
        self.pads[0].squeeze_u64s(&mut self.scratch_r);
        self.pads[1].squeeze_u64s(&mut self.scratch_s);
        let mut own = Vec::with_capacity(pairs.len());
        for ((&(a, b), &r), &s) in pairs.iter().zip(&self.scratch_r).zip(&self.scratch_s) {
            own.push((a.0[0] & (b.0[0] ^ b.0[1])) ^ (a.0[1] & b.0[0]) ^ r ^ s);
        }
        #[cfg(test)]
        if let Some(FaultInjection::BitAnd {
            ref mut call_countdown,
            gate,
            lane,
        }) = self.fault
        {
            if *call_countdown == 0 {
                let idx = gate.min(own.len() - 1);
                own[idx] ^= 1u64 << (lane & 63);
                self.fault = None;
            } else {
                *call_countdown -= 1;
            }
        }
        let (mut mine, mut next) = self.raw_share_owned(own)?;
        let out: Word = mine.iter().zip(&next).map(|(&a, &b)| Bit([a, b])).collect();
        ct_zeroize_u64s(&mut mine);
        ct_zeroize_u64s(&mut next);
        self.pending_bits_raw.reserve(pairs.len() * 6);
        for (&(a, b), &z) in pairs.iter().zip(&out) {
            self.pending_bits_raw
                .extend_from_slice(&[a.0[0], a.0[1], b.0[0], b.0[1], z.0[0], z.0[1]]);
        }
        if self.pending_bits_raw.len() >= MAX_PENDING_BITS * 6 {
            self.flush_pending_bits()?;
        }
        Ok(out)
    }

    /// Reconstruct only explicitly public data after verifying all pending
    /// Boolean and prime-field multiplications. Both holders supply every
    /// component; inconsistencies abort before the caller receives any output.
    pub fn open(&mut self, bits: &[Bit]) -> Result<Vec<u64>, Error> {
        self.verify_all_pending()?;
        self.open_raw_bits(bits)
    }

    pub fn agree(&mut self, root: [u8; 32]) -> Result<(), Error> {
        self.verify_all_pending()?;
        let words: Vec<_> = root
            .chunks_exact(8)
            .map(|b| u64::from_le_bytes(b.try_into().unwrap()))
            .collect();
        let received = self.raw_exchange([words.clone(), words.clone()])?;
        for (i, r) in received.iter().enumerate() {
            if r != &words {
                self.poisoned = true;
                return Err(Error::Disagreement(
                    (self.party + if i == 0 { 2 } else { 1 }) % 3,
                ));
            }
        }
        Ok(())
    }

    pub fn number(&self, x: Value, n: usize) -> Word {
        (0..n)
            .map(|i| {
                self.constant(if i < 256 && (x[i / 64] >> (i % 64)) & 1 != 0 {
                    u64::MAX
                } else {
                    0
                })
            })
            .collect()
    }

    pub fn xor(&self, a: &[Bit], b: &[Bit]) -> Word {
        a.iter().zip(b).map(|(&a, &b)| a ^ b).collect()
    }

    #[cfg(test)]
    pub fn select(&mut self, c: Bit, a: &[Bit], b: &[Bit]) -> Result<Word, Error> {
        let pairs: Vec<_> = a.iter().zip(b).map(|(&a, &b)| (c, a ^ b)).collect();
        Ok(self
            .and(&pairs)?
            .iter()
            .zip(b)
            .map(|(&x, &b)| x ^ b)
            .collect())
    }

    pub fn select_many(
        &mut self,
        conds: &[Bit],
        a_words: &[Word],
        b_words: &[Word],
    ) -> Result<Vec<Word>, Error> {
        if a_words.is_empty() {
            return Ok(Vec::new());
        }
        let width = a_words[0].len();
        let mut pairs = Vec::with_capacity(a_words.len() * width);
        for ((&c, a), b) in conds.iter().zip(a_words).zip(b_words) {
            for (&ai, &bi) in a.iter().zip(b) {
                pairs.push((c, ai ^ bi));
            }
        }
        let prods = self.and(&pairs)?;
        let mut out = Vec::with_capacity(a_words.len());
        for (b, chunk) in b_words.iter().zip(prods.chunks_exact(width)) {
            out.push(chunk.iter().zip(b).map(|(&p, &bi)| p ^ bi).collect());
        }
        Ok(out)
    }

    /// Parallel-prefix binary adder; logarithmic communication depth for single words.
    #[cfg(test)]
    pub fn add(&mut self, a: &[Bit], b: &[Bit], carry: Bit) -> Result<(Word, Bit), Error> {
        let n = a.len();
        let p = self.xor(a, b);
        let mut pp = p.clone();
        let mut g = self.and(&a.iter().copied().zip(b.iter().copied()).collect::<Vec<_>>())?;
        let mut step = 1;
        while step < n {
            let indices: Vec<_> = (2 * step - 1..n).step_by(2 * step).collect();
            self.prefix_layer(&indices, step, &mut pp, &mut g)?;
            step *= 2;
        }
        step /= 4;
        while step != 0 {
            let indices: Vec<_> = (3 * step - 1..n).step_by(2 * step).collect();
            self.prefix_layer(&indices, step, &mut pp, &mut g)?;
            step /= 2;
        }
        let cs = self.and(&pp.into_iter().map(|p| (p, carry)).collect::<Vec<_>>())?;
        for (gi, &csi) in g.iter_mut().zip(&cs) {
            *gi = *gi ^ csi;
        }
        Ok((
            (0..n)
                .map(|i| p[i] ^ if i == 0 { carry } else { g[i - 1] })
                .collect(),
            g[n - 1],
        ))
    }

    #[cfg(test)]
    fn prefix_layer(
        &mut self,
        indices: &[usize],
        step: usize,
        p: &mut [Bit],
        g: &mut [Bit],
    ) -> Result<(), Error> {
        if indices.is_empty() {
            return Ok(());
        }
        let pairs: Vec<_> = indices
            .iter()
            .flat_map(|&i| [(p[i], g[i - step]), (p[i], p[i - step])])
            .collect();
        let products = self.and(&pairs)?;
        for (k, &i) in indices.iter().enumerate() {
            g[i] = g[i] ^ products[2 * k];
            p[i] = products[2 * k + 1];
        }
        Ok(())
    }

    /// Vectorized 1-AND-per-bit Boyar-Peralta adder across `K` words in parallel.
    pub fn add_many(
        &mut self,
        a_words: &[Word],
        b_words: &[Word],
        carry_mask: u64,
    ) -> Result<(Vec<Word>, Vec<Bit>), Error> {
        if a_words.is_empty() {
            return Ok((Vec::new(), Vec::new()));
        }
        let k = a_words.len();
        let n = a_words[0].len();
        let mut sums: Vec<Word> = (0..k).map(|_| Vec::with_capacity(n)).collect();
        let mut carries = vec![self.constant(carry_mask); k];
        let mut pairs = Vec::with_capacity(k);
        for bit in 0..n {
            pairs.clear();
            for ((a, b), (&c, sum_w)) in a_words
                .iter()
                .zip(b_words)
                .zip(carries.iter().zip(&mut sums))
            {
                let ai = a[bit];
                let bi = b[bit];
                sum_w.push(ai ^ bi ^ c);
                pairs.push((ai ^ c, bi ^ c));
            }
            let prods = self.and(&pairs)?;
            for (c, &p) in carries.iter_mut().zip(&prods) {
                *c = *c ^ p;
            }
        }
        Ok((sums, carries))
    }

    /// Vectorized addition of `a_words` with a public constant `k_val` (`1` `AND` per bit).
    fn add_public_many(
        &mut self,
        a_words: &[Word],
        k_val: Value,
        carry_mask: u64,
        width: usize,
    ) -> Result<(Vec<Word>, Vec<Bit>), Error> {
        if a_words.is_empty() {
            return Ok((Vec::new(), Vec::new()));
        }
        let k = a_words.len();
        let k_bits = self.number(k_val, width);
        let mut sums: Vec<Word> = (0..k).map(|_| Vec::with_capacity(width)).collect();
        let mut carries = vec![self.constant(carry_mask); k];
        let mut pairs = Vec::with_capacity(k);
        for (bit, &kb) in k_bits.iter().enumerate() {
            pairs.clear();
            for (a, (&c, sum_w)) in a_words.iter().zip(carries.iter().zip(&mut sums)) {
                let ai = a[bit];
                sum_w.push(ai ^ kb ^ c);
                pairs.push((ai ^ c, kb ^ c));
            }
            let prods = self.and(&pairs)?;
            for (c, &p) in carries.iter_mut().zip(&prods) {
                *c = *c ^ p;
            }
        }
        Ok((sums, carries))
    }

    fn domain_c_const(d: Domain) -> Value {
        match d {
            Domain::Ed => [19, 0, 0, 0],
            Domain::Secp => [0x1_0000_03d1, 0, 0, 0],
            Domain::Gold => [0xffff_ffff, 0, 0, 0],
            Domain::Bit => [0, 0, 0, 0],
        }
    }

    /// Check `v < d.modulus()` across `v_words` (`width == d.width()`).
    /// Since `p = 2^n - c`, `v < p <==> v + c < 2^n <==> carry_out_n(v + c) == 0`.
    pub fn less_than_modulus_many(
        &mut self,
        v_words: &[Word],
        d: Domain,
    ) -> Result<Vec<Bit>, Error> {
        if v_words.is_empty() {
            return Ok(Vec::new());
        }
        let (_, carries) = self.add_public_many(v_words, Self::domain_c_const(d), 0, d.width())?;
        let ones = self.constant(u64::MAX);
        Ok(carries.into_iter().map(|ge| ge ^ ones).collect())
    }

    #[cfg(test)]
    pub fn reduce_once(&mut self, a: &[Bit], d: Domain) -> Result<Word, Error> {
        let modulus = self.number(d.modulus(), a.len());
        let not_m: Vec<_> = modulus
            .iter()
            .map(|&x| x ^ self.constant(u64::MAX))
            .collect();
        let (difference, ge) = self.add(a, &not_m, self.constant(u64::MAX))?;
        Ok(self.select(ge, &difference, a)?[..d.width()].to_vec())
    }

    #[cfg(test)]
    pub fn field_add(&mut self, a: &[Bit], b: &[Bit], d: Domain) -> Result<Word, Error> {
        if d == Domain::Bit {
            return Ok(self.xor(a, b));
        }
        let (mut s, c) = self.add(a, b, self.constant(0))?;
        s.push(c);
        self.reduce_once(&s, d)
    }

    pub fn field_add_many(
        &mut self,
        a_words: &[Word],
        b_words: &[Word],
        d: Domain,
    ) -> Result<Vec<Word>, Error> {
        if a_words.is_empty() {
            return Ok(Vec::new());
        }
        if d == Domain::Bit {
            return Ok(a_words
                .iter()
                .zip(b_words)
                .map(|(a, b)| self.xor(a, b))
                .collect());
        }
        let n = d.width();
        let (sums, overflow) = self.add_many(a_words, b_words, 0)?;
        // `0 <= a + b < 2p = 2^(n+1) - 2c`, so `overflow` and `carry_c` are mutually exclusive.
        let (diffs, carry_c) = self.add_public_many(&sums, Self::domain_c_const(d), 0, n)?;
        let ge: Vec<Bit> = overflow
            .into_iter()
            .zip(carry_c)
            .map(|(ov, cc)| ov ^ cc)
            .collect();
        self.select_many(&ge, &diffs, &sums)
    }

    #[cfg(test)]
    pub fn field_sub(&mut self, a: &[Bit], b: &[Bit], d: Domain) -> Result<Word, Error> {
        if d == Domain::Bit {
            return Ok(self.xor(a, b));
        }
        let not_b: Vec<_> = b.iter().map(|&x| x ^ self.constant(u64::MAX)).collect();
        let (difference, no_borrow) = self.add(a, &not_b, self.constant(u64::MAX))?;
        let modulus = self.number(d.modulus(), a.len());
        let (corrected, _) = self.add(&difference, &modulus, self.constant(0))?;
        self.select(no_borrow, &difference, &corrected)
    }

    pub fn field_sub_many(
        &mut self,
        a_words: &[Word],
        b_words: &[Word],
        d: Domain,
    ) -> Result<Vec<Word>, Error> {
        if a_words.is_empty() {
            return Ok(Vec::new());
        }
        if d == Domain::Bit {
            return Ok(a_words
                .iter()
                .zip(b_words)
                .map(|(a, b)| self.xor(a, b))
                .collect());
        }
        let ones = self.constant(u64::MAX);
        let not_b: Vec<Word> = b_words
            .iter()
            .map(|b| b.iter().map(|&x| x ^ ones).collect())
            .collect();
        let (diffs, no_borrow) = self.add_many(a_words, &not_b, u64::MAX)?;
        let (corrected, _) = self.add_public_many(&diffs, d.modulus(), 0, d.width())?;
        self.select_many(&no_borrow, &diffs, &corrected)
    }

    /// Carry-save tree; all compressors at a level share one network round.
    #[cfg(test)]
    fn sum_rows(&mut self, mut rows: Vec<Word>, width: usize) -> Result<Word, Error> {
        for r in &mut rows {
            r.resize(width, self.constant(0));
        }
        while rows.len() > 2 {
            let count = rows.len() / 3;
            let pairs: Vec<_> = rows
                .chunks_exact(3)
                .flat_map(|r| (0..width).map(move |i| (r[0][i] ^ r[1][i], r[0][i] ^ r[2][i])))
                .collect();
            let products = self.and(&pairs)?;
            let mut next = Vec::with_capacity(count * 2 + 2);
            for (k, r) in rows.chunks_exact(3).enumerate() {
                next.push((0..width).map(|i| r[0][i] ^ r[1][i] ^ r[2][i]).collect());
                let mut carry = vec![self.constant(0)];
                carry.extend((0..width - 1).map(|i| r[0][i] ^ products[k * width + i]));
                next.push(carry);
            }
            next.extend(rows[count * 3..].iter().cloned());
            rows = next;
        }
        if rows.len() == 1 {
            Ok(rows.remove(0))
        } else {
            Ok(self.add(&rows[0], &rows[1], self.constant(0))?.0)
        }
    }
    #[cfg(test)]
    pub fn field_mul(&mut self, a: &[Bit], b: &[Bit], d: Domain) -> Result<Word, Error> {
        if d == Domain::Bit {
            return self.and(&[(a[0], b[0])]);
        }
        let n = d.width();
        let pairs: Vec<_> = (0..n)
            .flat_map(|i| (0..n).map(move |j| (a[i], b[j])))
            .collect();
        let products = self.and(&pairs)?;
        let rows: Vec<_> = (0..n)
            .map(|i| {
                let mut row = vec![self.constant(0); i];
                row.extend_from_slice(&products[i * n..(i + 1) * n]);
                row
            })
            .collect();
        let wide = self.sum_rows(rows, 2 * n)?;
        self.reduce_wide(wide, d)
    }
    #[cfg(test)]
    pub fn field_scale(&mut self, a: &[Bit], value: Value, d: Domain) -> Result<Word, Error> {
        if d == Domain::Bit {
            return Ok(if value[0] == 0 {
                vec![self.constant(0)]
            } else {
                a.to_vec()
            });
        }
        let mut coefficient = [value[0], value[1], value[2], value[3], 0];
        let mut digits = Vec::new();
        let mut shift = 0;
        while coefficient.iter().any(|&x| x != 0) {
            if coefficient[0] & 1 != 0 {
                let negative = coefficient[0] & 3 == 3;
                digits.push((shift, negative));
                if negative {
                    let mut carry = true;
                    for limb in &mut coefficient {
                        let (v, c) = limb.overflowing_add(u64::from(carry));
                        *limb = v;
                        carry = c;
                    }
                } else {
                    coefficient[0] -= 1;
                }
            }
            for i in 0..4 {
                coefficient[i] = (coefficient[i] >> 1) | (coefficient[i + 1] << 63);
            }
            coefficient[4] >>= 1;
            shift += 1;
        }
        if digits.is_empty() {
            return Ok(vec![self.constant(0); d.width()]);
        }
        let width = d.width() + digits.last().unwrap().0 + 1;
        let mut correction = 0;
        let mut rows: Vec<_> = digits
            .into_iter()
            .map(|(shift, negative)| {
                let mut row = vec![self.constant(0); shift];
                row.extend_from_slice(a);
                row.resize(width, self.constant(0));
                if negative {
                    correction += 1;
                    for bit in &mut row {
                        *bit = *bit ^ self.constant(u64::MAX);
                    }
                }
                row
            })
            .collect();
        if correction != 0 {
            rows.push(self.number([correction, 0, 0, 0], width));
        }
        let wide = self.sum_rows(rows, width)?;
        self.reduce_wide(wide, d)
    }
    #[cfg(test)]
    fn reduce_wide(&mut self, mut wide: Word, d: Domain) -> Result<Word, Error> {
        let n = d.width();
        let c = match d {
            Domain::Ed => 19u64,
            Domain::Secp => 0x1_0000_03d1,
            Domain::Gold => 0xffff_ffff,
            Domain::Bit => unreachable!(),
        };
        let cbits = 64 - c.leading_zeros() as usize;
        while wide.len() > n + 1 {
            let high = wide[n..].to_vec();
            let width = core::cmp::max(n, high.len() + cbits) + 1;
            let mut rows = vec![wide[..n].to_vec()];
            for shift in 0..cbits {
                if (c >> shift) & 1 != 0 {
                    let mut r = vec![self.constant(0); shift];
                    r.extend_from_slice(&high);
                    rows.push(r);
                }
            }
            wide = self.sum_rows(rows, width)?;
        }
        self.reduce_once(&wide, d)
    }

    /// Lockstep 24-round `Keccak-f[1600]` across multiple 1600-bit states (`24` network rounds total).
    pub fn permutations(&mut self, states: &mut [&mut [Bit]]) -> Result<(), Error> {
        if states.is_empty() {
            return Ok(());
        }
        const RHO: [usize; 24] = [
            1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14, 27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20,
            44,
        ];
        const PI: [usize; 24] = [
            10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4, 15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1,
        ];
        let ones = self.constant(u64::MAX);
        let zero = self.constant(0);
        let mut pairs = Vec::with_capacity(states.len() * 1600);
        let mut c_buf = [zero; 320];
        let mut t_buf = [zero; 64];
        let mut next_buf = [zero; 64];

        for rc in KECCAK_RC {
            pairs.clear();
            for state in states.iter_mut() {
                for (i, c_slot) in c_buf.iter_mut().enumerate() {
                    let col = i / 64;
                    let z = i % 64;
                    *c_slot = state[col * 64 + z]
                        ^ state[(col + 5) * 64 + z]
                        ^ state[(col + 10) * 64 + z]
                        ^ state[(col + 15) * 64 + z]
                        ^ state[(col + 20) * 64 + z];
                }
                for x in 0..5 {
                    for z in 0..64 {
                        let d_xz = c_buf[((x + 4) % 5) * 64 + z]
                            ^ c_buf[((x + 1) % 5) * 64 + (z + 63) % 64];
                        for y in 0..5 {
                            state[(x + 5 * y) * 64 + z] = state[(x + 5 * y) * 64 + z] ^ d_xz;
                        }
                    }
                }
                t_buf.copy_from_slice(&state[64..128]);
                for (j, r) in PI.into_iter().zip(RHO) {
                    next_buf.copy_from_slice(&state[j * 64..j * 64 + 64]);
                    for z in 0..64 {
                        state[j * 64 + z] = t_buf[(z + 64 - r) % 64];
                    }
                    t_buf = next_buf;
                }
                for i in 0..1600 {
                    let row = (i / 320) * 320;
                    let x = (i / 64) % 5;
                    let z = i % 64;
                    pairs.push((
                        state[row + ((x + 1) % 5) * 64 + z] ^ ones,
                        state[row + ((x + 2) % 5) * 64 + z],
                    ));
                }
            }
            let prods = self.and(&pairs)?;
            for (state, chunk) in states.iter_mut().zip(prods.chunks_exact(1600)) {
                for (s, &v) in state.iter_mut().zip(chunk) {
                    *s = *s ^ v;
                }
                for (i, s) in state[..64].iter_mut().enumerate() {
                    if (rc >> i) & 1 != 0 {
                        *s = *s ^ ones;
                    }
                }
            }
        }
        Ok(())
    }

    pub fn permutation(&mut self, state: &mut Word) -> Result<(), Error> {
        self.permutations(&mut [state.as_mut_slice()])
    }
}

pub(crate) struct Sponge {
    pub(crate) state: Word,
    pub(crate) pos: usize,
}
impl Drop for Sponge {
    fn drop(&mut self) {
        for b in &mut self.state {
            ct_zeroize_u64s(&mut b.0);
        }
    }
}
impl Sponge {
    pub fn new<T: Transport>(e: &Engine<T>) -> Self {
        Self {
            state: vec![e.constant(0); 1600],
            pos: 0,
        }
    }
    pub fn absorb<T: Transport>(&mut self, e: &mut Engine<T>, input: &[Bit]) -> Result<(), Error> {
        for &b in input {
            self.state[self.pos] = self.state[self.pos] ^ b;
            self.pos += 1;
            if self.pos == 1088 {
                e.permutation(&mut self.state)?;
                self.pos = 0;
            }
        }
        Ok(())
    }
    pub fn public<T: Transport>(&mut self, e: &mut Engine<T>, bytes: &[u8]) -> Result<(), Error> {
        let bits = public_bytes(e, bytes);
        self.absorb(e, &bits)
    }
    pub fn pad_only<T: Transport>(&mut self, e: &Engine<T>, suffix: u8) {
        for i in 0..8 {
            if (suffix >> i) & 1 != 0 {
                self.state[self.pos + i] = self.state[self.pos + i] ^ e.constant(u64::MAX);
            }
        }
        self.state[1087] = self.state[1087] ^ e.constant(u64::MAX);
        self.pos = 0;
    }
    #[cfg(test)]
    pub fn finalize<T: Transport>(&mut self, e: &mut Engine<T>, suffix: u8) -> Result<(), Error> {
        self.pad_only(e, suffix);
        e.permutation(&mut self.state)?;
        Ok(())
    }
    #[cfg(test)]
    pub fn squeeze<T: Transport>(
        &mut self,
        e: &mut Engine<T>,
        count: usize,
    ) -> Result<Word, Error> {
        let mut out = Vec::with_capacity(count);
        for _ in 0..count {
            if self.pos == 1088 {
                e.permutation(&mut self.state)?;
                self.pos = 0;
            }
            out.push(self.state[self.pos]);
            self.pos += 1;
        }
        Ok(out)
    }
    /// Initialize a shared `cSHAKE256` sponge using the public pre-permuted `init_cshake256`
    /// state directly (`0` MPC rounds for the public customization block).
    pub fn cshake_public<T: Transport>(e: &Engine<T>, customization: &[u8]) -> Self {
        let native = init_cshake256(b"", customization);
        // Mirror the exact public 136-byte block permutation in constant shares.
        let mut s = Self::new(e);
        let _ = native;
        fn left(x: usize) -> Vec<u8> {
            let bytes = x.to_be_bytes();
            let i = bytes
                .iter()
                .position(|&x| x != 0)
                .unwrap_or(bytes.len() - 1);
            let mut out = vec![(bytes.len() - i) as u8];
            out.extend_from_slice(&bytes[i..]);
            out
        }
        let mut prefix = left(136);
        prefix.extend(left(0));
        prefix.extend(left(customization.len() * 8));
        prefix.extend_from_slice(customization);
        prefix.resize(prefix.len().div_ceil(136) * 136, 0);

        let mut st = [0u64; 25];
        for block in prefix.chunks_exact(136) {
            for (lane, chunk) in st[..17].iter_mut().zip(block.chunks_exact(8)) {
                let mut buf = [0u8; 8];
                buf.copy_from_slice(chunk);
                *lane ^= u64::from_le_bytes(buf);
            }
            keccak_f1600(&mut st);
        }
        for (lane_idx, &w) in st.iter().enumerate() {
            for bit in 0..64 {
                s.state[lane_idx * 64 + bit] =
                    e.constant(if (w >> bit) & 1 != 0 { u64::MAX } else { 0 });
            }
        }
        s
    }
    #[cfg(test)]
    pub fn cshake<T: Transport>(e: &mut Engine<T>, customization: &[u8]) -> Result<Self, Error> {
        Ok(Self::cshake_public(e, customization))
    }
}

/// Squeeze `counts[i]` bits from each `sponges[i]` in lockstep, sharing one
/// `Engine::permutations` batch call per 1088-bit block across all sponges that need more output.
pub(crate) fn squeeze_sponges_lockstep<T: Transport>(
    e: &mut Engine<T>,
    sponges: &mut [Sponge],
    counts: &[usize],
) -> Result<Vec<Word>, Error> {
    let mut outs: Vec<Word> = counts.iter().map(|&c| Vec::with_capacity(c)).collect();
    loop {
        let mut need_perm = Vec::new();
        for (idx, (sp, &target)) in sponges.iter_mut().zip(counts).enumerate() {
            let rem = target - outs[idx].len();
            if rem == 0 {
                continue;
            }
            if sp.pos < 1088 {
                let take = (1088 - sp.pos).min(rem);
                outs[idx].extend_from_slice(&sp.state[sp.pos..sp.pos + take]);
                sp.pos += take;
            }
            if outs[idx].len() < target && sp.pos == 1088 {
                need_perm.push(idx);
            }
        }
        if need_perm.is_empty() {
            break;
        }
        let mut refs: Vec<&mut [Bit]> = Vec::with_capacity(need_perm.len());
        // Split borrows safely across `sponges` in index order.
        let mut cursor = 0usize;
        let mut rest: &mut [Sponge] = &mut *sponges;
        for &idx in &need_perm {
            let (_, after) = rest.split_at_mut(idx - cursor);
            let (first, tail) = after.split_first_mut().unwrap();
            first.pos = 0;
            refs.push(first.state.as_mut_slice());
            rest = tail;
            cursor = idx + 1;
        }
        e.permutations(&mut refs)?;
    }
    Ok(outs)
}

pub(crate) fn public_bytes<T: Transport>(e: &Engine<T>, bytes: &[u8]) -> Word {
    bytes
        .iter()
        .flat_map(|b| (0..8).map(move |i| e.constant(if (b >> i) & 1 != 0 { u64::MAX } else { 0 })))
        .collect()
}
pub(crate) fn lane_bytes(words: &[u64], lane: usize) -> Vec<u8> {
    words
        .chunks_exact(8)
        .map(|chunk| {
            chunk
                .iter()
                .enumerate()
                .fold(0, |v, (i, b)| v | (((b >> lane) & 1) as u8) << i)
        })
        .collect()
}
pub(crate) fn encode(out: &mut Word, value: &[Bit]) {
    out.extend_from_slice(value);
    out.resize(out.len().div_ceil(8) * 8, Bit::default());
}

impl<T: Transport> Engine<T> {
    pub fn fconstant(&self, value: Value) -> FieldWord {
        vec![
            [
                if self.party == 0 { value } else { [0; 4] },
                if (self.party + 1) % 3 == 0 {
                    value
                } else {
                    [0; 4]
                }
            ];
            64
        ]
    }
    pub fn fadd(&self, a: &FieldWord, b: &FieldWord, d: Domain) -> FieldWord {
        a.iter()
            .zip(b)
            .map(|(a, b)| core::array::from_fn(|j| d.add(a[j], b[j])))
            .collect()
    }
    pub fn fsub(&self, a: &FieldWord, b: &FieldWord, d: Domain) -> FieldWord {
        a.iter()
            .zip(b)
            .map(|(a, b)| core::array::from_fn(|j| d.sub(a[j], b[j])))
            .collect()
    }
    pub fn fscale(&self, a: &FieldWord, b: Value, d: Domain) -> FieldWord {
        a.iter().map(|a| a.map(|v| d.mul(v, b))).collect()
    }

    fn field_pad(s: &mut WordSponge136, d: Domain) -> Value {
        if d == Domain::Gold {
            loop {
                let w = s.squeeze_u64();
                if w < GOLDILOCKS_P {
                    return [w, 0, 0, 0];
                }
            }
        }
        loop {
            let mut words = [0u64; 4];
            s.squeeze_u64s(&mut words);
            if d == Domain::Ed {
                words[3] &= 0x7fff_ffff_ffff_ffff;
            }
            if d.canonical(words) {
                return words;
            }
        }
    }

    fn frandom(&mut self, d: Domain) -> FieldWord {
        (0..64)
            .map(|_| {
                [
                    Self::field_pad(&mut self.pads[0], d),
                    Self::field_pad(&mut self.pads[1], d),
                ]
            })
            .collect()
    }

    pub fn fmul_many(
        &mut self,
        pairs: &[(&FieldWord, &FieldWord)],
        d: Domain,
    ) -> Result<Vec<FieldWord>, Error> {
        if self.poisoned {
            return Err(Error::MultiplicationCheck);
        }
        if pairs.is_empty() {
            return Ok(Vec::new());
        }
        let k = pairs.len();
        let mut own_flat = Vec::with_capacity(k * 256);
        let mut own_words: Vec<Vec<Value>> = Vec::with_capacity(k);
        for (pair_idx, &(a, b)) in pairs.iter().enumerate() {
            let masks = self.frandom(d);
            let mut word_own = Vec::with_capacity(64);
            #[cfg(test)]
            let inject_lane = match self.fault {
                Some(FaultInjection::FieldMul {
                    domain,
                    ref mut call_countdown,
                    lane,
                }) if domain == d && pair_idx == 0 => {
                    if *call_countdown == 0 {
                        let target_lane = lane & 63;
                        self.fault = None;
                        Some(target_lane)
                    } else {
                        *call_countdown -= 1;
                        None
                    }
                }
                _ => None,
            };
            #[cfg(not(test))]
            let _ = pair_idx;
            for (lane_idx, ((al, bl), r)) in a.iter().zip(b).zip(masks).enumerate() {
                #[cfg(not(test))]
                let _ = lane_idx;
                let base_prod = d.add(
                    d.add(d.mul(al[0], d.add(bl[0], bl[1])), d.mul(al[1], bl[0])),
                    d.sub(r[0], r[1]),
                );
                #[cfg(test)]
                let prod = if inject_lane == Some(lane_idx) {
                    d.add(base_prod, [1, 0, 0, 0])
                } else {
                    base_prod
                };
                #[cfg(not(test))]
                let prod = base_prod;
                own_flat.extend_from_slice(&prod);
                word_own.push(prod);
            }
            own_words.push(word_own);
        }
        let (_, next_raw) = self.raw_share_owned(own_flat)?;
        let mut results = Vec::with_capacity(k);
        for (word_own, word_next) in own_words.into_iter().zip(next_raw.chunks_exact(256)) {
            let mut fw = Vec::with_capacity(64);
            for (av, b_slice) in word_own.into_iter().zip(word_next.chunks_exact(4)) {
                let bv: Value = [b_slice[0], b_slice[1], b_slice[2], b_slice[3]];
                if !d.canonical(bv) {
                    self.poisoned = true;
                    return Err(Error::MultiplicationCheck);
                }
                fw.push([av, bv]);
            }
            results.push(fw);
        }
        let queue = match d {
            Domain::Secp => &mut self.pending_secp,
            Domain::Ed => &mut self.pending_ed,
            Domain::Gold => &mut self.pending_gold,
            Domain::Bit => return Err(Error::InvalidConfiguration),
        };
        for (&(a, b), z) in pairs.iter().zip(&results) {
            queue.push((a.clone(), b.clone(), z.clone()));
        }
        if queue.len() >= MAX_PENDING_FIELD_WORDS {
            self.flush_pending_domain(d)?;
        }
        Ok(results)
    }

    pub fn fmul(&mut self, a: &FieldWord, b: &FieldWord, d: Domain) -> Result<FieldWord, Error> {
        Ok(self.fmul_many(&[(a, b)], d)?.pop().unwrap())
    }

    fn fopen_many(&mut self, words: &[FieldWord], d: Domain) -> Result<Vec<Vec<Value>>, Error> {
        if words.is_empty() {
            return Ok(Vec::new());
        }
        self.verify_all_pending()?;
        let k = words.len();
        let mut payload = Vec::with_capacity(k * 512);
        for w in words {
            for pair in w {
                payload.extend_from_slice(&pair[0]);
                payload.extend_from_slice(&pair[1]);
            }
        }
        let received = self.raw_exchange([payload.clone(), payload])?;
        if received.iter().any(|v| v.len() != k * 512) {
            self.poisoned = true;
            return Err(Error::InvalidConfiguration);
        }
        let mut all_out = Vec::with_capacity(k);
        for (w_idx, w) in words.iter().enumerate() {
            let base_w = w_idx * 512;
            let mut out = Vec::with_capacity(64);
            for (lane, a) in w.iter().enumerate() {
                let off = base_w + 8 * lane;
                let prev: [Value; 2] = core::array::from_fn(|j| {
                    let s = &received[0][off + 4 * j..off + 4 * j + 4];
                    [s[0], s[1], s[2], s[3]]
                });
                let next: [Value; 2] = core::array::from_fn(|j| {
                    let s = &received[1][off + 4 * j..off + 4 * j + 4];
                    [s[0], s[1], s[2], s[3]]
                });
                if prev[1] != a[0] {
                    self.poisoned = true;
                    return Err(Error::Disagreement((self.party + 2) % 3));
                }
                if next[0] != a[1] || prev[0] != next[1] || !d.canonical(prev[0]) {
                    self.poisoned = true;
                    return Err(Error::Disagreement((self.party + 1) % 3));
                }
                out.push(d.add(d.add(a[0], a[1]), prev[0]));
            }
            all_out.push(out);
        }
        Ok(all_out)
    }

    /// Binary encoding of additive sharings without reconstructing their sums.
    fn component_bits_many(&mut self, words: &[FieldWord], d: Domain) -> Result<Vec<Word>, Error> {
        let width = d.width();
        let make_owner = |owner: usize| -> Vec<Word> {
            words
                .iter()
                .map(|a| {
                    (0..width)
                        .map(|bit| {
                            Bit(core::array::from_fn(|j| {
                                if (self.party + j) % 3 != owner {
                                    0
                                } else {
                                    a.iter().enumerate().fold(0, |mask, (lane, value)| {
                                        mask | (((value[j][bit / 64] >> (bit % 64)) & 1) << lane)
                                    })
                                }
                            }))
                        })
                        .collect()
                })
                .collect()
        };
        let p0 = make_owner(0);
        let p1 = make_owner(1);
        let p2 = make_owner(2);
        let sum01 = self.field_add_many(&p0, &p1, d)?;
        self.field_add_many(&sum01, &p2, d)
    }

    /// Convert binary to additive sharing with fresh uniformly random field masks.
    /// All pending multiplications are actively verified before `v - r` opens.
    pub fn bits_to_field_many(
        &mut self,
        words: &[Word],
        d: Domain,
    ) -> Result<Vec<FieldWord>, Error> {
        if words.is_empty() {
            return Ok(Vec::new());
        }
        let width = d.width();
        let mut all_out = Vec::with_capacity(words.len());
        for chunk in words.chunks(CONVERT_CHUNK_WORDS) {
            let mut r_list: Vec<FieldWord> = (0..chunk.len()).map(|_| self.frandom(d)).collect();
            let rb_list = self.component_bits_many(&r_list, d)?;
            let deltas = self.field_sub_many(chunk, &rb_list, d)?;
            let mut flat = Vec::with_capacity(chunk.len() * width);
            for dw in &deltas {
                flat.extend_from_slice(dw);
            }
            let opened = self.open(&flat)?;
            for (r_fw, op_slice) in r_list.iter_mut().zip(opened.chunks_exact(width)) {
                for (lane, pair) in r_fw.iter_mut().enumerate() {
                    let mut value = [0u64; 4];
                    for (bit, &word) in op_slice.iter().enumerate() {
                        value[bit / 64] |= ((word >> lane) & 1) << (bit % 64);
                    }
                    for (j, part) in pair.iter_mut().enumerate() {
                        if (self.party + j) % 3 == 0 {
                            *part = d.add(*part, value);
                        }
                    }
                }
            }
            all_out.extend(r_list);
        }
        Ok(all_out)
    }

    #[cfg(test)]
    pub fn bits_to_field(&mut self, v: &[Bit], d: Domain) -> Result<FieldWord, Error> {
        Ok(self.bits_to_field_many(&[v.to_vec()], d)?.pop().unwrap())
    }

    /// Convert additive to binary sharing by opening only fresh masked differences
    /// after actively verifying all pending Boolean and prime-field multiplications.
    pub fn field_to_bits_many(
        &mut self,
        words: &[&FieldWord],
        d: Domain,
    ) -> Result<Vec<Word>, Error> {
        if words.is_empty() {
            return Ok(Vec::new());
        }
        let mut all_out = Vec::with_capacity(words.len());
        for chunk in words.chunks(CONVERT_CHUNK_WORDS) {
            let mut r_list: Vec<FieldWord> = (0..chunk.len()).map(|_| self.frandom(d)).collect();
            let deltas: Vec<FieldWord> = chunk
                .iter()
                .zip(&r_list)
                .map(|(v, r)| self.fsub(v, r, d))
                .collect();
            let opened_list = self.fopen_many(&deltas, d)?;
            for (r_fw, opened) in r_list.iter_mut().zip(&opened_list) {
                for (pair, &val) in r_fw.iter_mut().zip(opened) {
                    for (j, part) in pair.iter_mut().enumerate() {
                        if (self.party + j) % 3 == 0 {
                            *part = d.add(*part, val);
                        }
                    }
                }
            }
            all_out.extend(self.component_bits_many(&r_list, d)?);
        }
        Ok(all_out)
    }

    #[cfg(test)]
    pub fn field_to_bits(&mut self, v: &FieldWord, d: Domain) -> Result<Word, Error> {
        Ok(self.field_to_bits_many(&[v], d)?.pop().unwrap())
    }

    pub fn lift_bits_many(&mut self, bits: &[Bit], d: Domain) -> Result<Vec<FieldWord>, Error> {
        if bits.is_empty() {
            return Ok(Vec::new());
        }
        let make_owner = |owner: usize| -> Vec<FieldWord> {
            bits.iter()
                .map(|&bit| {
                    (0..64)
                        .map(|lane| {
                            core::array::from_fn(|j| {
                                if (self.party + j) % 3 == owner {
                                    [(bit.0[j] >> lane) & 1, 0, 0, 0]
                                } else {
                                    [0; 4]
                                }
                            })
                        })
                        .collect()
                })
                .collect()
        };
        let p0 = make_owner(0);
        let p1 = make_owner(1);
        let p2 = make_owner(2);
        let pairs01: Vec<_> = p0.iter().zip(&p1).collect();
        let ab01 = self.fmul_many(&pairs01, d)?;
        let firsts: Vec<FieldWord> = p0
            .iter()
            .zip(&p1)
            .zip(&ab01)
            .map(|((a, b), ab)| {
                let sum = self.fadd(a, b, d);
                self.fsub(&sum, &self.fscale(ab, [2, 0, 0, 0], d), d)
            })
            .collect();
        let pairs12: Vec<_> = firsts.iter().zip(&p2).collect();
        let ab12 = self.fmul_many(&pairs12, d)?;
        Ok(firsts
            .iter()
            .zip(&p2)
            .zip(&ab12)
            .map(|((f, c), ab)| {
                let sum = self.fadd(f, c, d);
                self.fsub(&sum, &self.fscale(ab, [2, 0, 0, 0], d), d)
            })
            .collect())
    }

    pub fn finverse(&mut self, a: &FieldWord, d: Domain) -> Result<FieldWord, Error> {
        let exponent = crate::scalar::sub(d.modulus(), [2, 0, 0, 0], d.modulus());
        let mut out = self.fconstant([1, 0, 0, 0]);
        for i in (0..d.width()).rev() {
            out = self.fmul(&out, &out, d)?;
            if (exponent[i / 64] >> (i % 64)) & 1 != 0 {
                out = self.fmul(&out, a, d)?;
            }
        }
        Ok(out)
    }
}

#[cfg(test)]
pub(crate) mod tests {
    extern crate std;
    use super::*;
    use qsag_asm::gf2_128_mul_portable;
    use std::sync::{
        Arc,
        atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering},
        mpsc::{self, Receiver, Sender},
    };

    pub struct Network {
        trace: Option<Arc<Trace>>,
        stream: usize,
        children: Vec<Network>,
        sends: [Sender<Envelope>; 2],
        receives: [Receiver<Envelope>; 2],
    }

    struct Trace {
        party_id: AtomicUsize,
        msg_count: AtomicU64,
        word_count: AtomicU64,
        digest: AtomicU64,
        candidates: std::sync::Mutex<Vec<[u8; 32]>>,
        private_view: std::sync::Mutex<Vec<u8>>,
    }
    impl Default for Trace {
        fn default() -> Self {
            Self {
                party_id: AtomicUsize::new(usize::MAX),
                msg_count: AtomicU64::new(0),
                word_count: AtomicU64::new(0),
                digest: AtomicU64::new(0),
                candidates: std::sync::Mutex::new(Vec::new()),
                private_view: std::sync::Mutex::new(Vec::new()),
            }
        }
    }
    pub(crate) struct AuditHandle(Arc<Trace>);
    impl AuditHandle {
        pub fn candidates(&self) -> Vec<[u8; 32]> {
            self.0.candidates.lock().unwrap().clone()
        }
    }
    impl Trace {
        fn new(_party: usize) -> Self {
            Self::default()
        }
        fn record(&self, stream: usize, direction: u8, m: &Envelope) {
            let expected_party = self.party_id.load(Ordering::Acquire);
            assert_ne!(expected_party, usize::MAX);
            assert_eq!(
                expected_party,
                if direction == 0 {
                    m.sender
                } else {
                    m.recipient
                }
            );
            let mut local_digest =
                (stream as u64).rotate_left(7) ^ u64::from(direction) ^ m.sequence;
            for &word in &m.payload {
                local_digest ^= word;
            }
            for &byte in &m.tag {
                local_digest = local_digest.rotate_left(1) ^ u64::from(byte);
            }
            self.msg_count.fetch_add(1, Ordering::Relaxed);
            self.word_count
                .fetch_add(m.payload.len() as u64, Ordering::Relaxed);
            self.digest.fetch_xor(local_digest, Ordering::Relaxed);
        }
        fn stats(&self) -> (u64, u64) {
            (
                self.msg_count.load(Ordering::Acquire),
                self.word_count.load(Ordering::Acquire),
            )
        }
    }
    impl Network {
        fn record(&self, direction: u8, m: &Envelope) {
            if let Some(trace) = &self.trace {
                trace.record(self.stream, direction, m);
            }
        }
    }
    impl Transport for Network {
        fn audit_transcript(&self) -> Option<(u64, u64)> {
            self.trace.as_ref().map(|t| t.stats())
        }
        fn audit_candidates(&self, candidates: Vec<[u8; 32]>) {
            self.trace
                .as_ref()
                .unwrap()
                .candidates
                .lock()
                .unwrap()
                .extend(candidates);
        }
        fn audit_private_state(
            &self,
            party: usize,
            session: &[u8; 32],
            witness: &[u8; 32],
            entropy: &[u8; 32],
            keys: &[[u8; 32]; 2],
            statement: &crate::zk_engine::MigrationStatement,
        ) {
            if let Some(trace) = &self.trace {
                let mut private = trace.private_view.lock().unwrap();
                assert!(private.is_empty());
                private.push(party as u8);
                for bytes in [session, witness, entropy, &keys[0], &keys[1]] {
                    private.extend_from_slice(bytes);
                }
                private.extend_from_slice(&statement.to_transcript_bytes());
                trace.party_id.store(party, Ordering::Release);
            }
        }
        fn fork(&mut self, _batch: usize) -> Option<Self> {
            if self.children.is_empty() {
                None
            } else {
                Some(self.children.remove(0))
            }
        }
        fn exchange(&mut self, out: [Envelope; 2]) -> Result<[Envelope; 2], Error> {
            for (s, m) in self.sends.iter().zip(out) {
                self.record(0, &m);
                s.send(m).map_err(|_| Error::Transport)?;
            }
            let messages = [
                self.receives[0].recv().map_err(|_| Error::Transport)?,
                self.receives[1].recv().map_err(|_| Error::Transport)?,
            ];
            for m in &messages {
                self.record(1, m);
            }
            Ok(messages)
        }
    }
    pub fn networks() -> [Network; 3] {
        let mut roots = raw_networks();
        for _ in 0..crate::zk_engine::MIT_REPETITIONS.div_ceil(64) {
            for (root, child) in roots.iter_mut().zip(raw_networks()) {
                root.children.push(child);
            }
        }
        roots
    }
    fn raw_networks() -> [Network; 3] {
        let mut sends: Vec<Vec<Option<Sender<Envelope>>>> =
            (0..3).map(|_| (0..2).map(|_| None).collect()).collect();
        let mut receives: Vec<Vec<Option<Receiver<Envelope>>>> =
            (0..3).map(|_| (0..2).map(|_| None).collect()).collect();
        for (p, row) in sends.iter_mut().enumerate() {
            for (i, entry) in row.iter_mut().enumerate() {
                let (s, r) = mpsc::channel();
                *entry = Some(s);
                let peer = (p + if i == 0 { 2 } else { 1 }) % 3;
                receives[peer][1 - i] = Some(r);
            }
        }
        core::array::from_fn(|p| Network {
            trace: None,
            stream: 0,
            children: Vec::new(),
            sends: core::array::from_fn(|i| sends[p][i].take().unwrap()),
            receives: core::array::from_fn(|i| receives[p][i].take().unwrap()),
        })
    }
    pub fn keys(p: usize) -> [[u8; 32]; 2] {
        [[((p + 2) % 3 + 1) as u8; 32], [(p + 1) as u8; 32]]
    }
    pub fn run<F: Fn(usize, Network) + Sync>(f: F) {
        std::thread::scope(|scope| {
            for (p, n) in networks().into_iter().enumerate() {
                let f = &f;
                scope.spawn(move || f(p, n));
            }
        });
    }
    pub fn audited_networks() -> [(Network, AuditHandle); 3] {
        let mut networks = networks().map(Some);
        core::array::from_fn(|p| {
            let mut network = networks[p].take().unwrap();
            let trace = Arc::new(Trace::new(p));
            for (batch, child) in network.children.iter_mut().enumerate() {
                child.trace = Some(trace.clone());
                child.stream = batch + 1;
            }
            network.trace = Some(trace.clone());
            (network, AuditHandle(trace))
        })
    }

    pub(crate) fn valid_mac_tag(key: &[u8; 32], session: &[u8; 32], m: &Envelope) -> [u8; 32] {
        let bytes: Vec<u8> = m.payload.iter().flat_map(|w| w.to_le_bytes()).collect();
        cshake256_framed_32(
            b"QSAG.OUTER.MESSAGE.V1",
            &[
                key,
                session,
                &[m.sender as u8, m.recipient as u8],
                &m.sequence.to_le_bytes(),
                &bytes,
            ],
        )
    }

    #[test]
    fn zero_alloc_mac_tag_and_word_sponge_match_reference_across_all_alignments() {
        let session = [0x42u8; 32];
        run(|p, n| {
            let e = Engine::new(p, session, keys(p), n).unwrap();
            if p == 0 {
                for len in 0..=300usize {
                    let payload: Vec<u64> = (0..len)
                        .map(|i| 0x9e37_79b9_7f4a_7c15u64.wrapping_mul(i as u64 + 1))
                        .collect();
                    let seq = 0xfedc_ba98_7654_3210u64.wrapping_add(len as u64);
                    let fast = e.tag(0, 0, 2, seq, &payload);
                    let dummy = Envelope {
                        sender: 0,
                        recipient: 2,
                        sequence: seq,
                        payload,
                        tag: [0; 32],
                    };
                    let reference = valid_mac_tag(&keys(0)[0], &session, &dummy);
                    assert_eq!(fast, reference, "mismatch at payload len {len}");
                }
            }
        });
    }

    #[test]
    fn bitsliced_wiedemann_tower_and_gold_ext3_match_field_axioms() {
        let backend = detect_backend();
        let mut xof = WordSponge136::from_shake_seed(&[0x77; 32]);
        let mut a = [0u64; 128];
        let mut b = [0u64; 128];
        xof.squeeze_u64s(&mut a);
        xof.squeeze_u64s(&mut b);

        // 1. Verify `poly128_mul_x` and `poly128_mul_x16` match `gf2_128_mul_portable`.
        for _ in 0..64 {
            let elem_u = xof.squeeze_u128();
            let elem = u128_to_gf128(elem_u);
            assert_eq!(
                u128_to_gf128(poly128_mul_x(elem_u)),
                gf2_128_mul_portable(elem, [2, 0])
            );
            assert_eq!(
                u128_to_gf128(poly128_mul_x16(elem_u)),
                gf2_128_mul_portable(elem, [1u64 << 16, 0])
            );
        }

        // 2. Verify `transpose_pair_bs128_to_lanes` and `transpose_pair_lanes_to_bs128` round-trip.
        let mut scratch = BitCheckScratch::new_boxed();
        let mut lanes_a = [[0u64; 2]; 64];
        let mut lanes_b = [[0u64; 2]; 64];
        transpose_pair_bs128_to_lanes(
            &a,
            &b,
            &mut lanes_a,
            &mut lanes_b,
            &mut scratch.tr_rows,
            backend,
        );
        for lane in 0..64 {
            let mut al = 0u128;
            let mut bl = 0u128;
            for bit in 0..128 {
                al |= (((a[bit] >> lane) & 1) as u128) << bit;
                bl |= (((b[bit] >> lane) & 1) as u128) << bit;
            }
            assert_eq!(lanes_a[lane], u128_to_gf128(al), "lane_a {lane}");
            assert_eq!(lanes_b[lane], u128_to_gf128(bl), "lane_b {lane}");
        }
        let mut rt_a = [0u64; 128];
        let mut rt_b = [0u64; 128];
        transpose_pair_lanes_to_bs128(
            &lanes_a,
            &lanes_b,
            &mut rt_a,
            &mut rt_b,
            &mut scratch.tr_rows,
            backend,
        );
        assert_eq!(rt_a, a);
        assert_eq!(rt_b, b);

        // 3. Verify `gf128_dot_acc` (`gf2_128_mul_acc_batch_with_backend`) matches `gf2_128_mul_portable`
        //    across full 64-lane, 15-element, and 7-element Arity-8 slices.
        for len in [7usize, 15, 64] {
            let mut acc_fast = [0u64; 2];
            gf128_dot_acc(&mut acc_fast, &lanes_a[..len], &lanes_b[..len], backend);
            let mut acc_ref = [0u64; 2];
            for (&la, &lb) in lanes_a[..len].iter().zip(&lanes_b[..len]) {
                acc_ref = xor_gf128(acc_ref, gf2_128_mul_portable(la, lb));
            }
            assert_eq!(acc_fast, acc_ref, "gf128_dot_acc mismatch at len {len}");
        }

        // 4. Verify 4-block `Bs256` byte evaluation, `xor_mul_bs256_by_public`, and
        //    `bs256_col_mul_x_pow16` match `gf2_128_mul_portable` across all 256 block-lanes.
        let cols: [u128; 16] = core::array::from_fn(|_| xof.squeeze_u128());
        let row_masks = transpose_cols16_to_u16(&cols);
        let words16: [BitPlane256; 16] =
            core::array::from_fn(|u| [a[u], b[u], a[16 + u], b[16 + u]]);
        build_byte_tabs_bs256(&words16, &mut scratch.tabs8);
        eval_public_matrix_128x16_bs256(&row_masks, &scratch.tabs8, &mut scratch.bs256_buf);
        let mut quad_out = [[[0u64; 2]; 64]; 4];
        transpose_bs256_to_quad_lanes(
            &scratch.bs256_buf,
            &mut quad_out,
            &mut scratch.tr_rows,
            backend,
        );
        for (sub, ql) in quad_out.iter().enumerate() {
            for (lane, &got) in ql.iter().enumerate() {
                let mut expected = 0u128;
                for (u, &col) in cols.iter().enumerate() {
                    if (words16[u][sub] >> lane) & 1 != 0 {
                        expected ^= col;
                    }
                }
                assert_eq!(
                    got,
                    u128_to_gf128(expected),
                    "bs256 16-gate eval sub {sub} lane {lane}"
                );
            }
        }

        let pub_c = u128_to_gf128(xof.squeeze_u128());
        let pub_masks8 = build_public_mul_masks_bs256(pub_c);
        let src_bs = *scratch.bs256_buf;
        let mut prod_bs = [[0u64; 4]; 128];
        xor_mul_bs256_by_public(&src_bs, &pub_masks8, &mut scratch.tabs8, &mut prod_bs);
        let mut prod_quad = [[[0u64; 2]; 64]; 4];
        transpose_bs256_to_quad_lanes(&prod_bs, &mut prod_quad, &mut scratch.tr_rows, backend);
        for sub in 0..4 {
            for lane in 0..64 {
                assert_eq!(
                    prod_quad[sub][lane],
                    gf2_128_mul_portable(quad_out[sub][lane], pub_c),
                    "xor_mul_bs256_by_public sub {sub} lane {lane}"
                );
            }
        }

        for blocks in 0..8 {
            let mut shifted_bs = src_bs;
            for sub in 0..4 {
                bs256_col_mul_x_pow16(&mut shifted_bs, sub, blocks);
            }
            let mut shifted_quad = [[[0u64; 2]; 64]; 4];
            transpose_bs256_to_quad_lanes(
                &shifted_bs,
                &mut shifted_quad,
                &mut scratch.tr_rows,
                backend,
            );
            let factor = u128_to_gf128(1u128 << (16 * blocks));
            for sub in 0..4 {
                for lane in 0..64 {
                    assert_eq!(
                        shifted_quad[sub][lane],
                        gf2_128_mul_portable(quad_out[sub][lane], factor),
                        "shift {blocks} sub {sub} lane {lane}"
                    );
                }
            }
        }

        // 5. Verify `BitCheckScratch::wipe_all` deterministically zeroizes up to `hwm`.
        scratch.prepare(4);
        scratch.hwm_step0 = 64;
        scratch.step0_buf[0] = [0x1111_2222, 0x3333_4444];
        scratch.a_bs[0][0][0][0] = [0xdead_beef, 0xcafe_babe, 1, 2];
        scratch.a_bs[0][0].truncate(1);
        scratch.c_claim[0][0] = lanes_a;
        scratch.wipe_all();
        assert!(scratch.a_bs[0][0].is_empty());
        assert_eq!(scratch.hwm_bs, 0);
        assert_eq!(scratch.hwm_step0, 0);
        assert_eq!(scratch.step0_buf[0], [0, 0]);
        assert!(scratch.c_claim[0][0].iter().all(|&w| w == [0, 0]));
        assert!(scratch.tabs8.iter().flatten().all(|&w| w == [0, 0, 0, 0]));

        // 6. Verify `u^3 - 7` is irreducible over Goldilocks: `3 | (p - 1)` and `7^((p-1)/3) != 1`.
        let exp = (GOLDILOCKS_P - 1) / 3;
        assert_eq!(exp * 3, GOLDILOCKS_P - 1);
        let mut base = 7u64;
        let mut acc = 1u64;
        let mut e_rem = exp;
        while e_rem > 0 {
            if e_rem & 1 != 0 {
                acc = gl_mul(acc, base);
            }
            base = gl_mul(base, base);
            e_rem >>= 1;
        }
        assert_ne!(acc, 1, "7 must be a cubic non-residue mod Goldilocks p");

        // Verify associativity & distributivity of `GoldExt3`.
        let x = squeeze_g3_challenge(&mut xof);
        let y = squeeze_g3_challenge(&mut xof);
        let z = squeeze_g3_challenge(&mut xof);
        assert_eq!(g3_mul(g3_mul(x, y), z), g3_mul(x, g3_mul(y, z)));
        assert_eq!(g3_mul(x, g3_add(y, z)), g3_add(g3_mul(x, y), g3_mul(x, z)));
    }

    #[test]
    fn replicated_arithmetic_and_shared_sponge_match_native() {
        run(|p, n| {
            let mut e = Engine::new(p, [27; 32], keys(p), n).unwrap();
            let secret = e
                .share(&[if p == 0 {
                    0x5555
                } else if p == 1 {
                    0x3333
                } else {
                    0xf0f0
                }])
                .unwrap();
            let square = e.and(&[(secret[0], secret[0])]).unwrap();
            assert_eq!(e.open(&square).unwrap(), vec![0x5555 ^ 0x3333 ^ 0xf0f0]);
            // Exercise both halves of a super-block, partial 16-gate blocks,
            // odd quad folding, and the maximum flush boundary with varied lanes.
            for len in [15, 16, 17, 63, 64, 65, 127, 128, 129, 193, MAX_PENDING_BITS + 1] {
                let xs: Vec<_> = (0..len).map(|i| {
                    (i as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15).rotate_left(p as u32 * 7)
                }).collect();
                let ys: Vec<_> = xs.iter().map(|x| x.rotate_left(23) ^ 0xa55a_f00f_1234_5678).collect();
                let x = e.share(&xs).unwrap();
                let y = e.share(&ys).unwrap();
                let pairs: Vec<_> = x.into_iter().zip(y).collect();
                let z = e.and(&pairs).unwrap();
                let opened = e.open(&z).unwrap();
                for (i, got) in opened.into_iter().enumerate() {
                    let mut clear_x = 0;
                    let mut clear_y = 0;
                    for party in 0..3 {
                        let x = (i as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15).rotate_left(party * 7);
                        clear_x ^= x;
                        clear_y ^= x.rotate_left(23) ^ 0xa55a_f00f_1234_5678;
                    }
                    assert_eq!(got, clear_x & clear_y, "length {len}, gate {i}");
                }
            }
            for d in [Domain::Gold, Domain::Secp, Domain::Ed] {
                let a = d.sub(d.modulus(), [2, 0, 0, 0]);
                let b = [0xfedc_ba98_7654_3211, 0, 0, 0];
                let aa = e.number(a, d.width());
                let bb = e.number(b, d.width());
                let scale = d.sub(d.modulus(), [1, 0, 0, 0]);
                for operation in 0..4 {
                    let out = match operation {
                        0 => e.field_add(&aa, &bb, d),
                        1 => e.field_sub(&aa, &bb, d),
                        2 => e.field_mul(&aa, &bb, d),
                        _ => e.field_scale(&aa, scale, d),
                    }
                    .unwrap();
                    let expected = match operation {
                        0 => d.add(a, b),
                        1 => d.sub(a, b),
                        2 => d.mul(a, b),
                        _ => d.mul(a, scale),
                    };
                    let clear = e.open(&out).unwrap();
                    for (i, &bit) in clear.iter().enumerate() {
                        assert_eq!(
                            bit,
                            if (expected[i / 64] >> (i % 64)) & 1 != 0 {
                                u64::MAX
                            } else {
                                0
                            },
                            "domain {d:?}, operation {operation}, bit {i}"
                        );
                    }
                }
            }
            let mut s = Sponge::cshake(&mut e, b"test").unwrap();
            s.public(&mut e, &1u64.to_le_bytes()).unwrap();
            s.public(&mut e, &3u64.to_le_bytes()).unwrap();
            s.public(&mut e, b"abc").unwrap();
            s.finalize(&mut e, 4).unwrap();
            let hash = s.squeeze(&mut e, 256).unwrap();
            assert_eq!(
                lane_bytes(&e.open(&hash).unwrap(), 0),
                cshake256_framed_32(b"test", &[b"abc"])
            );
        });
    }

    #[test]
    fn arithmetic_matches_native_over_independent_lanes() {
        run(|p, n| {
            let mut e = Engine::new(p, [28; 32], keys(p), n).unwrap();
            for d in [Domain::Gold, Domain::Secp, Domain::Ed] {
                let values: Vec<[Value; 2]> = (0..64u8)
                    .map(|lane| {
                        core::array::from_fn(|side| {
                            let bytes =
                                cshake256_framed_32(b"OUTER.FIELD.TEST", &[&[lane, side as u8]]);
                            let mut value = crate::scalar::decode(&bytes);
                            if d == Domain::Gold {
                                value = [value[0] >> 1, 0, 0, 0];
                            } else {
                                value[3] >>= 2;
                            }
                            value
                        })
                    })
                    .collect();
                let operands: [Word; 2] = core::array::from_fn(|side| {
                    (0..d.width())
                        .map(|bit| {
                            e.constant(values.iter().enumerate().fold(0, |mask, (lane, v)| {
                                mask | (((v[side][bit / 64] >> (bit % 64)) & 1) << lane)
                            }))
                        })
                        .collect()
                });
                for operation in 0..4 {
                    let out = match operation {
                        0 => e.field_add(&operands[0], &operands[1], d),
                        1 => e.field_sub(&operands[0], &operands[1], d),
                        2 => e.field_mul(&operands[0], &operands[1], d),
                        _ => e.field_scale(&operands[0], [27, 0, 0, 0], d),
                    }
                    .unwrap();
                    let clear = e.open(&out).unwrap();
                    for (lane, v) in values.iter().enumerate() {
                        let expected = match operation {
                            0 => d.add(v[0], v[1]),
                            1 => d.sub(v[0], v[1]),
                            2 => d.mul(v[0], v[1]),
                            _ => d.mul(v[0], [27, 0, 0, 0]),
                        };
                        for (bit, &word) in clear.iter().enumerate() {
                            assert_eq!((word >> lane) & 1, (expected[bit / 64] >> (bit % 64)) & 1);
                        }
                    }
                }
            }
        });
    }

    #[test]
    fn masked_field_conversions_and_products_match_all_lanes() {
        run(|p, n| {
            let mut e = Engine::new(p, [61; 32], keys(p), n).unwrap();
            for d in [Domain::Gold, Domain::Secp, Domain::Ed] {
                let values: Vec<[Value; 2]> = (0..64u8)
                    .map(|lane| {
                        core::array::from_fn(|side| {
                            let mut value = crate::scalar::decode(&cshake256_framed_32(
                                b"OUTER.CONVERT.TEST",
                                &[&[lane, side as u8]],
                            ));
                            if d == Domain::Gold {
                                value = [value[0] >> 1, 0, 0, 0];
                            } else {
                                value[3] >>= 2;
                            }
                            value
                        })
                    })
                    .collect();
                let bits: [Word; 2] = core::array::from_fn(|side| {
                    (0..d.width())
                        .map(|bit| {
                            e.constant(values.iter().enumerate().fold(0, |v, (lane, x)| {
                                v | (((x[side][bit / 64] >> (bit % 64)) & 1) << lane)
                            }))
                        })
                        .collect()
                });
                let a = e.bits_to_field(&bits[0], d).unwrap();
                let b = e.bits_to_field(&bits[1], d).unwrap();
                let product = e.fmul(&a, &b, d).unwrap();
                let outputs = [
                    e.fadd(&a, &b, d),
                    e.fsub(&a, &b, d),
                    product,
                    e.fscale(&a, [27, 0, 0, 0], d),
                ];
                for (op, output) in outputs.iter().enumerate() {
                    let encoded = e.field_to_bits(output, d).unwrap();
                    let clear = e.open(&encoded).unwrap();
                    for (lane, x) in values.iter().enumerate() {
                        let expected = match op {
                            0 => d.add(x[0], x[1]),
                            1 => d.sub(x[0], x[1]),
                            2 => d.mul(x[0], x[1]),
                            _ => d.mul(x[0], [27, 0, 0, 0]),
                        };
                        for (bit, word) in clear.iter().enumerate() {
                            assert_eq!((word >> lane) & 1, (expected[bit / 64] >> (bit % 64)) & 1);
                        }
                    }
                }
            }
        });
    }

    #[test]
    fn authentication_rejects_altered_envelope() {
        struct Tamper(Network, bool);
        impl Transport for Tamper {
            fn exchange(&mut self, mut out: [Envelope; 2]) -> Result<[Envelope; 2], Error> {
                if self.1 {
                    out[0].tag[0] ^= 1;
                }
                self.0.exchange(out)
            }
        }
        run(|p, n| {
            let mut e = Engine::new(p, [7; 32], keys(p), Tamper(n, p == 0)).unwrap();
            let result = e.share(&[123]);
            if p == 2 {
                assert!(matches!(result, Err(Error::Authentication(0))));
            } else {
                assert!(result.is_ok());
            }
        });
    }

    #[test]
    fn active_one_bit_boolean_and_fault_with_valid_mac_aborts_before_any_wire_opens() {
        struct CorruptBoolReshare {
            inner: Network,
            is_corrupt: bool,
            target_seq: u64,
            key0: [u8; 32],
            session: [u8; 32],
            exchanges_after_check: Arc<AtomicUsize>,
            check_finished: Arc<AtomicBool>,
        }
        impl Transport for CorruptBoolReshare {
            fn exchange(&mut self, mut out: [Envelope; 2]) -> Result<[Envelope; 2], Error> {
                if self.check_finished.load(Ordering::SeqCst) {
                    self.exchanges_after_check.fetch_add(1, Ordering::SeqCst);
                }
                if self.is_corrupt && out[0].sequence == self.target_seq {
                    // Flip exactly 1 bit in lane 37 of gate 19 and sign a valid MAC.
                    out[0].payload[19] ^= 1u64 << 37;
                    out[0].tag = valid_mac_tag(&self.key0, &self.session, &out[0]);
                }
                self.inner.exchange(out)
            }
        }

        for corrupt_p in 0..3 {
            let session = [0x91 + corrupt_p as u8; 32];
            let after_check: [Arc<AtomicUsize>; 3] =
                core::array::from_fn(|_| Arc::new(AtomicUsize::new(0)));
            let flags: [Arc<AtomicBool>; 3] =
                core::array::from_fn(|_| Arc::new(AtomicBool::new(false)));

            run(|p, n| {
                let transport = CorruptBoolReshare {
                    inner: n,
                    is_corrupt: p == corrupt_p,
                    // seq 0 = share(x), seq 1 = share(y), seq 2 = `and` resharing!
                    target_seq: 2,
                    key0: keys(p)[0],
                    session,
                    exchanges_after_check: after_check[p].clone(),
                    check_finished: flags[p].clone(),
                };
                let mut e = Engine::new(p, session, keys(p), transport).unwrap();
                let x = e
                    .share(&vec![0xdead_beef_cafe_babeu64.wrapping_add(p as u64); 33])
                    .unwrap();
                let y = e
                    .share(&vec![
                        0x0123_4567_89ab_cdefu64.wrapping_mul(p as u64 + 3);
                        33
                    ])
                    .unwrap();
                let pairs: Vec<_> = x.iter().copied().zip(y.iter().copied()).collect();
                let z = e.and(&pairs).unwrap();

                // Attempt to open `z`: pre-open check must fail before `open_raw_bits(&z)` runs.
                let res = e.open(&z);
                flags[p].store(true, Ordering::SeqCst);
                if p != corrupt_p {
                    assert_eq!(
                        res,
                        Err(Error::MultiplicationCheck),
                        "honest custodian {p} must abort with MultiplicationCheck when {corrupt_p} cheats"
                    );
                    // Engine is poisoned: subsequent open attempts must fail with 0 network messages.
                    assert_eq!(e.open(&x), Err(Error::MultiplicationCheck));
                    assert_eq!(after_check[p].load(Ordering::SeqCst), 0);
                }
            });
        }
    }

    #[test]
    fn active_one_limb_prime_field_fault_with_valid_mac_aborts_before_a2b_and_b2a_openings() {
        struct CorruptFieldReshare {
            inner: Network,
            is_corrupt: bool,
            corrupted_once: bool,
            domain: Domain,
            key0: [u8; 32],
            session: [u8; 32],
            opened_masked_diff: Arc<AtomicBool>,
        }
        impl Transport for CorruptFieldReshare {
            fn exchange(&mut self, mut out: [Envelope; 2]) -> Result<[Envelope; 2], Error> {
                // `fmul` resharing has 256 `u64`s to peer 0 and 0 `u64`s to peer 1.
                if self.is_corrupt
                    && !self.corrupted_once
                    && out[0].payload.len() == 256
                    && out[1].payload.is_empty()
                {
                    self.corrupted_once = true;
                    // Add 1 modulo `p` to lane 13's share so it remains 100% canonical `< p`
                    // AND carries a valid pairwise MAC!
                    let off = 13 * 4;
                    let cur: Value = out[0].payload[off..off + 4].try_into().unwrap();
                    let bad = self.domain.add(cur, [1, 0, 0, 0]);
                    out[0].payload[off..off + 4].copy_from_slice(&bad);
                    out[0].tag = valid_mac_tag(&self.key0, &self.session, &out[0]);
                }
                // Detect if `fopen_many` (`512` `u64`s to both peers) or `open` of A2B/B2A delta
                // (`d.width() * 2` `u64`s: `128`, `510`, or `512` `u64`s) ever gets transmitted!
                let len0 = out[0].payload.len();
                let len1 = out[1].payload.len();
                let is_conversion_delta_open =
                    len0 == len1 && (len0 == 512 || len0 == 510 || len0 == 128);
                if is_conversion_delta_open {
                    self.opened_masked_diff.store(true, Ordering::SeqCst);
                }
                self.inner.exchange(out)
            }
        }

        for d in [Domain::Gold, Domain::Secp, Domain::Ed] {
            for a2b in [true, false] {
                for corrupt_p in 0..3 {
                    let session = [0xa0 + (corrupt_p as u8) * 7 + u8::from(a2b); 32];
                    let leaked: [Arc<AtomicBool>; 3] =
                        core::array::from_fn(|_| Arc::new(AtomicBool::new(false)));

                    run(|p, n| {
                        let transport = CorruptFieldReshare {
                            inner: n,
                            is_corrupt: p == corrupt_p,
                            corrupted_once: false,
                            domain: d,
                            key0: keys(p)[0],
                            session,
                            opened_masked_diff: leaked[p].clone(),
                        };
                        let mut e = Engine::new(p, session, keys(p), transport).unwrap();
                        let a = e.fconstant([7, 0, 0, 0]);
                        let b = e.fconstant([11, 0, 0, 0]);
                        let bad_prod = e.fmul(&a, &b, d).unwrap();

                        let res = if a2b {
                            // A2B (`field_to_bits`): must abort BEFORE `v - r` (`512` `u64`s) opens!
                            e.field_to_bits(&bad_prod, d).map(|_| ())
                        } else {
                            // B2A (`bits_to_field`): pending `fmul` fault must abort BEFORE `v - r` opens!
                            let dummy_bits = e.number([5, 0, 0, 0], d.width());
                            e.bits_to_field(&dummy_bits, d).map(|_| ())
                        };
                        if p != corrupt_p {
                            assert_eq!(
                                res,
                                Err(Error::MultiplicationCheck),
                                "domain {d:?}, a2b={a2b}, honest {p}, corrupt {corrupt_p}"
                            );
                            assert!(
                                !leaked[p].load(Ordering::SeqCst),
                                "honest custodian {p} must NEVER open masked A2B/B2A delta on failure!"
                            );
                        }
                    });
                }
            }
        }
    }

    #[test]
    fn consistent_share_additive_faults_are_caught_by_bbcggi19_check_with_zero_wire_openings() {
        struct ConsistentFaultTransport {
            inner: Network,
            fault: Option<FaultInjection>,
            wire_opened: Arc<AtomicBool>,
        }
        impl Transport for ConsistentFaultTransport {
            fn test_fault_raw(&self) -> Option<[usize; 4]> {
                self.fault.map(FaultInjection::to_raw)
            }
            fn exchange(&mut self, out: [Envelope; 2]) -> Result<[Envelope; 2], Error> {
                let len0 = out[0].payload.len();
                let len1 = out[1].payload.len();
                // Detect any opening of secret wires (`33 * 2 = 66` u64s) or A2B/B2A deltas (`128`, `510`, `512`).
                if len0 == len1 && matches!(len0, 66 | 128 | 510 | 512) {
                    self.wire_opened.store(true, Ordering::SeqCst);
                }
                self.inner.exchange(out)
            }
        }

        // 1. Consistent 1-bit Boolean `AND` additive fault (`z = (x & y) ^ (1 << 37)`):
        //    All MACs, edge transcripts, and replicated share consistency checks pass;
        //    ONLY the `GF(2^128)` BBCGGI19 algebraic sacrifice check catches this fault!
        for corrupt_p in 0..3 {
            let session = [0xb1 + corrupt_p as u8; 32];
            let leaked: [Arc<AtomicBool>; 3] =
                core::array::from_fn(|_| Arc::new(AtomicBool::new(false)));
            run(|p, n| {
                let transport = ConsistentFaultTransport {
                    inner: n,
                    fault: (p == corrupt_p).then_some(FaultInjection::BitAnd {
                        call_countdown: 0,
                        gate: 19,
                        lane: 37,
                    }),
                    wire_opened: leaked[p].clone(),
                };
                let mut e = Engine::new(p, session, keys(p), transport).unwrap();
                let x = e.share(&vec![0xaaaa_5555_f0f0_0f0fu64; 33]).unwrap();
                let y = e.share(&vec![0x1234_5678_9abc_def0u64; 33]).unwrap();
                let pairs: Vec<_> = x.iter().copied().zip(y.iter().copied()).collect();
                let z = e.and(&pairs).unwrap();
                assert_eq!(e.open(&z), Err(Error::MultiplicationCheck));
                assert!(!leaked[p].load(Ordering::SeqCst));
            });
        }

        // 2. Consistent 1-limb prime-field `fmul` additive fault (`z = x * y + 1 mod p`)
        //    across `Gold` (`GF(p^3)`), `Secp`, and `Ed` before A2B and B2A openings!
        for d in [Domain::Gold, Domain::Secp, Domain::Ed] {
            for a2b in [true, false] {
                for corrupt_p in 0..3 {
                    let session = [0xc0 + (corrupt_p as u8) * 5 + u8::from(a2b); 32];
                    let leaked: [Arc<AtomicBool>; 3] =
                        core::array::from_fn(|_| Arc::new(AtomicBool::new(false)));
                    run(|p, n| {
                        let transport = ConsistentFaultTransport {
                            inner: n,
                            fault: (p == corrupt_p).then_some(FaultInjection::FieldMul {
                                domain: d,
                                call_countdown: 0,
                                lane: 29,
                            }),
                            wire_opened: leaked[p].clone(),
                        };
                        let mut e = Engine::new(p, session, keys(p), transport).unwrap();
                        let a = e.fconstant([13, 0, 0, 0]);
                        let b = e.fconstant([17, 0, 0, 0]);
                        let bad_prod = e.fmul(&a, &b, d).unwrap();
                        let res = if a2b {
                            e.field_to_bits(&bad_prod, d).map(|_| ())
                        } else {
                            let dummy_bits = e.number([9, 0, 0, 0], d.width());
                            e.bits_to_field(&dummy_bits, d).map(|_| ())
                        };
                        assert_eq!(res, Err(Error::MultiplicationCheck));
                        assert!(!leaked[p].load(Ordering::SeqCst));
                    });
                }
            }
        }
    }
}
