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
    BitPlane256, SimdBackend, detect_backend, gf2_128_mul_acc_batch_portable,
    gf2_128_mul_acc_batch_with_backend, gf2_128_mul_portable, transpose64x256_portable,
};

const MAX_PENDING_BITS: usize = 65_536;
const D0_BITS: usize = 16;
const SUPER_BLOCKS: usize = 8;
const SUPER_BITS: usize = D0_BITS * SUPER_BLOCKS;
const STEP0_CHUNK: usize = 128;
const FOLD_ARITY: usize = 4;
const MAX_PENDING_FIELD_WORDS: usize = 2_048;
const CONVERT_CHUNK_WORDS: usize = 2_048;

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
#[inline(always)]
const fn poly128_mul_x16(c: u128) -> u128 {
    let h = c >> 112;
    (c << 16) ^ h ^ (h << 1) ^ (h << 2) ^ (h << 7)
}

/// Pad power-of-two `groups >= 64` by `+4` (`64`B = 1 cache line) so 64-lane gathers step
/// across all 64 L1D cache sets without conflict misses while keeping `0..groups` contiguous.
#[inline(always)]
const fn fold_stride(groups: usize) -> usize {
    if groups >= 64 && (groups & 15) == 0 {
        groups + 4
    } else {
        groups
    }
}

#[inline(always)]
const fn fold_idx(t: usize, u: usize, lane: usize, g: usize, stride: usize) -> usize {
    (((t * FOLD_ARITY + u) * 64 + lane) * stride) + g
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
fn build_public_tabs_16(words16: &[u64], tabs: &mut ([u64; 256], [u64; 256])) {
    let (tab_lo, tab_hi) = tabs;
    tab_lo[0] = 0;
    tab_hi[0] = 0;
    for bit in 0..8 {
        let step = 1usize << bit;
        let w_lo = words16[bit];
        let w_hi = words16[8 + bit];
        for prev in 0..step {
            tab_lo[step + prev] = tab_lo[prev] ^ w_lo;
            tab_hi[step + prev] = tab_hi[prev] ^ w_hi;
        }
    }
}

/// Evaluate a public `128 x 16` bit-matrix on a prebuilt Four-Russians table pair
/// indexed solely by the public `row_masks`.
#[inline(always)]
fn eval_public_matrix_128x16(
    row_masks: &[u16; 128],
    tabs: &([u64; 256], [u64; 256]),
) -> Bs128 {
    let (tab_lo, tab_hi) = tabs;
    let mut out = [0u64; 128];
    for (dst, &mask) in out.iter_mut().zip(row_masks) {
        *dst = tab_lo[(mask & 0xff) as usize] ^ tab_hi[(mask >> 8) as usize];
    }
    out
}

/// XOR-accumulate a public `128 x 16` bit-matrix on a prebuilt Four-Russians table pair
/// indexed solely by the public `row_masks`.
#[inline(always)]
fn xor_public_matrix_128x16(
    row_masks: &[u16; 128],
    tabs: &([u64; 256], [u64; 256]),
    dst: &mut Bs128,
) {
    let (tab_lo, tab_hi) = tabs;
    for (d, &mask) in dst.iter_mut().zip(row_masks) {
        *d ^= tab_lo[(mask & 0xff) as usize] ^ tab_hi[(mask >> 8) as usize];
    }
}

/// Precompute the eight public `128 x 16` bit-matrices representing multiplication
/// by a public coin-flipped challenge `c` in `GF(2^128)`.
#[inline]
fn build_public_mul_masks(c: Gf128) -> [[u16; 128]; 8] {
    let mut cur = gf128_to_u128(c);
    core::array::from_fn(|_| {
        let cols: [u128; 16] = core::array::from_fn(|_| {
            let v = cur;
            cur = poly128_mul_x(cur);
            v
        });
        transpose_cols16_to_u16(&cols)
    })
}

/// Constant-time bitsliced multiplication of 64 `GF(2^128)` lanes (`plane`) by a
/// public scalar (`masks`), XOR-accumulated into `dst` with zero secret-indexed lookups.
#[inline]
fn xor_bs128_by_public(
    plane: &Bs128,
    masks: &[[u16; 128]; 8],
    tabs: &mut ([u64; 256], [u64; 256]),
    dst: &mut Bs128,
) {
    for (blk, mask_blk) in masks.iter().enumerate() {
        let base = blk * 16;
        build_public_tabs_16(&plane[base..base + 16], tabs);
        xor_public_matrix_128x16(mask_blk, tabs, dst);
    }
}

/// Dispatch `GF(2^128)` dot products: avoid serializing `CPUID` calls on tiny (`<= 4`)
/// slices while leveraging `VPCLMULQDQ`/`PCLMULQDQ` on larger batches.
#[inline]
fn gf128_dot_acc(acc: &mut Gf128, a: &[Gf128], b: &[Gf128], backend: SimdBackend) {
    if a.len() <= 4 {
        gf2_128_mul_acc_batch_portable(acc, a, b);
    } else {
        gf2_128_mul_acc_batch_with_backend(acc, a, b, backend);
    }
}

/// Convert two 64-lane bitsliced 128-bit planes into two 64-element `Gf128` arrays via
/// a zero-`CPUID` constant-time 64x256 butterfly transpose using caller-owned wiped `rows`.
#[inline]
fn transpose_pair_bs128_to_lanes(
    plane_a: &Bs128,
    plane_b: &Bs128,
    out_a: &mut Gf128Lanes,
    out_b: &mut Gf128Lanes,
    rows: &mut [BitPlane256; 64],
) {
    for (r, row) in rows.iter_mut().enumerate() {
        *row = [plane_a[r], plane_a[64 + r], plane_b[r], plane_b[64 + r]];
    }
    transpose64x256_portable(rows);
    for (lane, row) in rows.iter().enumerate() {
        out_a[lane] = [row[0], row[1]];
        out_b[lane] = [row[2], row[3]];
    }
}

/// Inverse 64x256 butterfly transpose from two 64-element `Gf128` lane arrays into
/// two 64-lane bitsliced 128-bit planes using caller-owned wiped `rows`.
#[inline]
fn transpose_pair_lanes_to_bs128(
    in_a: &Gf128Lanes,
    in_b: &Gf128Lanes,
    plane_a: &mut Bs128,
    plane_b: &mut Bs128,
    rows: &mut [BitPlane256; 64],
) {
    for (lane, row) in rows.iter_mut().enumerate() {
        *row = [
            in_a[lane][0],
            in_a[lane][1],
            in_b[lane][0],
            in_b[lane][1],
        ];
    }
    transpose64x256_portable(rows);
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
fn zeroize_gf128_vec_hwm(vec_buf: &mut Vec<Gf128>, hwm: usize) {
    let target = hwm.min(vec_buf.capacity());
    if vec_buf.len() < target {
        vec_buf.resize(target, [0u64; 2]);
    }
    zeroize_gf128_slice(vec_buf);
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
    planes: Box<[Bs128; 32]>,
    tr_rows: Box<[BitPlane256; 64]>,
    step0_buf: Vec<Gf128>,
    hwm_step0: usize,
    step0_acc: Box<[[Gf128Lanes; 32]; 2]>,
    h0_flat: Vec<Gf128Lanes>,
    a_cur: [Vec<Gf128>; 2],
    b_cur: [Vec<Gf128>; 2],
    a_next: [Vec<Gf128>; 2],
    b_next: [Vec<Gf128>; 2],
    b_sum: Vec<Gf128>,
    hwm_cur: usize,
    hwm_next: usize,
    tabs: ([u64; 256], [u64; 256]),
    fold_in_a: Gf128Lanes,
    fold_in_b: Gf128Lanes,
    fold_plane_a: Bs128,
    fold_plane_b: Bs128,
    h_fold: [Gf128Lanes; 12],
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
            planes: Box::new([[0u64; 128]; 32]),
            tr_rows: Box::new([[0u64; 4]; 64]),
            step0_buf: vec![[0u64; 2]; 32 * 64 * STEP0_CHUNK],
            hwm_step0: 0,
            step0_acc: Box::new([[z_lanes; 32]; 2]),
            h0_flat: Vec::with_capacity(60),
            a_cur: [Vec::new(), Vec::new()],
            b_cur: [Vec::new(), Vec::new()],
            a_next: [Vec::new(), Vec::new()],
            b_next: [Vec::new(), Vec::new()],
            b_sum: Vec::new(),
            hwm_cur: 0,
            hwm_next: 0,
            tabs: ([0u64; 256], [0u64; 256]),
            fold_in_a: z_lanes,
            fold_in_b: z_lanes,
            fold_plane_a: [0u64; 128],
            fold_plane_b: [0u64; 128],
            h_fold: [z_lanes; 12],
            c_claim: [[z_lanes; 2]; 2],
            a_fin: [[z_lanes; 2]; 2],
            b_fin: [[z_lanes; 2]; 2],
            u_mask: [[z_lanes; 2]; 2],
            v_mask: [[z_lanes; 2]; 2],
            base_locals: [z_lanes; 4],
        })
    }

    fn prepare(&mut self, groups: usize) {
        if self.a_cur[0].capacity() < self.a_next[0].capacity() {
            core::mem::swap(&mut self.a_cur, &mut self.a_next);
            core::mem::swap(&mut self.b_cur, &mut self.b_next);
            core::mem::swap(&mut self.hwm_cur, &mut self.hwm_next);
        }
        let stride_cur = fold_stride(groups);
        let len_cur = 2 * FOLD_ARITY * 64 * stride_cur;
        if len_cur > self.hwm_cur {
            self.hwm_cur = len_cur;
        }
        for vec_buf in self.a_cur.iter_mut().chain(self.b_cur.iter_mut()) {
            vec_buf.clear();
            vec_buf.resize(len_cur, [0u64; 2]);
        }
        self.b_sum.clear();
        self.b_sum.resize(len_cur, [0u64; 2]);
        if groups > 1 {
            let next_groups = groups.div_ceil(FOLD_ARITY);
            let len_next = 2 * FOLD_ARITY * 64 * fold_stride(next_groups);
            if len_next > self.hwm_next {
                self.hwm_next = len_next;
            }
            for vec_buf in self.a_next.iter_mut().chain(self.b_next.iter_mut()) {
                vec_buf.clear();
                vec_buf.resize(len_next, [0u64; 2]);
            }
        }
        let z_lanes = [[0u64; 2]; 64];
        self.step0_acc[0].fill(z_lanes);
        self.step0_acc[1].fill(z_lanes);
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
        for inst in self.step0_acc.iter_mut() {
            for plane in inst.iter_mut() {
                zeroize_gf128_slice(plane);
            }
        }
        for h in &mut self.h0_flat {
            zeroize_gf128_slice(h);
        }
        self.h0_flat.clear();
        zeroize_gf128_vec_hwm(&mut self.a_cur[0], self.hwm_cur);
        zeroize_gf128_vec_hwm(&mut self.a_cur[1], self.hwm_cur);
        zeroize_gf128_vec_hwm(&mut self.b_cur[0], self.hwm_cur);
        zeroize_gf128_vec_hwm(&mut self.b_cur[1], self.hwm_cur);
        zeroize_gf128_vec_hwm(&mut self.b_sum, self.hwm_cur);
        zeroize_gf128_vec_hwm(&mut self.a_next[0], self.hwm_next);
        zeroize_gf128_vec_hwm(&mut self.a_next[1], self.hwm_next);
        zeroize_gf128_vec_hwm(&mut self.b_next[0], self.hwm_next);
        zeroize_gf128_vec_hwm(&mut self.b_next[1], self.hwm_next);
        self.hwm_cur = 0;
        self.hwm_next = 0;
        ct_zeroize_u64s(&mut self.tabs.0);
        ct_zeroize_u64s(&mut self.tabs.1);
        zeroize_gf128_slice(&mut self.fold_in_a);
        zeroize_gf128_slice(&mut self.fold_in_b);
        ct_zeroize_u64s(&mut self.fold_plane_a);
        ct_zeroize_u64s(&mut self.fold_plane_b);
        for h in &mut self.h_fold {
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
    let c1 = gl_add(gl_add(gl_mul(a[0], b[1]), gl_mul(a[1], b[0])), gl_mul(7, a2b2));
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
