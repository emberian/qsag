//! Genuine Boyle–Couteau–Gilboa–Ishai (BCGI) Dense Dual-LPN Compact Pseudorandom Correlation
//! Generator (`PCG`) with Active Malicious SPCOT GGM-Sum Consistency Verification.
//!
//! Resolves `P0-02` (sparse 99.9%-zero share/mask collapse), `P1-06` (peer-ID & punctured-index
//! wire validation), and `P1-07` (active malicious SPCOT consistency check + single-use non-`Clone`
//! seed consumption):
//!
//! 1. **Validated Regular-Noise GGM Bundle (`t = 64` trees, `depth ∈ {14, 15}`):**
//!    - [`PcgTreeDepth`] strictly enforces `depth ∈ {14, 15}` (`16,384` or `32,768` leaves per tree,
//!      total regular-noise vector length $M \in \{2^{20}, 2^{21}\}$ of Hamming weight $t = 64$).
//!    - Both full-tree Sender expansion and punctured-tree Receiver expansion batch 4 parallel
//!      `Keccak-f[1600]` states via [`qsag_asm::keccak_f1600_batch`].
//! 2. **Dense Expand-Accumulate Parity-Check Matrix ($H_{\mathrm{lpn}} = E \circ \mathrm{Acc}$):**
//!    - Sender expands full 128-bit leaf seeds $s[\mathrm{col}]$ and computes its dense baseline
//!      via $H_{\mathrm{lpn}} \cdot s$.
//!    - Receiver expands punctured leaf seeds $s_{\neq p^*_r}$ (`0` at $p^*_r$) and computes
//!      $H_{\mathrm{lpn}} \cdot s_{\neq p^*_r} \oplus H_{\mathrm{lpn}}[:, p^*_r] \cdot \Delta_{\mathrm{corr}}$,
//!      guaranteeing exact algebraic cancellation to $(H_{\mathrm{lpn}} \cdot e_{p^*}) \cdot \Delta_S$
//!      while ensuring **both** individual party shares and reconstructed Beaver masks `(a, b)` and
//!      $\mathbb{F}_{2^{128}}$ VOLE companions are computationally indistinguishable from uniform.
//! 3. **Active Malicious SPCOT GGM-Sum Consistency Check:**
//!    - Verifies every punctured GGM leaf sum and correlation offset under a public-coin random
//!      $\mathbb{F}_{2^{128}}$ linear combination masked by an LHL-amplified one-time VOLE both
//!      interactively during [`setup_dense_pcg_seeds`] and locally inside
//!      [`DensePcgPartySeed::expand_local`] before any triple or VOLE correlation is produced.
//!    - The check is repeated twice with independently derived tree weights and leaf challenges
//!      and an independent VOLE mask per repetition; both must accept. Leaf weights are powers
//!      of one challenge per repetition, so a fixed discrepancy passes one repetition with
//!      probability at most $(2^d + 1)/(2^{128} - 2)$ and both with at most the square of that:
//!      about $2^{-226}$ per directed pair at depth 15 (a single repetition gives $2^{-113}$).
//! 4. **Single-use seeds:** expansion burns the seed's `(session, party)` identity digest in a
//!    [`SeedBurnTracker`] before any work, so a serialized seed that is decoded again, edited
//!    or not, cannot be expanded a second time against the same tracker.
//! 5. **Punctured index handling:** the receiver's GGM traversal and check evaluation use masks
//!    instead of branches or lookups on the punctured index (a source-level property, not a
//!    statement about the compiled code).

use alloc::collections::BTreeSet;
use alloc::vec;
use alloc::vec::Vec;
use core::convert::TryFrom;
use core::hint::black_box;

use crate::field::tower::Tower128;
use crate::preprocessing::{
    OtMesh, PartyPrivateRng, PreprocessError, run_commit_and_open_coin,
};
use crate::sponge::keccak::{Cshake256Xof, cshake256_32, encode_multi_frame};
use crate::wipe::{
    ct_eq_bytes32, wipe_bytes, wipe_bytes32, wipe_tower128_slice, wipe_u16s,
    wipe_u64s, wipe_u128s,
};

/// Number of regular-noise GGM trees per ordered peer pair (`t = 64`).
pub const DENSE_PCG_NUM_TREES: usize = 64;

/// Number of pseudorandom accumulator taps per tree in $H_{\mathrm{lpn}} = E \circ \mathrm{Acc}$.
pub const DENSE_PCG_TAPS_PER_TREE: usize = 3;

/// Number of 64-bit words of Boolean Beaver triples and BDOZ Subfield-VOLEs (`N = 1024`).
pub const DENSE_PCG_NUM_WORDS: usize = 1024;

/// Total Boolean Beaver triples `(a, b, c = a & b)` expanded from a single seed (`65,536`).
pub const DENSE_PCG_NUM_BOOL_TRIPLES: usize = DENSE_PCG_NUM_WORDS * 64;

/// Number of full-field $\mathbb{F}_{2^{128}}$ (`Tower128`) VOLE companions per peer (`64`).
pub const DENSE_PCG_NUM_VOLE128: usize = 64;

/// Strict upper bound on canonical wire seed byte length for every party count (`36 KiB = 36,864` bytes).
pub const DENSE_PCG_MAX_SEED_BYTES: usize = 36 * 1024;

/// Version 3 uses 256-bit GGM nodes and two SPCOT mask MACs per peer.
const DENSE_PCG_WIRE_MAGIC: &[u8; 8] = b"QSAGDPC3";
/// Wire magic of the earlier layout with one SPCOT mask MAC per peer; no longer accepted.
const DENSE_PCG_WIRE_MAGIC_V1: &[u8; 8] = b"QSAGDPC1";
const VOLE128_GADGET_WORDS: usize = (DENSE_PCG_NUM_VOLE128 * 128) / 64;
const TOTAL_LPN_WORDS: usize = 2 * DENSE_PCG_NUM_WORDS + VOLE128_GADGET_WORDS;
const TOTAL_LPN_ROWS: usize = TOTAL_LPN_WORDS * 64;
const SLICE0_VOLE_ROW_START: usize = 0;
const SLICE1_BEAVER_ROW_START: usize = DENSE_PCG_NUM_BOOL_TRIPLES;
const SLICE2_GF128_ROW_START: usize = 2 * DENSE_PCG_NUM_BOOL_TRIPLES;

/// Validated GGM tree depth for dense dual-LPN PCG (`depth ∈ {14, 15}`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PcgTreeDepth {
    /// Compact unit-test profile; never accepted or constructed in production.
    #[cfg(test)]
    TestDepth8 = 8,
    /// $2^{14} = 16{,}384$ leaves per tree ($M = 64 \cdot 2^{14} = 2^{20}$ total columns).
    Depth14 = 14,
    /// $2^{15} = 32{,}768$ leaves per tree ($M = 64 \cdot 2^{15} = 2^{21}$ total columns).
    Depth15 = 15,
}

impl PcgTreeDepth {
    /// Return the integer tree depth (`14` or `15`).
    #[inline]
    pub const fn depth(self) -> usize {
        match self {
            #[cfg(test)]
            Self::TestDepth8 => 8,
            Self::Depth14 => 14,
            Self::Depth15 => 15,
        }
    }

    /// Return the number of leaves per GGM tree (`1 << depth`).
    #[inline]
    pub const fn num_leaves(self) -> usize {
        1usize << self.depth()
    }
}

impl TryFrom<usize> for PcgTreeDepth {
    type Error = PreprocessError;

    #[inline]
    fn try_from(depth: usize) -> Result<Self, Self::Error> {
        match depth {
            #[cfg(test)]
            8 => Ok(Self::TestDepth8),
            14 => Ok(Self::Depth14),
            15 => Ok(Self::Depth15),
            _ => Err(PreprocessError::PcgDepthOutOfRange { depth }),
        }
    }
}

/// Fault-injection target for adversarial testing of interactive SPCOT setup.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SpcotFaultTarget {
    /// Corrupt a Sender GGM level sibling XOR before OT encryption.
    GgmLevelSibling {
        sender_id: usize,
        receiver_id: usize,
        tree_idx: usize,
        level: usize,
        xor_mask: [u8; 16],
    },
    /// Corrupt a Sender SPCOT correlation offset `c_corr[tree_idx]`.
    CorrelationOffset {
        sender_id: usize,
        receiver_id: usize,
        tree_idx: usize,
        xor_mask: u128,
    },
}

#[derive(Clone, Copy)]
struct GgmTreeDomain {
    session_id: [u8; 32],
    sender_id: u16,
    receiver_id: u16,
    tree_idx: u8,
}

struct FullGgmExpansion {
    leaves: Vec<u128>,
    level_lr_xors: Vec<([u8; 32], [u8; 32])>,
    leaf_xor_sum: Tower128,
}

impl Drop for FullGgmExpansion {
    fn drop(&mut self) {
        wipe_u128s(&mut self.leaves);
        for (l, r) in &mut self.level_lr_xors {
            wipe_bytes32(l);
            wipe_bytes32(r);
        }
        wipe_tower128_elem(&mut self.leaf_xor_sum);
    }
}

struct PuncturedGgmExpansion {
    /// Exact leaf seeds at `col != punctured_idx`, and `0` at `col == punctured_idx`.
    punc_leaves: Vec<u128>,
    /// Sum $\bigoplus_{u \neq p^*} s[u]$ of all non-punctured leaves.
    punc_xor_sum: Tower128,
}

impl Drop for PuncturedGgmExpansion {
    fn drop(&mut self) {
        wipe_u128s(&mut self.punc_leaves);
        wipe_tower128_elem(&mut self.punc_xor_sum);
    }
}

#[inline]
fn wipe_tower128_elem(elem: &mut Tower128) {
    wipe_tower128_slice(core::slice::from_mut(elem));
}

#[inline]
fn read_u64_le(buf: &[u8], off: usize) -> u64 {
    u64::from_le_bytes([
        buf[off],
        buf[off + 1],
        buf[off + 2],
        buf[off + 3],
        buf[off + 4],
        buf[off + 5],
        buf[off + 6],
        buf[off + 7],
    ])
}

#[inline]
fn read_u128_le(buf: &[u8], off: usize) -> u128 {
    u128::from_le_bytes([
        buf[off],
        buf[off + 1],
        buf[off + 2],
        buf[off + 3],
        buf[off + 4],
        buf[off + 5],
        buf[off + 6],
        buf[off + 7],
        buf[off + 8],
        buf[off + 9],
        buf[off + 10],
        buf[off + 11],
        buf[off + 12],
        buf[off + 13],
        buf[off + 14],
        buf[off + 15],
    ])
}

/// Populate one 72-byte `SHAKE256` single-block GGM internal node state (`rate = 136` bytes).
#[inline]
fn encode_ggm_node_state(
    dom: &GgmTreeDomain,
    level: u8,
    node_idx: u32,
    seed: &[u8; 32],
    state: &mut [u64; 25],
) {
    let mut blk = [0u8; 96];
    blk[0..16].copy_from_slice(b"QSAG.DPCG.GGM.N2");
    blk[16..48].copy_from_slice(&dom.session_id);
    blk[48..50].copy_from_slice(&dom.sender_id.to_le_bytes());
    blk[50..52].copy_from_slice(&dom.receiver_id.to_le_bytes());
    blk[52] = dom.tree_idx;
    blk[53] = level;
    blk[54..58].copy_from_slice(&node_idx.to_le_bytes());
    blk[58..90].copy_from_slice(seed);
    blk[90] = 0x1F;
    for (w, slot) in state.iter_mut().enumerate().take(12) {
        *slot = read_u64_le(&blk, 8 * w);
    }
    for slot in state.iter_mut().skip(12) {
        *slot = 0;
    }
    state[16] ^= 0x80u64 << 56;
    wipe_bytes(&mut blk);
}

/// Derive `64` deterministic 256-bit GGM root seeds from `sender_master_seed`.
fn derive_sender_tree_roots(
    session_id: &[u8; 32],
    sender_id: usize,
    receiver_id: usize,
    sender_master_seed: &[u8; 32],
) -> [[u8; 32]; DENSE_PCG_NUM_TREES] {
    let mut xof = Cshake256Xof::new(b"QSAG.DPCG.ROOTS/v2");
    xof.absorb(session_id);
    xof.absorb(&(sender_id as u64).to_le_bytes());
    xof.absorb(&(receiver_id as u64).to_le_bytes());
    xof.absorb(sender_master_seed);
    let mut raw = [0u8; DENSE_PCG_NUM_TREES * 32];
    xof.squeeze(&mut raw);
    let roots = core::array::from_fn(|j| {
        let mut r = [0u8; 32];
        r.copy_from_slice(&raw[32 * j..32 * (j + 1)]);
        r
    });
    wipe_bytes(&mut raw);
    roots
}

/// Expand a full GGM tree of `depth ∈ {14, 15}` using 4-way batched `Keccak-f[1600]`.
fn ggm_expand_full_4x(
    dom: &GgmTreeDomain,
    depth: PcgTreeDepth,
    root_seed: &[u8; 32],
) -> FullGgmExpansion {
    ggm_expand_full_depth(dom, depth.depth(), root_seed)
}

/// [`ggm_expand_full_4x`] for an arbitrary depth `d` (`2^d` leaves).
fn ggm_expand_full_depth(dom: &GgmTreeDomain, d: usize, root_seed: &[u8; 32]) -> FullGgmExpansion {
    let mut cur_level = vec![*root_seed];
    let mut level_lr_xors = Vec::with_capacity(d);

    for lvl in 0..d {
        let mut next_level = Vec::with_capacity(cur_level.len() * 2);
        let mut l_xor = [0u8; 32];
        let mut r_xor = [0u8; 32];

        let mut base_idx = 0usize;
        for chunk in cur_level.chunks(4) {
            let mut states = [[0u64; 25]; 4];
            for (lane, node) in states.iter_mut().zip(chunk.iter()) {
                encode_ggm_node_state(dom, lvl as u8, (base_idx) as u32, node, lane);
                base_idx += 1;
            }
            qsag_asm::keccak_f1600_batch(&mut states[..chunk.len()]);
            for state in states.iter_mut().take(chunk.len()) {
                let mut left = [0u8; 32];
                let mut right = [0u8; 32];
                for word in 0..4 {
                    left[8 * word..8 * (word + 1)].copy_from_slice(&state[word].to_le_bytes());
                    right[8 * word..8 * (word + 1)].copy_from_slice(&state[word + 4].to_le_bytes());
                }
                for (lx, &lb) in l_xor.iter_mut().zip(left.iter()) {
                    *lx ^= lb;
                }
                for (rx, &rb) in r_xor.iter_mut().zip(right.iter()) {
                    *rx ^= rb;
                }
                next_level.push(left);
                next_level.push(right);
                wipe_bytes32(&mut left);
                wipe_bytes32(&mut right);
                wipe_u64s(state);
            }
        }

        for node in &mut cur_level {
            wipe_bytes32(node);
        }
        cur_level = next_level;
        level_lr_xors.push((l_xor, r_xor));
    }

    let mut leaves = Vec::with_capacity(cur_level.len());
    let mut xor_acc = 0u128;
    for node in &mut cur_level {
        let val = read_u128_le(node, 0);
        xor_acc ^= val;
        leaves.push(val);
        wipe_bytes32(node);
    }

    FullGgmExpansion {
        leaves,
        level_lr_xors,
        leaf_xor_sum: Tower128(xor_acc),
    }
}

/// All-ones `u64` iff `a == b`, computed without a comparison or a branch.
#[inline]
fn ct_eq_mask_u64(a: u64, b: u64) -> u64 {
    let diff = black_box(a ^ b);
    let nonzero = (diff | diff.wrapping_neg()) >> 63;
    nonzero.wrapping_sub(1)
}

/// All-ones `u128` iff `a == b` (see [`ct_eq_mask_u64`]).
#[inline]
fn ct_eq_mask_u128(a: usize, b: usize) -> u128 {
    let m = ct_eq_mask_u64(a as u64, b as u64) as u128;
    m | (m << 64)
}

/// All-ones `u128` iff `bit == 1`, all-zeros iff `bit == 0`.
#[inline]
fn ct_bit_mask_u128(bit: u64) -> u128 {
    let m = 0u64.wrapping_sub(black_box(bit & 1)) as u128;
    m | (m << 64)
}

/// Expand a punctured GGM tree (`0` at `punctured_idx`) from `copath` using 4-way batched Keccak.
///
/// The traversal is oblivious in the punctured index at source level: see
/// [`ggm_expand_punctured_oblivious`].
fn ggm_expand_punctured_4x(
    dom: &GgmTreeDomain,
    depth: PcgTreeDepth,
    punctured_idx: usize,
    copath: &[[u8; 32]],
) -> PuncturedGgmExpansion {
    ggm_expand_punctured_oblivious(dom, depth.depth(), punctured_idx, copath)
}

/// Punctured GGM expansion of depth `d` whose sequence of operations and memory addresses is a
/// function of `d` alone.
///
/// Every node of every level is expanded, including the one node per level the receiver does
/// not know; that node is carried as a zero placeholder and its children are masked back to
/// zero. Which child feeds the level sum, which nodes are excluded from it, and where the
/// recovered sibling is written are all decided by masks derived from `punctured_idx`
/// (`ct_eq_mask_*`, `ct_bit_mask_u128`) applied in a full scan of the level; `punctured_idx` is
/// never used as an index, a loop bound or a branch condition.
///
/// This is a property of the Rust source. The compiler is free to turn a mask into a branch,
/// and nothing here has been checked at machine-code level.
///
/// Cost relative to the skipping traversal: one extra Keccak permutation per level (`d` per
/// tree, on top of `2^d - 1`), plus one mask-and-store pass over each level.
fn ggm_expand_punctured_oblivious(
    dom: &GgmTreeDomain, d: usize, punctured_idx: usize, copath: &[[u8; 32]],
) -> PuncturedGgmExpansion {
    let mut cur_level = vec![[0u8; 32]; 1];
    let mut missing_prefix = 0usize;
    for (lvl, sibling_msg) in copath.iter().enumerate().take(d) {
        let bit = ((punctured_idx >> (d - 1 - lvl)) & 1) as u64;
        let path_right = ct_bit_mask_u128(bit) as u8;
        let mut next_level = vec![[0u8; 32]; cur_level.len() * 2];
        let mut known_xor = [0u8; 32];
        for (batch, (chunk, out)) in cur_level.chunks(4).zip(next_level.chunks_mut(8)).enumerate() {
            let base = batch * 4;
            let mut states = [[0u64; 25]; 4];
            for (off, (state, seed)) in states.iter_mut().zip(chunk).enumerate() {
                encode_ggm_node_state(dom, lvl as u8, (base + off) as u32, seed, state);
            }
            qsag_asm::keccak_f1600_batch(&mut states[..chunk.len()]);
            for (off, (state, pair)) in states.iter_mut().zip(out.chunks_mut(2)).enumerate() {
                let known = !ct_eq_mask_u64((base + off) as u64, missing_prefix as u64) as u8;
                for byte in 0..32 {
                    let left = (state[byte / 8] >> (8 * (byte % 8))) as u8;
                    let right = (state[4 + byte / 8] >> (8 * (byte % 8))) as u8;
                    known_xor[byte] ^= (right ^ (path_right & (left ^ right))) & known;
                    pair[0][byte] = left & known;
                    pair[1][byte] = right & known;
                }
                wipe_u64s(state);
            }
        }
        for (idx, pair) in next_level.chunks_mut(2).enumerate() {
            let below = ct_eq_mask_u64(idx as u64, missing_prefix as u64) as u8;
            for byte in 0..32 {
                let recovered = sibling_msg[byte] ^ known_xor[byte];
                pair[0][byte] ^= below & path_right & recovered;
                pair[1][byte] ^= below & !path_right & recovered;
            }
        }
        wipe_bytes32(&mut known_xor);
        missing_prefix = (missing_prefix << 1) | bit as usize;
        for node in &mut cur_level { wipe_bytes32(node); }
        cur_level = next_level;
    }
    // Leaves are field elements, not further PRF keys. Internal and copath seeds
    // retain all 256 bits; projecting the final output to GF(2^128) is intentional.
    let mut punc_leaves = Vec::with_capacity(cur_level.len());
    let mut punc_xor = 0u128;
    for (idx, node) in cur_level.iter_mut().enumerate() {
        let leaf = read_u128_le(node, 0) & !ct_eq_mask_u128(idx, punctured_idx);
        punc_xor ^= leaf; punc_leaves.push(leaf); wipe_bytes32(node);
    }
    PuncturedGgmExpansion { punc_leaves, punc_xor_sum: Tower128(punc_xor) }
}

// ============================================================================
// 2. Dense Expand-Accumulate Parity-Check Matrix (`H_lpn = E ∘ Acc`)
// ============================================================================

#[derive(Clone, Copy)]
struct LpnTapStreamCtx {
    session_id: [u8; 32],
    sender_id: u16,
    receiver_id: u16,
    tree_idx: u8,
    depth: u8,
}

/// Deterministic 4-way batched `Keccak-f[1600]` stream producing uniform masked tap indices in `0..2^d`.
struct BatchedTapGenerator {
    ctx: LpnTapStreamCtx,
    leaf_mask: usize,
    next_block_ctr: u64,
    buf_u16: [u16; 272],
    pos: usize,
    filled: usize,
}

impl BatchedTapGenerator {
    fn new(ctx: LpnTapStreamCtx) -> Self {
        let leaf_mask = (1usize << (ctx.depth as usize)) - 1;
        Self {
            ctx,
            leaf_mask,
            next_block_ctr: 0,
            buf_u16: [0u16; 272],
            pos: 0,
            filled: 0,
        }
    }

    fn refill(&mut self) {
        let mut states = [[0u64; 25]; 4];
        for (lane_idx, state) in states.iter_mut().enumerate() {
            let ctr = self.next_block_ctr + (lane_idx as u64);
            let mut blk = [0u8; 64];
            blk[0..16].copy_from_slice(b"QSAG.DPCG.LPNTAP");
            blk[16..48].copy_from_slice(&self.ctx.session_id);
            blk[48..50].copy_from_slice(&self.ctx.sender_id.to_le_bytes());
            blk[50..52].copy_from_slice(&self.ctx.receiver_id.to_le_bytes());
            blk[52] = self.ctx.tree_idx;
            blk[53] = self.ctx.depth;
            blk[54..62].copy_from_slice(&ctr.to_le_bytes());
            blk[62] = 0x1F;
            for (w, slot) in state.iter_mut().enumerate().take(8) {
                *slot = read_u64_le(&blk, 8 * w);
            }
            state[16] ^= 0x80u64 << 56;
        }
        self.next_block_ctr += 4;
        qsag_asm::keccak_f1600_batch(&mut states);

        let mut write_idx = 0usize;
        for state in &states {
            for &word in state.iter().take(17) {
                self.buf_u16[write_idx] = word as u16;
                self.buf_u16[write_idx + 1] = (word >> 16) as u16;
                self.buf_u16[write_idx + 2] = (word >> 32) as u16;
                self.buf_u16[write_idx + 3] = (word >> 48) as u16;
                write_idx += 4;
            }
        }
        self.pos = 0;
        self.filled = 272;
    }

    #[inline]
    fn next_three_taps(&mut self) -> [usize; DENSE_PCG_TAPS_PER_TREE] {
        let mut out = [0usize; DENSE_PCG_TAPS_PER_TREE];
        for slot in &mut out {
            if self.pos >= self.filled {
                self.refill();
            }
            *slot = (self.buf_u16[self.pos] as usize) & self.leaf_mask;
            self.pos += 1;
        }
        out
    }
}

/// Sender dense dual-LPN accumulation: `out_keys += H_lpn^{(tree)} * full_leaves`.
fn accumulate_sender_lpn_tree(
    ctx: LpnTapStreamCtx,
    full_leaves: &[u128],
    out_keys: &mut [u128],
) {
    let mut acc = Vec::with_capacity(full_leaves.len());
    let mut running = 0u128;
    for &leaf in full_leaves {
        running ^= leaf;
        acc.push(running);
    }

    let mut tap_gen = BatchedTapGenerator::new(ctx);
    for key_row in out_keys.iter_mut() {
        let taps = tap_gen.next_three_taps();
        *key_row ^= acc[taps[0]] ^ acc[taps[1]] ^ acc[taps[2]];
    }

    wipe_u128s(&mut acc);
}

/// Receiver dense dual-LPN accumulation:
/// `out_macs += H_lpn^{(tree)} * s_{≠ p*} ⊕ H_lpn^{(tree)}[:, p*] · delta_corr`
/// and `out_choices += H_lpn^{(tree)} * e_{p*}`.
fn accumulate_receiver_lpn_tree(
    ctx: LpnTapStreamCtx,
    punc_leaves: &[u128],
    p_star: usize,
    delta_corr: u128,
    out_macs: &mut [u128],
    out_choice_words: &mut [u64],
) {
    let mut acc = Vec::with_capacity(punc_leaves.len());
    let mut running = 0u128;
    for &leaf in punc_leaves {
        running ^= leaf;
        acc.push(running);
    }

    let mut tap_gen = BatchedTapGenerator::new(ctx);
    for (row_idx, mac_row) in out_macs.iter_mut().enumerate() {
        let taps = tap_gen.next_three_taps();
        let punc_term = acc[taps[0]] ^ acc[taps[1]] ^ acc[taps[2]];
        // `tap >= p_star` as the complement of the borrow of `tap - p_star` (both below 2^16).
        let p = p_star as u64;
        let h_bit = 1
            ^ ((taps[0] as u64).wrapping_sub(p) >> 63)
            ^ ((taps[1] as u64).wrapping_sub(p) >> 63)
            ^ ((taps[2] as u64).wrapping_sub(p) >> 63);
        let corr_mask = 0u128.wrapping_sub(black_box(h_bit as u128));
        *mac_row ^= punc_term ^ (corr_mask & delta_corr);
        out_choice_words[row_idx >> 6] ^= h_bit << (row_idx & 63);
    }

    wipe_u128s(&mut acc);
}

// ============================================================================
// 3. Active Malicious SPCOT GGM-Sum Consistency Check
// ============================================================================

/// Number of independent repetitions of the SPCOT consistency check. Each repetition has its
/// own tree weights, its own leaf challenge and its own one-time VOLE mask; all must accept.
const SPCOT_CHECK_REPS: usize = 2;

struct SpcotChallengeWeights {
    tree_gammas: [Tower128; DENSE_PCG_NUM_TREES],
    leaf_powers: Vec<Tower128>,
}

fn squeeze_nonzero_tower128(xof: &mut Cshake256Xof) -> Tower128 {
    loop {
        let mut buf = [0u8; 16];
        xof.squeeze(&mut buf);
        let v = read_u128_le(&buf, 0);
        if v != 0 && v != 1 {
            return Tower128(v);
        }
    }
}

/// Expand the post-commitment coin `chal_coin` into the weights of repetition `rep`.
///
/// Repetitions are separate cSHAKE expansions of the same coin, distinguished by the absorbed
/// repetition index, so the `(gamma, chi)` sets of different repetitions are independent in the
/// random-oracle model. The coin itself is opened only after the checked values are fixed.
fn derive_spcot_challenge_weights(
    session_id: &[u8; 32],
    sender_id: usize,
    receiver_id: usize,
    chal_coin: &[u8; 32],
    depth: PcgTreeDepth,
    rep: usize,
) -> SpcotChallengeWeights {
    let mut xof = Cshake256Xof::new(b"QSAG.DPCG.SPCOT.CHAL/v1");
    xof.absorb(session_id);
    xof.absorb(&(sender_id as u64).to_le_bytes());
    xof.absorb(&(receiver_id as u64).to_le_bytes());
    xof.absorb(&(depth.depth() as u32).to_le_bytes());
    xof.absorb(&(rep as u32).to_le_bytes());
    xof.absorb(chal_coin);

    let tree_gammas = core::array::from_fn(|_| squeeze_nonzero_tower128(&mut xof));
    let chi_base = squeeze_nonzero_tower128(&mut xof);

    let num_leaves = depth.num_leaves();
    let mut leaf_powers = Vec::with_capacity(num_leaves);
    let mut cur = chi_base;
    for _ in 0..num_leaves {
        leaf_powers.push(cur);
        cur = cur.mul(chi_base);
    }

    SpcotChallengeWeights {
        tree_gammas,
        leaf_powers,
    }
}

fn derive_all_spcot_challenge_weights(
    session_id: &[u8; 32],
    sender_id: usize,
    receiver_id: usize,
    chal_coin: &[u8; 32],
    depth: PcgTreeDepth,
) -> [SpcotChallengeWeights; SPCOT_CHECK_REPS] {
    core::array::from_fn(|rep| {
        derive_spcot_challenge_weights(session_id, sender_id, receiver_id, chal_coin, depth, rep)
    })
}

/// Accumulate $\gamma_j \cdot \bigoplus_{u=0}^{2^d - 1} \chi^{u+1} \cdot s[j, u]$ for one full GGM
/// leaf vector.
fn eval_tree_spcot_linear_combo(
    gamma_j: Tower128,
    leaf_powers: &[Tower128],
    leaves: &[u128],
) -> Tower128 {
    let mut sum = Tower128::ZERO;
    for (&pow, &leaf) in leaf_powers.iter().zip(leaves.iter()) {
        sum = sum.add(pow.mul(Tower128(leaf)));
    }
    gamma_j.mul(sum)
}

/// Receiver side of one tree in one repetition.
struct ReceiverTreeSpcotTerm {
    /// $\gamma_j \cdot \bigoplus_u \chi^{u+1} \cdot s'[j, u]$, where $s'$ is the punctured leaf
    /// vector with `delta_corr = punc_xor_sum ^ c_corr` filled in at `punctured_idx`.
    combo: Tower128,
    /// $\gamma_j \cdot \chi^{p^*_j + 1}$, the weight of the punctured leaf.
    punctured_weight: Tower128,
}

/// Evaluate [`ReceiverTreeSpcotTerm`] for one punctured tree. The punctured position is filled
/// in and its weight is picked out by an equality mask in a scan over all leaves, so
/// `punctured_idx` is not used as an index or a branch condition.
fn eval_punctured_tree_spcot_term(
    gamma_j: Tower128,
    leaf_powers: &[Tower128],
    punc_leaves: &[u128],
    punctured_idx: usize,
    delta_corr: Tower128,
) -> ReceiverTreeSpcotTerm {
    let mut sum = Tower128::ZERO;
    let mut punctured_pow = 0u128;
    for (u, (&pow, &leaf)) in leaf_powers.iter().zip(punc_leaves.iter()).enumerate() {
        let at_puncture = ct_eq_mask_u128(u, punctured_idx);
        let effective = leaf ^ (at_puncture & (leaf ^ delta_corr.0));
        sum = sum.add(pow.mul(Tower128(effective)));
        punctured_pow ^= at_puncture & pow.0;
    }
    ReceiverTreeSpcotTerm {
        combo: gamma_j.mul(sum),
        punctured_weight: gamma_j.mul(Tower128(punctured_pow)),
    }
}

/// Tag binding the check values of all repetitions; two tags are equal only if every
/// repetition's value agrees.
fn compute_spcot_check_tag(
    session_id: &[u8; 32],
    sender_id: usize,
    receiver_id: usize,
    chal_coin: &[u8; 32],
    w_vals: &[Tower128; SPCOT_CHECK_REPS],
) -> [u8; 32] {
    let s_bytes = (sender_id as u64).to_le_bytes();
    let r_bytes = (receiver_id as u64).to_le_bytes();
    let mut w_bytes = [0u8; 16 * SPCOT_CHECK_REPS];
    for (chunk, w) in w_bytes.as_chunks_mut::<16>().0.iter_mut().zip(w_vals.iter()) {
        *chunk = w.0.to_le_bytes();
    }
    let tag = cshake256_32(
        b"QSAG.DPCG.SPCOT.TAG/v1",
        &encode_multi_frame(&[session_id, &s_bytes, &r_bytes, chal_coin, &w_bytes]),
    );
    wipe_bytes(&mut w_bytes);
    tag
}

/// Final receiver tag comparison after OT-branch parity verification.
fn verify_spcot_receiver_tag(
    expected: &[u8; 32], received: &[u8; 32], sender_id: usize,
) -> Result<(), PreprocessError> {
    if !ct_eq_bytes32(expected, received) {
        return Err(PreprocessError::MacCheckFailed {
            phase: "pcg_dense_spcot_consistency", accused_party: Some(sender_id),
        });
    }
    Ok(())
}

/// Sender's parity messages for the 256 OT transfers of one SPCOT mask.
/// Corrections and key parities must be fixed before the LHL and SPCOT coins.
/// The receiver uses only its selected OT pads and private choices to check them.
/// This is a component of the SPCOT consistency protocol, not a standalone proof
/// that an arbitrary advertised scalar was used by the sender.
pub struct SpcotParityMessage {
    pub corrections: [Tower128; 256],
    pub key_parities: [u64; 4],
}

impl SpcotParityMessage {
    /// Check selected OT branches, then return exactly the MACs used by the LHL
    /// combiner. No sender scalar or unselected OT pad is available to this verifier.
    pub fn verify_receiver(&self, choices: &[u64; 4], selected_pads: &[[u8; 48]]) -> Result<Vec<Tower128>, PreprocessError> {
        if selected_pads.len() != 256 { return Err(PreprocessError::PcgInvalidWireSeed); }
        let mut macs = Vec::with_capacity(256);
        let mut bad = 0u128;
        for (i, pad) in selected_pads.iter().enumerate() {
            let bit = (choices[i / 64] >> (i % 64)) & 1;
            let mac = read_u128_le(pad, 0) ^ (ct_bit_mask_u128(bit) & self.corrections[i].0);
            let key_bit = (self.key_parities[i / 64] >> (i % 64)) & 1;
            bad |= (mac ^ u128::from(key_bit ^ bit)) & 1;
            macs.push(Tower128(mac));
        }
        if bad != 0 {
            wipe_tower128_slice(&mut macs);
            return Err(PreprocessError::MacCheckFailed { phase: "pcg_dense_spcot_parity", accused_party: None });
        }
        Ok(macs)
    }

    fn bind(&self, xof: &mut Cshake256Xof) {
        for correction in &self.corrections { xof.absorb(&correction.0.to_le_bytes()); }
        for parity in self.key_parities { xof.absorb(&parity.to_le_bytes()); }
    }
}

struct OneTimeVole128Mask {
    key_sender: Tower128,
    x_receiver: Tower128,
    mac_receiver: Tower128,
    transcript_digest: [u8; 32],
}

impl Drop for OneTimeVole128Mask {
    fn drop(&mut self) {
        wipe_tower128_elem(&mut self.key_sender);
        wipe_tower128_elem(&mut self.x_receiver);
        wipe_tower128_elem(&mut self.mac_receiver);
    }
}

/// Generate a 1-element $\mathbb{F}_{2^{128}}$ VOLE mask `mac_R ^ key_S == x_R * alpha_S` via
/// 256 active-secure KOS OTs compressed through `[I_128 | R_{128x128}]` Leftover-Hash combiner.
/// Each check repetition `rep` runs its own 256 OTs and its own combiner coin.
fn run_lhl_vole128_mask(
    session_id: &[u8; 32],
    sender_id: usize,
    receiver_id: usize,
    rep: usize,
    alpha_sender: Tower128,
    ot_mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
) -> Result<OneTimeVole128Mask, PreprocessError> {
    let mut choice_words = [0u64; 4];
    for slot in &mut choice_words {
        *slot = party_rngs[receiver_id].next_u64();
    }
    let (send_pads, recv_pads) =
        ot_mesh.run_correlated_ot_words(sender_id, receiver_id, &choice_words, party_rngs)?;

    let mut parity = SpcotParityMessage { corrections: [Tower128::ZERO; 256], key_parities: [0; 4] };
    for (i, (p0, p1)) in send_pads.iter().take(256).enumerate() {
        let k0 = read_u128_le(p0, 0);
        parity.corrections[i] = Tower128(k0 ^ read_u128_le(p1, 0) ^ alpha_sender.0);
        parity.key_parities[i / 64] |= ((k0 & 1) as u64) << (i % 64);
    }
    let mut receiver_macs = parity.verify_receiver(&choice_words, &recv_pads)?;
    let mut bind_xof = Cshake256Xof::new(b"QSAG.DPCG.SPCOT.LHL.BIND/v2");
    parity.bind(&mut bind_xof);
    bind_xof.absorb(session_id);
    bind_xof.absorb(&(sender_id as u64).to_le_bytes());
    bind_xof.absorb(&(receiver_id as u64).to_le_bytes());
    bind_xof.absorb(&(rep as u32).to_le_bytes());
    let mut transcript_digest = [0u8; 32];
    bind_xof.squeeze(&mut transcript_digest);
    let lhl_coin = run_commit_and_open_coin(
        session_id,
        b"QSAG.DPCG.SPCOT.LHL.COIN/v1",
        &transcript_digest,
        party_rngs,
    )?;

    let mut mat_xof = Cshake256Xof::new(b"QSAG.DPCG.SPCOT.LHL.MAT/v1");
    mat_xof.absorb(session_id);
    mat_xof.absorb(&lhl_coin);

    let mut weights = Vec::with_capacity(256);
    for b in 0..128 {
        weights.push(Tower128(1u128 << b));
    }
    for _ in 0..128 {
        let mut buf = [0u8; 16];
        mat_xof.squeeze(&mut buf);
        weights.push(Tower128(read_u128_le(&buf, 0)));
    }

    let mut key_sender = Tower128::ZERO;
    let mut x_receiver = Tower128::ZERO;
    let mut mac_receiver = Tower128::ZERO;

    for (t, ((pads, _recv_pad), &w_t)) in send_pads
        .iter()
        .zip(recv_pads.iter())
        .zip(weights.iter())
        .enumerate()
    {
        let mut k0 = Tower128(read_u128_le(&pads.0, 0));

        key_sender = key_sender.add(w_t.mul(k0));

        let r_bit = ((choice_words[t >> 6] >> (t & 63)) & 1) == 1;
        let m_t = receiver_macs[t];
        if r_bit {
            x_receiver = x_receiver.add(w_t);
        }
        mac_receiver = mac_receiver.add(w_t.mul(m_t));

        wipe_tower128_elem(&mut k0);

    }

    wipe_u64s(&mut choice_words);
    wipe_tower128_slice(&mut receiver_macs);
    Ok(OneTimeVole128Mask {
        key_sender,
        x_receiver,
        mac_receiver,
        transcript_digest,
    })
}

// ============================================================================
// 4. Batched 4-Way Keccak Correlation-Robust Hashing for Boolean Beaver Triples
// ============================================================================

#[inline]
fn encode_crh_beaver_state(
    session_id: &[u8; 32],
    sender_id: u16,
    receiver_id: u16,
    row_idx: u32,
    tag: u128,
    state: &mut [u64; 25],
) {
    let mut blk = [0u8; 80];
    blk[0..16].copy_from_slice(b"QSAG.DPCG.BVRCRH");
    blk[16..48].copy_from_slice(session_id);
    blk[48..50].copy_from_slice(&sender_id.to_le_bytes());
    blk[50..52].copy_from_slice(&receiver_id.to_le_bytes());
    blk[52..56].copy_from_slice(&row_idx.to_le_bytes());
    blk[56..72].copy_from_slice(&tag.to_le_bytes());
    blk[72] = 0x1F;
    for (w, slot) in state.iter_mut().enumerate().take(10) {
        *slot = read_u64_le(&blk, 8 * w);
    }
    for slot in state.iter_mut().skip(10) {
        *slot = 0;
    }
    state[16] ^= 0x80u64 << 56;
    wipe_bytes(&mut blk);
}

/// Sender CRH evaluation on Slice 1 (`q_rows[0..65536]`):
/// computes `a_words` (`h(q) ^ h(q ^ alpha)`) and cross-share `w_sender_words` (`h(q)`).
fn crh_beaver_sender_4x(
    session_id: &[u8; 32],
    sender_id: usize,
    receiver_id: usize,
    alpha_sender: u128,
    q_slice: &[u128],
) -> (Vec<u64>, Vec<u64>) {
    let mut a_words = vec![0u64; DENSE_PCG_NUM_WORDS];
    let mut w_words = vec![0u64; DENSE_PCG_NUM_WORDS];
    let sid = sender_id as u16;
    let rid = receiver_id as u16;

    for (pair_idx, pair) in q_slice.chunks(2).enumerate() {
        let r0 = (2 * pair_idx) as u32;
        let r1 = r0 + 1;
        let mut states = [[0u64; 25]; 4];
        encode_crh_beaver_state(session_id, sid, rid, r0, pair[0], &mut states[0]);
        encode_crh_beaver_state(
            session_id,
            sid,
            rid,
            r0,
            pair[0] ^ alpha_sender,
            &mut states[1],
        );
        encode_crh_beaver_state(session_id, sid, rid, r1, pair[1], &mut states[2]);
        encode_crh_beaver_state(
            session_id,
            sid,
            rid,
            r1,
            pair[1] ^ alpha_sender,
            &mut states[3],
        );
        qsag_asm::keccak_f1600_batch(&mut states);

        let u0_0 = states[0][0] & 1;
        let u1_0 = states[1][0] & 1;
        let u0_1 = states[2][0] & 1;
        let u1_1 = states[3][0] & 1;

        let idx0 = 2 * pair_idx;
        let idx1 = idx0 + 1;
        a_words[idx0 >> 6] |= (u0_0 ^ u1_0) << (idx0 & 63);
        w_words[idx0 >> 6] |= u0_0 << (idx0 & 63);
        a_words[idx1 >> 6] |= (u0_1 ^ u1_1) << (idx1 & 63);
        w_words[idx1 >> 6] |= u0_1 << (idx1 & 63);

        for st in &mut states {
            wipe_u64s(st);
        }
    }

    (a_words, w_words)
}

/// Receiver CRH evaluation on Slice 1 (`t_rows[0..65536]`): computes `w_receiver_words` (`h(t)`).
fn crh_beaver_receiver_4x(
    session_id: &[u8; 32],
    sender_id: usize,
    receiver_id: usize,
    t_slice: &[u128],
) -> Vec<u64> {
    let mut w_words = vec![0u64; DENSE_PCG_NUM_WORDS];
    let sid = sender_id as u16;
    let rid = receiver_id as u16;

    for (quad_idx, quad) in t_slice.chunks(4).enumerate() {
        let base_row = 4 * quad_idx;
        let mut states = [[0u64; 25]; 4];
        for (lane, (&tag, st)) in quad.iter().zip(states.iter_mut()).enumerate() {
            encode_crh_beaver_state(session_id, sid, rid, (base_row + lane) as u32, tag, st);
        }
        qsag_asm::keccak_f1600_batch(&mut states);
        for (lane, st) in states.iter_mut().enumerate() {
            let idx = base_row + lane;
            let bit = st[0] & 1;
            w_words[idx >> 6] |= bit << (idx & 63);
            wipe_u64s(st);
        }
    }

    w_words
}

// ============================================================================
// 5. Compact Wire Seed (`< 36 KiB`, `!Clone`), Seed Burn Tracker & Expanded Vault
// ============================================================================

/// Failure of a [`SeedBurnTracker`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SeedBurnError {
    /// The seed id is already recorded as burned.
    AlreadyBurned,
    /// The burn could not be recorded durably, or the stored record could not be read.
    Io,
}

/// Durable record of which PCG seeds have been expanded.
///
/// [`DensePcgPartySeed::expand_local`] calls [`Self::burn`] before it does any expansion work
/// and proceeds only on `Ok(())`. Implementations must uphold:
/// - `burn` returns `Ok(())` only once the record of `seed_id` would survive a power loss;
/// - `burn` returns [`SeedBurnError::AlreadyBurned`] for an id recorded by any earlier `burn`
///   that returned `Ok(())`, including one from before a restart;
/// - on [`SeedBurnError::Io`] nothing may be assumed about what was written.
///
/// A tracker that is restored from an older snapshot forgets burns and re-admits those seeds;
/// protecting the store against rollback is the implementation's job.
pub trait SeedBurnTracker {
    /// Gate expansion before any secret material is produced. Memory trackers leave
    /// this to their host; filesystem trackers require a consumed journal permit.
    fn begin_expansion(&mut self, _session: &[u8; 32], _seed: &[u8; 32]) -> Result<(), SeedBurnError> { Err(SeedBurnError::Io) }

    /// Record `seed_id` as burned, failing if it is already recorded.
    fn burn(&mut self, seed_id: &[u8; 32]) -> Result<(), SeedBurnError>;

    /// Whether `seed_id` is recorded as burned.
    fn is_burned(&self, seed_id: &[u8; 32]) -> Result<bool, SeedBurnError>;
}

/// Volatile [`SeedBurnTracker`] for tests and for hosts that supply their own durability one
/// level up. It is *not* durable: a process restart loses every burn.
#[derive(Clone, Debug, Default)]
pub struct MemorySeedBurnTracker {
    burned: BTreeSet<[u8; 32]>,
    fail_next: bool,
}

impl MemorySeedBurnTracker {
    pub fn new() -> Self {
        Self::default()
    }

    /// Number of recorded burns.
    pub fn burn_count(&self) -> usize {
        self.burned.len()
    }

    /// Make the next [`SeedBurnTracker::burn`] fail with [`SeedBurnError::Io`] without
    /// recording anything.
    pub fn fail_next_burn(&mut self) {
        self.fail_next = true;
    }
}

impl SeedBurnTracker for MemorySeedBurnTracker {
    fn begin_expansion(&mut self, _session: &[u8; 32], _seed: &[u8; 32]) -> Result<(), SeedBurnError> { Ok(()) }
    fn burn(&mut self, seed_id: &[u8; 32]) -> Result<(), SeedBurnError> {
        if self.fail_next {
            self.fail_next = false;
            return Err(SeedBurnError::Io);
        }
        if self.burned.insert(*seed_id) {
            Ok(())
        } else {
            Err(SeedBurnError::AlreadyBurned)
        }
    }

    fn is_burned(&self, seed_id: &[u8; 32]) -> Result<bool, SeedBurnError> {
        Ok(self.burned.contains(seed_id))
    }
}

/// Authenticated durable seed burns. Retain `checkpoint()` independently before
/// using expanded material, and supply that checkpoint when reopening.
#[cfg(feature = "std")]
pub struct FsSeedBurnTracker(crate::durable_ledger::Ledger, Option<crate::ceremony_journal::CeremonyReservation>);
#[cfg(feature = "std")]
impl FsSeedBurnTracker {
    /// Bind ceremony_id to the PCG session and epoch_or_codeword to seed_id().
    /// The journal transaction must commit before expansion can begin.
    pub fn authorize_release(&mut self, journal: &crate::ceremony_journal::FsCeremonyJournal,
        permit: crate::ceremony_journal::CeremonyReleasePermit) -> Result<(), SeedBurnError> {
        self.1 = None;
        self.1 = Some(journal.consume_release(permit).map_err(|_| SeedBurnError::Io)?);
        Ok(())
    }

    pub fn provision_genesis(path: impl Into<std::path::PathBuf>, key: [u8; 32]) -> Result<Self, SeedBurnError> {
        crate::durable_ledger::Ledger::create(path, key, b"QSAG.SEED_BURN.V1").map(|ledger| Self(ledger, None)).map_err(|_| SeedBurnError::Io)
    }
    pub fn open_existing(path: impl Into<std::path::PathBuf>, key: [u8; 32], checkpoint: crate::LedgerCheckpoint) -> Result<Self, SeedBurnError> {
        crate::durable_ledger::Ledger::open(path, key, b"QSAG.SEED_BURN.V1", checkpoint).map(|ledger| Self(ledger, None)).map_err(|_| SeedBurnError::Io)
    }
    pub fn checkpoint(&self) -> crate::LedgerCheckpoint { self.0.checkpoint() }
}
#[cfg(feature = "std")]
impl SeedBurnTracker for FsSeedBurnTracker {
    fn begin_expansion(&mut self, session: &[u8; 32], seed: &[u8; 32]) -> Result<(), SeedBurnError> {
        let r = self.1.take().ok_or(SeedBurnError::Io)?;
        if r.ceremony_id != *session || r.epoch_or_codeword != *seed { return Err(SeedBurnError::Io); }
        Ok(())
    }

    fn burn(&mut self, seed_id: &[u8; 32]) -> Result<(), SeedBurnError> {
        let mut stored = self.0.read().map_err(|_| SeedBurnError::Io)?;
        if stored.insert(seed_id.to_vec(), Vec::new()).is_some() { return Err(SeedBurnError::AlreadyBurned); }
        self.0.commit(&stored).map_err(|_| SeedBurnError::Io)
    }
    fn is_burned(&self, seed_id: &[u8; 32]) -> Result<bool, SeedBurnError> {
        Ok(self.0.read().map_err(|_| SeedBurnError::Io)?.contains_key(seed_id.as_slice()))
    }
}

/// Per-peer seed material inside a [`DensePcgPartySeed`] (`!Clone`, wiped on `Drop`).
pub struct DensePcgPeerSeed {
    /// Distinct peer party identifier in `0..num_parties`.
    pub peer_id: u16,
    sender_master_seed: [u8; 32],
    punctured_indices: [u16; DENSE_PCG_NUM_TREES],
    copaths: Vec<Vec<[u8; 32]>>,
    corr_offsets: [Tower128; DENSE_PCG_NUM_TREES],
    spcot_chal_coin: [u8; 32],
    /// Receiver MAC of the one-time VOLE mask of each check repetition.
    spcot_mask_macs: [Tower128; SPCOT_CHECK_REPS],
    spcot_expected_tag: [u8; 32],
}

impl Drop for DensePcgPeerSeed {
    fn drop(&mut self) {
        wipe_bytes32(&mut self.sender_master_seed);
        wipe_u16s(&mut self.punctured_indices);
        for cp in &mut self.copaths {
            for node in cp {
                wipe_bytes32(node);
            }
        }
        wipe_tower128_slice(&mut self.corr_offsets);
        wipe_bytes32(&mut self.spcot_chal_coin);
        wipe_tower128_slice(&mut self.spcot_mask_macs);
        wipe_bytes32(&mut self.spcot_expected_tag);
    }
}

/// Compact `< 36 KiB` Dense Dual-LPN PCG party seed.
///
/// The type is not `Clone` and [`Self::expand_local`] takes `self` by value, which stops one
/// in-memory value from being expanded twice. That does not cover a seed that was serialized
/// with [`Self::to_wire_bytes`] and decoded again, so expansion additionally burns
/// [`Self::seed_id`] in a [`SeedBurnTracker`] before doing any work.
pub struct DensePcgPartySeed {
    /// 32-byte protocol session identifier.
    pub session_id: [u8; 32],
    /// Owning party index in `0..num_parties`.
    pub party_id: usize,
    /// Total committee size (`>= 2`).
    pub num_parties: usize,
    /// Validated GGM tree depth (`14` or `15`).
    pub tree_depth: PcgTreeDepth,
    mac_alpha: Tower128,
    peers: Vec<DensePcgPeerSeed>,
    /// Present only when `num_parties >= 3` (`0` bytes for 2-party seeds!).
    multi_party_c_fix: Vec<u64>,
}

impl Drop for DensePcgPartySeed {
    fn drop(&mut self) {
        wipe_tower128_elem(&mut self.mac_alpha);
        wipe_u64s(&mut self.multi_party_c_fix);
    }
}

/// Flat contiguous BDOZ Subfield-VOLE and $\mathbb{F}_{2^{128}}$ VOLE material for one peer.
pub struct DensePcgPeerVoleMaterial {
    /// Peer party index in `0..num_parties`.
    pub peer_id: usize,
    /// `1024` `u64` words (`65,536` bits) of Receiver choice bits $x_R = H_{\mathrm{lpn}} \cdot e_{p^*}$.
    pub subfield_choice_words: Vec<u64>,
    /// `65,536` flat BDOZ Subfield-VOLE MACs ($t_R = H_{\mathrm{lpn}} \cdot s_{\neq p^*} \oplus H_{\mathrm{lpn}}[:, p^*] \cdot \Delta_{\mathrm{corr}}$).
    pub subfield_macs: Vec<Tower128>,
    /// `65,536` flat BDOZ Subfield-VOLE keys ($q_S = H_{\mathrm{lpn}} \cdot s$).
    pub subfield_keys: Vec<Tower128>,
    /// `64` $\mathbb{F}_{2^{128}}$ VOLE correlated field elements $u_R \in \mathcal{T}_7$.
    pub gf128_u_vals: Vec<Tower128>,
    /// `64` $\mathbb{F}_{2^{128}}$ VOLE MAC tags authenticating `gf128_u_vals` under peer's `mac_alpha`.
    pub gf128_macs: Vec<Tower128>,
    /// `64` $\mathbb{F}_{2^{128}}$ VOLE keys authenticating peer's `gf128_u_vals` under `self.mac_alpha`.
    pub gf128_keys: Vec<Tower128>,
    /// `64` dense additive $\mathbb{F}_{2^{128}}$ shares (`share_S ^ share_R == u` for each direction).
    pub gf128_sender_dense_shares: Vec<Tower128>,
    /// `64` dense additive $\mathbb{F}_{2^{128}}$ receiver shares (`share_S ^ share_R == gf128_u_vals`).
    pub gf128_receiver_dense_shares: Vec<Tower128>,
}

impl Drop for DensePcgPeerVoleMaterial {
    fn drop(&mut self) {
        wipe_u64s(&mut self.subfield_choice_words);
        wipe_tower128_slice(&mut self.subfield_macs);
        wipe_tower128_slice(&mut self.subfield_keys);
        wipe_tower128_slice(&mut self.gf128_u_vals);
        wipe_tower128_slice(&mut self.gf128_macs);
        wipe_tower128_slice(&mut self.gf128_keys);
        wipe_tower128_slice(&mut self.gf128_sender_dense_shares);
        wipe_tower128_slice(&mut self.gf128_receiver_dense_shares);
    }
}

/// Locally expanded vault holding `65,536` Boolean Beaver triples `(a, b, c = a & b)`,
/// `65,536` flat BDOZ Subfield-VOLEs, and `64` $\mathbb{F}_{2^{128}}$ VOLE companions per peer.
pub struct DensePcgExpandedVault {
    /// Owning party index in `0..num_parties`.
    pub party_id: usize,
    /// Committee size (`>= 2`).
    pub num_parties: usize,
    mac_alpha: Tower128,
    /// `1024` words (`65,536` bits) of additive Boolean share `a_i`.
    pub a_words: Vec<u64>,
    /// `1024` words (`65,536` bits) of additive Boolean share `b_i`.
    pub b_words: Vec<u64>,
    /// `1024` words (`65,536` bits) of additive Boolean product share `c_i` (`(\bigoplus a_i) & (\bigoplus b_i) == \bigoplus c_i`).
    pub c_words: Vec<u64>,
    /// Flat per-peer Subfield-VOLE and $\mathbb{F}_{2^{128}}$ VOLE companion storage.
    pub peer_voles: Vec<DensePcgPeerVoleMaterial>,
    word_cursor: usize,
}

impl Drop for DensePcgExpandedVault {
    fn drop(&mut self) {
        wipe_tower128_elem(&mut self.mac_alpha);
        wipe_u64s(&mut self.a_words);
        wipe_u64s(&mut self.b_words);
        wipe_u64s(&mut self.c_words);
    }
}

impl DensePcgExpandedVault {
    /// Global BDOZ / VOLE authentication scalar $\alpha_i \in \mathbb{F}_{2^{128}}$ (`LSB == 1`).
    #[inline]
    pub fn mac_alpha(&self) -> Tower128 {
        self.mac_alpha
    }

    /// Total Boolean Beaver triples in this vault (`65,536`).
    #[inline]
    pub fn num_boolean_triples(&self) -> usize {
        self.a_words.len() * 64
    }

    /// Stream the next 64 Boolean Beaver triples `(a_word, b_word, c_word)` without replacement.
    pub fn next_bool_triple_word64(&mut self) -> Result<(u64, u64, u64), PreprocessError> {
        if self.word_cursor >= self.a_words.len() {
            return Err(PreprocessError::VaultExhausted {
                kind: "pcg_dense_boolean_triples",
            });
        }
        let idx = self.word_cursor;
        self.word_cursor += 1;
        let out = (self.a_words[idx], self.b_words[idx], self.c_words[idx]);
        self.a_words[idx] = 0;
        self.b_words[idx] = 0;
        self.c_words[idx] = 0;
        Ok(out)
    }
}

impl DensePcgPartySeed {
    /// Global BDOZ / VOLE authentication scalar $\alpha_i \in \mathbb{F}_{2^{128}}$.
    #[inline]
    pub fn mac_alpha(&self) -> Tower128 {
        self.mac_alpha
    }

    /// Mutable test-only / audit-only helper to corrupt a Receiver GGM copath sibling byte in memory.
    #[cfg(test)]
    pub fn corrupt_copath_byte_for_audit(
        &mut self,
        peer_slot: usize,
        tree_idx: usize,
        level: usize,
        byte_idx: usize,
        xor_mask: u8,
    ) {
        self.peers[peer_slot].copaths[tree_idx][level][byte_idx] ^= xor_mask;
    }

    /// Mutable test-only / audit-only helper to corrupt a Receiver SPCOT correlation offset in memory.
    #[cfg(test)]
    pub fn corrupt_corr_offset_for_audit(
        &mut self,
        peer_slot: usize,
        tree_idx: usize,
        xor_mask: u128,
    ) {
        self.peers[peer_slot].corr_offsets[tree_idx].0 ^= xor_mask;
    }

    /// Validate structural, peer-ID, uniqueness, and punctured-index invariants (`P1-06`).
    pub fn validate_invariants(&self) -> Result<(), PreprocessError> {
        if self.num_parties < 2
            || self.party_id >= self.num_parties
            || (self.mac_alpha.0 & 1) == 0
            || self.peers.len() != self.num_parties - 1
        {
            return Err(PreprocessError::PcgInvalidWireSeed);
        }

        let d = self.tree_depth.depth();
        let max_leaves = self.tree_depth.num_leaves();

        for (slot_idx, peer) in self.peers.iter().enumerate() {
            let pid = peer.peer_id as usize;
            if pid >= self.num_parties || pid == self.party_id {
                return Err(PreprocessError::PcgInvalidWireSeed);
            }
            for earlier in self.peers.iter().take(slot_idx) {
                if earlier.peer_id == peer.peer_id {
                    return Err(PreprocessError::PcgInvalidWireSeed);
                }
            }
            if peer.copaths.len() != DENSE_PCG_NUM_TREES {
                return Err(PreprocessError::PcgInvalidWireSeed);
            }
            for (&p_idx, cp) in peer.punctured_indices.iter().zip(peer.copaths.iter()) {
                if (p_idx as usize) >= max_leaves || cp.len() != d {
                    return Err(PreprocessError::PcgInvalidWireSeed);
                }
            }
        }
        let expected_fix_len = if self.num_parties == 2 {
            0
        } else {
            DENSE_PCG_NUM_WORDS
        };
        if self.multi_party_c_fix.len() != expected_fix_len {
            return Err(PreprocessError::PcgInvalidWireSeed);
        }
        Ok(())
    }

    /// Serialize this compact PCG seed to canonical wire bytes (`~30 KiB` at depth 14, `~34 KiB` at depth 15 for 2 parties).
    pub fn to_wire_bytes(&self) -> Vec<u8> {
        let d = self.tree_depth.depth();
        let approx = 64
            + self.peers.len()
                * (164 + 16 * SPCOT_CHECK_REPS + DENSE_PCG_NUM_TREES * (34 + 32 * d));
        let mut out = Vec::with_capacity(approx);
        out.extend_from_slice(DENSE_PCG_WIRE_MAGIC);
        out.extend_from_slice(&self.session_id);
        out.extend_from_slice(&(self.party_id as u16).to_le_bytes());
        out.extend_from_slice(&(self.num_parties as u16).to_le_bytes());
        out.push(d as u8);
        out.extend_from_slice(&self.mac_alpha.0.to_le_bytes());
        out.extend_from_slice(&(self.peers.len() as u16).to_le_bytes());

        for peer in &self.peers {
            out.extend_from_slice(&peer.peer_id.to_le_bytes());
            out.extend_from_slice(&peer.sender_master_seed);
            for &p_idx in &peer.punctured_indices {
                out.extend_from_slice(&p_idx.to_le_bytes());
            }
            for cp in &peer.copaths {
                for node in cp {
                    out.extend_from_slice(node);
                }
            }
            for corr in &peer.corr_offsets {
                out.extend_from_slice(&corr.0.to_le_bytes());
            }
            out.extend_from_slice(&peer.spcot_chal_coin);
            for mac in &peer.spcot_mask_macs {
                out.extend_from_slice(&mac.0.to_le_bytes());
            }
            out.extend_from_slice(&peer.spcot_expected_tag);
        }
        if self.multi_party_c_fix.is_empty() {
            out.push(0u8);
        } else {
            out.push(1u8);
            for &w in &self.multi_party_c_fix {
                out.extend_from_slice(&w.to_le_bytes());
            }
        }
        out
    }

    /// Deserialize and strictly validate a [`DensePcgPartySeed`] from canonical wire bytes (`P1-06`).
    pub fn from_wire_bytes(bytes: &[u8]) -> Result<Self, PreprocessError> {
        if bytes.len() >= 8 && (&bytes[0..8] == DENSE_PCG_WIRE_MAGIC_V1 || &bytes[0..8] == b"QSAGDPC2") {
            return Err(PreprocessError::PcgObsoleteWireSeedFormat);
        }
        if bytes.len() > crate::preprocessing::MAX_FRAME_BUDGET || bytes.len() < 64 || &bytes[0..8] != DENSE_PCG_WIRE_MAGIC {
            return Err(PreprocessError::PcgInvalidWireSeed);
        }
        let mut session_id = [0u8; 32];
        session_id.copy_from_slice(&bytes[8..40]);
        let party_id = u16::from_le_bytes([bytes[40], bytes[41]]) as usize;
        let num_parties = u16::from_le_bytes([bytes[42], bytes[43]]) as usize;
        let tree_depth = PcgTreeDepth::try_from(bytes[44] as usize)
            .map_err(|_| PreprocessError::PcgInvalidWireSeed)?;
        let mac_alpha = Tower128(read_u128_le(bytes, 45));
        let num_peers = u16::from_le_bytes([bytes[61], bytes[62]]) as usize;

        if num_parties < 2
            || party_id >= num_parties
            || (mac_alpha.0 & 1) == 0
            || num_peers != num_parties - 1
        {
            return Err(PreprocessError::PcgInvalidWireSeed);
        }
        if bytes.len() > DENSE_PCG_MAX_SEED_BYTES {
            return Err(PreprocessError::PcgInvalidWireSeed);
        }

        let d = tree_depth.depth();
        let mut cur = 63usize;
        let peer_bytes = 2 + 32 + 2 * DENSE_PCG_NUM_TREES + 32 * d * DENSE_PCG_NUM_TREES
            + 16 * DENSE_PCG_NUM_TREES + 32 + 16 * SPCOT_CHECK_REPS + 32;
        crate::preprocessing::validate_frame_count(num_peers, peer_bytes, bytes.len() - cur)?;
        let mut peers = Vec::with_capacity(num_peers);

        for _ in 0..num_peers {
            let fixed_need = 2
                + 32
                + 2 * DENSE_PCG_NUM_TREES
                + 32 * d * DENSE_PCG_NUM_TREES
                + 16 * DENSE_PCG_NUM_TREES
                + 32
                + 16 * SPCOT_CHECK_REPS
                + 32;
            if cur + fixed_need > bytes.len() {
                return Err(PreprocessError::PcgInvalidWireSeed);
            }
            let peer_id = u16::from_le_bytes([bytes[cur], bytes[cur + 1]]);
            cur += 2;

            let mut sender_master_seed = [0u8; 32];
            sender_master_seed.copy_from_slice(&bytes[cur..cur + 32]);
            cur += 32;

            let mut punctured_indices = [0u16; DENSE_PCG_NUM_TREES];
            for slot in &mut punctured_indices {
                *slot = u16::from_le_bytes([bytes[cur], bytes[cur + 1]]);
                cur += 2;
            }

            let mut copaths = Vec::with_capacity(DENSE_PCG_NUM_TREES);
            for _ in 0..DENSE_PCG_NUM_TREES {
                let mut cp = Vec::with_capacity(d);
                for _ in 0..d {
                    let mut node = [0u8; 32];
                    node.copy_from_slice(&bytes[cur..cur + 32]);
                    cur += 32;
                    cp.push(node);
                }
                copaths.push(cp);
            }

            let mut corr_offsets = [Tower128::ZERO; DENSE_PCG_NUM_TREES];
            for slot in &mut corr_offsets {
                *slot = Tower128(read_u128_le(bytes, cur));
                cur += 16;
            }

            let mut spcot_chal_coin = [0u8; 32];
            spcot_chal_coin.copy_from_slice(&bytes[cur..cur + 32]);
            cur += 32;

            let mut spcot_mask_macs = [Tower128::ZERO; SPCOT_CHECK_REPS];
            for slot in &mut spcot_mask_macs {
                *slot = Tower128(read_u128_le(bytes, cur));
                cur += 16;
            }

            let mut spcot_expected_tag = [0u8; 32];
            spcot_expected_tag.copy_from_slice(&bytes[cur..cur + 32]);
            cur += 32;

            peers.push(DensePcgPeerSeed {
                peer_id,
                sender_master_seed,
                punctured_indices,
                copaths,
                corr_offsets,
                spcot_chal_coin,
                spcot_mask_macs,
                spcot_expected_tag,
            });
        }

        if cur >= bytes.len() {
            return Err(PreprocessError::PcgInvalidWireSeed);
        }
        let has_c_fix = bytes[cur];
        cur += 1;
        let multi_party_c_fix = match (num_parties == 2, has_c_fix) {
            (true, 0) => Vec::new(),
            (false, 1) => {
                let byte_len = DENSE_PCG_NUM_WORDS * 8;
                if cur + byte_len > bytes.len() {
                    return Err(PreprocessError::PcgInvalidWireSeed);
                }
                let mut words = Vec::with_capacity(DENSE_PCG_NUM_WORDS);
                for _ in 0..DENSE_PCG_NUM_WORDS {
                    words.push(read_u64_le(bytes, cur));
                    cur += 8;
                }
                words
            }
            _ => return Err(PreprocessError::PcgInvalidWireSeed),
        };

        if cur != bytes.len() {
            return Err(PreprocessError::PcgInvalidWireSeed);
        }

        let seed = Self {
            session_id,
            party_id,
            num_parties,
            tree_depth,
            mac_alpha,
            peers,
            multi_party_c_fix,
        };
        seed.validate_invariants()?;
        Ok(seed)
    }

    /// Identity under which this seed is burned: a domain-separated digest of the session id
    /// and the owning party index, and of nothing else.
    ///
    /// Every hash that produces a correlation (GGM nodes, tap streams, the Beaver CRH) is keyed
    /// by the session id and by the ordered pair of party indices, and each party receives one
    /// seed per session. `(session, party)` therefore names the correlations this seed can
    /// expand to, while no editable field of the seed is part of the id: a copy with a changed
    /// `multi_party_c_fix`, MAC key, master seed or check field has the same id and is refused
    /// once the original was expanded. Changing the session id or party index in a copy gives
    /// another id, and also re-keys every hash, so nothing of the original expansion recurs.
    ///
    /// Consequence: the first seed expanded under a `(session, party)` identity burns it, also
    /// when that seed then fails its SPCOT check. A session id must not be reused for a second
    /// setup.
    pub fn seed_id(&self) -> [u8; 32] {
        let party = (self.party_id as u64).to_le_bytes();
        cshake256_32(
            b"QSAG.DPCG.SEED.ID/v2",
            &encode_multi_frame(&[&self.session_id, &party]),
        )
    }

    /// Consume this seed and expand `65,536` Boolean Beaver triples, `65,536` BDOZ
    /// Subfield-VOLEs and `64` $\mathbb{F}_{2^{128}}$ VOLE companions per peer with no network I/O.
    ///
    /// Order of operations:
    /// 1. structural validation;
    /// 2. [`Self::seed_id`] is burned in `burn_tracker`. If the id was burned before, this
    ///    returns [`PreprocessError::PcgSeedAlreadyBurned`]; if the tracker cannot record the
    ///    burn, [`PreprocessError::PcgSeedBurnNotRecorded`]. Nothing is expanded in either case;
    /// 3. per peer, the SPCOT consistency check (all repetitions) is verified on the `64`
    ///    punctured trees before any correlation derived from them is used.
    ///
    /// The burn is not rolled back if step 3 fails: a seed that failed its check stays burned.
    pub fn expand_local<T: SeedBurnTracker + ?Sized>(
        self,
        burn_tracker: &mut T,
    ) -> Result<DensePcgExpandedVault, PreprocessError> {
        self.validate_invariants()?;

        let seed_id = self.seed_id();
        burn_tracker.begin_expansion(&self.session_id, &seed_id).map_err(|_| PreprocessError::PcgSeedBurnNotRecorded)?;
        match burn_tracker.burn(&seed_id) {
            Ok(()) => {}
            Err(SeedBurnError::AlreadyBurned) => return Err(PreprocessError::PcgSeedAlreadyBurned),
            Err(SeedBurnError::Io) => return Err(PreprocessError::PcgSeedBurnNotRecorded),
        }

        let me = self.party_id;
        let n = self.num_parties;
        let depth = self.tree_depth;
        let d_u8 = depth.depth() as u8;

        let mut a_words = vec![0u64; DENSE_PCG_NUM_WORDS];
        let mut b_words = vec![0u64; DENSE_PCG_NUM_WORDS];
        let mut cross_xor_words = vec![0u64; DENSE_PCG_NUM_WORDS];
        let mut x_self_sum_words = vec![0u64; DENSE_PCG_NUM_WORDS];
        let mut peer_voles = Vec::with_capacity(self.peers.len());

        for (slot_idx, peer) in self.peers.iter().enumerate() {
            let q = peer.peer_id as usize;

            // Step 1: verify the SPCOT GGM-sum consistency check on all 64 punctured trees from
            // peer `q` before any punctured leaf or correlation offset is used.
            let mut q_to_me_macs = vec![0u128; TOTAL_LPN_ROWS];
            let mut q_to_me_choices = vec![0u64; TOTAL_LPN_WORDS];
            let mut w_recv = receiver_spcot_check_values(
                &self.session_id,
                me,
                depth,
                peer,
                &mut q_to_me_macs,
                &mut q_to_me_choices,
            );

            let recomputed_tag = compute_spcot_check_tag(
                &self.session_id,
                q,
                me,
                &peer.spcot_chal_coin,
                &w_recv,
            );
            wipe_tower128_slice(&mut w_recv);
            if !ct_eq_bytes32(&recomputed_tag, &peer.spcot_expected_tag) {
                wipe_u128s(&mut q_to_me_macs);
                wipe_u64s(&mut q_to_me_choices);
                wipe_u64s(&mut a_words);
                wipe_u64s(&mut b_words);
                wipe_u64s(&mut cross_xor_words);
                wipe_u64s(&mut x_self_sum_words);
                return Err(PreprocessError::MacCheckFailed {
                    phase: "pcg_dense_spcot_consistency",
                    accused_party: Some(q),
                });
            }

            // Step 2: Expand `me -> q` full GGM trees (`H_lpn * s`).
            let roots = derive_sender_tree_roots(
                &self.session_id,
                me,
                q,
                &peer.sender_master_seed,
            );
            let mut me_to_q_keys = vec![0u128; TOTAL_LPN_ROWS];
            for (tree_idx, root_seed) in roots.iter().enumerate() {
                let dom = GgmTreeDomain {
                    session_id: self.session_id,
                    sender_id: me as u16,
                    receiver_id: q as u16,
                    tree_idx: tree_idx as u8,
                };
                let full = ggm_expand_full_4x(&dom, depth, root_seed);
                let tap_ctx = LpnTapStreamCtx {
                    session_id: self.session_id,
                    sender_id: me as u16,
                    receiver_id: q as u16,
                    tree_idx: tree_idx as u8,
                    depth: d_u8,
                };
                accumulate_sender_lpn_tree(tap_ctx, &full.leaves, &mut me_to_q_keys);
            }

            // Step 3: Slice 0 (`0..65,536`) -> Flat BDOZ Subfield-VOLEs.
            let subfield_choice_words = q_to_me_choices[0..DENSE_PCG_NUM_WORDS].to_vec();
            let subfield_macs: Vec<Tower128> = q_to_me_macs
                [SLICE0_VOLE_ROW_START..SLICE0_VOLE_ROW_START + DENSE_PCG_NUM_BOOL_TRIPLES]
                .iter()
                .map(|&v| Tower128(v))
                .collect();
            let subfield_keys: Vec<Tower128> = me_to_q_keys
                [SLICE0_VOLE_ROW_START..SLICE0_VOLE_ROW_START + DENSE_PCG_NUM_BOOL_TRIPLES]
                .iter()
                .map(|&v| Tower128(v))
                .collect();

            // Step 4: Slice 1 (`65,536..131,072`) -> Dense Boolean Beaver Triples `(a, b, c = a & b)`.
            // Dense `b_i` share combines `LSB(H_lpn * s)` (as Sender) and `LSB(H_lpn * s_{!= p*} ^ ...)` (as Receiver)
            // so `b_S ^ b_R == x_R` (`LSB(alpha) == 1`) while every individual share is 50% dense!
            let q_slice1 = &me_to_q_keys
                [SLICE1_BEAVER_ROW_START..SLICE1_BEAVER_ROW_START + DENSE_PCG_NUM_BOOL_TRIPLES];
            let t_slice1 = &q_to_me_macs
                [SLICE1_BEAVER_ROW_START..SLICE1_BEAVER_ROW_START + DENSE_PCG_NUM_BOOL_TRIPLES];
            let x_slice1_words =
                &q_to_me_choices[DENSE_PCG_NUM_WORDS..2 * DENSE_PCG_NUM_WORDS];

            for (row_idx, (&q_tag, &t_tag)) in q_slice1.iter().zip(t_slice1.iter()).enumerate() {
                let b_dense_bit = ((q_tag ^ t_tag) & 1) as u64;
                b_words[row_idx >> 6] ^= b_dense_bit << (row_idx & 63);
            }
            for (dst, &xw) in x_self_sum_words.iter_mut().zip(x_slice1_words.iter()) {
                *dst ^= xw;
            }

            let (mut a_pair_words, mut w_send_words) =
                crh_beaver_sender_4x(&self.session_id, me, q, self.mac_alpha.0, q_slice1);
            let mut w_recv_words = crh_beaver_receiver_4x(&self.session_id, q, me, t_slice1);

            if slot_idx == 0 {
                a_words.copy_from_slice(&a_pair_words);
            }

            for ((cw, &ws), &wr) in cross_xor_words
                .iter_mut()
                .zip(w_send_words.iter())
                .zip(w_recv_words.iter())
            {
                *cw ^= ws ^ wr;
            }

            wipe_u64s(&mut a_pair_words);
            wipe_u64s(&mut w_send_words);
            wipe_u64s(&mut w_recv_words);

            // Step 5: Slice 2 (`131,072..139,264`) -> `64` full-field `GF(2^128)` VOLE companions
            // via 128-bit `Tower128` basis gadget `e_b = Tower128(1u128 << b)`.
            let mut gf128_u_vals = Vec::with_capacity(DENSE_PCG_NUM_VOLE128);
            let mut gf128_macs = Vec::with_capacity(DENSE_PCG_NUM_VOLE128);
            let mut gf128_keys = Vec::with_capacity(DENSE_PCG_NUM_VOLE128);
            let mut gf128_sender_dense_shares = Vec::with_capacity(DENSE_PCG_NUM_VOLE128);
            let mut gf128_receiver_dense_shares = Vec::with_capacity(DENSE_PCG_NUM_VOLE128);

            for m in 0..DENSE_PCG_NUM_VOLE128 {
                let word_lo = 2 * DENSE_PCG_NUM_WORDS + 2 * m;
                let u_lo = q_to_me_choices[word_lo] as u128;
                let u_hi = q_to_me_choices[word_lo + 1] as u128;
                let u_elem = Tower128(u_lo | (u_hi << 64));

                let row_base = SLICE2_GF128_ROW_START + 128 * m;
                let mut mac_acc = Tower128::ZERO;
                let mut key_acc = Tower128::ZERO;
                let mut s_share_bits = 0u128;
                let mut r_share_bits = 0u128;

                for bit in 0..128 {
                    let basis = Tower128(1u128 << bit);
                    let t_val = q_to_me_macs[row_base + bit];
                    let q_val = me_to_q_keys[row_base + bit];
                    mac_acc = mac_acc.add(Tower128(t_val).mul(basis));
                    key_acc = key_acc.add(Tower128(q_val).mul(basis));
                    s_share_bits |= (q_val & 1) << bit;
                    r_share_bits |= (t_val & 1) << bit;
                }

                gf128_u_vals.push(u_elem);
                gf128_macs.push(mac_acc);
                gf128_keys.push(key_acc);
                gf128_sender_dense_shares.push(Tower128(s_share_bits));
                gf128_receiver_dense_shares.push(Tower128(r_share_bits));
            }

            wipe_u128s(&mut q_to_me_macs);
            wipe_u64s(&mut q_to_me_choices);
            wipe_u128s(&mut me_to_q_keys);

            peer_voles.push(DensePcgPeerVoleMaterial {
                peer_id: q,
                subfield_choice_words,
                subfield_macs,
                subfield_keys,
                gf128_u_vals,
                gf128_macs,
                gf128_keys,
                gf128_sender_dense_shares,
                gf128_receiver_dense_shares,
            });
        }

        let mut c_words = vec![0u64; DENSE_PCG_NUM_WORDS];
        for (((cw, &aw), &xw), &cross_w) in c_words
            .iter_mut()
            .zip(a_words.iter())
            .zip(x_self_sum_words.iter())
            .zip(cross_xor_words.iter())
        {
            *cw = (aw & xw) ^ cross_w;
        }
        for (cw, &fix_w) in c_words.iter_mut().zip(self.multi_party_c_fix.iter()) {
            *cw ^= fix_w;
        }
        wipe_u64s(&mut cross_xor_words);
        wipe_u64s(&mut x_self_sum_words);

        Ok(DensePcgExpandedVault {
            party_id: me,
            num_parties: n,
            mac_alpha: self.mac_alpha,
            a_words,
            b_words,
            c_words,
            peer_voles,
            word_cursor: 0,
        })
    }
}

/// Receiver side of the SPCOT consistency check for the trees peer `peer.peer_id` sent to
/// `receiver_id`: expand the `64` punctured trees, accumulate their dual-LPN contribution into
/// `out_macs` / `out_choice_words`, and return the receiver check value of every repetition
/// (`mask MAC + sum of per-tree terms`). The caller compares these against the sender's tag
/// before using `out_macs` / `out_choice_words`.
fn receiver_spcot_check_values(
    session_id: &[u8; 32],
    receiver_id: usize,
    depth: PcgTreeDepth,
    peer: &DensePcgPeerSeed,
    out_macs: &mut [u128],
    out_choice_words: &mut [u64],
) -> [Tower128; SPCOT_CHECK_REPS] {
    let sender_id = peer.peer_id as usize;
    let weights = derive_all_spcot_challenge_weights(
        session_id,
        sender_id,
        receiver_id,
        &peer.spcot_chal_coin,
        depth,
    );
    let mut w_recv = peer.spcot_mask_macs;

    for tree_idx in 0..DENSE_PCG_NUM_TREES {
        let p_star = peer.punctured_indices[tree_idx] as usize;
        let dom = GgmTreeDomain {
            session_id: *session_id,
            sender_id: sender_id as u16,
            receiver_id: receiver_id as u16,
            tree_idx: tree_idx as u8,
        };
        let punc = ggm_expand_punctured_4x(&dom, depth, p_star, &peer.copaths[tree_idx]);
        let delta_corr = punc.punc_xor_sum.add(peer.corr_offsets[tree_idx]);

        for (w, rep_weights) in w_recv.iter_mut().zip(weights.iter()) {
            let term = eval_punctured_tree_spcot_term(
                rep_weights.tree_gammas[tree_idx],
                &rep_weights.leaf_powers,
                &punc.punc_leaves,
                p_star,
                delta_corr,
            );
            *w = w.add(term.combo);
        }

        let tap_ctx = LpnTapStreamCtx {
            session_id: *session_id,
            sender_id: sender_id as u16,
            receiver_id: receiver_id as u16,
            tree_idx: tree_idx as u8,
            depth: depth.depth() as u8,
        };
        accumulate_receiver_lpn_tree(
            tap_ctx,
            &punc.punc_leaves,
            p_star,
            delta_corr.0,
            out_macs,
            out_choice_words,
        );
    }
    w_recv
}

// ============================================================================
// 6. Interactive Malicious-Secure Seed Setup Over `OtMesh`
// ============================================================================

struct DirectedSpcotTranscript {
    sender_master_seed: [u8; 32],
    punctured_indices: [u16; DENSE_PCG_NUM_TREES],
    copaths: Vec<Vec<[u8; 32]>>,
    corr_offsets: [Tower128; DENSE_PCG_NUM_TREES],
    spcot_chal_coin: [u8; 32],
    spcot_mask_macs: [Tower128; SPCOT_CHECK_REPS],
    spcot_expected_tag: [u8; 32],
    sender_a_words_slice1: Vec<u64>,
    sender_w_words_slice1: Vec<u64>,
    sender_b_lsb_words: Vec<u64>,
    receiver_w_words_slice1: Vec<u64>,
    receiver_b_lsb_words: Vec<u64>,
    receiver_x_words_slice1: Vec<u64>,
}

impl Drop for DirectedSpcotTranscript {
    fn drop(&mut self) {
        wipe_bytes32(&mut self.sender_master_seed);
        wipe_u16s(&mut self.punctured_indices);
        for cp in &mut self.copaths {
            for node in cp {
                wipe_bytes32(node);
            }
        }
        wipe_tower128_slice(&mut self.corr_offsets);
        wipe_tower128_slice(&mut self.spcot_mask_macs);
        wipe_u64s(&mut self.sender_a_words_slice1);
        wipe_u64s(&mut self.sender_w_words_slice1);
        wipe_u64s(&mut self.sender_b_lsb_words);
        wipe_u64s(&mut self.receiver_w_words_slice1);
        wipe_u64s(&mut self.receiver_b_lsb_words);
        wipe_u64s(&mut self.receiver_x_words_slice1);
    }
}

#[derive(Clone, Copy)]
struct DirectedSpcotParams {
    session_id: [u8; 32],
    tree_depth: PcgTreeDepth,
    sender_id: usize,
    receiver_id: usize,
    alpha_sender: Tower128,
    fault: Option<SpcotFaultTarget>,
}

/// Run interactive dealerless setup of compact `< 36 KiB` [`DensePcgPartySeed`]s across `n >= 2` parties.
pub fn setup_dense_pcg_seeds(
    session_id: [u8; 32],
    tree_depth: PcgTreeDepth,
    ot_mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<DensePcgPartySeed>, PreprocessError> {
    setup_dense_pcg_seeds_inner(session_id, tree_depth, ot_mesh, party_rngs, None)
}

/// Same as [`setup_dense_pcg_seeds`], with an optional adversarial [`SpcotFaultTarget`] hook
/// verifying that corrupted GGM copath siblings or SPCOT correlation offsets are deterministically
/// rejected during interactive setup before any seed is accepted.
#[cfg(test)]
pub fn setup_dense_pcg_seeds_with_fault_hook(
    session_id: [u8; 32], tree_depth: PcgTreeDepth, ot_mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng], fault: Option<SpcotFaultTarget>,
) -> Result<Vec<DensePcgPartySeed>, PreprocessError> {
    setup_dense_pcg_seeds_inner(session_id, tree_depth, ot_mesh, party_rngs, fault)
}

fn setup_dense_pcg_seeds_inner(
    session_id: [u8; 32],
    tree_depth: PcgTreeDepth,
    ot_mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
    fault: Option<SpcotFaultTarget>,
) -> Result<Vec<DensePcgPartySeed>, PreprocessError> {
    let n = party_rngs.len();
    if n < 2 || ot_mesh.n != n {
        return Err(PreprocessError::InvalidThreshold { t: 2, n });
    }

    let mut alphas = Vec::with_capacity(n);
    for rng in party_rngs.iter_mut() {
        let mut a = rng.next_tower128();
        a.0 |= 1; // Enforce LSB(alpha_i) == 1 (`127`-bit entropy, exact dense bit projection)
        alphas.push(a);
    }

    let mut directed: Vec<Vec<Option<DirectedSpcotTranscript>>> =
        (0..n).map(|_| (0..n).map(|_| None).collect()).collect();

    for (sender_id, row) in directed.iter_mut().enumerate() {
        for (receiver_id, slot) in row.iter_mut().enumerate() {
            if sender_id == receiver_id {
                continue;
            }
            let params = DirectedSpcotParams {
                session_id,
                tree_depth,
                sender_id,
                receiver_id,
                alpha_sender: alphas[sender_id],
                fault,
            };
            let tr = run_directed_spcot_setup(params, ot_mesh, party_rngs)?;
            *slot = Some(tr);
        }
    }

    // For `n >= 3`, use authenticated KOS/MASCOT multiplication with batch sacrifice so multi-party
    // `(\bigoplus a_p) & (\bigoplus b_p) == \bigoplus c_p` holds with 0 cleartext leakage (`0` bytes for `n == 2`!).
    let c_fixes = if n >= 3 {
        compute_multiparty_beaver_c_fixes(&directed, ot_mesh, party_rngs)?
    } else {
        (0..n).map(|_| Vec::new()).collect()
    };

    let mut out_seeds = Vec::with_capacity(n);
    for (me, multi_party_c_fix) in c_fixes.into_iter().enumerate() {
        let mut peers = Vec::with_capacity(n - 1);
        for (q, (me_slot, row_q)) in directed[me].iter().zip(directed.iter()).enumerate() {
            if q == me {
                continue;
            }
            let me_to_q = me_slot
                .as_ref()
                .ok_or(PreprocessError::PcgInvalidWireSeed)?;
            let q_to_me = row_q[me]
                .as_ref()
                .ok_or(PreprocessError::PcgInvalidWireSeed)?;

            peers.push(DensePcgPeerSeed {
                peer_id: q as u16,
                sender_master_seed: me_to_q.sender_master_seed,
                punctured_indices: q_to_me.punctured_indices,
                copaths: q_to_me.copaths.clone(),
                corr_offsets: q_to_me.corr_offsets,
                spcot_chal_coin: q_to_me.spcot_chal_coin,
                spcot_mask_macs: q_to_me.spcot_mask_macs,
                spcot_expected_tag: q_to_me.spcot_expected_tag,
            });
        }

        out_seeds.push(DensePcgPartySeed {
            session_id,
            party_id: me,
            num_parties: n,
            tree_depth,
            mac_alpha: alphas[me],
            peers,
            multi_party_c_fix,
        });
    }

    wipe_tower128_slice(&mut alphas);
    Ok(out_seeds)
}

fn compute_multiparty_beaver_c_fixes(
    directed: &[Vec<Option<DirectedSpcotTranscript>>],
    ot_mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<Vec<u64>>, PreprocessError> {
    let n = directed.len();
    let mut a_party = vec![vec![0u64; DENSE_PCG_NUM_WORDS]; n];
    let mut b_party = vec![vec![0u64; DENSE_PCG_NUM_WORDS]; n];
    let mut c_ggm = vec![vec![0u64; DENSE_PCG_NUM_WORDS]; n];

    for me in 0..n {
        let mut x_sum = vec![0u64; DENSE_PCG_NUM_WORDS];
        let mut cross_xor = vec![0u64; DENSE_PCG_NUM_WORDS];
        let mut slot = 0usize;
        for (q, (me_slot, row_q)) in directed[me].iter().zip(directed.iter()).enumerate() {
            if q == me {
                continue;
            }
            let me_to_q = me_slot
                .as_ref()
                .ok_or(PreprocessError::PcgInvalidWireSeed)?;
            let q_to_me = row_q[me]
                .as_ref()
                .ok_or(PreprocessError::PcgInvalidWireSeed)?;
            if slot == 0 {
                a_party[me].copy_from_slice(&me_to_q.sender_a_words_slice1);
            }
            for ((bw, &bs), &br) in b_party[me]
                .iter_mut()
                .zip(me_to_q.sender_b_lsb_words.iter())
                .zip(q_to_me.receiver_b_lsb_words.iter())
            {
                *bw ^= bs ^ br;
            }
            for (xs, &xw) in x_sum.iter_mut().zip(q_to_me.receiver_x_words_slice1.iter()) {
                *xs ^= xw;
            }
            for ((cx, &ws), &wr) in cross_xor
                .iter_mut()
                .zip(me_to_q.sender_w_words_slice1.iter())
                .zip(q_to_me.receiver_w_words_slice1.iter())
            {
                *cx ^= ws ^ wr;
            }
            slot += 1;
        }
        for (((cg, &aw), &xw), &cx) in c_ggm[me]
            .iter_mut()
            .zip(a_party[me].iter())
            .zip(x_sum.iter())
            .zip(cross_xor.iter())
        {
            *cg = (aw & xw) ^ cx;
        }
        wipe_u64s(&mut x_sum);
        wipe_u64s(&mut cross_xor);
    }

    let sid = directed[0][1].as_ref().ok_or(PreprocessError::PcgInvalidWireSeed)?.spcot_chal_coin;
    let mut c_target = crate::preprocessing::checked_boolean_product(
        &sid, &a_party, &b_party, ot_mesh, party_rngs)?;

    let mut fixes = Vec::with_capacity(n);
    for (ct, cg) in c_target.iter_mut().zip(c_ggm.iter_mut()) {
        let fix = ct.iter().zip(cg.iter()).map(|(&t, &g)| t ^ g).collect();
        fixes.push(fix);
        wipe_u64s(ct);
        wipe_u64s(cg);
    }
    for mut av in a_party {
        wipe_u64s(&mut av);
    }
    for mut bv in b_party {
        wipe_u64s(&mut bv);
    }
    Ok(fixes)
}

fn run_directed_spcot_setup(
    params: DirectedSpcotParams,
    ot_mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
) -> Result<DirectedSpcotTranscript, PreprocessError> {
    let session_id = &params.session_id;
    let tree_depth = params.tree_depth;
    let sender_id = params.sender_id;
    let receiver_id = params.receiver_id;
    let alpha_sender = params.alpha_sender;
    let fault = params.fault;
    let d = tree_depth.depth();
    let leaf_mask = (tree_depth.num_leaves() - 1) as u16;

    // 1. Receiver samples 64 regular-noise punctured leaf positions `p*[0..64]`.
    let mut punctured_indices = [0u16; DENSE_PCG_NUM_TREES];
    for slot in &mut punctured_indices {
        *slot = (party_rngs[receiver_id].next_u64() as u16) & leaf_mask;
    }

    let total_ot_bits = DENSE_PCG_NUM_TREES * d;
    let num_ot_words = total_ot_bits.div_ceil(64);
    let mut choice_words = vec![0u64; num_ot_words];
    for (tree_idx, &p_star) in punctured_indices.iter().enumerate() {
        for lvl in 0..d {
            let bit = ((p_star as usize) >> (d - 1 - lvl)) & 1;
            let ot_pos = tree_idx * d + lvl;
            choice_words[ot_pos >> 6] |= (bit as u64) << (ot_pos & 63);
        }
    }

    let (send_pads, recv_pads) =
        ot_mesh.run_correlated_ot_words(sender_id, receiver_id, &choice_words, party_rngs)?;
    wipe_u64s(&mut choice_words);

    // 2. Sender expands its 64 full GGM trees (`4-way Keccak`), encrypts `(R_xor, L_xor)` under
    // KOS OT pads, and forms `corr_offsets[j] = leaf_xor_sum[j] ^ alpha_sender`.
    let sender_master_seed = party_rngs[sender_id].next_bytes32();
    let roots = derive_sender_tree_roots(session_id, sender_id, receiver_id, &sender_master_seed);

    let mut full_trees = Vec::with_capacity(DENSE_PCG_NUM_TREES);
    let mut corr_offsets = [Tower128::ZERO; DENSE_PCG_NUM_TREES];
    let mut ot_cts: Vec<([u8; 32], [u8; 32])> = Vec::with_capacity(total_ot_bits);

    for (tree_idx, root) in roots.iter().enumerate() {
        let dom = GgmTreeDomain {
            session_id: *session_id,
            sender_id: sender_id as u16,
            receiver_id: receiver_id as u16,
            tree_idx: tree_idx as u8,
        };
        let mut full = ggm_expand_full_4x(&dom, tree_depth, root);
        let mut c_off = full.leaf_xor_sum.add(alpha_sender);

        match fault {
            Some(SpcotFaultTarget::CorrelationOffset {
                sender_id: fs,
                receiver_id: fr,
                tree_idx: ft,
                xor_mask,
            }) if fs == sender_id && fr == receiver_id && ft == tree_idx => {
                c_off.0 ^= xor_mask;
            }
            _ => {}
        }
        corr_offsets[tree_idx] = c_off;

        for (lvl, (l_xor, r_xor)) in full.level_lr_xors.iter_mut().enumerate() {
            match fault {
                Some(SpcotFaultTarget::GgmLevelSibling {
                    sender_id: fs,
                    receiver_id: fr,
                    tree_idx: ft,
                    level: fl,
                    xor_mask,
                }) if fs == sender_id && fr == receiver_id && ft == tree_idx && fl == lvl => {
                    for (rb, &mb) in r_xor.iter_mut().zip(xor_mask.iter()) {
                        *rb ^= mb;
                    }
                    for (lb, &mb) in l_xor.iter_mut().zip(xor_mask.iter()) {
                        *lb ^= mb;
                    }
                }
                _ => {}
            }

            let ot_pos = tree_idx * d + lvl;
            let (p0, p1) = &send_pads[ot_pos];
            let mut ct0 = [0u8; 32];
            let mut ct1 = [0u8; 32];
            for ((dst, &m), &pad) in ct0.iter_mut().zip(r_xor.iter()).zip(p0[..32].iter()) {
                *dst = m ^ pad;
            }
            for ((dst, &m), &pad) in ct1.iter_mut().zip(l_xor.iter()).zip(p1[..32].iter()) {
                *dst = m ^ pad;
            }
            ot_cts.push((ct0, ct1));
        }
        full_trees.push(full);
    }

    // 3. Receiver decrypts its `64` GGM copaths from `ot_cts` and `recv_pads`.
    let mut copaths = Vec::with_capacity(DENSE_PCG_NUM_TREES);
    for (tree_idx, &p_star) in punctured_indices.iter().enumerate() {
        let mut cp = Vec::with_capacity(d);
        for lvl in 0..d {
            let bit = (((p_star as usize) >> (d - 1 - lvl)) & 1) as u8;
            let take_ct1 = 0u8.wrapping_sub(black_box(bit));
            let ot_pos = tree_idx * d + lvl;
            let (ct0, ct1) = &ot_cts[ot_pos];
            let rpad = &recv_pads[ot_pos];
            let mut node = [0u8; 32];
            for (((dst, &c0), &c1), &p) in node
                .iter_mut()
                .zip(ct0.iter())
                .zip(ct1.iter())
                .zip(rpad[..32].iter())
            {
                *dst = (c0 ^ (take_ct1 & (c0 ^ c1))) ^ p;
            }
            cp.push(node);
        }
        copaths.push(cp);
    }

    // 4. One LHL-amplified one-time `Tower128` VOLE mask per check repetition, each from its
    // own OTs and its own combiner coin.
    let vole_masks = [
        run_lhl_vole128_mask(session_id, sender_id, receiver_id, 0, alpha_sender, ot_mesh, party_rngs)?,
        run_lhl_vole128_mask(session_id, sender_id, receiver_id, 1, alpha_sender, ot_mesh, party_rngs)?,
    ];

    // 5. Commit-and-open public coin `spcot_chal_coin`, bound to a digest of all `ot_cts` and
    // `corr_offsets`, drawn after those and both VOLE masks are fixed.
    let mut tr_xof = Cshake256Xof::new(b"QSAG.DPCG.SPCOT.TR/v1");
    tr_xof.absorb(session_id);
    tr_xof.absorb(&(sender_id as u64).to_le_bytes());
    tr_xof.absorb(&(receiver_id as u64).to_le_bytes());
    for (ct0, ct1) in &ot_cts {
        tr_xof.absorb(ct0);
        tr_xof.absorb(ct1);
    }
    for mask in &vole_masks { tr_xof.absorb(&mask.transcript_digest); }
    for corr in &corr_offsets {
        tr_xof.absorb(&corr.0.to_le_bytes());
    }
    let mut tr_digest = [0u8; 32];
    tr_xof.squeeze(&mut tr_digest);

    let spcot_chal_coin = run_commit_and_open_coin(
        session_id,
        b"QSAG.DPCG.SPCOT.COIN/v1",
        &tr_digest,
        party_rngs,
    )?;

    // 6. SPCOT GGM-sum consistency check, run `SPCOT_CHECK_REPS = 2` times.
    //
    // Repetition `r` expands the coin into its own tree weights `gamma_r[j]` and leaf challenge
    // `chi_r`, and compares `mask_r + sum_j gamma_r[j] * sum_u chi_r^(u+1) * leaf[j, u]` between
    // the sender's full trees and the receiver's reconstruction. For a discrepancy fixed before
    // the coin is opened, one repetition accepts with probability at most
    // `(2^d + 1) / (2^128 - 2)`: each tree's error polynomial has degree at most `2^d` in
    // `chi_r`, and if some tree's error evaluates non-zero the `gamma_r` combination vanishes
    // with probability `1 / (2^128 - 2)`. With the two repetitions modelled as independent
    // (separate expansions of the coin, see `derive_spcot_challenge_weights`), both accept with
    // probability at most `((2^d + 1) / (2^128 - 2))^2`, about `2^-226` at `d = 15` and `2^-228`
    // at `d = 14`. This bounds one directed pair in one session; a union bound over pairs and
    // sessions applies on top, as does the collision resistance of the 256-bit tag.
    let chal_weights = derive_all_spcot_challenge_weights(
        session_id,
        sender_id,
        receiver_id,
        &spcot_chal_coin,
        tree_depth,
    );

    let need_preview = n_requires_derand_preview(party_rngs.len());
    let mut recv_mac_preview = if need_preview {
        vec![0u128; TOTAL_LPN_ROWS]
    } else {
        Vec::new()
    };
    let mut recv_choice_preview = if need_preview {
        vec![0u64; TOTAL_LPN_WORDS]
    } else {
        Vec::new()
    };
    let d_u8 = d as u8;

    let mut x_chk: [Tower128; SPCOT_CHECK_REPS] =
        core::array::from_fn(|rep| vole_masks[rep].x_receiver);
    let mut w_recv: [Tower128; SPCOT_CHECK_REPS] =
        core::array::from_fn(|rep| vole_masks[rep].mac_receiver);
    for (tree_idx, &p_star_u16) in punctured_indices.iter().enumerate() {
        let p_star = p_star_u16 as usize;

        let dom = GgmTreeDomain {
            session_id: *session_id,
            sender_id: sender_id as u16,
            receiver_id: receiver_id as u16,
            tree_idx: tree_idx as u8,
        };
        let punc = ggm_expand_punctured_4x(&dom, tree_depth, p_star, &copaths[tree_idx]);
        let delta_corr = punc.punc_xor_sum.add(corr_offsets[tree_idx]);
        for (rep, rep_weights) in chal_weights.iter().enumerate() {
            let term = eval_punctured_tree_spcot_term(
                rep_weights.tree_gammas[tree_idx],
                &rep_weights.leaf_powers,
                &punc.punc_leaves,
                p_star,
                delta_corr,
            );
            // The receiver's message of repetition `rep` is its punctured-leaf weights masked
            // by that repetition's own VOLE input `x_receiver`.
            x_chk[rep] = x_chk[rep].add(term.punctured_weight);
            w_recv[rep] = w_recv[rep].add(term.combo);
        }

        if need_preview {
            let tap_ctx = LpnTapStreamCtx {
                session_id: *session_id,
                sender_id: sender_id as u16,
                receiver_id: receiver_id as u16,
                tree_idx: tree_idx as u8,
                depth: d_u8,
            };
            accumulate_receiver_lpn_tree(
                tap_ctx,
                &punc.punc_leaves,
                p_star,
                delta_corr.0,
                &mut recv_mac_preview,
                &mut recv_choice_preview,
            );
        }
    }

    let mut w_send: [Tower128; SPCOT_CHECK_REPS] = core::array::from_fn(|rep| {
        vole_masks[rep].key_sender.add(x_chk[rep].mul(alpha_sender))
    });
    let mut sender_keys = if need_preview {
        vec![0u128; TOTAL_LPN_ROWS]
    } else {
        Vec::new()
    };
    for (tree_idx, full) in full_trees.iter().enumerate() {
        for (w, rep_weights) in w_send.iter_mut().zip(chal_weights.iter()) {
            let combo_s = eval_tree_spcot_linear_combo(
                rep_weights.tree_gammas[tree_idx],
                &rep_weights.leaf_powers,
                &full.leaves,
            );
            *w = w.add(combo_s);
        }

        if need_preview {
            let tap_ctx = LpnTapStreamCtx {
                session_id: *session_id,
                sender_id: sender_id as u16,
                receiver_id: receiver_id as u16,
                tree_idx: tree_idx as u8,
                depth: d_u8,
            };
            accumulate_sender_lpn_tree(tap_ctx, &full.leaves, &mut sender_keys);
        }
    }

    // One tag over the check values of both repetitions: the tags agree only if both do.
    let spcot_expected_tag =
        compute_spcot_check_tag(session_id, sender_id, receiver_id, &spcot_chal_coin, &w_send);
    let receiver_tag =
        compute_spcot_check_tag(session_id, sender_id, receiver_id, &spcot_chal_coin, &w_recv);
    wipe_tower128_slice(&mut w_send);
    wipe_tower128_slice(&mut w_recv);
    wipe_tower128_slice(&mut x_chk);

    if verify_spcot_receiver_tag(&spcot_expected_tag, &receiver_tag, sender_id).is_err() {
        wipe_u128s(&mut sender_keys);
        wipe_u128s(&mut recv_mac_preview);
        wipe_u64s(&mut recv_choice_preview);
        return Err(PreprocessError::MacCheckFailed {
            phase: "pcg_dense_spcot_consistency",
            accused_party: Some(sender_id),
        });
    }

    let (
        sender_a_words_slice1,
        sender_w_words_slice1,
        sender_b_lsb_words,
        receiver_w_words_slice1,
        receiver_b_lsb_words,
        receiver_x_words_slice1,
    ) = if need_preview {
        let q_slice1 = &sender_keys
            [SLICE1_BEAVER_ROW_START..SLICE1_BEAVER_ROW_START + DENSE_PCG_NUM_BOOL_TRIPLES];
        let t_slice1 = &recv_mac_preview
            [SLICE1_BEAVER_ROW_START..SLICE1_BEAVER_ROW_START + DENSE_PCG_NUM_BOOL_TRIPLES];
        let (a_words, w_s_words) =
            crh_beaver_sender_4x(session_id, sender_id, receiver_id, alpha_sender.0, q_slice1);
        let w_r_words = crh_beaver_receiver_4x(session_id, sender_id, receiver_id, t_slice1);

        let mut b_s = vec![0u64; DENSE_PCG_NUM_WORDS];
        let mut b_r = vec![0u64; DENSE_PCG_NUM_WORDS];
        for (idx, (&qv, &tv)) in q_slice1.iter().zip(t_slice1.iter()).enumerate() {
            b_s[idx >> 6] |= ((qv & 1) as u64) << (idx & 63);
            b_r[idx >> 6] |= ((tv & 1) as u64) << (idx & 63);
        }
        let x_r = recv_choice_preview[DENSE_PCG_NUM_WORDS..2 * DENSE_PCG_NUM_WORDS].to_vec();
        (a_words, w_s_words, b_s, w_r_words, b_r, x_r)
    } else {
        (
            Vec::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
        )
    };
    wipe_u128s(&mut sender_keys);
    wipe_u128s(&mut recv_mac_preview);
    wipe_u64s(&mut recv_choice_preview);

    Ok(DirectedSpcotTranscript {
        sender_master_seed,
        punctured_indices,
        copaths,
        corr_offsets,
        spcot_chal_coin,
        spcot_mask_macs: core::array::from_fn(|rep| vole_masks[rep].mac_receiver),
        spcot_expected_tag,
        sender_a_words_slice1,
        sender_w_words_slice1,
        sender_b_lsb_words,
        receiver_w_words_slice1,
        receiver_b_lsb_words,
        receiver_x_words_slice1,
    })
}

#[inline]
const fn n_requires_derand_preview(num_parties: usize) -> bool {
    num_parties >= 3
}


