//! `FrontierSumFts` — Clean-room Few-Time Signature over root-to-leaf binary-tree
//! antichain frontiers + constant-sum Winternitz chains.
//!
//! Security & Constant-Time Guarantees:
//! 1. Finite audited `FrontierFtsProfile` whitelist prevents unbounded DP allocation DoS.
//! 2. Exact `U384` (and `u128` fast-view) factorized DP tables `M(h, w, L, S) = N(h, L) * D(L, S)`;
//!    `unrank` / `rank` operate exclusively on **public** randomized message digests
//!    `H_msg(R, pk, M, ctr)` (never secret ranks), while secret `SK.seed`/`SK.prf` expansion and
//!    `U384` primitives exefrontiere in straight-line constant time.
//! 3. Mandatory `SK.prf`-derived per-signature randomizer `R` + monotonic `UseBudgetLatch`
//!    preventing deterministic 2-message reuse or unbounded `q >= 3` over-signing.
//! 4. Full 256-bit message digest pre-binding across all profiles, with exact `514 B`, `770 B`,
//!    `1,122 B`, `1,314 B`, and `Full256Bit` (`2,338 B`) wire profiles.

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use qsag_accel::AcceleratorBackend;
use qsag_accel::ct::{
    RedactedSecret, ct_conditional_assign_bytes, ct_eq_bytes, ct_eq_u64, ct_lt_u64, ct_select_u64,
    ct_zeroize_bytes,
};
use qsag_accel::keccak::cshake256_framed_xof;

use crate::u384::U384;

const TAG_LEAF: &[u8] = b"QSAG.FTS.LEAF.V1";
const TAG_MERGE: &[u8] = b"QSAG.FTS.MERGE.V1";
const TAG_CHAIN: &[u8] = b"QSAG.FTS.CHAIN.V1";
const TAG_RAND: &[u8] = b"QSAG.FTS.RAND.V1";
const TAG_MSG_PRE: &[u8] = b"QSAG.FTS.MSG256.V1";
const TAG_HMSG: &[u8] = b"QSAG.FTS.HMSG.V1";

/// Parameter profiles for `FrontierSumFts`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum FrontierFtsProfile {
    /// 16-byte nodes cap generic preimage strength at 128 classical / 64 Grover bits.
    /// Ultra-compact `514 B` 1-use signature (`h=14, w=5, L=31, S=62, n=16, r=128, s=16`, `M` fits in `u128`!).
    Compact514,
    /// 16-byte nodes: 64-bit generic Grover preimage ceiling (not 128-bit PQ).
    /// Compact `770 B` signature (`h=15, w=5, L=47, S=118, n=16, r=190, s=16`, >80-bit 2-use security).
    Compact770,
    /// 16-byte nodes: 64-bit generic Grover preimage ceiling (not 128-bit PQ).
    /// High-resilience `1,314 B` signature (`h=15, w=5, L=81, S=162, n=16, r=335, s=16`, 128-bit 2-use).
    Compact1314,
    /// Single-use 1,122-byte profile: 34 chain values, a 32-byte randomizer and a 2-byte counter.
    /// `(h=8, w=96, L=34, S=1615, n=32, r=256)` gives `M > 2^263`.
    /// Fits a 1,232-byte payload with a 96-byte vote header (1,218 bytes total).
    /// 256-bit nodes and ranks avoid truncating the generic preimage/Grover search domain;
    /// these parameter checks are not a complete signature-security reduction.
    Compact1122,
    /// 32-byte nodes cap generic preimage strength at 256 classical / 128 Grover bits.
    /// The constant-sum frontier domain contains every 256-bit message rank.
    /// Full 256-bit chain-width `2,338 B` 1-use custody profile (`h=8, w=5, L=72, S=144, n=32, r=256, s=16`).
    Full256Bit,
    /// Fast small-tree 1-use profile (`h=5, w=4, L=8, S=12, n=32, r=24, s=16`, `290 B`) for rapid KATs & MPC bridges.
    #[cfg(any(test, feature = "test-params"))]
    Fast256Test,
}

/// Concrete validated parameters for `FrontierSumFts`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FrontierFtsParams {
    pub node_bytes: usize,
    pub tree_height: usize,
    pub winternitz_w: usize,
    pub frontier_len: usize,
    pub target_sum: usize,
    pub index_bits: usize,
    pub counter_bits: usize,
    pub max_safe_uses: u8,
}

impl FrontierFtsProfile {
    pub const fn params(self) -> FrontierFtsParams {
        match self {
            Self::Compact514 => FrontierFtsParams {
                node_bytes: 16,
                tree_height: 14,
                winternitz_w: 5,
                frontier_len: 31,
                target_sum: 62,
                index_bits: 128,
                counter_bits: 16,
                max_safe_uses: 1,
            },
            Self::Compact770 => FrontierFtsParams {
                node_bytes: 16,
                tree_height: 15,
                winternitz_w: 5,
                frontier_len: 47,
                target_sum: 118,
                index_bits: 190,
                counter_bits: 16,
                max_safe_uses: 2,
            },
            Self::Compact1314 => FrontierFtsParams {
                node_bytes: 16,
                tree_height: 15,
                winternitz_w: 5,
                frontier_len: 81,
                target_sum: 162,
                index_bits: 335,
                counter_bits: 16,
                max_safe_uses: 2,
            },
            Self::Compact1122 => FrontierFtsParams {
                node_bytes: 32,
                tree_height: 8,
                winternitz_w: 96,
                frontier_len: 34,
                target_sum: 1615,
                index_bits: 256,
                counter_bits: 16,
                max_safe_uses: 1,
            },
            Self::Full256Bit => FrontierFtsParams {
                node_bytes: 32,
                tree_height: 8,
                winternitz_w: 5,
                frontier_len: 72,
                target_sum: 144,
                index_bits: 256,
                counter_bits: 16,
                max_safe_uses: 1,
            },
            #[cfg(any(test, feature = "test-params"))]
            Self::Fast256Test => FrontierFtsParams {
                node_bytes: 32,
                tree_height: 5,
                winternitz_w: 4,
                frontier_len: 8,
                target_sum: 12,
                index_bits: 24,
                counter_bits: 16,
                max_safe_uses: 1,
            },
        }
    }

    /// Exact serialized byte length of a `FrontierSumFtsSignature`.
    pub const fn signature_bytes(self) -> usize {
        let p = self.params();
        (p.frontier_len + 1) * p.node_bytes + p.counter_bits.div_ceil(8)
    }

    /// Canonical 56-byte big-endian parameter identifier (`PID`).
    pub fn pid_bytes(self) -> [u8; 56] {
        let p = self.params();
        let mut pid = [0u8; 56];
        pid[0..8].copy_from_slice(&(p.node_bytes as u64).to_be_bytes());
        pid[8..16].copy_from_slice(&(p.tree_height as u64).to_be_bytes());
        pid[16..24].copy_from_slice(&(p.winternitz_w as u64).to_be_bytes());
        pid[24..32].copy_from_slice(&(p.frontier_len as u64).to_be_bytes());
        pid[32..40].copy_from_slice(&(p.target_sum as u64).to_be_bytes());
        pid[40..48].copy_from_slice(&(p.index_bits as u64).to_be_bytes());
        pid[48..56].copy_from_slice(&(p.counter_bits as u64).to_be_bytes());
        pid
    }
}

/// Errors produced during `FrontierSumFts` ranking, signing, or verification.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FrontierFtsError {
    ProfileMismatch,
    PersistenceFailed,
    RankOutOfRange,
    InvalidAntichainFrontier,
    InvalidDecorationSum,
    UseBudgetExhausted,
    GrindingExhausted,
    MalformedSignatureLength,
    SignatureVerificationFailed,
}

/// Deterministic combinatorics table `M(h, w, L, S) = N(h, L) * D(L, S)` computed purely from
/// `(h, w, L, S)` over fixed-width `U384` (with lossless `u128` view whenever `M < 2^128`).
#[derive(Clone, Debug)]
pub struct FrontierDpTable {
    pub params: FrontierFtsParams,
    l_stride: usize,
    s_stride: usize,
    /// `sub_counts[t * l_stride + ell]` = number of antichain frontiers of size `ell` in a non-root
    /// subtree of height `t` (`0 <= t < h`), and at `t = h` (`ell >= 2`) for the root split.
    sub_counts: Vec<U384>,
    /// `dec_counts[k * s_stride + u]` = `[x^u] (1 + x + ... + x^{w-1})^k`.
    dec_counts: Vec<U384>,
    pub frontier_cardinality: U384,
    pub decoration_cardinality: U384,
    pub total_cardinality: U384,
}

impl FrontierDpTable {
    /// Build one of the fixed supported profiles. Cardinality overflow indicates
    /// an invalid built-in profile and is a programming error.
    pub fn build(profile: FrontierFtsProfile) -> Self {
        let params = profile.params();
        let h = params.tree_height;
        let w = params.winternitz_w;
        let l = params.frontier_len;
        let s = params.target_sum;
        assert!((1..=20).contains(&h));
        assert!(l >= 2 && l <= (1usize << h));
        assert!(w >= 1 && s <= l * (w - 1));

        let l_stride = l + 1;
        let mut sub_counts = vec![U384::ZERO; (h + 1) * l_stride];
        // Base height t = 0 (leaf): only size 1 frontier (the leaf itself) exists.
        sub_counts[1] = U384::ONE;

        for t in 1..=h {
            // For non-root subtrees (`t < h`), `ell = 1` frontiers directly at the subtree root node.
            if t < h {
                sub_counts[t * l_stride + 1] = U384::ONE;
            }
            let half_leaves = 1usize << (t - 1);
            let max_ell = l.min(1usize << t);
            for ell in 2..=max_ell {
                let i_min = 1usize.max(ell.saturating_sub(half_leaves));
                let i_max = half_leaves.min(ell - 1);
                let mut acc = U384::ZERO;
                for i in i_min..=i_max {
                    let left = sub_counts[(t - 1) * l_stride + i];
                    let right = sub_counts[(t - 1) * l_stride + (ell - i)];
                    let prod = match left.checked_mul(right) {
                        Some(value) => value,
                        None => panic!("FrontierDpTable subtree product fits in U384"),
                    };
                    acc = match acc.checked_add(prod) {
                        Some(value) => value,
                        None => panic!("FrontierDpTable subtree sum fits in U384"),
                    };
                }
                sub_counts[t * l_stride + ell] = acc;
            }
        }

        let s_stride = s + 1;
        let mut dec_counts = vec![U384::ZERO; (l + 1) * s_stride];
        dec_counts[0] = U384::ONE;
        for k in 1..=l {
            for u in 0..=s {
                let a_max = (w - 1).min(u);
                let mut acc = U384::ZERO;
                for a in 0..=a_max {
                    acc = match acc.checked_add(dec_counts[(k - 1) * s_stride + (u - a)]) {
                        Some(value) => value,
                        None => panic!("FrontierDpTable decoration sum fits in U384"),
                    };
                }
                dec_counts[k * s_stride + u] = acc;
            }
        }

        let frontier_cardinality = sub_counts[h * l_stride + l];
        let decoration_cardinality = dec_counts[l * s_stride + s];
        let total_cardinality = match frontier_cardinality.checked_mul(decoration_cardinality) {
            Some(value) => value,
            None => panic!("FrontierDpTable total cardinality fits in U384"),
        };

        Self {
            params,
            l_stride,
            s_stride,
            sub_counts,
            dec_counts,
            frontier_cardinality,
            decoration_cardinality,
            total_cardinality,
        }
    }

    /// Return `Some(total_cardinality as u128)` when `M < 2^128` (e.g. `Compact514`, `Fast256Test`).
    pub fn total_cardinality_u128(&self) -> Option<u128> {
        if self.total_cardinality.0[2] == 0
            && self.total_cardinality.0[3] == 0
            && self.total_cardinality.0[4] == 0
            && self.total_cardinality.0[5] == 0
        {
            Some(self.total_cardinality.low_u128())
        } else {
            None
        }
    }

    #[inline]
    fn n_at(&self, t: usize, ell: usize) -> U384 {
        if ell >= self.l_stride {
            U384::ZERO
        } else {
            self.sub_counts[t * self.l_stride + ell]
        }
    }

    #[inline]
    fn d_at(&self, k: usize, u: usize) -> U384 {
        if u >= self.s_stride {
            U384::ZERO
        } else {
            self.dec_counts[k * self.s_stride + u]
        }
    }

    /// Unrank a **public** message-digest decoration index `r_dec < D(L, S)` into `L` chain
    /// offsets in `0..w` summing to `S` (fixed `0..w` inner loop without early break; caller passes
    /// public `H_msg(R, pk, M, ctr)` digest ranks, never secret key material).
    pub fn unrank_decorations(&self, mut r_dec: U384) -> Result<Vec<u8>, FrontierFtsError> {
        if !r_dec.ct_lt(self.decoration_cardinality) {
            return Err(FrontierFtsError::RankOutOfRange);
        }
        let l = self.params.frontier_len;
        let w = self.params.winternitz_w;
        let mut rem_sum = self.params.target_sum as u64;
        let mut out = vec![0u8; l];

        for (pos, slot) in out.iter_mut().enumerate() {
            let rem_k = l - 1 - pos;
            let mut chosen_a = 0u64;
            let mut chosen_r = r_dec;
            let mut found = false;

            for a in 0..w {
                let a_u64 = a as u64;
                let fits_sum = !ct_lt_u64(rem_sum, a_u64);
                let sub_u = ct_select_u64(fits_sum, rem_sum.wrapping_sub(a_u64), 0) as usize;
                let bucket = U384::ct_select(fits_sum, self.d_at(rem_k, sub_u), U384::ZERO);
                let in_bucket = r_dec.ct_lt(bucket);
                let take = (!found) & fits_sum & in_bucket;

                chosen_a = ct_select_u64(take, a_u64, chosen_a);
                chosen_r = U384::ct_select(take, r_dec, chosen_r);

                let (reduced, _) = r_dec.overflowing_sub(bucket);
                r_dec = U384::ct_select(!found && !in_bucket, reduced, r_dec);
                found |= take;
            }
            *slot = chosen_a as u8;
            rem_sum -= chosen_a;
            r_dec = chosen_r;
        }
        Ok(out)
    }

    /// Rank `L` public signature chain offsets in `0..w` summing to `S` back into `[0, D(L, S))`.
    pub fn rank_decorations(&self, offsets: &[u8]) -> Result<U384, FrontierFtsError> {
        let l = self.params.frontier_len;
        let w = self.params.winternitz_w;
        if offsets.len() != l {
            return Err(FrontierFtsError::InvalidDecorationSum);
        }
        let mut sum = 0usize;
        for &a in offsets {
            if (a as usize) >= w {
                return Err(FrontierFtsError::InvalidDecorationSum);
            }
            sum += a as usize;
        }
        if sum != self.params.target_sum {
            return Err(FrontierFtsError::InvalidDecorationSum);
        }

        let mut rem_sum = self.params.target_sum as u64;
        let mut rank = U384::ZERO;
        for (pos, &cur_b) in offsets.iter().enumerate() {
            let rem_k = l - 1 - pos;
            let cur_a = cur_b as u64;
            for a in 0..w {
                let a_u64 = a as u64;
                let lt_cur = ct_lt_u64(a_u64, cur_a);
                let fits = !ct_lt_u64(rem_sum, a_u64);
                let sub_u = ct_select_u64(fits, rem_sum.wrapping_sub(a_u64), 0) as usize;
                let term = U384::ct_select(lt_cur & fits, self.d_at(rem_k, sub_u), U384::ZERO);
                rank = rank.overflowing_add(term).0;
            }
            rem_sum -= cur_a;
        }
        Ok(rank)
    }

    fn unrank_subtree_frontier(
        &self,
        node: u32,
        t: usize,
        ell: usize,
        r_f: U384,
        out: &mut Vec<u32>,
    ) {
        if ell == 1 {
            out.push(node);
            return;
        }
        let half_leaves = 1usize << (t - 1);
        let i_min = 1usize.max(ell.saturating_sub(half_leaves));
        let i_max = half_leaves.min(ell - 1);

        let mut cur_r = r_f;
        let mut chosen_i = i_min as u64;
        let mut chosen_r = U384::ZERO;
        let mut chosen_right_cnt = U384::ONE;
        let mut found = false;

        // Fixed-iteration scan over all feasible left-subtree split cardinalities `i_min..=i_max`.
        for i in i_min..=i_max {
            let left_cnt = self.n_at(t - 1, i);
            let right_cnt = self.n_at(t - 1, ell - i);
            let bucket = left_cnt.wrapping_mul(right_cnt);
            let in_bucket = cur_r.ct_lt(bucket);
            let take = (!found) & in_bucket;

            chosen_i = ct_select_u64(take, i as u64, chosen_i);
            chosen_r = U384::ct_select(take, cur_r, chosen_r);
            chosen_right_cnt = U384::ct_select(take, right_cnt, chosen_right_cnt);

            let (reduced, _) = cur_r.overflowing_sub(bucket);
            cur_r = U384::ct_select(!found && !in_bucket, reduced, cur_r);
            found |= take;
        }

        let (r_left, r_right) = chosen_r.ct_divmod(chosen_right_cnt);
        let left_sz = chosen_i as usize;
        self.unrank_subtree_frontier(2 * node, t - 1, left_sz, r_left, out);
        self.unrank_subtree_frontier(2 * node + 1, t - 1, ell - left_sz, r_right, out);
    }

    /// Unrank a **public** message-digest frontier index `r_front < N(h, L)` into a sorted
    /// left-to-right binary-tree antichain frontier of `L` 1-indexed heap node indices (`v > 1`).
    pub fn unrank_frontier(&self, r_front: U384) -> Result<Vec<u32>, FrontierFtsError> {
        if !r_front.ct_lt(self.frontier_cardinality) {
            return Err(FrontierFtsError::RankOutOfRange);
        }
        let mut out = Vec::with_capacity(self.params.frontier_len);
        self.unrank_subtree_frontier(
            1,
            self.params.tree_height,
            self.params.frontier_len,
            r_front,
            &mut out,
        );
        Ok(out)
    }

    /// Validate that `frontier` is a canonical left-to-right root-to-leaf antichain partition of
    /// `[2^h, 2^{h+1})` of length `L`, and compute its exact rank `< N(h, L)`.
    pub fn rank_frontier(&self, frontier: &[u32]) -> Result<U384, FrontierFtsError> {
        if frontier.len() != self.params.frontier_len {
            return Err(FrontierFtsError::InvalidAntichainFrontier);
        }
        self.rank_subtree_slice(1, self.params.tree_height, frontier)
    }

    fn node_leaf_interval(node: u32, h: usize) -> Result<(u32, u32), FrontierFtsError> {
        if node <= 1 {
            return Err(FrontierFtsError::InvalidAntichainFrontier);
        }
        let depth = 31usize.saturating_sub(node.leading_zeros() as usize);
        if depth > h {
            return Err(FrontierFtsError::InvalidAntichainFrontier);
        }
        let shift = h - depth;
        let lo = node << shift;
        let hi = (node + 1) << shift;
        Ok((lo, hi))
    }

    fn rank_subtree_slice(
        &self,
        node: u32,
        t: usize,
        slice: &[u32],
    ) -> Result<U384, FrontierFtsError> {
        if slice.is_empty() {
            return Err(FrontierFtsError::InvalidAntichainFrontier);
        }
        if slice.len() == 1 {
            if node > 1 && slice[0] == node {
                return Ok(U384::ZERO);
            }
            return Err(FrontierFtsError::InvalidAntichainFrontier);
        }
        if t == 0 {
            return Err(FrontierFtsError::InvalidAntichainFrontier);
        }

        // Partition `slice` into nodes inside left child `2 * node` vs right child `2 * node + 1`.
        let h = self.params.tree_height;
        let depth = 31usize.saturating_sub(node.leading_zeros() as usize);
        let shift = h - depth;
        let mid_leaf = (2 * node + 1) << (shift - 1);

        let mut split_idx = 0usize;
        let mut expected_leaf = node << shift;
        for (idx, &v) in slice.iter().enumerate() {
            let (lo, hi) = Self::node_leaf_interval(v, h)?;
            if lo != expected_leaf {
                return Err(FrontierFtsError::InvalidAntichainFrontier);
            }
            expected_leaf = hi;
            if hi <= mid_leaf {
                split_idx = idx + 1;
            }
        }
        let end_leaf = (node + 1) << shift;
        if expected_leaf != end_leaf || split_idx == 0 || split_idx >= slice.len() {
            return Err(FrontierFtsError::InvalidAntichainFrontier);
        }

        let ell = slice.len();
        let half_leaves = 1usize << (t - 1);
        let i_min = 1usize.max(ell.saturating_sub(half_leaves));
        let i_max = half_leaves.min(ell - 1);
        if split_idx < i_min || split_idx > i_max {
            return Err(FrontierFtsError::InvalidAntichainFrontier);
        }

        let mut prefix_rank = U384::ZERO;
        for i in i_min..=i_max {
            let lt_split = ct_lt_u64(i as u64, split_idx as u64);
            let bucket = self.n_at(t - 1, i).wrapping_mul(self.n_at(t - 1, ell - i));
            prefix_rank = prefix_rank
                .overflowing_add(U384::ct_select(lt_split, bucket, U384::ZERO))
                .0;
        }

        let r_left = self.rank_subtree_slice(2 * node, t - 1, &slice[..split_idx])?;
        let r_right = self.rank_subtree_slice(2 * node + 1, t - 1, &slice[split_idx..])?;
        let right_cnt = self.n_at(t - 1, ell - split_idx);
        let combined = r_left.wrapping_mul(right_cnt).overflowing_add(r_right).0;
        Ok(prefix_rank.overflowing_add(combined).0)
    }

    /// Combined bijective unrank `R < M(h, w, L, S)` -> `(frontier_nodes, chain_offsets)`.
    pub fn unrank(&self, rank: U384) -> Result<(Vec<u32>, Vec<u8>), FrontierFtsError> {
        if !rank.ct_lt(self.total_cardinality) {
            return Err(FrontierFtsError::RankOutOfRange);
        }
        let (r_front, r_dec) = rank.ct_divmod(self.decoration_cardinality);
        let frontier = self.unrank_frontier(r_front)?;
        let offsets = self.unrank_decorations(r_dec)?;
        Ok((frontier, offsets))
    }

    /// Combined bijective rank `(frontier_nodes, chain_offsets)` -> `R < M(h, w, L, S)`.
    pub fn rank(&self, frontier: &[u32], offsets: &[u8]) -> Result<U384, FrontierFtsError> {
        let r_front = self.rank_frontier(frontier)?;
        let r_dec = self.rank_decorations(offsets)?;
        Ok(r_front
            .wrapping_mul(self.decoration_cardinality)
            .overflowing_add(r_dec)
            .0)
    }
}

// ============================================================================
// Chained Binary Tree Key Generation, Signing, & Verification
// ============================================================================

/// Public key for `FrontierSumFts` (`32 B` `pk_seed` + `n_trunc`-byte `root`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FrontierFtsPublicKey {
    pub profile: FrontierFtsProfile,
    pub pk_seed: [u8; 32],
    pub root: Vec<u8>,
}

/// Signing key for `FrontierSumFts` with mandatory monotonic use-budget latch, `<REDACTED>` `Debug`,
/// and `write_volatile` zeroization of both secret seeds AND cached chain states on `Drop`.
/// Durable monotonic use reservation. Implementations must sync before returning.
pub trait FtsEpochWal {
    fn uses_completed(&self, key: &[u8; 32]) -> Result<u8, FrontierFtsError>;
    fn reserve_use(&mut self, key: &[u8; 32], next: u8) -> Result<(), FrontierFtsError>;
}

#[cfg(test)]
#[derive(Clone, Copy, Debug)]
enum FrontierFaultInjection {
    ChainByteFlip { index: usize, mask: u8 },
    PreGrindRandomizerFlip { index: usize, mask: u8 },
    SkipMinimalGrindCounter,
}

pub struct FrontierFtsSigningKey {
    pub profile: FrontierFtsProfile,
    sk_seed: RedactedSecret<32>,
    sk_prf: RedactedSecret<32>,
    pub pk: FrontierFtsPublicKey,
    uses_completed: u8,
    wal: Option<alloc::boxed::Box<dyn FtsEpochWal>>,
    max_uses: u8,
    /// Write-once `(randomizer, grind_counter)` consistency record per use index.
    released_uses: Vec<Option<(Vec<u8>, u16)>>,
    /// Optional flat cache of `[X_{v, j}]` across `v in 2..2^{h+1}, j in 0..w` (`n_trunc` bytes each)
    /// wiped via `ct_zeroize_bytes` on `Drop`.
    cached_chains: Option<Vec<u8>>,
    #[cfg(test)]
    test_fault: Option<FrontierFaultInjection>,
}

impl fmt::Debug for FrontierFtsSigningKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("FrontierFtsSigningKey")
            .field("profile", &self.profile)
            .field("sk_seed", &"<REDACTED>")
            .field("sk_prf", &"<REDACTED>")
            .field("uses_completed", &self.uses_completed)
            .field("max_uses", &self.max_uses)
            .finish()
    }
}

impl Drop for FrontierFtsSigningKey {
    fn drop(&mut self) {
        if let Some(ref mut buf) = self.cached_chains {
            ct_zeroize_bytes(buf);
        }
    }
}

/// Compact `FrontierSumFts` signature (size is determined by its profile).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FrontierFtsSignature {
    pub randomizer: Vec<u8>,
    pub grind_counter: u16,
    pub chain_values: Vec<u8>,
}

impl FrontierFtsSignature {
    pub fn to_bytes(&self, profile: FrontierFtsProfile) -> Vec<u8> {
        let p = profile.params();
        let ctr_bytes = p.counter_bits.div_ceil(8);
        let mut out = Vec::with_capacity(profile.signature_bytes());
        out.extend_from_slice(&self.randomizer);
        if ctr_bytes == 2 {
            out.extend_from_slice(&self.grind_counter.to_be_bytes());
        } else if ctr_bytes == 1 {
            out.push(self.grind_counter as u8);
        }
        out.extend_from_slice(&self.chain_values);
        out
    }

    pub fn from_bytes(profile: FrontierFtsProfile, bytes: &[u8]) -> Result<Self, FrontierFtsError> {
        if bytes.len() != profile.signature_bytes() {
            return Err(FrontierFtsError::MalformedSignatureLength);
        }
        let p = profile.params();
        let n = p.node_bytes;
        let ctr_bytes = p.counter_bits.div_ceil(8);
        let randomizer = bytes[0..n].to_vec();
        let grind_counter = match ctr_bytes {
            0 => 0u16,
            1 => bytes[n] as u16,
            2 => u16::from_be_bytes([bytes[n], bytes[n + 1]]),
            _ => return Err(FrontierFtsError::MalformedSignatureLength),
        };
        let chain_values = bytes[n + ctr_bytes..].to_vec();
        Ok(Self {
            randomizer,
            grind_counter,
            chain_values,
        })
    }
}

/// Link from `epoch` to `epoch + 1`, authenticated by the current epoch's vote.
/// Epoch keys share the public profile and `pk_seed`; their secret seeds must be independent.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EpochKeyLink {
    pub epoch: u64,
    pub next_epoch_pk_root: [u8; 32],
}

/// A fixed 72-byte vote/link header followed by the profile's canonical signature.
/// With `Compact1122` the envelope is 1,194 bytes. Transport framing is additional.
/// A trusted current key and expected epoch are required: this is not a self-authenticating
/// initial key or a durable replay tracker. Persist the verified next key before advancing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RotatedEpochVote {
    pub link: EpochKeyLink,
    pub vote_digest: [u8; 32],
    pub signature: FrontierFtsSignature,
}

impl EpochKeyLink {
    fn message(&self, chain_id: &[u8; 32], vote_digest: &[u8; 32]) -> [u8; 32] {
        let mut digest = [0; 32];
        cshake256_framed_xof(
            b"QSAG.FTS.EPOCH.VOTE.V1",
            &[
                chain_id,
                &self.epoch.to_be_bytes(),
                vote_digest,
                &self.next_epoch_pk_root,
            ],
            &mut digest,
        );
        digest
    }
}

impl RotatedEpochVote {
    pub fn to_bytes(&self, profile: FrontierFtsProfile) -> Vec<u8> {
        let mut out = Vec::with_capacity(72 + profile.signature_bytes());
        out.extend_from_slice(&self.link.epoch.to_be_bytes());
        out.extend_from_slice(&self.vote_digest);
        out.extend_from_slice(&self.link.next_epoch_pk_root);
        out.extend_from_slice(&self.signature.to_bytes(profile));
        out
    }

    pub fn from_bytes(profile: FrontierFtsProfile, bytes: &[u8]) -> Result<Self, FrontierFtsError> {
        if bytes.len() != 72 + profile.signature_bytes() {
            return Err(FrontierFtsError::MalformedSignatureLength);
        }
        Ok(Self {
            link: EpochKeyLink {
                epoch: u64::from_be_bytes(core::array::from_fn(|i| bytes[i])),
                next_epoch_pk_root: core::array::from_fn(|i| bytes[40 + i]),
            },
            vote_digest: core::array::from_fn(|i| bytes[8 + i]),
            signature: FrontierFtsSignature::from_bytes(profile, &bytes[72..])?,
        })
    }

    /// Authenticate the vote and return the key for exactly `expected_epoch + 1`.
    pub fn verify(
        &self,
        current: &FrontierFtsPublicKey,
        dp: &FrontierDpTable,
        chain_id: &[u8; 32],
        expected_epoch: u64,
        expected_vote_digest: &[u8; 32],
    ) -> Result<FrontierFtsPublicKey, FrontierFtsError> {
        if current.profile.params().node_bytes != 32
            || current.profile.params().max_safe_uses != 1
            || current.root.len() != 32
            || self.link.epoch != expected_epoch
            || expected_epoch.checked_add(1).is_none()
            || &self.vote_digest != expected_vote_digest
        {
            return Err(FrontierFtsError::SignatureVerificationFailed);
        }
        verify_frontier_fts(
            current,
            dp,
            &self.link.message(chain_id, &self.vote_digest),
            &self.signature,
        )?;
        Ok(FrontierFtsPublicKey {
            profile: current.profile,
            pk_seed: current.pk_seed,
            root: self.link.next_epoch_pk_root.to_vec(),
        })
    }
}

impl FrontierFtsSigningKey {
    /// Sign the current vote and the next key together, spending the normal durable use budget.
    /// Reusing the public `pk_seed` lets the envelope carry only the next 32-byte root.
    pub fn sign_rotated_epoch_vote(
        &mut self,
        dp: &FrontierDpTable,
        chain_id: &[u8; 32],
        link: EpochKeyLink,
        vote_digest: [u8; 32],
        opt_hedging_nonce: &[u8; 32],
    ) -> Result<RotatedEpochVote, FrontierFtsError> {
        if self.profile.params().node_bytes != 32
            || self.profile.params().max_safe_uses != 1
            || link.epoch.checked_add(1).is_none()
        {
            return Err(FrontierFtsError::ProfileMismatch);
        }
        let signature = self.sign(dp, &link.message(chain_id, &vote_digest), opt_hedging_nonce)?;
        Ok(RotatedEpochVote {
            link,
            vote_digest,
            signature,
        })
    }
}

#[inline]
fn fts_leaf_start(
    pid: &[u8; 56],
    pk_seed: &[u8; 32],
    sk_seed: &[u8; 32],
    node_v: u32,
    out: &mut [u8],
) {
    let v_be = (node_v as u64).to_be_bytes();
    cshake256_framed_xof(TAG_LEAF, &[pid, pk_seed, &v_be, sk_seed], out);
}

#[inline]
fn fts_chain_step(
    pid: &[u8; 56],
    pk_seed: &[u8; 32],
    node_v: u32,
    step_j: usize,
    cur: &[u8],
    out: &mut [u8],
) {
    let v_be = (node_v as u64).to_be_bytes();
    let j_be = (step_j as u64).to_be_bytes();
    cshake256_framed_xof(TAG_CHAIN, &[pid, pk_seed, &v_be, &j_be, cur], out);
}

#[inline]
fn fts_merge(
    pid: &[u8; 56],
    pk_seed: &[u8; 32],
    node_v: u32,
    left_end: &[u8],
    right_end: &[u8],
    out: &mut [u8],
) {
    let v_be = (node_v as u64).to_be_bytes();
    cshake256_framed_xof(TAG_MERGE, &[pid, pk_seed, &v_be, left_end, right_end], out);
}

fn prehash_message_256(pid: &[u8; 56], pk_seed: &[u8; 32], pk_root: &[u8], msg: &[u8]) -> [u8; 32] {
    let mut out = [0u8; 32];
    cshake256_framed_xof(TAG_MSG_PRE, &[pid, pk_seed, pk_root, msg], &mut out);
    out
}

fn squeeze_target_index(
    pid: &[u8; 56],
    pk_seed: &[u8; 32],
    pk_root: &[u8],
    randomizer: &[u8],
    msg_digest32: &[u8; 32],
    counter: u16,
    index_bits: usize,
) -> U384 {
    let ctr_be = counter.to_be_bytes();
    let needed = index_bits.div_ceil(8);
    let mut buf = [0u8; 48];
    cshake256_framed_xof(
        TAG_HMSG,
        &[pid, &ctr_be, pk_seed, pk_root, randomizer, msg_digest32],
        &mut buf[..needed],
    );
    let val = U384::from_top_bits_be(&buf[..needed], index_bits);
    ct_zeroize_bytes(&mut buf);
    val
}

/// Eight equal-shape framed cSHAKE messages. Every length and address is public;
/// the backend packs these states into KeccakState8x on AVX-512 hosts.
fn framed_hash8<B: AcceleratorBackend, const F: usize>(
    tag: &[u8],
    frames: [[&[u8]; F]; 8],
    out: &mut [[u8; 32]; 8],
    accel: &B,
) {
    const RATE: usize = 136;
    assert!(tag.len() < 32);
    let mut messages = [[0u8; 512]; 8];
    let mut len = 0;
    for (message, fields) in messages.iter_mut().zip(frames) {
        // bytepad(encode_string("") || encode_string(tag), 136).
        message[..6].copy_from_slice(&[1, 136, 1, 0, 1, (tag.len() * 8) as u8]);
        message[6..6 + tag.len()].copy_from_slice(tag);
        let mut cursor = RATE;
        message[cursor..cursor + 8].copy_from_slice(&(F as u64).to_le_bytes());
        cursor += 8;
        for field in fields {
            message[cursor..cursor + 8].copy_from_slice(&(field.len() as u64).to_le_bytes());
            cursor += 8;
            message[cursor..cursor + field.len()].copy_from_slice(field);
            cursor += field.len();
        }
        if len != 0 {
            assert_eq!(len, cursor);
        }
        len = cursor;
        message[cursor] ^= 0x04;
        message[(cursor / RATE + 1) * RATE - 1] ^= 0x80;
    }
    let mut states = [[0u64; 25]; 8];
    for block in 0..=len / RATE {
        for (state, message) in states.iter_mut().zip(&messages) {
            for (word, bytes) in state
                .iter_mut()
                .zip(message[block * RATE..][..RATE].as_chunks::<8>().0.iter())
            {
                *word ^= u64::from_le_bytes(*bytes);
            }
        }
        accel.batch_keccak_f1600(&mut states);
    }
    for (output, state) in out.iter_mut().zip(&states) {
        for (bytes, word) in output.as_chunks_mut::<8>().0.iter_mut().zip(state) {
            bytes.copy_from_slice(&word.to_le_bytes());
        }
    }
    for message in &mut messages {
        ct_zeroize_bytes(message);
    }
    for state in &mut states {
        qsag_accel::ct::ct_zeroize_u64s(state);
    }
}

impl FrontierFtsSigningKey {
    /// Generate a `FrontierSumFts` keypair from `(sk_seed, sk_prf, pk_seed)`.
    /// When `cache_tree == true`, caches chain values so signing runs in `< 1 ms` with constant-time
    /// slot selection across chain offsets `0..w`.
    pub fn keygen<B: AcceleratorBackend>(
        profile: FrontierFtsProfile,
        sk_seed: [u8; 32],
        sk_prf: [u8; 32],
        pk_seed: [u8; 32],
        cache_tree: bool,
        accel: &B,
    ) -> Self {
        let p = profile.params();
        let pid = profile.pid_bytes();
        let n = p.node_bytes;
        let w = p.winternitz_w;
        let h = p.tree_height;
        let total_nodes = 1usize << (h + 1);

        // Compute bottom-up: if caching, store `[total_nodes * w * n]`; else store endpoints `[total_nodes * n]`.
        let mut endpoints = vec![0u8; total_nodes * n];
        let mut cache = if cache_tree {
            Some(vec![0u8; total_nodes * w * n])
        } else {
            None
        };

        // Finish every level before its parents, batching eight independent chains.
        let mut cur = [[0u8; 32]; 8];
        for depth in (1..=h).rev() {
            let begin = 1usize << depth;
            let end = 1usize << (depth + 1);
            for base in (begin..end).step_by(8) {
                let count = (end - base).min(8);
                // Dummy lanes duplicate a valid node; they never enter the tree.
                let nodes: [usize; 8] = core::array::from_fn(|i| base + i.min(count - 1));
                let indices = nodes.map(|v| (v as u64).to_be_bytes());
                if depth == h {
                    framed_hash8(
                        TAG_LEAF,
                        core::array::from_fn(|i| [pid.as_slice(), &pk_seed, &indices[i], &sk_seed]),
                        &mut cur,
                        accel,
                    );
                } else {
                    framed_hash8(
                        TAG_MERGE,
                        core::array::from_fn(|i| {
                            let v = nodes[i];
                            [
                                pid.as_slice(),
                                &pk_seed,
                                &indices[i],
                                &endpoints[2 * v * n..(2 * v + 1) * n],
                                &endpoints[(2 * v + 1) * n..(2 * v + 2) * n],
                            ]
                        }),
                        &mut cur,
                        accel,
                    );
                }
                for step in 0..w {
                    if let Some(ref mut cbuf) = cache {
                        for i in 0..count {
                            let off = (nodes[i] * w + step) * n;
                            cbuf[off..off + n].copy_from_slice(&cur[i][..n]);
                        }
                    }
                    if step + 1 < w {
                        let j_be = (step as u64).to_be_bytes();
                        let mut next = [[0u8; 32]; 8];
                        framed_hash8(
                            TAG_CHAIN,
                            core::array::from_fn(|i| {
                                [pid.as_slice(), &pk_seed, &indices[i], &j_be, &cur[i][..n]]
                            }),
                            &mut next,
                            accel,
                        );
                        cur = next;
                        for lane in &mut next {
                            ct_zeroize_bytes(lane);
                        }
                    }
                }
                for i in 0..count {
                    endpoints[nodes[i] * n..(nodes[i] + 1) * n].copy_from_slice(&cur[i][..n]);
                }
            }
        }

        let mut root = vec![0u8; n];
        fts_merge(
            &pid,
            &pk_seed,
            1,
            &endpoints[2 * n..3 * n],
            &endpoints[3 * n..4 * n],
            &mut root,
        );

        for lane in &mut cur {
            ct_zeroize_bytes(lane);
        }
        ct_zeroize_bytes(&mut endpoints);

        let pk = FrontierFtsPublicKey {
            profile,
            pk_seed,
            root,
        };
        Self {
            profile,
            sk_seed: RedactedSecret::new(sk_seed),
            sk_prf: RedactedSecret::new(sk_prf),
            pk,
            uses_completed: 0,
            wal: None,
            max_uses: p.max_safe_uses,
            released_uses: vec![None; p.max_safe_uses as usize],
            cached_chains: cache,
            #[cfg(test)]
            test_fault: None,
        }
    }

    /// Identity binds the profile and complete public key to the use journal.
    pub fn wal_key(&self) -> [u8; 32] {
        qsag_accel::keccak::cshake256_framed_32(
            b"QSAG.FRONTIER.WAL.V1",
            &[&self.profile.pid_bytes(), &self.pk.pk_seed, &self.pk.root],
        )
    }
    pub fn attach_wal(
        mut self,
        mut wal: alloc::boxed::Box<dyn FtsEpochWal>,
    ) -> Result<Self, FrontierFtsError> {
        let used = wal.uses_completed(&self.wal_key())?;
        if used > self.max_uses {
            return Err(FrontierFtsError::PersistenceFailed);
        }
        // A reservation may have reached the vault before the WAL. Burn the gap;
        // never roll either monotonic counter backward after recovery.
        for next in used..self.uses_completed {
            wal.reserve_use(&self.wal_key(), next + 1)?;
        }
        self.uses_completed = used.max(self.uses_completed);
        self.wal = Some(wal);
        Ok(self)
    }

    pub const fn uses_remaining(&self) -> u8 {
        self.max_uses.saturating_sub(self.uses_completed)
    }

    /// Number of signatures this key has already released.
    pub const fn uses_completed(&self) -> u8 {
        self.uses_completed
    }

    /// Restore the use counter of a key regenerated from its seeds, from durable storage.
    /// The counter only moves forward and never past the profile's safe-use budget.
    pub fn resume_at(mut self, uses_completed: u8) -> Result<Self, FrontierFtsError> {
        if uses_completed < self.uses_completed || uses_completed > self.max_uses {
            return Err(FrontierFtsError::UseBudgetExhausted);
        }
        self.uses_completed = uses_completed;
        Ok(self)
    }

    /// Sign `msg` using mandatory `SK.prf`-derived randomized `R`, 256-bit message pre-binding,
    /// and strict monotonic use-budget enforcement (`uses_completed < max_uses`).
    pub fn sign(
        &mut self,
        dp: &FrontierDpTable,
        msg: &[u8],
        opt_hedging_nonce: &[u8; 32],
    ) -> Result<FrontierFtsSignature, FrontierFtsError> {
        if dp.params != self.profile.params() {
            return Err(FrontierFtsError::ProfileMismatch);
        }
        if self.uses_completed >= self.max_uses {
            return Err(FrontierFtsError::UseBudgetExhausted);
        }
        // Latch use counter BEFORE computing or releasing any signature material!
        let use_seq = self.uses_completed;
        self.uses_completed += 1;
        let key = self.wal_key();
        if let Some(wal) = &mut self.wal {
            if wal.reserve_use(&key, self.uses_completed).is_err() {
                self.uses_completed = self.max_uses;
                return Err(FrontierFtsError::PersistenceFailed);
            }
        } else if !cfg!(test) {
            self.uses_completed = self.max_uses;
            return Err(FrontierFtsError::PersistenceFailed);
        }

        let p = self.profile.params();
        let pid = self.profile.pid_bytes();
        let n = p.node_bytes;
        let w = p.winternitz_w;

        let msg_digest32 = prehash_message_256(&pid, &self.pk.pk_seed, &self.pk.root, msg);
        let seq_bytes = [use_seq];
        let mut randomizer = vec![0u8; n];
        cshake256_framed_xof(
            TAG_RAND,
            &[
                &pid,
                self.sk_prf.expose(),
                &self.pk.pk_seed,
                &self.pk.root,
                opt_hedging_nonce,
                &seq_bytes,
                &msg_digest32,
            ],
            &mut randomizer,
        );
        #[cfg(test)]
        if let Some(FrontierFaultInjection::PreGrindRandomizerFlip { index, mask }) =
            self.test_fault
            && let Some(slot) = randomizer.get_mut(index)
        {
            *slot ^= mask;
        }

        let max_ctr: u32 = 1u32 << p.counter_bits;
        let mut found_ctr = None;
        let mut target_rank = U384::ZERO;
        #[cfg(test)]
        let mut skipped_minimal = false;
        for ctr in 0..max_ctr {
            let cand = squeeze_target_index(
                &pid,
                &self.pk.pk_seed,
                &self.pk.root,
                &randomizer,
                &msg_digest32,
                ctr as u16,
                p.index_bits,
            );
            if cand.ct_lt(dp.total_cardinality) {
                #[cfg(test)]
                if matches!(
                    self.test_fault,
                    Some(FrontierFaultInjection::SkipMinimalGrindCounter)
                ) && !skipped_minimal
                {
                    skipped_minimal = true;
                    continue;
                }
                found_ctr = Some(ctr as u16);
                target_rank = cand;
                break;
            }
        }
        let grind_counter = found_ctr.ok_or(FrontierFtsError::GrindingExhausted)?;
        let (frontier, offsets) = dp.unrank(target_rank)?;

        let mut chain_values = vec![0u8; p.frontier_len * n];
        if let Some(ref cbuf) = self.cached_chains {
            // Constant-time scan across all `j in 0..w` for each frontier node `v`.
            let mut slot_val = [0u8; 32];
            for (idx, (&v, &a_pos)) in frontier.iter().zip(offsets.iter()).enumerate() {
                slot_val.fill(0);
                for j in 0..w {
                    let match_j = ct_eq_u64(j as u64, a_pos as u64);
                    let src_off = ((v as usize) * w + j) * n;
                    ct_conditional_assign_bytes(
                        match_j,
                        &mut slot_val[..n],
                        &cbuf[src_off..src_off + n],
                    )
                    .map_err(|_| FrontierFtsError::ProfileMismatch)?;
                }
                chain_values[idx * n..(idx + 1) * n].copy_from_slice(&slot_val[..n]);
            }
            ct_zeroize_bytes(&mut slot_val);
        } else {
            // Uncached subtree evaluation for arbitrary frontier nodes.
            let mut tmp = [0u8; 32];
            for (idx, (&v, &a_pos)) in frontier.iter().zip(offsets.iter()).enumerate() {
                self.eval_node_at_pos(&pid, v, a_pos as usize, &mut tmp[..n])?;
                chain_values[idx * n..(idx + 1) * n].copy_from_slice(&tmp[..n]);
            }
            ct_zeroize_bytes(&mut tmp);
        }
        #[cfg(test)]
        if let Some(FrontierFaultInjection::ChainByteFlip { index, mask }) = self.test_fault
            && let Some(slot) = chain_values.get_mut(index)
        {
            *slot ^= mask;
        }

        let sig = FrontierFtsSignature {
            randomizer,
            grind_counter,
            chain_values,
        };
        // Mandatory verify-before-release + pre-grind randomizer & canonical counter check!
        self.verify_before_release(dp, use_seq, msg, opt_hedging_nonce, &sig)?;
        Ok(sig)
    }

    fn verify_before_release(
        &mut self,
        dp: &FrontierDpTable,
        use_seq: u8,
        msg: &[u8],
        opt_hedging_nonce: &[u8; 32],
        sig: &FrontierFtsSignature,
    ) -> Result<(), FrontierFtsError> {
        let p = self.profile.params();
        let pid = self.profile.pid_bytes();
        let n = p.node_bytes;
        let mut expected_digest = prehash_message_256(&pid, &self.pk.pk_seed, &self.pk.root, msg);
        let seq_bytes = [use_seq];
        let mut expected_randomizer = vec![0u8; n];
        cshake256_framed_xof(
            TAG_RAND,
            &[
                &pid,
                self.sk_prf.expose(),
                &self.pk.pk_seed,
                &self.pk.root,
                opt_hedging_nonce,
                &seq_bytes,
                &expected_digest,
            ],
            &mut expected_randomizer,
        );
        let rand_ok = ct_eq_bytes(&sig.randomizer, &expected_randomizer);
        let max_ctr: u32 = 1u32 << p.counter_bits;
        let mut canonical_ctr = None;
        for ctr in 0..max_ctr {
            let cand = squeeze_target_index(
                &pid,
                &self.pk.pk_seed,
                &self.pk.root,
                &expected_randomizer,
                &expected_digest,
                ctr as u16,
                p.index_bits,
            );
            if cand.ct_lt(dp.total_cardinality) {
                canonical_ctr = Some(ctr as u16);
                break;
            }
        }
        ct_zeroize_bytes(&mut expected_digest);
        ct_zeroize_bytes(&mut expected_randomizer);
        let Some(expected_ctr) = canonical_ctr else {
            return Err(FrontierFtsError::SignatureVerificationFailed);
        };
        if !rand_ok || !ct_eq_u64(sig.grind_counter as u64, expected_ctr as u64) {
            return Err(FrontierFtsError::SignatureVerificationFailed);
        }
        let Some(slot) = self.released_uses.get_mut(use_seq as usize) else {
            return Err(FrontierFtsError::SignatureVerificationFailed);
        };
        if let Some((prev_rand, prev_ctr)) = slot.as_ref()
            && (!ct_eq_bytes(&sig.randomizer, prev_rand) || sig.grind_counter != *prev_ctr)
        {
            return Err(FrontierFtsError::SignatureVerificationFailed);
        }
        verify_frontier_fts(&self.pk, dp, msg, sig)?;
        let roundtrip =
            FrontierFtsSignature::from_bytes(self.profile, &sig.to_bytes(self.profile))?;
        if roundtrip != *sig {
            return Err(FrontierFtsError::SignatureVerificationFailed);
        }
        *slot = Some((sig.randomizer.clone(), sig.grind_counter));
        Ok(())
    }

    fn eval_node_at_pos(
        &self,
        pid: &[u8; 56],
        v: u32,
        target_pos: usize,
        out: &mut [u8],
    ) -> Result<(), FrontierFtsError> {
        let p = self.profile.params();
        let n = p.node_bytes;
        let w = p.winternitz_w;
        let first_leaf = 1u32 << p.tree_height;
        if out.len() != n {
            return Err(FrontierFtsError::ProfileMismatch);
        }
        let mut cur = [0u8; 32];
        let mut next = [0u8; 32];
        if v >= first_leaf {
            fts_leaf_start(
                pid,
                &self.pk.pk_seed,
                self.sk_seed.expose(),
                v,
                &mut cur[..n],
            );
        } else {
            let mut l_end = [0u8; 32];
            let mut r_end = [0u8; 32];
            self.eval_node_at_pos(pid, 2 * v, w - 1, &mut l_end[..n])?;
            self.eval_node_at_pos(pid, 2 * v + 1, w - 1, &mut r_end[..n])?;
            fts_merge(
                pid,
                &self.pk.pk_seed,
                v,
                &l_end[..n],
                &r_end[..n],
                &mut cur[..n],
            );
            ct_zeroize_bytes(&mut l_end);
            ct_zeroize_bytes(&mut r_end);
        }
        // Fixed `w - 1` iterations with constant-time conditional capture at `step == target_pos`!
        out.copy_from_slice(&cur[..n]);
        for step in 0..(w - 1) {
            fts_chain_step(pid, &self.pk.pk_seed, v, step, &cur[..n], &mut next[..n]);
            cur[..n].copy_from_slice(&next[..n]);
            let hit = ct_eq_u64((step + 1) as u64, target_pos as u64);
            ct_conditional_assign_bytes(hit, out, &cur[..n])
                .map_err(|_| FrontierFtsError::ProfileMismatch)?;
        }
        ct_zeroize_bytes(&mut cur);
        ct_zeroize_bytes(&mut next);
        Ok(())
    }
}

/// Verify a `FrontierSumFtsSignature` against `pk` and `msg`.
pub fn verify_frontier_fts(
    pk: &FrontierFtsPublicKey,
    dp: &FrontierDpTable,
    msg: &[u8],
    sig: &FrontierFtsSignature,
) -> Result<(), FrontierFtsError> {
    let p = pk.profile.params();
    if dp.params != p {
        return Err(FrontierFtsError::SignatureVerificationFailed);
    }
    let n = p.node_bytes;
    let w = p.winternitz_w;
    if sig.randomizer.len() != n || sig.chain_values.len() != p.frontier_len * n {
        return Err(FrontierFtsError::MalformedSignatureLength);
    }
    if (sig.grind_counter as u32) >= (1u32 << p.counter_bits) {
        return Err(FrontierFtsError::SignatureVerificationFailed);
    }

    let pid = pk.profile.pid_bytes();
    let msg_digest32 = prehash_message_256(&pid, &pk.pk_seed, &pk.root, msg);
    let target_rank = squeeze_target_index(
        &pid,
        &pk.pk_seed,
        &pk.root,
        &sig.randomizer,
        &msg_digest32,
        sig.grind_counter,
        p.index_bits,
    );
    if !target_rank.ct_lt(dp.total_cardinality) {
        return Err(FrontierFtsError::SignatureVerificationFailed);
    }

    let (frontier, offsets) = dp.unrank(target_rank)?;

    // Advance every frontier node `v_i` from `a_i` to `w - 1`, then fold sibling pairs `(2u, 2u+1)` up to `root`.
    let mut stack: Vec<(u32, [u8; 32])> = Vec::with_capacity(p.frontier_len);
    let mut cur = [0u8; 32];
    let mut next = [0u8; 32];

    for (idx, (&v, &a_pos)) in frontier.iter().zip(offsets.iter()).enumerate() {
        cur[..n].copy_from_slice(&sig.chain_values[idx * n..(idx + 1) * n]);
        for step in (a_pos as usize)..(w - 1) {
            fts_chain_step(&pid, &pk.pk_seed, v, step, &cur[..n], &mut next[..n]);
            cur[..n].copy_from_slice(&next[..n]);
        }
        stack.push((v, cur));

        while stack.len() >= 2 {
            let len = stack.len();
            let left_v = stack[len - 2].0;
            let right_v = stack[len - 1].0;
            if (left_v & 1) == 0 && right_v == left_v + 1 {
                let r_end = stack[len - 1].1;
                let l_end = stack[len - 2].1;
                stack.truncate(len - 2);
                let parent_v = left_v >> 1;
                fts_merge(
                    &pid,
                    &pk.pk_seed,
                    parent_v,
                    &l_end[..n],
                    &r_end[..n],
                    &mut cur[..n],
                );
                if parent_v > 1 {
                    for step in 0..(w - 1) {
                        fts_chain_step(
                            &pid,
                            &pk.pk_seed,
                            parent_v,
                            step,
                            &cur[..n],
                            &mut next[..n],
                        );
                        cur[..n].copy_from_slice(&next[..n]);
                    }
                }
                stack.push((parent_v, cur));
            } else {
                break;
            }
        }
    }

    if stack.len() != 1 || stack[0].0 != 1 {
        return Err(FrontierFtsError::SignatureVerificationFailed);
    }
    if !ct_eq_bytes(&stack[0].1[..n], &pk.root) {
        return Err(FrontierFtsError::SignatureVerificationFailed);
    }
    Ok(())
}

impl core::fmt::Display for FrontierFtsError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{self:?}")
    }
}
impl core::error::Error for FrontierFtsError {}

#[cfg(test)]
mod rank_domain_tests {
    use super::*;

    #[test]
    fn full_digest_domain_is_injective_and_constant_sum() {
        let profile = FrontierFtsProfile::Full256Bit;
        let dp = FrontierDpTable::build(profile);
        let maximum = U384::from_top_bits_be(&[255; 32], 256);
        assert!(maximum.ct_lt(dp.total_cardinality));
        assert_eq!(profile.params().index_bits, 256);
        let base = dp.unrank(U384::ZERO).unwrap();
        let pid = profile.pid_bytes();
        let base_digest_rank =
            squeeze_target_index(&pid, &[1; 32], &[2; 32], &[3; 32], &[0; 32], 0, 256);

        for bit in 0..256 {
            let mut digest = [0; 32];
            digest[bit / 8] = 1 << (bit % 8);
            let rank = U384::from_top_bits_be(&digest, 256);
            let message_rank =
                squeeze_target_index(&pid, &[1; 32], &[2; 32], &[3; 32], &digest, 0, 256);
            assert_ne!(message_rank, base_digest_rank);
            assert_eq!(
                message_rank,
                squeeze_target_index(&pid, &[1; 32], &[2; 32], &[3; 32], &digest, 0, 256)
            );
            assert_ne!(
                dp.unrank(message_rank).unwrap(),
                dp.unrank(base_digest_rank).unwrap()
            );

            let coordinates = dp.unrank(rank).unwrap();
            assert_ne!(coordinates, base);
            assert_eq!(dp.rank(&coordinates.0, &coordinates.1).unwrap(), rank);
            if coordinates.0 == base.0 {
                assert!(coordinates.1.iter().zip(&base.1).any(|(a, b)| a < b));
                assert!(coordinates.1.iter().zip(&base.1).any(|(a, b)| a > b));
            }
        }
    }

    #[test]
    fn verify_before_release_blocks_chain_randomizer_and_grind_counter_faults() {
        use qsag_accel::CpuReferenceBackend;

        let profile = FrontierFtsProfile::Compact514;
        let dp = FrontierDpTable::build(profile);
        let msg = b"frontier fault-grafting regression";
        let hedge = [0x42u8; 32];

        // 1. Chain bit-flip fault aborts before release while burning the use slot.
        let mut sk_chain = FrontierFtsSigningKey::keygen(
            profile,
            [1u8; 32],
            [2u8; 32],
            [3u8; 32],
            true,
            &CpuReferenceBackend::new(),
        );
        sk_chain.test_fault = Some(FrontierFaultInjection::ChainByteFlip {
            index: 0,
            mask: 0x01,
        });
        assert_eq!(
            sk_chain.sign(&dp, msg, &hedge),
            Err(FrontierFtsError::SignatureVerificationFailed)
        );
        assert_eq!(sk_chain.uses_completed(), 1);

        // 2. Pre-grind randomizer bit-flip produces a self-consistent signature that WOULD pass
        //    bare `verify_frontier_fts`, yet `sign` deterministically aborts!
        let mut sk_rand = FrontierFtsSigningKey::keygen(
            profile,
            [1u8; 32],
            [2u8; 32],
            [3u8; 32],
            true,
            &CpuReferenceBackend::new(),
        );
        sk_rand.test_fault = Some(FrontierFaultInjection::PreGrindRandomizerFlip {
            index: 0,
            mask: 0x80,
        });
        assert_eq!(
            sk_rand.sign(&dp, msg, &hedge),
            Err(FrontierFtsError::SignatureVerificationFailed)
        );
        assert_eq!(sk_rand.uses_completed(), 1);

        // 3. Skipping the minimal valid grinding counter also produces a valid codeword under
        //    bare `verify_frontier_fts`, yet `sign` deterministically aborts!
        let mut sk_ctr = FrontierFtsSigningKey::keygen(
            profile,
            [1u8; 32],
            [2u8; 32],
            [3u8; 32],
            true,
            &CpuReferenceBackend::new(),
        );
        sk_ctr.test_fault = Some(FrontierFaultInjection::SkipMinimalGrindCounter);
        assert_eq!(
            sk_ctr.sign(&dp, msg, &hedge),
            Err(FrontierFtsError::SignatureVerificationFailed)
        );
        assert_eq!(sk_ctr.uses_completed(), 1);

        // 4. Write-once per-use `(randomizer, grind_counter)` consistency rejects conflicting release.
        let mut sk_cache = FrontierFtsSigningKey::keygen(
            profile,
            [1u8; 32],
            [2u8; 32],
            [3u8; 32],
            true,
            &CpuReferenceBackend::new(),
        );
        sk_cache.released_uses[0] = Some((vec![0xFF; profile.params().node_bytes], 7));
        assert_eq!(
            sk_cache.sign(&dp, msg, &hedge),
            Err(FrontierFtsError::SignatureVerificationFailed)
        );
    }
}

#[path = "frontier_batch.rs"]
mod batch;
pub use batch::{
    FrontierVerifyInput, RotatedEpochVerifyInput, verify_frontier_fts_batch,
    verify_rotated_epoch_votes_batch,
};

#[cfg(test)]
mod batch_hash_tests {
    use super::*;
    #[test]
    fn eight_lane_hash_matches_scalar_for_every_node_size_and_domain() {
        let pid = FrontierFtsProfile::Compact1122.pid_bytes();
        let seed = [73; 32];
        let indices: [[u8; 8]; 8] = core::array::from_fn(|i| (i as u64).to_be_bytes());
        for tag in [TAG_LEAF, TAG_MERGE, TAG_CHAIN] {
            for n in [16, 32] {
                let frames = core::array::from_fn(|i| {
                    [
                        pid.as_slice(),
                        &seed[..n],
                        &indices[i],
                        &seed[..n],
                        &seed[..n],
                    ]
                });
                let mut actual = [[0; 32]; 8];
                framed_hash8(tag, frames, &mut actual, &qsag_accel::CpuReferenceBackend);
                for (fields, output) in frames.iter().zip(actual) {
                    let mut expected = [0; 32];
                    cshake256_framed_xof(tag, fields, &mut expected);
                    assert_eq!(output, expected);
                }
            }
        }
    }
}
