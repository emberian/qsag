//! `WOTS+C` (`w = 4`) and the chain sweep shared by `Baggy` and `Jorts`.
//!
//! * **Encoding.** The signed value is a 256-bit digest read as 128 base-4 digits. A digest
//!   is valid when its last `zero_digits` digits are zero and its first `chains` digits sum
//!   to `target_sum`; the signer finds a valid digest by counting a public grind counter up
//!   from zero. Only the first `chains` digits have chains. Because the sum is fixed, no
//!   other valid digest dominates a signed one digit by digit, so no checksum chains are
//!   needed. The preset [`WotsCParams::V128`] signs all 128 digits and forces none to zero:
//!   a forgery on a signed leaf needs a second preimage of the full 256-bit digest (about
//!   `2^128` quantum work), as in the [`crate::tsw_baggy::PqHashParams`] presets, and the
//!   grind only has to hit the sum.
//! * **Hashing.** Chains use the single-block tweakable hashes of [`crate::tsw_baggy`]
//!   (`PRF`, then `F` per step), so every chain step is one `Keccak-f[1600]`.
//! * **Sweep.** [`Sweep`] evaluates any number of chains (and FORS leaves) level by level on
//!   the 256-lane engine: one wave per 256 lanes, every lane of a level in parallel, and all
//!   intermediate nodes kept shared until the caller opens the ones it is entitled to.

use alloc::vec;
use alloc::vec::Vec;

use qsag_asm::KeccakState4x;

use crate::keccak_mpc::{
    TSW_F_SECRET_OFFSET, TSW_PRF_SECRET_OFFSET, TSW_SUITE_MIDSTATE, tsw_secret32_frame,
    tsw_secret32_offset,
};
use crate::rss256::{
    LANES, Plane, Rss256Engine, Rss256Error, SharedDigest256, SharedState256, active_lane_mask,
};
use crate::sponge::keccak::SHAKE256_RATE_BYTES;
use crate::tsw_baggy::{
    AdrsKind, Cshake256Suite, HashAdrs, PqSecretKey, TAG_PRF, TAG_TH_F, th_node_h, th_tweak_tl,
    wots_chain_steps, wots_secret_base,
};

/// Winternitz parameter.
pub const WOTS_W: usize = 4;
/// Chain length in hash steps (`w - 1`).
pub const WOTS_STEPS: usize = WOTS_W - 1;
/// Base-4 digits in the 256-bit digest.
pub const WOTS_DIGEST_DIGITS: usize = 128;

/// `WOTS+C` parameters for `w = 4`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WotsCParams {
    /// Signed chains (`v`).
    pub chains: usize,
    /// Trailing digest digits forced to zero by grinding.
    pub zero_digits: usize,
    /// Required sum of the first `chains` digits.
    pub target_sum: usize,
}

impl WotsCParams {
    /// `v = 128` chains over the whole digest, no forced-zero digits, target sum 192: the
    /// most likely sum of 128 uniform base-4 digits (probability about 0.0315), so the grind
    /// takes about 32 public hashes on average.
    pub const V128: Self = Self {
        chains: 128,
        zero_digits: 0,
        target_sum: 192,
    };

    pub const fn is_well_formed(&self) -> bool {
        self.chains >= 1
            && self.chains + self.zero_digits == WOTS_DIGEST_DIGITS
            && self.target_sum <= WOTS_STEPS * self.chains
    }

    /// Digits of `hash` if it is a valid `WOTS+C` digest for these parameters. Digit `i` is
    /// bits `7 - 2 (i % 4)` and `6 - 2 (i % 4)` of byte `i / 4`, the base-4 reading of
    /// [`crate::tsw_baggy::extract_base_w_digits_checked`]. Nothing is allocated for an invalid digest.
    pub fn digits(&self, hash: &[u8; 32]) -> Option<Vec<u8>> {
        let digit = |i: usize| (hash[i / 4] >> (6 - 2 * (i % 4))) & 3;
        if (self.chains..WOTS_DIGEST_DIGITS).any(|i| digit(i) != 0) {
            return None;
        }
        let sum: usize = (0..self.chains).map(|i| usize::from(digit(i))).sum();
        if sum != self.target_sum {
            return None;
        }
        Some((0..self.chains).map(digit).collect())
    }
}

/// Four-way evaluator of the public tweakable hash
/// `th_call(Cshake256Suite, tag, pk_seed, adrs, [value])` over a running `adrs.hash_step`
/// counter. The frame is a single rate block, so each candidate costs one permutation lane.
pub struct DigestGrinder {
    base: [u64; 25],
    step_off: usize,
}

impl DigestGrinder {
    /// `adrs.hash_step` is replaced by the grind counter.
    pub fn new(tag: &[u8], pk_seed: &[u8; 32], adrs: &HashAdrs, value: &[u8; 32]) -> Self {
        let zero_step = HashAdrs {
            hash_step: 0,
            ..*adrs
        };
        let mut frame = tsw_secret32_frame(tag, pk_seed, &zero_step);
        let value_off = tsw_secret32_offset(tag.len());
        frame[value_off..value_off + 32].copy_from_slice(value);
        let mut base = TSW_SUITE_MIDSTATE;
        for (i, byte) in frame.iter().enumerate() {
            base[i / 8] ^= u64::from(*byte) << (8 * (i % 8));
        }
        // Frame layout: count, tag field, pk_seed field, then the length byte and 32 bytes of
        // the address; `hash_step` is its last four bytes, big-endian.
        let adrs_off = 1 + (1 + tag.len()) + (1 + 32) + 1;
        Self {
            base,
            step_off: adrs_off + 28,
        }
    }

    /// Digests for counters `ctr, ctr + 1, ctr + 2, ctr + 3` (wrapping).
    pub fn hash4(&self, ctr: u32) -> [[u8; 32]; 4] {
        let mut st = KeccakState4x::default();
        for (lane, row) in st.0.iter_mut().enumerate() {
            *row = [self.base[lane]; 4];
        }
        for (i, counter) in core::array::from_fn::<_, 4, _>(|i| ctr.wrapping_add(i as u32)).iter().enumerate() {
            let step = counter.to_be_bytes();
            for (k, byte) in step.iter().enumerate() {
                let pos = self.step_off + k;
                st.0[pos / 8][i] ^= u64::from(*byte) << (8 * (pos % 8));
            }
        }
        qsag_asm::keccak_f1600_x4(&mut st);
        core::array::from_fn(|i| {
            let mut out = [0u8; 32];
            for (chunk, lane) in out.as_chunks_mut::<8>().0.iter_mut().zip(&st.0[..4]) {
                *chunk = lane[i].to_le_bytes();
            }
            out
        })
    }

    /// Smallest counter below `max_grind` whose digest is valid, with its digits.
    pub fn grind(&self, params: &WotsCParams, max_grind: u32) -> Option<(u32, Vec<u8>)> {
        let mut ctr = 0u32;
        while ctr < max_grind {
            for (i, hash) in self.hash4(ctr).iter().enumerate() {
                let c = ctr.wrapping_add(i as u32);
                if c < max_grind
                    && let Some(digits) = params.digits(hash)
                {
                    return Some((c, digits));
                }
            }
            ctr = ctr.saturating_add(4);
        }
        None
    }

    /// Digits for one given counter, if valid.
    pub fn digits_at(&self, params: &WotsCParams, ctr: u32) -> Option<Vec<u8>> {
        params.digits(&self.hash4(ctr)[0])
    }
}

/// Address of the `WOTS+C` digest of the value signed by leaf `(layer, tree, key_pair)`.
pub const fn wots_c_digest_adrs(layer: u32, tree: u64, key_pair: u32) -> HashAdrs {
    HashAdrs {
        layer,
        tree,
        kind: AdrsKind::WotsHash,
        key_pair,
        chain_idx: u32::MAX,
        hash_step: 0,
    }
}

/// Recompute a leaf's compressed public key from signature nodes and their digits.
pub fn wots_c_recover_pk(
    params: &WotsCParams,
    pk_seed: &[u8; 32],
    layer: u32,
    tree: u64,
    key_pair: u32,
    digits: &[u8],
    sig_chains: &[[u8; 32]],
) -> Option<[u8; 32]> {
    if digits.len() != params.chains || sig_chains.len() != params.chains {
        return None;
    }
    let mut endpoints = Vec::with_capacity(params.chains);
    for (chain, (digit, node)) in digits.iter().zip(sig_chains).enumerate() {
        let d = usize::from(*digit);
        if d > WOTS_STEPS {
            return None;
        }
        endpoints.push(wots_chain_steps(
            Cshake256Suite,
            pk_seed,
            layer,
            tree,
            key_pair,
            chain as u32,
            d as u32,
            WOTS_STEPS - d,
            *node,
        ));
    }
    Some(wots_c_leaf(pk_seed, layer, tree, key_pair, &endpoints))
}

/// Compress the chain endpoints of a leaf into its public key.
pub fn wots_c_leaf(
    pk_seed: &[u8; 32],
    layer: u32,
    tree: u64,
    key_pair: u32,
    endpoints: &[[u8; 32]],
) -> [u8; 32] {
    let adrs = HashAdrs {
        layer,
        tree,
        kind: AdrsKind::WotsPk,
        key_pair,
        chain_idx: 0,
        hash_step: 0,
    };
    th_tweak_tl(Cshake256Suite, pk_seed, &adrs, endpoints)
}

/// Single-party reference: the node of every chain at the position given by its digit.
pub fn wots_c_reference_nodes(
    params: &WotsCParams,
    sk: &PqSecretKey,
    layer: u32,
    tree: u64,
    key_pair: u32,
    positions: &[u8],
) -> Vec<[u8; 32]> {
    (0..params.chains)
        .map(|chain| {
            let base = wots_secret_base(Cshake256Suite, sk, layer, tree, key_pair, chain as u32);
            wots_chain_steps(
                Cshake256Suite,
                &sk.pk_seed,
                layer,
                tree,
                key_pair,
                chain as u32,
                0,
                usize::from(positions[chain]),
                base,
            )
        })
        .collect()
}

/// Single-party reference: a leaf's compressed public key.
pub fn wots_c_reference_leaf(
    params: &WotsCParams,
    sk: &PqSecretKey,
    layer: u32,
    tree: u64,
    key_pair: u32,
) -> [u8; 32] {
    let ends =
        wots_c_reference_nodes(params, sk, layer, tree, key_pair, &vec![3u8; params.chains]);
    wots_c_leaf(&sk.pk_seed, layer, tree, key_pair, &ends)
}

/// Every level of a Merkle tree, leaves first, using the node addressing of
/// [`crate::tsw_baggy::walk_merkle_auth_path`] (`chain_idx` = height of the node,
/// `hash_step` = `base_node_idx << (height - node height)` plus its index in the level).
/// `key_pair` is the FORS key pair for a FORS tree and `0` for a hypertree subtree.
pub fn merkle_levels(
    pk_seed: &[u8; 32],
    layer: u32,
    tree: u64,
    kind: AdrsKind,
    key_pair: u32,
    leaves: &[[u8; 32]],
    base_node_idx: usize,
) -> Vec<Vec<[u8; 32]>> {
    debug_assert!(leaves.len().is_power_of_two());
    let height = leaves.len().trailing_zeros() as usize;
    let mut levels = Vec::with_capacity(height + 1);
    levels.push(leaves.to_vec());
    for h in 1..=height {
        let prev = &levels[h - 1];
        let offset = base_node_idx << (height - h);
        let next: Vec<[u8; 32]> = prev
            .as_chunks::<2>()
            .0
            .iter()
            .enumerate()
            .map(|(i, pair)| {
                let adrs = HashAdrs {
                    layer,
                    tree,
                    kind,
                    key_pair,
                    chain_idx: h as u32,
                    hash_step: (offset + i) as u32,
                };
                th_node_h(Cshake256Suite, pk_seed, &adrs, &pair[0], &pair[1])
            })
            .collect();
        levels.push(next);
    }
    levels
}

/// Root-first authentication path of leaf `idx` from [`merkle_levels`].
pub fn merkle_auth_path(levels: &[Vec<[u8; 32]>], idx: usize) -> Vec<[u8; 32]> {
    let height = levels.len() - 1;
    let mut path: Vec<[u8; 32]> = (0..height).map(|h| levels[h][(idx >> h) ^ 1]).collect();
    path.reverse();
    path
}

/// One lane of a [`Sweep`]: a secret derived by `PRF` at address `prf`, followed by `steps`
/// applications of `F`.
#[derive(Clone, Copy, Debug)]
pub struct LaneSpec {
    pub prf: HashAdrs,
    pub f: HashAdrs,
    pub steps: u8,
    /// Whether step `s` uses `f` with `hash_step = s` (WOTS chains) or `f` as is (FORS).
    pub step_indexed: bool,
}

impl LaneSpec {
    /// One WOTS chain: positions `0..=3`.
    pub const fn wots(layer: u32, tree: u64, key_pair: u32, chain: u32) -> Self {
        Self {
            prf: HashAdrs {
                layer,
                tree,
                kind: AdrsKind::WotsPrf,
                key_pair,
                chain_idx: chain,
                hash_step: 0,
            },
            f: HashAdrs {
                layer,
                tree,
                kind: AdrsKind::WotsHash,
                key_pair,
                chain_idx: chain,
                hash_step: 0,
            },
            steps: WOTS_STEPS as u8,
            step_indexed: true,
        }
    }

    /// One FORS leaf: position 0 is the secret, position 1 its leaf hash.
    pub const fn fors(tree: u64, key_pair: u32, fors_tree: u32, leaf: u32) -> Self {
        Self {
            prf: HashAdrs {
                layer: 0,
                tree,
                kind: AdrsKind::ForsPrf,
                key_pair,
                chain_idx: fors_tree,
                hash_step: leaf,
            },
            f: HashAdrs {
                layer: 0,
                tree,
                kind: AdrsKind::ForsTree,
                key_pair,
                chain_idx: fors_tree,
                hash_step: leaf,
            },
            steps: 1,
            step_indexed: false,
        }
    }
}

/// Shared results of a level-by-level chain evaluation: `pos[wave][position]` holds, for the
/// lanes of that wave, the value after `position` applications of `F`.
pub struct Sweep {
    lanes: Vec<LaneSpec>,
    pos: Vec<Vec<SharedDigest256>>,
}

impl Sweep {
    /// Evaluate every lane to `min(lane.steps, max_steps)` steps. Lanes must be ordered by
    /// non-increasing `steps`, so the lanes still running at any level are a prefix of each
    /// wave. Each level is declared to the engine as one sequential permutation level.
    pub fn evaluate(
        engine: &mut Rss256Engine,
        pk_seed: &[u8; 32],
        lanes: Vec<LaneSpec>,
        max_steps: u8,
    ) -> Result<Self, Rss256Error> {
        if lanes.is_empty() || lanes.windows(2).any(|w| w[0].steps < w[1].steps) {
            return Err(Rss256Error::InvalidParameters);
        }
        let mut pos: Vec<Vec<SharedDigest256>> = Vec::new();
        engine.mark_sequential_level();
        for chunk in lanes.chunks(LANES) {
            let frames: Vec<[u8; SHAKE256_RATE_BYTES]> = chunk
                .iter()
                .map(|l| tsw_secret32_frame(TAG_PRF, pk_seed, &l.prf))
                .collect();
            let mut st = SharedState256::from_public_frames(&TSW_SUITE_MIDSTATE, &frames)?;
            st.xor_shared_key(
                TSW_PRF_SECRET_OFFSET,
                engine.sk_seed_slots(),
                &active_lane_mask(chunk.len()),
            )?;
            engine.permute(&mut st, chunk.len())?;
            pos.push(vec![st.digest()]);
        }
        let deepest = lanes[0].steps.min(max_steps);
        for step in 0..deepest {
            engine.mark_sequential_level();
            for (wave, chunk) in lanes.chunks(LANES).enumerate() {
                let running = chunk
                    .iter()
                    .take_while(|l| l.steps.min(max_steps) > step)
                    .count();
                if running == 0 {
                    continue;
                }
                let frames: Vec<[u8; SHAKE256_RATE_BYTES]> = chunk[..running]
                    .iter()
                    .map(|l| {
                        let adrs = if l.step_indexed {
                            HashAdrs {
                                hash_step: u32::from(step),
                                ..l.f
                            }
                        } else {
                            l.f
                        };
                        tsw_secret32_frame(TAG_TH_F, pk_seed, &adrs)
                    })
                    .collect();
                let mut st = SharedState256::from_public_frames(&TSW_SUITE_MIDSTATE, &frames)?;
                st.xor_shared_digest(TSW_F_SECRET_OFFSET, &pos[wave][usize::from(step)]);
                engine.permute(&mut st, running)?;
                pos[wave].push(st.digest());
            }
        }
        Ok(Self { lanes, pos })
    }

    pub fn lane_count(&self) -> usize {
        self.lanes.len()
    }

    /// Open, for each `(lane, position)` pick, that lane's value at that position. The
    /// engine refuses unless every gate has passed a barrier. All picks of one call are
    /// independent openings that travel in the same round.
    pub fn open_positions(
        &self,
        engine: &mut Rss256Engine,
        picks: &[(usize, u8)],
    ) -> Result<Vec<[u8; 32]>, Rss256Error> {
        let mut out = vec![[0u8; 32]; picks.len()];
        // Group picks by (wave, position); each group is one masked opening.
        let mut groups: Vec<(usize, u8, Plane, Vec<usize>)> = Vec::new();
        for (i, &(lane, position)) in picks.iter().enumerate() {
            let wave = lane / LANES;
            if lane >= self.lanes.len() || usize::from(position) >= self.pos[wave].len() {
                return Err(Rss256Error::InvalidParameters);
            }
            let in_wave = lane % LANES;
            let slot = match groups
                .iter()
                .position(|g| g.0 == wave && g.1 == position)
            {
                Some(idx) => idx,
                None => {
                    groups.push((wave, position, [0u64; 4], Vec::new()));
                    groups.len() - 1
                }
            };
            groups[slot].2[in_wave / 64] |= 1u64 << (in_wave % 64);
            groups[slot].3.push(i);
        }
        for (wave, position, mask, members) in groups {
            let opened =
                engine.open_digests(&self.pos[wave][usize::from(position)], &mask, LANES)?;
            for i in members {
                out[i] = opened[picks[i].0 % LANES];
            }
        }
        Ok(out)
    }

    /// Erase the shares of `lanes` at every position (used once a one-time leaf is spent).
    pub fn wipe_lanes(&mut self, lanes: core::ops::Range<usize>) {
        let zero = SharedDigest256::zeroed();
        for lane in lanes {
            let mut mask = [0u64; 4];
            mask[(lane % LANES) / 64] = 1u64 << (lane % 64);
            for digest in &mut self.pos[lane / LANES] {
                digest.assign_masked(&zero, &mask);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::keccak_mpc::run_dealerless_rss_dkg_2of3;
    use crate::preprocessing::PartyPrivateRng;
    use crate::tsw_baggy::{
        build_merkle_from_leaves_topdown, extract_base_w_digits_checked,
        fors_leaf_hash_from_secret, fors_secret_leaf, th_call, walk_merkle_auth_path,
    };

    pub(crate) fn test_engine(tag: u8) -> (Rss256Engine, PqSecretKey) {
        let sid = [tag; 32];
        let mut rngs: [PartyPrivateRng; 3] = core::array::from_fn(|p| {
            PartyPrivateRng::from_seed([tag ^ ((p as u8) << 4); 32], b"wots-c")
        });
        let (keys, _) = run_dealerless_rss_dkg_2of3(sid, 32, &mut rngs).unwrap();
        let engine = Rss256Engine::new(sid, keys, rngs).unwrap();
        // Reference-only reconstruction of the test key.
        let xor3 = |slots: [&[u8]; 3]| -> [u8; 32] {
            core::array::from_fn(|i| slots[0][i] ^ slots[1][i] ^ slots[2][i])
        };
        let sk = PqSecretKey {
            sk_seed: xor3(engine.sk_seed_slots()),
            sk_prf: xor3(engine.sk_prf_slots()),
            pk_seed: engine.pk_seed(),
        };
        (engine, sk)
    }

    #[test]
    fn grinder_matches_the_scalar_tweakable_hash_and_finds_the_smallest_valid_counter() {
        let params = WotsCParams::V128;
        assert!(params.is_well_formed());
        let pk_seed = [0x5A; 32];
        let value = [0xC3; 32];
        let adrs = wots_c_digest_adrs(3, 0x1234_5678_9ABC, 2);
        let tag = b"QSAG.TEST.DIGEST/v1";
        let g = DigestGrinder::new(tag, &pk_seed, &adrs, &value);
        for ctr in [0u32, 1, 255, 256, 0x0102_0304, u32::MAX - 1] {
            let got = g.hash4(ctr);
            for (i, digest) in got.iter().enumerate() {
                let a = HashAdrs {
                    hash_step: ctr.wrapping_add(i as u32),
                    ..adrs
                };
                assert_eq!(*digest, th_call(Cshake256Suite, tag, &pk_seed, &a, &[&value]));
            }
        }
        // The allocation-free digit reader agrees with the generic base-w extractor.
        for ctr in 0..64u32 {
            for hash in g.hash4(4 * ctr) {
                let all =
                    extract_base_w_digits_checked(WOTS_W, WOTS_DIGEST_DIGITS, &hash[..]).unwrap();
                let valid = all.iter().sum::<usize>() == 192;
                let want = valid.then(|| all.iter().map(|d| *d as u8).collect::<Vec<u8>>());
                assert_eq!(params.digits(&hash), want);
            }
        }
        let (ctr, digits) = g.grind(&params, 1 << 22).expect("a valid counter exists");
        assert_eq!(digits.len(), 128);
        assert_eq!(digits.iter().map(|d| usize::from(*d)).sum::<usize>(), 192);
        assert_eq!(g.digits_at(&params, ctr), Some(digits));
        // Minimality: no smaller counter is valid.
        for c in 0..ctr {
            assert_eq!(g.digits_at(&params, c), None, "counter {c}");
        }
        assert_eq!(g.grind(&params, ctr), None);
    }

    #[test]
    fn merkle_levels_agree_with_the_verifier_walk() {
        let pk_seed = [7u8; 32];
        let leaves: Vec<[u8; 32]> = (0..16u8).map(|i| [i; 32]).collect();
        let levels = merkle_levels(&pk_seed, 2, 9, AdrsKind::Tree, 0, &leaves, 0);
        for idx in 0..16 {
            let (root, path) = build_merkle_from_leaves_topdown(
                Cshake256Suite,
                &pk_seed,
                2,
                9,
                AdrsKind::Tree,
                0,
                &leaves,
                4,
                0,
                idx,
            );
            assert_eq!(levels[4][0], root);
            assert_eq!(merkle_auth_path(&levels, idx), path);
            assert_eq!(
                walk_merkle_auth_path(
                    Cshake256Suite,
                    &pk_seed,
                    2,
                    9,
                    AdrsKind::Tree,
                    0,
                    4,
                    0,
                    idx,
                    leaves[idx],
                    &path
                ),
                Some(root)
            );
        }
    }

    #[test]
    fn sweep_matches_reference_chains_and_fors_leaves_across_wave_boundaries() {
        let (mut engine, sk) = test_engine(0xA1);
        let pk_seed = sk.pk_seed;
        // Three WOTS leaves (384 chains: two waves), then 40 FORS leaves.
        let chains = WotsCParams::V128.chains;
        let wots_lanes = 3 * chains;
        let mut lanes = Vec::new();
        for kp in 0..3u32 {
            for chain in 0..chains as u32 {
                lanes.push(LaneSpec::wots(1, 77, kp, chain));
            }
        }
        for leaf in 0..40u32 {
            lanes.push(LaneSpec::fors(77, 3, leaf % 4, leaf));
        }
        let sweep = Sweep::evaluate(&mut engine, &pk_seed, lanes, 3).unwrap();
        assert_eq!(sweep.lane_count(), wots_lanes + 40);
        // PRF, three chain steps: four sequential levels in total.
        assert_eq!(engine.stats().perm_levels, 4);
        assert_eq!(
            sweep.open_positions(&mut engine, &[(0, 0)]),
            Err(Rss256Error::OpenBeforeCheck)
        );
        engine.check().unwrap();

        // Endpoints of every chain, a mixed set of interior nodes, and FORS values.
        let mut picks: Vec<(usize, u8)> = (0..wots_lanes).map(|l| (l, 3u8)).collect();
        picks.extend((0..wots_lanes).map(|l| (l, (l % 3) as u8)));
        picks.extend((wots_lanes..wots_lanes + 40).map(|l| (l, 1u8)));
        picks.push((wots_lanes + 17, 0));
        engine.mark_open_round();
        let opened = sweep.open_positions(&mut engine, &picks).unwrap();
        for (i, &(lane, position)) in picks.iter().enumerate() {
            let want = if lane < wots_lanes {
                let (kp, chain) = ((lane / chains) as u32, (lane % chains) as u32);
                let base = wots_secret_base(Cshake256Suite, &sk, 1, 77, kp, chain);
                wots_chain_steps(
                    Cshake256Suite,
                    &pk_seed,
                    1,
                    77,
                    kp,
                    chain,
                    0,
                    usize::from(position),
                    base,
                )
            } else {
                let leaf = (lane - wots_lanes) as u32;
                let secret = fors_secret_leaf(Cshake256Suite, &sk, 77, 3, leaf % 4, leaf);
                if position == 0 {
                    secret
                } else {
                    fors_leaf_hash_from_secret(
                        Cshake256Suite,
                        &pk_seed,
                        77,
                        3,
                        leaf % 4,
                        leaf,
                        &secret,
                    )
                }
            };
            assert_eq!(opened[i], want, "pick {i}: lane {lane} position {position}");
        }
        // Reference leaf agrees with the opened endpoints.
        assert_eq!(
            wots_c_leaf(&pk_seed, 1, 77, 2, &opened[2 * chains..3 * chains]),
            wots_c_reference_leaf(&WotsCParams::V128, &sk, 1, 77, 2)
        );
    }

    #[test]
    fn wiped_lanes_open_as_zero_and_capped_sweeps_stop_early() {
        let (mut engine, sk) = test_engine(0xA2);
        let lanes: Vec<LaneSpec> = (0..58u32).map(|c| LaneSpec::wots(0, 0, 5, c)).collect();
        let mut sweep = Sweep::evaluate(&mut engine, &sk.pk_seed, lanes, 2).unwrap();
        assert_eq!(engine.stats().perm_levels, 3);
        engine.check().unwrap();
        // Position 3 was never computed.
        assert_eq!(
            sweep.open_positions(&mut engine, &[(0, 3)]),
            Err(Rss256Error::InvalidParameters)
        );
        let before = sweep.open_positions(&mut engine, &[(4, 2), (5, 2)]).unwrap();
        assert_ne!(before[0], [0u8; 32]);
        sweep.wipe_lanes(4..5);
        let after = sweep.open_positions(&mut engine, &[(4, 2), (5, 2)]).unwrap();
        assert_eq!(after[0], [0u8; 32]);
        assert_eq!(after[1], before[1]);
    }
}

#[cfg(test)]
mod address_regression {
    use super::*;
    #[test]
    fn fors_internal_nodes_bind_key_pair_in_build_and_walk() {
        use crate::tsw_baggy::{build_merkle_from_leaves_topdown, walk_merkle_auth_path};
        let leaves = [[42; 32]; 4];
        let seed = [9; 32];
        let a = merkle_levels(&seed, 0, 13, AdrsKind::ForsTree, 5, &leaves, 2);
        let b = merkle_levels(&seed, 0, 13, AdrsKind::ForsTree, 6, &leaves, 2);
        assert_ne!(a[1][0], b[1][0]);
        assert_ne!(a[2][0], b[2][0]);
        for kp in [5, 6] {
            let levels = merkle_levels(&seed, 0, 13, AdrsKind::ForsTree, kp, &leaves, 2);
            let (root, path) = build_merkle_from_leaves_topdown(Cshake256Suite, &seed, 0, 13, AdrsKind::ForsTree, kp, &leaves, 2, 2, 1);
            assert_eq!(root, levels[2][0]);
            assert_eq!(walk_merkle_auth_path(Cshake256Suite, &seed, 0, 13, AdrsKind::ForsTree, kp, 2, 2, 1, leaves[1], &path), Some(root));
            assert_ne!(walk_merkle_auth_path(Cshake256Suite, &seed, 0, 13, AdrsKind::ForsTree, kp + 1, 2, 2, 1, leaves[1], &path), Some(root));
        }
    }
}
