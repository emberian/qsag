//! Pre-locked 32-byte `HashAdrs`, polymorphic `TweakableHashSuite` (`Cshake256Suite` &
//! `Poseidon2Suite`), 256-bit Target-Sum Winternitz (`TSW`), FORS, XMSS, stateless
//! `Corduroy-Custody-128` & `Baggy-128f`, stateful `JortsPoseidon2` with mandatory
//! monotonic `StatefulEpochLatch` + deterministic `r_rand`, committed-identity `HybridPinnedSig`,
//! and tri-state `VerifyReply`.

use alloc::vec::Vec;
use core::fmt;

use crate::field::goldilocks::Goldilocks;
use crate::sponge::keccak::{cshake256_32, encode_multi_frame, leb128};
use crate::sponge::poseidon2::{pack_bytes32_to_limbs56_canonical, poseidon2_hash32};
use crate::wipe::{ct_eq_bytes32, wipe_bytes32, wipe_slice};

/// Domain customization strings (`QSAG.PQ.*`).
pub const PQ_CSHAKE_SUITE_CUSTOM: &[u8] = b"QSAG.PQ.SUITE.CSHAKE256/v1";
pub const PQ_POSEIDON2_SUITE_ID: &[u8] = b"QSAG.PQ.SUITE.POSEIDON2/v1";

pub const TAG_PRF_MSG: &[u8] = b"QSAG.PQ.PRFMSG/v1";
pub const TAG_H_MSG: &[u8] = b"QSAG.PQ.HMSG/v1";
pub const TAG_H_XOF: &[u8] = b"QSAG.PQ.HXOF/v1";
pub const TAG_H_INTERNAL: &[u8] = b"QSAG.PQ.HINT/v1";
pub const TAG_PRF: &[u8] = b"QSAG.PQ.PRF/v1";
pub const TAG_TH_F: &[u8] = b"QSAG.PQ.TH_F/v1";
pub const TAG_TH_H: &[u8] = b"QSAG.PQ.TH_H/v1";
pub const TAG_TH_TL: &[u8] = b"QSAG.PQ.TH_TL/v1";
pub const TAG_H_PRE: &[u8] = b"QSAG.PQ.PRE/v1";
pub const TAG_JORTS_DET_RAND: &[u8] = b"QSAG.PQ.BAGGYSIG.DET/v1";
/// Domain tag of the stateless threshold signers' deterministic `opt_rand` frame.
pub const TAG_STATELESS_DET_RAND: &[u8] = b"QSAG.PQ.STATELESS.DET/v1";
pub const HYBRID_ID_CUSTOM: &[u8] = b"QSAG.PQ.HYBRID.ID/v1";
pub const HYBRID_MSG_TAG: &[u8] = b"QSAG.PQ.HYBRID.MSG/v1";

/// Canonical 5-byte wire header magic `"QSAG\x01"` (`[0x51, 0x53, 0x41, 0x47, 0x01]`).
pub const PQ_WIRE_MAGIC: [u8; 5] = *b"QSAG\x01";

/// Domain-separation role of a 32-byte hash address inside the hypertree / FORS / WOTS+C hierarchy.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AdrsKind {
    WotsHash = 0,
    WotsPk = 1,
    Tree = 2,
    ForsTree = 3,
    ForsRoots = 4,
    WotsPrf = 5,
    ForsPrf = 6,
    /// Leaf-secret derivation of a [`crate::pors_fp`] tree.
    PorsPrf = 7,
    /// Leaves and internal nodes of a [`crate::pors_fp`] tree.
    PorsTree = 8,
}

impl AdrsKind {
    #[inline]
    pub const fn to_code(self) -> u32 {
        self as u32
    }

    #[inline]
    pub const fn from_code(code: u32) -> Option<Self> {
        match code {
            0 => Some(Self::WotsHash),
            1 => Some(Self::WotsPk),
            2 => Some(Self::Tree),
            3 => Some(Self::ForsTree),
            4 => Some(Self::ForsRoots),
            5 => Some(Self::WotsPrf),
            6 => Some(Self::ForsPrf),
            7 => Some(Self::PorsPrf),
            8 => Some(Self::PorsTree),
            _ => None,
        }
    }
}

/// Canonical 32-byte tweakable hash address (`ADRS`):
/// `[0..4) layer || [4..8) 0 || [8..16) tree || [16..20) kind || [20..24) key_pair || [24..28) chain_idx || [28..32) hash_step`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct HashAdrs {
    pub layer: u32,
    pub tree: u64,
    pub kind: AdrsKind,
    pub key_pair: u32,
    pub chain_idx: u32,
    pub hash_step: u32,
}

impl HashAdrs {
    pub const ZERO: Self = Self {
        layer: 0,
        tree: 0,
        kind: AdrsKind::WotsHash,
        key_pair: 0,
        chain_idx: 0,
        hash_step: 0,
    };

    #[inline]
    pub fn to_bytes(&self) -> [u8; 32] {
        encode_adrs(self)
    }
}

/// Pre-locked 32-byte big-endian `ADRS` frame.
#[inline]
pub fn encode_adrs(a: &HashAdrs) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[0..4].copy_from_slice(&a.layer.to_be_bytes());
    out[8..16].copy_from_slice(&a.tree.to_be_bytes());
    out[16..20].copy_from_slice(&a.kind.to_code().to_be_bytes());
    out[20..24].copy_from_slice(&a.key_pair.to_be_bytes());
    out[24..28].copy_from_slice(&a.chain_idx.to_be_bytes());
    out[28..32].copy_from_slice(&a.hash_step.to_be_bytes());
    out
}

/// Decode a canonical 32-byte `ADRS` frame (`None` if reserved `[4..8)` != 0 or unknown `AdrsKind`).
pub fn decode_adrs(bytes: &[u8; 32]) -> Option<HashAdrs> {
    if bytes[4..8] != [0, 0, 0, 0] {
        return None;
    }
    let layer = u32::from_be_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
    let tree = u64::from_be_bytes([
        bytes[8], bytes[9], bytes[10], bytes[11], bytes[12], bytes[13], bytes[14], bytes[15],
    ]);
    let kind_code = u32::from_be_bytes([bytes[16], bytes[17], bytes[18], bytes[19]]);
    let kind = AdrsKind::from_code(kind_code)?;
    let key_pair = u32::from_be_bytes([bytes[20], bytes[21], bytes[22], bytes[23]]);
    let chain_idx = u32::from_be_bytes([bytes[24], bytes[25], bytes[26], bytes[27]]);
    let hash_step = u32::from_be_bytes([bytes[28], bytes[29], bytes[30], bytes[31]]);
    Some(HashAdrs {
        layer,
        tree,
        kind,
        key_pair,
        chain_idx,
        hash_step,
    })
}

#[inline]
fn push_leb128(out: &mut Vec<u8>, mut n: usize) {
    while n >= 128 {
        out.push(0x80 | ((n & 0x7F) as u8));
        n >>= 7;
    }
    out.push(n as u8);
}

/// Polymorphic 256-bit tweakable hash suite abstracting `cSHAKE256` and `Poseidon2`.
pub trait TweakableHashSuite: Copy + Sync {
    fn suite_id(&self) -> &'static [u8];
    fn raw_hash(&self, preimage: &[u8]) -> [u8; 32];
}

/// NIST SP 800-185 `cSHAKE256` instantiation (`Corduroy-Custody-128` / `Baggy-128f`).
#[derive(Clone, Copy, Debug, Default)]
pub struct Cshake256Suite;

impl TweakableHashSuite for Cshake256Suite {
    #[inline]
    fn suite_id(&self) -> &'static [u8] {
        PQ_CSHAKE_SUITE_CUSTOM
    }

    #[inline]
    fn raw_hash(&self, preimage: &[u8]) -> [u8; 32] {
        cshake256_32(PQ_CSHAKE_SUITE_CUSTOM, preimage)
    }
}

/// Width-12 Goldilocks `Poseidon2` instantiation (`JortsPoseidon2`).
#[derive(Clone, Copy, Debug, Default)]
pub struct Poseidon2Suite;

impl TweakableHashSuite for Poseidon2Suite {
    #[inline]
    fn suite_id(&self) -> &'static [u8] {
        PQ_POSEIDON2_SUITE_ID
    }

    #[inline]
    fn raw_hash(&self, preimage: &[u8]) -> [u8; 32] {
        poseidon2_hash32(preimage)
    }
}

/// Build the self-delimiting preimage `encodeMultiFrame([role_tag, pk_seed, encodeAdrs(adrs)] ++ args)`.
/// Pre-sizes exact capacity so zero heap reallocations occur while appending secret or public slices.
pub fn th_preimage(role_tag: &[u8], pk_seed: &[u8], adrs: &HashAdrs, args: &[&[u8]]) -> Vec<u8> {
    let adrs_bytes = encode_adrs(adrs);
    let count = 3 + args.len();
    let mut exact_cap = leb128(count).len()
        + leb128(role_tag.len()).len()
        + role_tag.len()
        + leb128(pk_seed.len()).len()
        + pk_seed.len()
        + leb128(32).len()
        + 32;
    for a in args {
        exact_cap += leb128(a.len()).len() + a.len();
    }
    let mut out = Vec::with_capacity(exact_cap);
    push_leb128(&mut out, count);
    push_leb128(&mut out, role_tag.len());
    out.extend_from_slice(role_tag);
    push_leb128(&mut out, pk_seed.len());
    out.extend_from_slice(pk_seed);
    push_leb128(&mut out, 32);
    out.extend_from_slice(&adrs_bytes);
    for a in args {
        push_leb128(&mut out, a.len());
        out.extend_from_slice(a);
    }
    debug_assert_eq!(out.len(), exact_cap);
    out
}

/// Build `(template_with_zeroed_32b_slot, offset)` for `th_prf_msg(TAG_PRF_MSG, [], ZERO, [sk_prf, opt_rand, mu])`.
pub fn build_prf_msg_template(opt_rand: &[u8], mu: &[u8; 32]) -> (Vec<u8>, usize) {
    let dummy_sk = [0u8; 32];
    let tmpl = th_preimage(
        TAG_PRF_MSG,
        &[],
        &HashAdrs::ZERO,
        &[&dummy_sk, opt_rand, mu],
    );
    let tail_len = leb128(opt_rand.len()).len() + opt_rand.len() + 1 + 32;
    let sk_offset = tmpl.len() - tail_len - 32;
    (tmpl, sk_offset)
}

/// Build `(template_with_zeroed_32b_slot, offset)` for `th_call(role_tag, pk_seed, adrs, &[32_byte_secret])`.
#[inline]
pub fn build_single_secret32_template(
    role_tag: &[u8],
    pk_seed: &[u8; 32],
    adrs: &HashAdrs,
) -> (Vec<u8>, usize) {
    let tmpl = th_preimage(role_tag, pk_seed, adrs, &[&[0u8; 32]]);
    let off = tmpl.len() - 32;
    (tmpl, off)
}

#[inline]
pub fn th_call<S: TweakableHashSuite>(
    suite: S,
    role_tag: &[u8],
    pk_seed: &[u8],
    adrs: &HashAdrs,
    args: &[&[u8]],
) -> [u8; 32] {
    let pre = th_preimage(role_tag, pk_seed, adrs, args);
    suite.raw_hash(&pre)
}

/// Secret-bearing tweakable hash call that deterministically zeroizes the serialized preimage buffer
/// before returning (`[P1-06]`).
#[inline]
pub fn th_call_secret<S: TweakableHashSuite>(
    suite: S,
    role_tag: &[u8],
    pk_seed: &[u8],
    adrs: &HashAdrs,
    args: &[&[u8]],
) -> [u8; 32] {
    let mut pre = th_preimage(role_tag, pk_seed, adrs, args);
    let out = suite.raw_hash(&pre);
    wipe_slice(&mut pre);
    out
}

#[inline]
pub fn th_chain_f<S: TweakableHashSuite>(
    suite: S,
    pk_seed: &[u8],
    adrs: &HashAdrs,
    x: &[u8; 32],
) -> [u8; 32] {
    th_call_secret(suite, TAG_TH_F, pk_seed, adrs, &[x])
}

#[inline]
pub fn th_node_h<S: TweakableHashSuite>(
    suite: S,
    pk_seed: &[u8],
    adrs: &HashAdrs,
    left: &[u8; 32],
    right: &[u8; 32],
) -> [u8; 32] {
    th_call(suite, TAG_TH_H, pk_seed, adrs, &[left, right])
}

pub fn th_tweak_tl<S: TweakableHashSuite>(
    suite: S,
    pk_seed: &[u8],
    adrs: &HashAdrs,
    limbs: &[[u8; 32]],
) -> [u8; 32] {
    let refs: Vec<&[u8]> = limbs.iter().map(|l| l.as_slice()).collect();
    th_call(suite, TAG_TH_TL, pk_seed, adrs, &refs)
}

#[inline]
pub fn th_secret_prf<S: TweakableHashSuite>(
    suite: S,
    pk_seed: &[u8],
    sk_seed: &[u8],
    adrs: &HashAdrs,
) -> [u8; 32] {
    th_call_secret(suite, TAG_PRF, pk_seed, adrs, &[sk_seed])
}

#[inline]
pub fn th_prf_msg<S: TweakableHashSuite>(
    suite: S,
    sk_prf: &[u8],
    opt_rand: &[u8],
    mu: &[u8; 32],
) -> [u8; 32] {
    th_call_secret(
        suite,
        TAG_PRF_MSG,
        &[],
        &HashAdrs::ZERO,
        &[sk_prf, opt_rand, mu],
    )
}

/// Deterministic stateful `Jorts` `opt_rand` domain frame binding `(epoch, pk_seed)`.
/// Forbids caller-supplied `opt_rand` on crash-retry so retrying `(ep, mu)` outputs bit-identical
/// `r_rand` and codeword $d$, leaking zero second-codeword information (`[P0-04]`).
#[inline]
pub fn build_stateful_det_opt_domain(epoch: u64, pk_seed: &[u8; 32]) -> Vec<u8> {
    encode_multi_frame(&[TAG_JORTS_DET_RAND, &epoch.to_be_bytes(), pk_seed])
}

/// Deterministic `opt_rand` frame of the stateless threshold signers, binding `pk_seed`.
///
/// With this frame `R = PRF_msg(SK.prf, frame, mu)` is a function of the key and the message
/// digest only: a retry of the same `(key, message)` yields the same `R`, hence the same FORS
/// instance, and neither a caller nor a signing party contributes a value that could steer it.
#[inline]
pub fn build_stateless_det_opt_domain(pk_seed: &[u8; 32]) -> Vec<u8> {
    encode_multi_frame(&[TAG_STATELESS_DET_RAND, pk_seed])
}

/// Single-holder reference for the randomiser the stateless threshold signers derive under MPC.
#[inline]
pub fn derive_stateless_r_rand<S: TweakableHashSuite>(
    suite: S,
    sk_prf: &[u8; 32],
    pk_seed: &[u8; 32],
    mu: &[u8; 32],
) -> [u8; 32] {
    let opt_domain = build_stateless_det_opt_domain(pk_seed);
    th_prf_msg(suite, sk_prf, &opt_domain, mu)
}

#[inline]
pub fn derive_stateful_r_rand<S: TweakableHashSuite>(
    suite: S,
    sk_prf: &[u8; 32],
    epoch: u64,
    pk_seed: &[u8; 32],
    mu: &[u8; 32],
) -> [u8; 32] {
    let opt_domain = build_stateful_det_opt_domain(epoch, pk_seed);
    th_prf_msg(suite, sk_prf, &opt_domain, mu)
}

#[inline]
pub fn th_pre_hash<S: TweakableHashSuite>(
    suite: S,
    pk_seed: &[u8],
    pk_root: &[u8],
    msg: &[u8],
) -> [u8; 32] {
    th_call(suite, TAG_H_PRE, pk_seed, &HashAdrs::ZERO, &[pk_root, msg])
}

/// One-time bottom-layer message representative hash used **exclusively** at `layer == 0` in
/// stateful `Jorts` (`stateful == true`), binding `key_pair = kp_idx` (`[P0-02]`).
#[inline]
#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the existing explicit protocol interface for callers"
)]
pub fn th_hash_leaf_msg<S: TweakableHashSuite>(
    suite: S,
    r_rand: &[u8; 32],
    pk_seed: &[u8],
    pk_root: &[u8],
    mu: &[u8; 32],
    tree_idx: u64,
    kp_idx: u32,
    ctr: u32,
) -> [u8; 32] {
    let adrs = HashAdrs {
        layer: 0,
        tree: tree_idx,
        kind: AdrsKind::WotsHash,
        key_pair: kp_idx,
        chain_idx: 0,
        hash_step: ctr,
    };
    let ctr_be = ctr.to_be_bytes();
    th_call(
        suite,
        TAG_H_MSG,
        pk_seed,
        &adrs,
        &[r_rand, pk_root, mu, &ctr_be],
    )
}

/// Deterministic internal-node / FORS-root WOTS+C message representative hash (`[P0-02]`, `[P0-03]`).
///
/// **Security Invariant:** NEVER accepts `r_rand` or external `mu`! Upper hypertree layers
/// (`layer_idx >= 1`) sign deterministic child XMSS roots, and layer `0` in stateless
/// `Corduroy`/`Baggy` (`fors_trees > 0`) signs the deterministic `fors_pk` root of `(tree0, kp0)`.
/// Because `(pk_seed, pk_root, child_or_fors_root, layer_idx, tree_idx, kp_idx)` is 100% static for
/// a given keypair, counter grinding produces the **exact same** `(ctr, digits)` across every
/// signature traversing that subtree, revealing strictly 1 WOTS+C codeword over the key lifetime.
#[inline]
#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the existing explicit protocol interface for callers"
)]
pub fn th_hash_internal_node<S: TweakableHashSuite>(
    suite: S,
    pk_seed: &[u8],
    pk_root: &[u8],
    node_root: &[u8; 32],
    layer_idx: u32,
    tree_idx: u64,
    kp_idx: u32,
    ctr: u32,
) -> [u8; 32] {
    let adrs = HashAdrs {
        layer: layer_idx,
        tree: tree_idx,
        kind: AdrsKind::WotsHash,
        key_pair: kp_idx,
        chain_idx: 0,
        hash_step: ctr,
    };
    let ctr_be = ctr.to_be_bytes();
    th_call(
        suite,
        TAG_H_INTERNAL,
        pk_seed,
        &adrs,
        &[pk_root, node_root, &ctr_be],
    )
}

/// Multi-block counter-mode XOF `H_msg(r_rand, pk_seed, pk_root, mu)` for stateless `Corduroy` /
/// `Baggy`, producing `out_len` independent pseudorandom bytes over disjoint FORS and
/// hypertree leaf-index bit windows (`[P0-03]`).
pub fn th_xof_msg<S: TweakableHashSuite>(
    suite: S,
    r_rand: &[u8; 32],
    pk_seed: &[u8],
    pk_root: &[u8],
    mu: &[u8; 32],
    out_len: usize,
) -> Vec<u8> {
    let blocks = out_len.div_ceil(32);
    let mut out = Vec::with_capacity(blocks * 32);
    for blk in 0..blocks {
        let adrs = HashAdrs {
            layer: 0,
            tree: 0,
            kind: AdrsKind::ForsRoots,
            key_pair: 0,
            chain_idx: 0,
            hash_step: blk as u32,
        };
        let blk_be = (blk as u32).to_be_bytes();
        let digest = th_call(
            suite,
            TAG_H_XOF,
            pk_seed,
            &adrs,
            &[r_rand, pk_root, mu, &blk_be],
        );
        out.extend_from_slice(&digest);
    }
    out.truncate(out_len);
    out
}

/// Canonical `TSW` target sum $\lfloor \ell_1 (w - 1) / 2 \rfloor$.
#[inline]
pub const fn canonical_target_sum(w: usize, ell1: usize) -> usize {
    (ell1 * w.saturating_sub(1)) / 2
}

/// Target-Sum Winternitz (`TSW`) checker.
#[inline]
pub fn check_target_sum(w: usize, ell1: usize, target: usize, digits: &[usize]) -> bool {
    if digits.len() != ell1 {
        return false;
    }
    let mut sum = 0usize;
    for &d in digits {
        if d >= w {
            return false;
        }
        sum += d;
    }
    sum == target
}

/// Unpack `digest_bytes` into `ell1` base-`w` digits for power-of-two `w` (`2..=256`) with
/// **zero modulo wrapping** (`[P0-02]`). Returns `None` if `w` is not a valid power of two or if
/// `digest_bytes` has fewer than `ell1 * log2(w)` bits.
pub fn extract_base_w_digits_checked(
    w: usize,
    ell1: usize,
    digest_bytes: &[u8],
) -> Option<Vec<usize>> {
    if !(2..=256).contains(&w) || !w.is_power_of_two() {
        return None;
    }
    let lg_w = w.trailing_zeros() as usize;
    let needed_bits = ell1.checked_mul(lg_w)?;
    if needed_bits > digest_bytes.len().checked_mul(8)? {
        return None;
    }
    let mut out = Vec::with_capacity(ell1);
    for idx in 0..ell1 {
        let mut digit = 0usize;
        for bit in 0..lg_w {
            let pos = idx * lg_w + bit;
            digit = (digit << 1) | usize::from((digest_bytes[pos / 8] >> (7 - (pos % 8))) & 1);
        }
        out.push(digit);
    }
    Some(out)
}

/// Public CPU `TSW` counter grinder for one-time stateful leaf messages (`0` MPC gates).
#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the existing explicit protocol interface for callers"
)]
pub fn grind_tsw_leaf_counter<S: TweakableHashSuite>(
    suite: S,
    w: usize,
    ell1: usize,
    target: usize,
    r_rand: &[u8; 32],
    pk_seed: &[u8],
    pk_root: &[u8],
    mu: &[u8; 32],
    tree_idx: u64,
    kp_idx: u32,
    max_grind: u32,
) -> Option<(u32, Vec<usize>, [u8; 32])> {
    for ctr in 0..max_grind {
        let hmsg = th_hash_leaf_msg(suite, r_rand, pk_seed, pk_root, mu, tree_idx, kp_idx, ctr);
        let digits = extract_base_w_digits_checked(w, ell1, &hmsg)?;
        if check_target_sum(w, ell1, target, &digits) {
            return Some((ctr, digits, hmsg));
        }
    }
    None
}

/// Deterministic CPU `TSW` counter grinder for upper hypertree layers and stateless FORS-root
/// signatures (`[P0-02]`, `[P0-03]`).
#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the existing explicit protocol interface for callers"
)]
pub fn grind_tsw_internal_counter<S: TweakableHashSuite>(
    suite: S,
    w: usize,
    ell1: usize,
    target: usize,
    pk_seed: &[u8],
    pk_root: &[u8],
    node_root: &[u8; 32],
    layer_idx: u32,
    tree_idx: u64,
    kp_idx: u32,
    max_grind: u32,
) -> Option<(u32, Vec<usize>, [u8; 32])> {
    for ctr in 0..max_grind {
        let hmsg = th_hash_internal_node(
            suite, pk_seed, pk_root, node_root, layer_idx, tree_idx, kp_idx, ctr,
        );
        let digits = extract_base_w_digits_checked(w, ell1, &hmsg)?;
        if check_target_sum(w, ell1, target, &digits) {
            return Some((ctr, digits, hmsg));
        }
    }
    None
}

/// Parameter profile covering `Corduroy-Custody-128`, `Baggy-128f`, and stateful `JortsPoseidon2`.
///
/// Every valid profile enforces a full **256-bit** WOTS+C digest (`ell1 * log2(w) == 256`, e.g.,
/// `w = 4, ell1 = 128, target_sum = 192` or `w = 16, ell1 = 64, target_sum = 480`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PqHashParams {
    pub w: usize,
    pub ell1: usize,
    pub subtree_height: usize,
    pub num_layers: usize,
    pub fors_trees: usize,
    pub fors_height: usize,
    pub max_sigs_log2: usize,
    pub stateful: bool,
}

impl PqHashParams {
    #[inline]
    pub const fn target_sum(&self) -> usize {
        canonical_target_sum(self.w, self.ell1)
    }

    #[inline]
    pub const fn total_tree_bits(&self) -> Option<usize> {
        self.num_layers.checked_mul(self.subtree_height)
    }

    #[inline]
    pub const fn is_well_formed(&self) -> bool {
        if self.num_layers == 0 || self.w < 2 || self.w > 256 || !self.w.is_power_of_two() {
            return false;
        }
        let lg_w = self.w.trailing_zeros() as usize;
        let Some(digest_bits) = self.ell1.checked_mul(lg_w) else {
            return false;
        };
        // Full 256-bit WOTS+C collision/second-preimage resistance ([P0-02]).
        if digest_bits != 256 {
            return false;
        }
        if self.subtree_height == 0 || self.subtree_height > 30 || self.fors_height > 30 {
            return false;
        }
        let Some(total_bits) = self.num_layers.checked_mul(self.subtree_height) else {
            return false;
        };
        if total_bits == 0 || total_bits > 62 {
            return false;
        }
        if self.stateful {
            self.fors_trees == 0
                && self.fors_height == 0
                && self.max_sigs_log2 > 0
                && self.max_sigs_log2 <= total_bits
        } else {
            self.fors_trees > 0
                && self.fors_height > 0
                && self.max_sigs_log2 > 0
                && self.max_sigs_log2 <= total_bits
        }
    }

    /// Range check enforcing BOTH hypertree geometry `num_layers * subtree_height` AND
    /// (in stateful mode) the key's declared `max_sigs_log2` epoch cap (`[P0-04]`).
    #[inline]
    pub const fn leaf_idx_in_range(&self, leaf_global_idx: usize) -> bool {
        let Some(total_bits) = self.num_layers.checked_mul(self.subtree_height) else {
            return false;
        };
        let cap_bits = if self.stateful && self.max_sigs_log2 < total_bits {
            self.max_sigs_log2
        } else {
            total_bits
        };
        if cap_bits >= (usize::BITS as usize) {
            true
        } else {
            leaf_global_idx < (1usize << cap_bits)
        }
    }

    /// Exact canonical wire byte length of a `PqHashSig` (`PQ_WIRE_MAGIC` + body), checked against overflow.
    #[inline]
    pub const fn wire_sig_bytes_checked(&self) -> Option<usize> {
        let fors_bytes = if self.stateful {
            0usize
        } else {
            let per_tree = match self.fors_height.checked_mul(32) {
                Some(v) => match v.checked_add(32) {
                    Some(s) => s,
                    None => return None,
                },
                None => return None,
            };
            match self.fors_trees.checked_mul(per_tree) {
                Some(v) => v,
                None => return None,
            }
        };
        let wots_b = match self.ell1.checked_mul(32) {
            Some(v) => v,
            None => return None,
        };
        let auth_b = match self.subtree_height.checked_mul(32) {
            Some(v) => v,
            None => return None,
        };
        let per_layer = match 4usize.checked_add(wots_b) {
            Some(v) => match v.checked_add(auth_b) {
                Some(s) => s,
                None => return None,
            },
            None => return None,
        };
        let layer_bytes = match self.num_layers.checked_mul(per_layer) {
            Some(v) => v,
            None => return None,
        };
        let header = 5usize + 32 + 4 + 8;
        match header.checked_add(fors_bytes) {
            Some(v) => v.checked_add(layer_bytes),
            None => None,
        }
    }

    #[inline]
    pub const fn wire_sig_bytes(&self) -> usize {
        match self.wire_sig_bytes_checked() {
            Some(v) => v,
            None => 0,
        }
    }

    /// `Corduroy-Custody-128` (`Q_max = 2^12 = 4,096`, `h = 28, d = 7, h' = 4, w = 4, ell1 = 128, k = 33, a = 6` -> >200b FORS subset-resilience & 256b WOTS+C).
    pub const CORDUROY_CUSTODY_128: Self = Self {
        w: 4,
        ell1: 128,
        subtree_height: 4,
        num_layers: 7,
        fors_trees: 33,
        fors_height: 6,
        max_sigs_log2: 12,
        stateful: false,
    };

    /// `Baggy-128f` (`Q_max = 2^16 = 65,536`, `h = 32, d = 16, h' = 2, w = 4, ell1 = 128, k = 33, a = 6` -> >200b FORS subset-resilience & 256b WOTS+C).
    pub const BAGGY_TSW_128F: Self = Self {
        w: 4,
        ell1: 128,
        subtree_height: 2,
        num_layers: 16,
        fors_trees: 33,
        fors_height: 6,
        max_sigs_log2: 16,
        stateful: false,
    };

    /// Stateful algebraic `JortsPoseidon2` (`Q_max = 2^16`, `h = 16, d = 1, w = 4, ell1 = 128`, 256b WOTS+C).
    pub const JORTS_POSEIDON2: Self = Self {
        w: 4,
        ell1: 128,
        subtree_height: 16,
        num_layers: 1,
        fors_trees: 0,
        fors_height: 0,
        max_sigs_log2: 16,
        stateful: true,
    };

    /// Benchmark cached stateful `JortsPoseidon2` (`h = 8, d = 1, w = 4, ell1 = 128`, 256b WOTS+C).
    pub const JORTS_BENCH_CACHED: Self = Self {
        w: 4,
        ell1: 128,
        subtree_height: 8,
        num_layers: 1,
        fors_trees: 0,
        fors_height: 0,
        max_sigs_log2: 8,
        stateful: true,
    };

    /// Compact fast-test stateless profile (`w = 16, ell1 = 64` = 256b WOTS+C, `h = 20, d = 10, h' = 2, k = 24, a = 4`).
    pub const COMPACT_GOLDEN: Self = Self {
        w: 16,
        ell1: 64,
        subtree_height: 2,
        num_layers: 10,
        fors_trees: 24,
        fors_height: 4,
        max_sigs_log2: 4,
        stateful: false,
    };

    /// Compact fast-test stateful `Jorts` profile (`w = 16, ell1 = 64` = 256b WOTS+C, `d = 1, h' = 2`).
    pub const COMPACT_JORTS: Self = Self {
        w: 16,
        ell1: 64,
        subtree_height: 2,
        num_layers: 1,
        fors_trees: 0,
        fors_height: 0,
        max_sigs_log2: 2,
        stateful: true,
    };
}

/// Errors emitted by [`StatefulEpochLatch`] enforcing strictly monotonic OTS epoch consumption
/// and crash-recovery message binding (`[P0-04]`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EpochLatchError {
    /// Key lifetime exhausted (`next_epoch >= 2^max_sigs_log2`).
    Exhausted,
    /// Invalid `max_sigs_log2` (`0` or `> 62`).
    InvalidCapacity,
    /// Crash-retry requested for an epoch other than the currently latched in-flight epoch.
    EpochNotInFlight,
    /// Crash-retry attempted on the latched epoch with a **different** message digest `mu' != mu`.
    EquivocationRefused,
    /// Underlying WAL storage / `fsync` I/O failure.
    PersistenceFailure,
    /// A specific epoch was requested that this latch has already moved past, and it is not the
    /// in-flight epoch.
    StaleEpoch,
    /// The latches of a full-attendance signing set do not agree on the next epoch. No latch was
    /// advanced; a committee latch certificate for an epoch at or above every latch resynchronises
    /// them.
    LatchesDisagree,
}

/// Mandatory monotonic write-ahead epoch latch guarding stateful `Jorts` signing (`[P0-04]`).
///
/// Implementations MUST durably persist `(epoch, mu)` *before* returning `Ok(epoch)` so that no
/// power loss or process crash can ever reuse `epoch` on a distinct message `mu' != mu`.
pub trait StatefulEpochLatch {
    /// Reserve the next strictly unused epoch `ep < 2^max_sigs_log2`, binding it to `mu`.
    fn reserve_next_epoch(
        &mut self,
        max_sigs_log2: usize,
        mu: &[u8; 32],
    ) -> Result<u64, EpochLatchError>;

    /// Crash-recovery retry: permits re-evaluating the **currently latched in-flight epoch**
    /// if and only if `epoch` matches the last reserved epoch AND `mu` matches the bound digest
    /// in constant time. Refuses all equivocation attempts with [`EpochLatchError::EquivocationRefused`].
    fn retry_latched_epoch(&mut self, epoch: u64, mu: &[u8; 32]) -> Result<u64, EpochLatchError>;

    /// The epoch [`Self::reserve_next_epoch`] would return. Changes nothing.
    fn peek_next_epoch(&self) -> u64;

    /// The most recently reserved `(epoch, mu)`, if any. Changes nothing.
    fn peek_in_flight(&self) -> Option<(u64, [u8; 32])>;

    /// Durably reserve exactly `epoch`, bound to `mu`, skipping any lower unused epochs.
    ///
    /// Succeeds when [`Self::check_reserve_epoch_at`] does, with the same durability contract as
    /// [`Self::reserve_next_epoch`]. Skipped epochs are never handed out afterwards, so a latch
    /// that was absent from earlier signatures can join a committee-certified epoch without
    /// reusing one. If `(epoch, mu)` is already the in-flight reservation, nothing changes.
    fn reserve_epoch_at(
        &mut self,
        epoch: u64,
        max_sigs_log2: usize,
        mu: &[u8; 32],
    ) -> Result<(), EpochLatchError>;

    /// Whether [`Self::reserve_epoch_at`] would accept `(epoch, mu)`. Changes nothing, so a
    /// signing set can test every member's latch before any of them advances.
    ///
    /// `Ok(true)`: `(epoch, mu)` is already the in-flight reservation. `Ok(false)`: `epoch` is
    /// unused and at or above the next epoch. Errors: [`EpochLatchError::EquivocationRefused`] if
    /// `epoch` is in flight for another digest, [`EpochLatchError::StaleEpoch`] if the latch has
    /// moved past it, [`EpochLatchError::Exhausted`] beyond `2^max_sigs_log2`.
    fn check_reserve_epoch_at(
        &self,
        epoch: u64,
        max_sigs_log2: usize,
        mu: &[u8; 32],
    ) -> Result<bool, EpochLatchError> {
        if max_sigs_log2 == 0 || max_sigs_log2 > 62 {
            return Err(EpochLatchError::InvalidCapacity);
        }
        if epoch >= 1u64 << max_sigs_log2 {
            return Err(EpochLatchError::Exhausted);
        }
        if let Some((latched_ep, latched_mu)) = self.peek_in_flight()
            && latched_ep == epoch
        {
            return if ct_eq_bytes32(&latched_mu, mu) {
                Ok(true)
            } else {
                Err(EpochLatchError::EquivocationRefused)
            };
        }
        if epoch < self.peek_next_epoch() {
            return Err(EpochLatchError::StaleEpoch);
        }
        Ok(false)
    }
}

/// `no_std` monotonic epoch latch with bound `(epoch, mu)` crash-retry verification (`[P0-04]`).
/// Intentionally `!Clone` so epoch latches can never be forked into two reusable cursors.
/// For persistent disk deployments (`std`), use `FsWalEpochLatch` in `qsag-cli` / `dkg.rs` which
/// wraps this state machine with `fsync`-backed atomic WAL records.
#[derive(Debug, PartialEq, Eq)]
pub struct MonotonicEpochLatch {
    next_epoch: u64,
    in_flight: Option<(u64, [u8; 32])>,
}

impl MonotonicEpochLatch {
    /// Crate-private staging copy used strictly for crash-atomic WAL pre-write before commit.
    #[cfg(feature = "std")]
    #[inline]
    pub(crate) const fn stage_copy(&self) -> Self {
        Self {
            next_epoch: self.next_epoch,
            in_flight: self.in_flight,
        }
    }
    #[inline]
    pub const fn new(start_epoch: u64) -> Self {
        Self {
            next_epoch: start_epoch,
            in_flight: None,
        }
    }

    #[inline]
    pub const fn from_recovered_wal(next_epoch: u64, in_flight: Option<(u64, [u8; 32])>) -> Self {
        Self {
            next_epoch,
            in_flight,
        }
    }

    #[inline]
    pub const fn next_epoch(&self) -> u64 {
        self.next_epoch
    }

    #[inline]
    pub const fn in_flight(&self) -> Option<(u64, [u8; 32])> {
        self.in_flight
    }
}

impl Default for MonotonicEpochLatch {
    fn default() -> Self {
        Self::new(0)
    }
}

impl StatefulEpochLatch for MonotonicEpochLatch {
    fn reserve_next_epoch(
        &mut self,
        max_sigs_log2: usize,
        mu: &[u8; 32],
    ) -> Result<u64, EpochLatchError> {
        if max_sigs_log2 == 0 || max_sigs_log2 > 62 {
            return Err(EpochLatchError::InvalidCapacity);
        }
        let limit = 1u64 << max_sigs_log2;
        if self.next_epoch >= limit {
            return Err(EpochLatchError::Exhausted);
        }
        let ep = self.next_epoch;
        self.next_epoch = ep + 1;
        self.in_flight = Some((ep, *mu));
        Ok(ep)
    }

    fn retry_latched_epoch(&mut self, epoch: u64, mu: &[u8; 32]) -> Result<u64, EpochLatchError> {
        let Some((latched_ep, latched_mu)) = self.in_flight else {
            return Err(EpochLatchError::EpochNotInFlight);
        };
        if latched_ep != epoch {
            return Err(EpochLatchError::EpochNotInFlight);
        }
        if !ct_eq_bytes32(&latched_mu, mu) {
            return Err(EpochLatchError::EquivocationRefused);
        }
        Ok(latched_ep)
    }

    fn peek_next_epoch(&self) -> u64 {
        self.next_epoch
    }

    fn peek_in_flight(&self) -> Option<(u64, [u8; 32])> {
        self.in_flight
    }

    fn reserve_epoch_at(
        &mut self,
        epoch: u64,
        max_sigs_log2: usize,
        mu: &[u8; 32],
    ) -> Result<(), EpochLatchError> {
        if self.check_reserve_epoch_at(epoch, max_sigs_log2, mu)? {
            return Ok(());
        }
        // `epoch < 2^62` was checked above, so the increment cannot overflow.
        self.next_epoch = epoch + 1;
        self.in_flight = Some((epoch, *mu));
        Ok(())
    }
}

/// Single-party reference secret key `(sk_seed, sk_prf, pk_seed)`:
/// intentionally `!Clone`, redacted `Debug`, deterministically wiped on `Drop`, and never
/// instantiated in threshold MPC modules.
#[derive(PartialEq, Eq)]
pub struct PqSecretKey {
    pub sk_seed: [u8; 32],
    pub sk_prf: [u8; 32],
    pub pk_seed: [u8; 32],
}

impl fmt::Debug for PqSecretKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("PqSecretKey([REDACTED])")
    }
}

impl Drop for PqSecretKey {
    fn drop(&mut self) {
        wipe_bytes32(&mut self.sk_seed);
        wipe_bytes32(&mut self.sk_prf);
    }
}

/// Public key `(pk_seed, pk_root)` (`64` bytes canonical wire encoding).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct PqPublicKey {
    pub pk_seed: [u8; 32],
    pub pk_root: [u8; 32],
}

impl PqPublicKey {
    #[inline]
    pub fn to_wire_bytes(&self) -> [u8; 64] {
        let mut out = [0u8; 64];
        out[0..32].copy_from_slice(&self.pk_seed);
        out[32..64].copy_from_slice(&self.pk_root);
        out
    }

    #[inline]
    pub fn from_wire_bytes(raw: &[u8]) -> Result<Self, FaultStage> {
        if raw.len() != 64 {
            return Err(FaultStage::PublicKeyLength);
        }
        let mut pk_seed = [0u8; 32];
        let mut pk_root = [0u8; 32];
        pk_seed.copy_from_slice(&raw[0..32]);
        pk_root.copy_from_slice(&raw[32..64]);
        Ok(Self { pk_seed, pk_root })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LayerXmssSig {
    pub tsw_ctr: u32,
    pub wots_chains: Vec<[u8; 32]>,
    pub auth_path: Vec<[u8; 32]>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ForsTreeOpening {
    pub secret_val: [u8; 32],
    pub auth_path: Vec<[u8; 32]>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PqHashSig {
    pub r_rand: [u8; 32],
    pub msg_tsw_ctr: u32,
    pub leaf_global_idx: usize,
    pub fors_openings: Vec<ForsTreeOpening>,
    pub layer_sigs: Vec<LayerXmssSig>,
}

impl PqHashSig {
    /// Encode into canonical wire bytes (`PQ_WIRE_MAGIC` + fixed-layout fields for `params`).
    pub fn to_wire_bytes(&self, params: &PqHashParams) -> Result<Vec<u8>, FaultStage> {
        if !params.is_well_formed() || !params.leaf_idx_in_range(self.leaf_global_idx) {
            return Err(FaultStage::SignatureFraming);
        }
        if self.layer_sigs.len() != params.num_layers {
            return Err(FaultStage::LayerCountMismatch);
        }
        if self.msg_tsw_ctr != 0 {
            return Err(FaultStage::SignatureFraming);
        }
        if params.stateful {
            if !self.fors_openings.is_empty() {
                return Err(FaultStage::SignatureFraming);
            }
        } else if self.fors_openings.len() != params.fors_trees
            || self
                .fors_openings
                .iter()
                .any(|op| op.auth_path.len() != params.fors_height)
        {
            return Err(FaultStage::SignatureFraming);
        }
        if self.layer_sigs.iter().any(|ls| {
            ls.wots_chains.len() != params.ell1 || ls.auth_path.len() != params.subtree_height
        }) {
            return Err(FaultStage::SignatureFraming);
        }
        let Some(wire_len) = params.wire_sig_bytes_checked() else {
            return Err(FaultStage::SignatureFraming);
        };

        let mut out = Vec::with_capacity(wire_len);
        out.extend_from_slice(&PQ_WIRE_MAGIC);
        out.extend_from_slice(&self.r_rand);
        out.extend_from_slice(&self.msg_tsw_ctr.to_be_bytes());
        out.extend_from_slice(&(self.leaf_global_idx as u64).to_be_bytes());
        for op in &self.fors_openings {
            out.extend_from_slice(&op.secret_val);
            for sib in &op.auth_path {
                out.extend_from_slice(sib);
            }
        }
        for ls in &self.layer_sigs {
            out.extend_from_slice(&ls.tsw_ctr.to_be_bytes());
            for ch in &ls.wots_chains {
                out.extend_from_slice(ch);
            }
            for sib in &ls.auth_path {
                out.extend_from_slice(sib);
            }
        }
        debug_assert_eq!(out.len(), wire_len);
        Ok(out)
    }

    /// Decode canonical wire bytes (`PQ_WIRE_MAGIC` + body) without panicking on malformed inputs.
    pub fn from_wire_bytes(params: &PqHashParams, raw: &[u8]) -> Result<Self, FaultStage> {
        if !params.is_well_formed() {
            return Err(FaultStage::SignatureFraming);
        }
        if raw.len() < 5 || raw[0..5] != PQ_WIRE_MAGIC {
            return Err(FaultStage::HeaderMagicOrVersion);
        }
        let Some(expected_len) = params.wire_sig_bytes_checked() else {
            return Err(FaultStage::SignatureFraming);
        };
        if raw.len() != expected_len {
            return Err(FaultStage::SignatureFraming);
        }
        let mut off = 5usize;
        let mut r_rand = [0u8; 32];
        r_rand.copy_from_slice(&raw[off..off + 32]);
        off += 32;

        let msg_tsw_ctr = u32::from_be_bytes([raw[off], raw[off + 1], raw[off + 2], raw[off + 3]]);
        off += 4;
        if msg_tsw_ctr != 0 {
            return Err(FaultStage::SignatureFraming);
        }

        let leaf_u64 = u64::from_be_bytes([
            raw[off],
            raw[off + 1],
            raw[off + 2],
            raw[off + 3],
            raw[off + 4],
            raw[off + 5],
            raw[off + 6],
            raw[off + 7],
        ]);
        off += 8;
        let leaf_global_idx =
            usize::try_from(leaf_u64).map_err(|_| FaultStage::SignatureFraming)?;
        if !params.leaf_idx_in_range(leaf_global_idx) {
            return Err(FaultStage::SignatureFraming);
        }

        let mut fors_openings = Vec::new();
        if !params.stateful {
            fors_openings.reserve(params.fors_trees);
            for _ in 0..params.fors_trees {
                let mut secret_val = [0u8; 32];
                secret_val.copy_from_slice(&raw[off..off + 32]);
                off += 32;
                let mut auth_path = Vec::with_capacity(params.fors_height);
                for _ in 0..params.fors_height {
                    let mut sib = [0u8; 32];
                    sib.copy_from_slice(&raw[off..off + 32]);
                    off += 32;
                    auth_path.push(sib);
                }
                fors_openings.push(ForsTreeOpening {
                    secret_val,
                    auth_path,
                });
            }
        }

        let mut layer_sigs = Vec::with_capacity(params.num_layers);
        for _ in 0..params.num_layers {
            let tsw_ctr = u32::from_be_bytes([raw[off], raw[off + 1], raw[off + 2], raw[off + 3]]);
            off += 4;
            let mut wots_chains = Vec::with_capacity(params.ell1);
            for _ in 0..params.ell1 {
                let mut ch = [0u8; 32];
                ch.copy_from_slice(&raw[off..off + 32]);
                off += 32;
                wots_chains.push(ch);
            }
            let mut auth_path = Vec::with_capacity(params.subtree_height);
            for _ in 0..params.subtree_height {
                let mut sib = [0u8; 32];
                sib.copy_from_slice(&raw[off..off + 32]);
                off += 32;
                auth_path.push(sib);
            }
            layer_sigs.push(LayerXmssSig {
                tsw_ctr,
                wots_chains,
                auth_path,
            });
        }
        debug_assert_eq!(off, raw.len());
        Ok(Self {
            r_rand,
            msg_tsw_ctr,
            leaf_global_idx,
            fors_openings,
            layer_sigs,
        })
    }
}

/// Advance a WOTS+C chain `steps` iterations starting from `start_step`, wiping intermediate values.
#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the existing explicit protocol interface for callers"
)]
pub fn wots_chain_steps<S: TweakableHashSuite>(
    suite: S,
    pk_seed: &[u8; 32],
    layer: u32,
    tree: u64,
    kp: u32,
    chain: u32,
    start_step: u32,
    steps: usize,
    cur: [u8; 32],
) -> [u8; 32] {
    let mut val = cur;
    for s in 0..steps {
        let adrs = HashAdrs {
            layer,
            tree,
            kind: AdrsKind::WotsHash,
            key_pair: kp,
            chain_idx: chain,
            hash_step: start_step.wrapping_add(s as u32),
        };
        let next = th_chain_f(suite, pk_seed, &adrs, &val);
        wipe_bytes32(&mut val);
        val = next;
    }
    val
}

#[inline]
pub fn wots_secret_base<S: TweakableHashSuite>(
    suite: S,
    sk: &PqSecretKey,
    layer: u32,
    tree: u64,
    kp: u32,
    chain: u32,
) -> [u8; 32] {
    let adrs = HashAdrs {
        layer,
        tree,
        kind: AdrsKind::WotsPrf,
        key_pair: kp,
        chain_idx: chain,
        hash_step: 0,
    };
    th_secret_prf(suite, &sk.pk_seed, &sk.sk_seed, &adrs)
}

pub fn compute_wots_pk<S: TweakableHashSuite>(
    suite: S,
    params: &PqHashParams,
    sk: &PqSecretKey,
    layer: u32,
    tree: u64,
    kp: u32,
) -> [u8; 32] {
    let mut endpoints = Vec::with_capacity(params.ell1);
    for r in 0..params.ell1 {
        let mut base = wots_secret_base(suite, sk, layer, tree, kp, r as u32);
        let end = wots_chain_steps(
            suite,
            &sk.pk_seed,
            layer,
            tree,
            kp,
            r as u32,
            0,
            params.w - 1,
            base,
        );
        wipe_bytes32(&mut base);
        endpoints.push(end);
    }
    let adrs = HashAdrs {
        layer,
        tree,
        kind: AdrsKind::WotsPk,
        key_pair: kp,
        chain_idx: 0,
        hash_step: 0,
    };
    th_tweak_tl(suite, &sk.pk_seed, &adrs, &endpoints)
}

#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the existing explicit protocol interface for callers"
)]
pub fn recover_wots_pk_from_sig<S: TweakableHashSuite>(
    suite: S,
    params: &PqHashParams,
    pk_seed: &[u8; 32],
    layer: u32,
    tree: u64,
    kp: u32,
    digits: &[usize],
    sig_chains: &[[u8; 32]],
) -> [u8; 32] {
    let mut endpoints = Vec::with_capacity(params.ell1);
    for r in 0..params.ell1 {
        let dr = digits.get(r).copied().unwrap_or(0);
        let sig_val = sig_chains.get(r).copied().unwrap_or([0u8; 32]);
        let rem = (params.w - 1).saturating_sub(dr);
        endpoints.push(wots_chain_steps(
            suite, pk_seed, layer, tree, kp, r as u32, dr as u32, rem, sig_val,
        ));
    }
    let adrs = HashAdrs {
        layer,
        tree,
        kind: AdrsKind::WotsPk,
        key_pair: kp,
        chain_idx: 0,
        hash_step: 0,
    };
    th_tweak_tl(suite, pk_seed, &adrs, &endpoints)
}

/// Build bottom-up Merkle authentication path from pre-evaluated leaf slice `leaves[0..2^height]`.
#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the existing explicit protocol interface for callers"
)]
pub fn build_merkle_auth_path_from_leaves<S: TweakableHashSuite>(
    suite: S,
    pk_seed: &[u8; 32],
    layer: u32,
    tree: u64,
    node_kind: AdrsKind,
    key_pair: u32,
    leaves: &[[u8; 32]],
    height: usize,
    base_node_idx: usize,
    local_idx: usize,
) -> ([u8; 32], Vec<[u8; 32]>) {
    debug_assert_eq!(leaves.len(), 1usize << height);
    let levels = merkle_levels_in(
        suite,
        pk_seed,
        layer,
        tree,
        node_kind,
        key_pair,
        leaves,
        base_node_idx,
    );
    let path = (0..height)
        .map(|h| levels[h][(local_idx >> h) ^ 1])
        .collect();
    (levels[height][0], path)
}

/// Every level of a Merkle tree over `leaves` (a power of two), leaves first. This is the one
/// tree builder of the hash-based suites: a node of height `h` has `chain_idx = h` and
/// `hash_step = (base_node_idx << (height - h)) + index in its level`, the addressing
/// [`walk_merkle_auth_path`] verifies. `key_pair` is the few-time key pair for a FORS or PORS
/// tree and `0` for a hypertree subtree.
#[expect(
    clippy::too_many_arguments,
    reason = "Same explicit address fields as the other tree functions"
)]
pub fn merkle_levels_in<S: TweakableHashSuite>(
    suite: S,
    pk_seed: &[u8; 32],
    layer: u32,
    tree: u64,
    node_kind: AdrsKind,
    key_pair: u32,
    leaves: &[[u8; 32]],
    base_node_idx: usize,
) -> Vec<Vec<[u8; 32]>> {
    debug_assert!(leaves.len().is_power_of_two());
    let height = leaves.len().trailing_zeros() as usize;
    let mut levels = Vec::with_capacity(height + 1);
    levels.push(leaves.to_vec());
    for h in 1..=height {
        let offset = base_node_idx << (height - h);
        let next: Vec<[u8; 32]> = levels[h - 1]
            .as_chunks::<2>()
            .0
            .iter()
            .enumerate()
            .map(|(i, pair)| {
                let adrs = HashAdrs {
                    layer,
                    tree,
                    kind: node_kind,
                    key_pair,
                    chain_idx: h as u32,
                    hash_step: (offset + i) as u32,
                };
                th_node_h(suite, pk_seed, &adrs, &pair[0], &pair[1])
            })
            .collect();
        levels.push(next);
    }
    levels
}

/// Top-down `build_merkle_from_leaves_topdown`.
#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the existing explicit protocol interface for callers"
)]
pub fn build_merkle_from_leaves_topdown<S: TweakableHashSuite>(
    suite: S,
    pk_seed: &[u8; 32],
    layer: u32,
    tree: u64,
    node_kind: AdrsKind,
    key_pair: u32,
    leaves: &[[u8; 32]],
    height: usize,
    base_node_idx: usize,
    local_idx: usize,
) -> ([u8; 32], Vec<[u8; 32]>) {
    let (root, mut bottom_up_path) = build_merkle_auth_path_from_leaves(
        suite,
        pk_seed,
        layer,
        tree,
        node_kind,
        key_pair,
        leaves,
        height,
        base_node_idx,
        local_idx,
    );
    bottom_up_path.reverse();
    (root, bottom_up_path)
}

#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the existing explicit protocol interface for callers"
)]
pub fn walk_merkle_auth_path<S: TweakableHashSuite>(
    suite: S,
    pk_seed: &[u8; 32],
    layer: u32,
    tree: u64,
    node_kind: AdrsKind,
    key_pair: u32,
    height: usize,
    node_idx: usize,
    local_idx: usize,
    leaf_hash: [u8; 32],
    auth_path: &[[u8; 32]],
) -> Option<[u8; 32]> {
    if height == 0 {
        if auth_path.is_empty() {
            Some(leaf_hash)
        } else {
            None
        }
    } else {
        if auth_path.is_empty() {
            return None;
        }
        let sib = auth_path[0];
        let rest = &auth_path[1..];
        let half = 1usize << (height - 1);
        let adrs = HashAdrs {
            layer,
            tree,
            kind: node_kind,
            key_pair,
            chain_idx: height as u32,
            hash_step: node_idx as u32,
        };
        if local_idx < half {
            let sub = walk_merkle_auth_path(
                suite,
                pk_seed,
                layer,
                tree,
                node_kind,
                key_pair,
                height - 1,
                2 * node_idx,
                local_idx,
                leaf_hash,
                rest,
            )?;
            Some(th_node_h(suite, pk_seed, &adrs, &sub, &sib))
        } else {
            let sub = walk_merkle_auth_path(
                suite,
                pk_seed,
                layer,
                tree,
                node_kind,
                key_pair,
                height - 1,
                2 * node_idx + 1,
                local_idx - half,
                leaf_hash,
                rest,
            )?;
            Some(th_node_h(suite, pk_seed, &adrs, &sib, &sub))
        }
    }
}

/// FORS secret leaf PRF binding `(fors_tree_idx, leaf_in_tree)` in `(chain_idx, hash_step)`
/// so `fors_trees * 2^fors_height` can never overflow `u32` (`[P1-04]`).
#[inline]
pub fn fors_secret_leaf<S: TweakableHashSuite>(
    suite: S,
    sk: &PqSecretKey,
    tree_idx: u64,
    kp_idx: u32,
    fors_tree_idx: u32,
    leaf_in_tree: u32,
) -> [u8; 32] {
    let adrs = HashAdrs {
        layer: 0,
        tree: tree_idx,
        kind: AdrsKind::ForsPrf,
        key_pair: kp_idx,
        chain_idx: fors_tree_idx,
        hash_step: leaf_in_tree,
    };
    th_secret_prf(suite, &sk.pk_seed, &sk.sk_seed, &adrs)
}

/// The FORS public key of hypertree leaf `(tree, key_pair)`: the compression of its tree
/// roots. Signers, verifiers and the MPC engines all call this one function.
pub fn fors_pk_from_roots<S: TweakableHashSuite>(
    suite: S,
    pk_seed: &[u8; 32],
    tree: u64,
    key_pair: u32,
    roots: &[[u8; 32]],
) -> [u8; 32] {
    let adrs = HashAdrs {
        layer: 0,
        tree,
        kind: AdrsKind::ForsRoots,
        key_pair,
        chain_idx: 0,
        hash_step: 0,
    };
    th_tweak_tl(suite, pk_seed, &adrs, roots)
}

#[inline]
pub fn fors_leaf_hash_from_secret<S: TweakableHashSuite>(
    suite: S,
    pk_seed: &[u8; 32],
    tree_idx: u64,
    kp_idx: u32,
    fors_tree_idx: u32,
    leaf_in_tree: u32,
    sec_val: &[u8; 32],
) -> [u8; 32] {
    let adrs = HashAdrs {
        layer: 0,
        tree: tree_idx,
        kind: AdrsKind::ForsTree,
        key_pair: kp_idx,
        chain_idx: fors_tree_idx,
        hash_step: leaf_in_tree,
    };
    th_chain_f(suite, pk_seed, &adrs, sec_val)
}

/// Extract `width` bits (`0..=64`) starting at bit offset `start_bit` with **zero modulo wrapping**
/// (`[P0-02]`, `[P0-03]`). Returns `None` if `width > 64` or `start_bit + width > bytes.len() * 8`.
#[inline]
pub fn extract_bit_window_checked(bytes: &[u8], start_bit: usize, width: usize) -> Option<u64> {
    if width > 64 {
        return None;
    }
    if width == 0 {
        return Some(0);
    }
    let end_bit = start_bit.checked_add(width)?;
    if end_bit > bytes.len().checked_mul(8)? {
        return None;
    }
    let mut acc = 0u64;
    for b in 0..width {
        let pos = start_bit + b;
        let byte_val = bytes[pos / 8];
        let bit = ((byte_val >> (7 - (pos % 8))) & 1) as u64;
        acc = (acc << 1) | bit;
    }
    Some(acc)
}

/// Derive `(leaf_global_idx, fors_indices[0..k])` for stateless `Corduroy` / `Baggy` from
/// strictly disjoint XOF byte windows of `th_xof_msg(suite, r_rand, pk_seed, pk_root, mu)` (`[P0-03]`).
pub fn derive_stateless_leaf_and_fors_indices<S: TweakableHashSuite>(
    suite: S,
    params: &PqHashParams,
    r_rand: &[u8; 32],
    pk_seed: &[u8; 32],
    pk_root: &[u8; 32],
    mu: &[u8; 32],
) -> Option<(usize, Vec<usize>)> {
    if params.stateful || !params.is_well_formed() {
        return None;
    }
    let fors_bits = params.fors_trees.checked_mul(params.fors_height)?;
    let fors_bytes = fors_bits.div_ceil(8);
    let tree_bits = params.total_tree_bits()?;
    let tree_bytes = tree_bits.div_ceil(8);
    let total_bytes = fors_bytes.checked_add(tree_bytes)?;

    let xof = th_xof_msg(suite, r_rand, pk_seed, pk_root, mu, total_bytes);
    let fors_slice = &xof[..fors_bytes];
    let tree_slice = &xof[fors_bytes..total_bytes];

    let mut idxs = Vec::with_capacity(params.fors_trees);
    for j in 0..params.fors_trees {
        let bit_off = j.checked_mul(params.fors_height)?;
        let idx_u64 = extract_bit_window_checked(fors_slice, bit_off, params.fors_height)?;
        idxs.push(usize::try_from(idx_u64).ok()?);
    }
    let leaf_u64 = extract_bit_window_checked(tree_slice, 0, tree_bits)?;
    let leaf_global_idx = usize::try_from(leaf_u64).ok()?;
    Some((leaf_global_idx, idxs))
}

pub fn compute_xmss_subtree_root<S: TweakableHashSuite>(
    suite: S,
    params: &PqHashParams,
    sk: &PqSecretKey,
    layer: u32,
    tree_idx: u64,
) -> [u8; 32] {
    let leaf_count = 1usize << params.subtree_height;
    let mut leaves = Vec::with_capacity(leaf_count);
    for kp in 0..leaf_count {
        leaves.push(compute_wots_pk(
            suite, params, sk, layer, tree_idx, kp as u32,
        ));
    }
    let (root, _) = build_merkle_from_leaves_topdown(
        suite,
        &sk.pk_seed,
        layer,
        tree_idx,
        AdrsKind::Tree,
        0,
        &leaves,
        params.subtree_height,
        0,
        0,
    );
    root
}

/// Derive canonical `PqPublicKey` `(pk_seed, pk_root)`.
pub fn derive_public_key<S: TweakableHashSuite>(
    suite: S,
    params: &PqHashParams,
    sk: &PqSecretKey,
) -> PqPublicKey {
    let top_layer = (params.num_layers.saturating_sub(1)) as u32;
    let pk_root = compute_xmss_subtree_root(suite, params, sk, top_layer, 0);
    PqPublicKey {
        pk_seed: sk.pk_seed,
        pk_root,
    }
}

/// Internal core hypertree + FORS signer shared ONLY after stateless `H_msg` leaf derivation or
/// stateful `StatefulEpochLatch` reservation has fixed `(leaf_global_idx, r_rand)`.
#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the existing explicit protocol interface for callers"
)]
pub(crate) fn sign_hypertree_core<S: TweakableHashSuite>(
    suite: S,
    params: &PqHashParams,
    sk: &PqSecretKey,
    pk: &PqPublicKey,
    mu: &[u8; 32],
    r_rand: [u8; 32],
    leaf_global_idx: usize,
    fors_idxs: Option<&[usize]>,
    max_grind: u32,
) -> Option<PqHashSig> {
    let sub_leaves = 1usize << params.subtree_height;
    let (fors_openings, mut cur_root) = if params.stateful {
        (Vec::new(), *mu)
    } else {
        let idxs = fors_idxs?;
        let kp0 = (leaf_global_idx % sub_leaves) as u32;
        let tree0 = (leaf_global_idx / sub_leaves) as u64;
        let fors_leaf_count = 1usize << params.fors_height;
        let mut openings = Vec::with_capacity(params.fors_trees);
        let mut roots = Vec::with_capacity(params.fors_trees);
        for (j, &idx_j) in idxs.iter().enumerate().take(params.fors_trees) {
            let mut leaves_j = Vec::with_capacity(fors_leaf_count);
            let mut revealed_sec = [0u8; 32];
            for u in 0..fors_leaf_count {
                let mut sec = fors_secret_leaf(suite, sk, tree0, kp0, j as u32, u as u32);
                leaves_j.push(fors_leaf_hash_from_secret(
                    suite,
                    &sk.pk_seed,
                    tree0,
                    kp0,
                    j as u32,
                    u as u32,
                    &sec,
                ));
                if u == idx_j {
                    revealed_sec = sec;
                }
                wipe_bytes32(&mut sec);
            }
            let (root_j, path_j) = build_merkle_from_leaves_topdown(
                suite,
                &sk.pk_seed,
                0,
                tree0,
                AdrsKind::ForsTree,
                kp0,
                &leaves_j,
                params.fors_height,
                j,
                idx_j,
            );
            roots.push(root_j);
            openings.push(ForsTreeOpening {
                secret_val: revealed_sec,
                auth_path: path_j,
            });
        }
        let fors_pk = fors_pk_from_roots(suite, &sk.pk_seed, tree0, kp0, &roots);
        (openings, fors_pk)
    };

    let mut layer_sigs = Vec::with_capacity(params.num_layers);
    let mut cur_global = leaf_global_idx;
    for layer_idx in 0..params.num_layers {
        let kp_idx = cur_global % sub_leaves;
        let tree_idx_nat = cur_global / sub_leaves;
        let tree_idx = tree_idx_nat as u64;
        let layer_u32 = layer_idx as u32;
        let kp_u32 = kp_idx as u32;

        // CRITICAL ([P0-02], [P0-03]): ONLY stateful one-time layer 0 hashes `(r_rand, mu)`.
        // Every upper layer (`layer_idx >= 1`) AND stateless layer 0 (`!stateful`)
        // signs the deterministic child/FORS root WITHOUT `r_rand`!
        let (ctr, digits, _) = if params.stateful && layer_idx == 0 {
            grind_tsw_leaf_counter(
                suite,
                params.w,
                params.ell1,
                params.target_sum(),
                &r_rand,
                &sk.pk_seed,
                &pk.pk_root,
                &cur_root,
                tree_idx,
                kp_u32,
                max_grind,
            )?
        } else {
            grind_tsw_internal_counter(
                suite,
                params.w,
                params.ell1,
                params.target_sum(),
                &sk.pk_seed,
                &pk.pk_root,
                &cur_root,
                layer_u32,
                tree_idx,
                kp_u32,
                max_grind,
            )?
        };

        let mut wots_chains = Vec::with_capacity(params.ell1);
        for (r, &dr) in digits.iter().enumerate().take(params.ell1) {
            let mut base = wots_secret_base(suite, sk, layer_u32, tree_idx, kp_u32, r as u32);
            let ch = wots_chain_steps(
                suite,
                &sk.pk_seed,
                layer_u32,
                tree_idx,
                kp_u32,
                r as u32,
                0,
                dr,
                base,
            );
            wipe_bytes32(&mut base);
            wots_chains.push(ch);
        }
        let mut subtree_leaves = Vec::with_capacity(sub_leaves);
        for kp in 0..sub_leaves {
            subtree_leaves.push(compute_wots_pk(
                suite, params, sk, layer_u32, tree_idx, kp as u32,
            ));
        }
        let (next_root, auth_path) = build_merkle_from_leaves_topdown(
            suite,
            &sk.pk_seed,
            layer_u32,
            tree_idx,
            AdrsKind::Tree,
            0,
            &subtree_leaves,
            params.subtree_height,
            0,
            kp_idx,
        );
        layer_sigs.push(LayerXmssSig {
            tsw_ctr: ctr,
            wots_chains,
            auth_path,
        });
        cur_root = next_root;
        cur_global = tree_idx_nat;
    }

    let sig = PqHashSig {
        r_rand,
        msg_tsw_ctr: 0,
        leaf_global_idx,
        fors_openings,
        layer_sigs,
    };
    if !verify_pq_hash_sig_prehashed(suite, params, pk, mu, &sig) {
        return None;
    }
    Some(sig)
}

/// Stateless single-party reference signer (`Corduroy` / `Baggy`).
/// Rejects `params.stateful == true` and derives `leaf_global_idx` strictly from
/// `th_xof_msg(r_rand, pk_seed, pk_root, mu)` (`[P0-03]`).
pub fn eval_single_sign_stateless<S: TweakableHashSuite>(
    suite: S,
    params: &PqHashParams,
    sk: &PqSecretKey,
    pk: &PqPublicKey,
    msg: &[u8],
    opt_rand: &[u8],
    max_grind: u32,
) -> Option<PqHashSig> {
    if !params.is_well_formed() || params.stateful {
        return None;
    }
    let mu = th_pre_hash(suite, &pk.pk_seed, &pk.pk_root, msg);
    let r_rand = th_prf_msg(suite, &sk.sk_prf, opt_rand, &mu);
    let (leaf_global_idx, fors_idxs) = derive_stateless_leaf_and_fors_indices(
        suite,
        params,
        &r_rand,
        &pk.pk_seed,
        &pk.pk_root,
        &mu,
    )?;
    sign_hypertree_core(
        suite,
        params,
        sk,
        pk,
        &mu,
        r_rand,
        leaf_global_idx,
        Some(&fors_idxs),
        max_grind,
    )
}

/// Stateful single-party reference signer (`JortsPoseidon2`) gated behind a mandatory
/// [`StatefulEpochLatch`] and 100% deterministic `r_rand` (`[P0-04]`).
///
/// The caller holds the whole key, so `latch` is the only latch there is: a committee of one
/// whose single reservation is the committee-wide one. A key held as shares has one latch per
/// holder and must not be signed through this function; the threshold signers in
/// `poseidon2_mpc` additionally require full attendance or a committee latch certificate.
pub fn eval_single_sign_stateful<S: TweakableHashSuite, L: StatefulEpochLatch>(
    suite: S,
    params: &PqHashParams,
    sk: &PqSecretKey,
    pk: &PqPublicKey,
    latch: &mut L,
    msg: &[u8],
    max_grind: u32,
) -> Result<PqHashSig, EpochLatchError> {
    if !params.is_well_formed() || !params.stateful {
        return Err(EpochLatchError::InvalidCapacity);
    }
    let mu = th_pre_hash(suite, &pk.pk_seed, &pk.pk_root, msg);
    let ep = latch.reserve_next_epoch(params.max_sigs_log2, &mu)?;
    let leaf_global_idx = usize::try_from(ep).map_err(|_| EpochLatchError::Exhausted)?;
    if !params.leaf_idx_in_range(leaf_global_idx) {
        return Err(EpochLatchError::Exhausted);
    }
    let r_rand = derive_stateful_r_rand(suite, &sk.sk_prf, ep, &pk.pk_seed, &mu);
    sign_hypertree_core(
        suite,
        params,
        sk,
        pk,
        &mu,
        r_rand,
        leaf_global_idx,
        None,
        max_grind,
    )
    .ok_or(EpochLatchError::PersistenceFailure)
}

/// Crash-recovery retry for an in-flight stateful `Jorts` signature: succeeds **if and only if**
/// `epoch` is the currently latched epoch in `latch` AND `msg` hashes to the exact bound `mu`,
/// producing a bit-for-bit identical signature (`[P0-04]`).
#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the existing explicit protocol interface for callers"
)]
pub fn retry_single_sign_stateful<S: TweakableHashSuite, L: StatefulEpochLatch>(
    suite: S,
    params: &PqHashParams,
    sk: &PqSecretKey,
    pk: &PqPublicKey,
    latch: &mut L,
    epoch: u64,
    msg: &[u8],
    max_grind: u32,
) -> Result<PqHashSig, EpochLatchError> {
    if !params.is_well_formed() || !params.stateful {
        return Err(EpochLatchError::InvalidCapacity);
    }
    let mu = th_pre_hash(suite, &pk.pk_seed, &pk.pk_root, msg);
    let ep = latch.retry_latched_epoch(epoch, &mu)?;
    let leaf_global_idx = usize::try_from(ep).map_err(|_| EpochLatchError::Exhausted)?;
    let r_rand = derive_stateful_r_rand(suite, &sk.sk_prf, ep, &pk.pk_seed, &mu);
    sign_hypertree_core(
        suite,
        params,
        sk,
        pk,
        &mu,
        r_rand,
        leaf_global_idx,
        None,
        max_grind,
    )
    .ok_or(EpochLatchError::PersistenceFailure)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FaultCacheError {
    Rejected,
}

/// A verified OTS input, indexed by its canonical WOTS public-key address.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FaultCacheRecord {
    pub address: [u8; 32],
    pub root: [u8; 32],
    pub tsw_ctr: u32,
}

/// Transactional fault cache. Failure must prevent release of the candidate signature.
pub trait FaultCacheJournal {
    fn commit_verified(
        &mut self,
        key_id: [u8; 32],
        entries: &[FaultCacheRecord],
    ) -> Result<(), FaultCacheError>;
}

/// Authenticated persistent upper-layer cache, matching `verifyBeforeReleaseAll`.
/// Layer zero is intentionally excluded: the stateless FORS leaf can be revisited.
#[cfg(feature = "std")]
pub struct FsFaultCacheJournal(crate::durable_ledger::Ledger);

#[cfg(feature = "std")]
impl FsFaultCacheJournal {
    pub fn create_new(
        path: impl Into<std::path::PathBuf>,
        mac_key: [u8; 32],
    ) -> Result<Self, FaultCacheError> {
        crate::durable_ledger::Ledger::create(path, mac_key, b"QSAG.TSW.FAULT.CACHE/v1")
            .map(Self)
            .map_err(|_| FaultCacheError::Rejected)
    }
    pub fn open_existing_at_least(
        path: impl Into<std::path::PathBuf>,
        mac_key: [u8; 32],
        minimum: crate::durable_ledger::LedgerCheckpoint,
    ) -> Result<Self, FaultCacheError> {
        crate::durable_ledger::Ledger::open(path, mac_key, b"QSAG.TSW.FAULT.CACHE/v1", minimum)
            .map(Self)
            .map_err(|_| FaultCacheError::Rejected)
    }
    pub fn checkpoint(&self) -> crate::durable_ledger::LedgerCheckpoint {
        self.0.checkpoint()
    }
}

#[cfg(feature = "std")]
impl FaultCacheJournal for FsFaultCacheJournal {
    fn commit_verified(
        &mut self,
        key_id: [u8; 32],
        entries: &[FaultCacheRecord],
    ) -> Result<(), FaultCacheError> {
        let mut records = self.0.read().map_err(|_| FaultCacheError::Rejected)?;
        for entry in entries {
            let mut key = key_id.to_vec();
            key.extend_from_slice(&entry.address);
            let mut value = entry.root.to_vec();
            value.extend_from_slice(&entry.tsw_ctr.to_be_bytes());
            if records.get(&key).is_some_and(|old| old != &value) {
                return Err(FaultCacheError::Rejected);
            }
            records.insert(key, value);
        }
        self.0
            .commit(&records)
            .map_err(|_| FaultCacheError::Rejected)
    }
}

/// Verify every layer, then atomically commit the verified upper-layer `(root, tsw_ctr)`
/// inputs before the caller releases the signature. Invalid candidates never alter the cache.
pub fn verify_before_release_with_journal<S: TweakableHashSuite>(
    suite: S,
    params: &PqHashParams,
    pk: &PqPublicKey,
    msg: &[u8],
    sig: &PqHashSig,
    journal: &mut impl FaultCacheJournal,
) -> Result<(), FaultCacheError> {
    let mu = th_pre_hash(suite, &pk.pk_seed, &pk.pk_root, msg);
    let mut entries = Vec::new();
    if !verify_pq_hash_sig_collect(suite, params, pk, &mu, sig, &mut entries) {
        return Err(FaultCacheError::Rejected);
    }
    let key_id = cshake256_32(b"QSAG.TSW.FAULT.KEY/v1", &pk.to_wire_bytes());
    journal.commit_verified(key_id, &entries)
}

/// Opt-in persistent reference signing; legacy stateless entry points remain unchanged.
#[expect(
    clippy::too_many_arguments,
    reason = "Reference signer plus caller-owned durable fault journal"
)]
pub fn eval_single_sign_stateless_with_journal<S: TweakableHashSuite>(
    suite: S,
    params: &PqHashParams,
    sk: &PqSecretKey,
    pk: &PqPublicKey,
    msg: &[u8],
    opt_rand: &[u8],
    max_grind: u32,
    journal: &mut impl FaultCacheJournal,
) -> Option<PqHashSig> {
    let sig = eval_single_sign_stateless(suite, params, sk, pk, msg, opt_rand, max_grind)?;
    verify_before_release_with_journal(suite, params, pk, msg, &sig, journal).ok()?;
    Some(sig)
}

fn verify_pq_hash_sig_prehashed<S: TweakableHashSuite>(
    suite: S,
    params: &PqHashParams,
    pk: &PqPublicKey,
    mu: &[u8; 32],
    sig: &PqHashSig,
) -> bool {
    verify_pq_hash_sig_collect(suite, params, pk, mu, sig, &mut Vec::new())
}

fn verify_pq_hash_sig_collect<S: TweakableHashSuite>(
    suite: S,
    params: &PqHashParams,
    pk: &PqPublicKey,
    mu: &[u8; 32],
    sig: &PqHashSig,
    entries: &mut Vec<FaultCacheRecord>,
) -> bool {
    if !params.is_well_formed() || !params.leaf_idx_in_range(sig.leaf_global_idx) {
        return false;
    }
    if sig.layer_sigs.len() != params.num_layers || sig.msg_tsw_ctr != 0 {
        return false;
    }
    let sub_leaves = 1usize << params.subtree_height;

    let mut cur_root = if params.stateful {
        if !sig.fors_openings.is_empty() {
            return false;
        }
        *mu
    } else {
        if sig.fors_openings.len() != params.fors_trees {
            return false;
        }
        let Some((derived_leaf_idx, idxs)) = derive_stateless_leaf_and_fors_indices(
            suite,
            params,
            &sig.r_rand,
            &pk.pk_seed,
            &pk.pk_root,
            mu,
        ) else {
            return false;
        };
        // CRITICAL ([P0-03]): Reject signatures whose leaf index diverges from XOF `H_msg`!
        if sig.leaf_global_idx != derived_leaf_idx {
            return false;
        }
        let kp0 = (sig.leaf_global_idx % sub_leaves) as u32;
        let tree0 = (sig.leaf_global_idx / sub_leaves) as u64;
        let mut roots = Vec::with_capacity(params.fors_trees);
        let mut j = 0;
        while j < params.fors_trees {
            let idx_j = idxs[j];
            let op = &sig.fors_openings[j];
            let leaf_h = fors_leaf_hash_from_secret(
                suite,
                &pk.pk_seed,
                tree0,
                kp0,
                j as u32,
                idx_j as u32,
                &op.secret_val,
            );
            let Some(root_j) = walk_merkle_auth_path(
                suite,
                &pk.pk_seed,
                0,
                tree0,
                AdrsKind::ForsTree,
                kp0,
                params.fors_height,
                j,
                idx_j,
                leaf_h,
                &op.auth_path,
            ) else {
                return false;
            };
            roots.push(root_j);
            j += 1;
        }
        fors_pk_from_roots(suite, &pk.pk_seed, tree0, kp0, &roots)
    };

    let mut cur_global = sig.leaf_global_idx;
    for (layer_idx, lsig) in sig.layer_sigs.iter().enumerate() {
        let kp_idx = cur_global % sub_leaves;
        let tree_idx_nat = cur_global / sub_leaves;
        let tree_idx = tree_idx_nat as u64;
        let layer_u32 = layer_idx as u32;
        let kp_u32 = kp_idx as u32;

        let hmsg = if params.stateful && layer_idx == 0 {
            th_hash_leaf_msg(
                suite,
                &sig.r_rand,
                &pk.pk_seed,
                &pk.pk_root,
                &cur_root,
                tree_idx,
                kp_u32,
                lsig.tsw_ctr,
            )
        } else {
            th_hash_internal_node(
                suite,
                &pk.pk_seed,
                &pk.pk_root,
                &cur_root,
                layer_u32,
                tree_idx,
                kp_u32,
                lsig.tsw_ctr,
            )
        };
        let Some(digits) = extract_base_w_digits_checked(params.w, params.ell1, &hmsg) else {
            return false;
        };
        if !check_target_sum(params.w, params.ell1, params.target_sum(), &digits) {
            return false;
        }
        if lsig.wots_chains.len() != params.ell1 {
            return false;
        }
        let wots_pk = recover_wots_pk_from_sig(
            suite,
            params,
            &pk.pk_seed,
            layer_u32,
            tree_idx,
            kp_u32,
            &digits,
            &lsig.wots_chains,
        );
        let Some(next_root) = walk_merkle_auth_path(
            suite,
            &pk.pk_seed,
            layer_u32,
            tree_idx,
            AdrsKind::Tree,
            0,
            params.subtree_height,
            0,
            kp_idx,
            wots_pk,
            &lsig.auth_path,
        ) else {
            return false;
        };
        if layer_idx > 0 {
            entries.push(FaultCacheRecord {
                address: HashAdrs {
                    layer: layer_u32,
                    tree: tree_idx,
                    kind: AdrsKind::WotsPk,
                    key_pair: kp_u32,
                    chain_idx: 0,
                    hash_step: 0,
                }
                .to_bytes(),
                root: cur_root,
                tsw_ctr: lsig.tsw_ctr,
            });
        }
        cur_root = next_root;
        cur_global = tree_idx_nat;
    }

    ct_eq_bytes32(&cur_root, &pk.pk_root)
}

/// Unified verifier for stateless `Corduroy` / `Baggy` and stateful `Jorts`.
pub fn verify_pq_hash_sig<S: TweakableHashSuite>(
    suite: S,
    params: &PqHashParams,
    pk: &PqPublicKey,
    msg: &[u8],
    sig: &PqHashSig,
) -> bool {
    let mu = th_pre_hash(suite, &pk.pk_seed, &pk.pk_root, msg);
    verify_pq_hash_sig_prehashed(suite, params, pk, &mu, sig)
}

/// Batch verification relation over `Poseidon2` `Jorts` signatures enforcing non-emptiness AND
/// strict pairwise distinctness of `(pk, sig.leaf_global_idx)` (`[P0-04]`).
pub fn valid_jorts_batch(params: &PqHashParams, items: &[(PqPublicKey, &[u8], PqHashSig)]) -> bool {
    if !params.stateful || !params.is_well_formed() || items.is_empty() {
        return false;
    }
    let mut seen_keys_epochs: Vec<([u8; 64], u64)> = Vec::with_capacity(items.len());
    for (pk, _, sig) in items {
        seen_keys_epochs.push((pk.to_wire_bytes(), sig.leaf_global_idx as u64));
    }
    seen_keys_epochs.sort_unstable();
    for pair in seen_keys_epochs.windows(2) {
        if pair[0] == pair[1] {
            return false;
        }
    }
    items
        .iter()
        .all(|(pk, msg, sig)| verify_pq_hash_sig(Poseidon2Suite, params, pk, msg, sig))
}

/// Enrolled identity digest `idCommit = cSHAKE256("QSAG.PQ.HYBRID.ID/v1", encodeMultiFrame [pk1, pk2])`.
#[inline]
pub fn compute_hybrid_id_commit(pk1_bytes: &[u8], pk2_bytes: &[u8]) -> [u8; 32] {
    let frame = encode_multi_frame(&[pk1_bytes, pk2_bytes]);
    cshake256_32(HYBRID_ID_CUSTOM, &frame)
}

/// Domain-separated bound message `encodeMultiFrame([HYBRID_MSG_TAG, id_commit, pk1, pk2, msg])`
/// signed by BOTH component schemes so neither signature can be stripped or replayed under a
/// substitute partner key (`[P2-04]`).
#[inline]
pub fn build_hybrid_bound_message(
    id_commit: &[u8; 32],
    pk1_bytes: &[u8],
    carried_pk2: &PqPublicKey,
    msg: &[u8],
) -> Vec<u8> {
    let pk2_wire = carried_pk2.to_wire_bytes();
    encode_multi_frame(&[HYBRID_MSG_TAG, id_commit, pk1_bytes, &pk2_wire, msg])
}

/// Committed-identity pinning check.
#[inline]
pub fn check_hybrid_pinning(
    id_commit: &[u8; 32],
    pk1_bytes: &[u8],
    carried_pk2: &PqPublicKey,
) -> bool {
    let pk2_wire = carried_pk2.to_wire_bytes();
    let cand = compute_hybrid_id_commit(pk1_bytes, &pk2_wire);
    ct_eq_bytes32(&cand, id_commit)
}

/// Wire envelope carrying auxiliary signature `sig1`, candidate `carried_pk2`, and PQ signature `sig2`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HybridPinnedSig<Sig1> {
    pub sig1: Sig1,
    pub carried_pk2: PqPublicKey,
    pub sig2: PqHashSig,
}

/// Construct a committed-identity hybrid signature binding `id_commit || pk1 || pk2 || msg` into
/// both component signatures.
#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the existing explicit protocol interface for callers"
)]
pub fn sign_hybrid_pinned_stateless<S: TweakableHashSuite, Sig1, FSign1>(
    suite: S,
    params: &PqHashParams,
    pk1_bytes: &[u8],
    sign_s1: FSign1,
    sk2: &PqSecretKey,
    pk2: &PqPublicKey,
    msg: &[u8],
    opt_rand: &[u8],
    max_grind: u32,
) -> Option<([u8; 32], HybridPinnedSig<Sig1>)>
where
    FSign1: FnOnce(&[u8]) -> Sig1,
{
    let pk2_wire = pk2.to_wire_bytes();
    let id_commit = compute_hybrid_id_commit(pk1_bytes, &pk2_wire);
    let bound_msg = build_hybrid_bound_message(&id_commit, pk1_bytes, pk2, msg);
    let sig1 = sign_s1(&bound_msg);
    let sig2 =
        eval_single_sign_stateless(suite, params, sk2, pk2, &bound_msg, opt_rand, max_grind)?;
    Some((
        id_commit,
        HybridPinnedSig {
            sig1,
            carried_pk2: *pk2,
            sig2,
        },
    ))
}

/// Committed-identity hybrid signature verifier (`S_1 && S_2` bound under `id_commit || pk1 || pk2 || msg`).
pub fn verify_hybrid_pinned_sig<S: TweakableHashSuite, Sig1, F1>(
    suite: S,
    params: &PqHashParams,
    id_commit: &[u8; 32],
    pk1_bytes: &[u8],
    verify_s1: F1,
    msg: &[u8],
    hsig: &HybridPinnedSig<Sig1>,
) -> bool
where
    F1: FnOnce(&[u8], &[u8], &Sig1) -> bool,
{
    if !check_hybrid_pinning(id_commit, pk1_bytes, &hsig.carried_pk2) {
        return false;
    }
    let bound_msg = build_hybrid_bound_message(id_commit, pk1_bytes, &hsig.carried_pk2, msg);
    verify_s1(pk1_bytes, &bound_msg, &hsig.sig1)
        && verify_pq_hash_sig(suite, params, &hsig.carried_pk2, &bound_msg, &hsig.sig2)
}

/// Exact wire-codec failure stage distinguishing malformed syntax from cryptographic rejection.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FaultStage {
    HeaderMagicOrVersion,
    PublicKeyLength,
    SignatureFraming,
    LayerCountMismatch,
}

/// Tri-state verification reply (`VerifyReply`): never conflates `WireMalformed` with `Reject`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VerifyReply {
    Accept,
    Reject,
    WireMalformed(FaultStage),
}

/// Tri-state wire envelope verifier.
pub fn verify_pq_wire_envelope<S: TweakableHashSuite>(
    suite: S,
    params: &PqHashParams,
    raw_pk: &[u8],
    raw_msg: &[u8],
    magic_prefix: &[u8],
    r_rand_slice: &[u8],
    sig: &PqHashSig,
) -> VerifyReply {
    if magic_prefix != PQ_WIRE_MAGIC {
        return VerifyReply::WireMalformed(FaultStage::HeaderMagicOrVersion);
    }
    let Ok(pk) = PqPublicKey::from_wire_bytes(raw_pk) else {
        return VerifyReply::WireMalformed(FaultStage::PublicKeyLength);
    };
    if !params.is_well_formed() || !params.leaf_idx_in_range(sig.leaf_global_idx) {
        return VerifyReply::WireMalformed(FaultStage::SignatureFraming);
    }
    if sig.layer_sigs.len() != params.num_layers {
        return VerifyReply::WireMalformed(FaultStage::LayerCountMismatch);
    }
    if r_rand_slice.len() != 32 || r_rand_slice != sig.r_rand.as_slice() || sig.msg_tsw_ctr != 0 {
        return VerifyReply::WireMalformed(FaultStage::SignatureFraming);
    }
    if params.stateful {
        if !sig.fors_openings.is_empty() {
            return VerifyReply::WireMalformed(FaultStage::SignatureFraming);
        }
    } else if sig.fors_openings.len() != params.fors_trees
        || sig
            .fors_openings
            .iter()
            .any(|op| op.auth_path.len() != params.fors_height)
    {
        return VerifyReply::WireMalformed(FaultStage::SignatureFraming);
    }
    if sig.layer_sigs.iter().any(|ls| {
        ls.wots_chains.len() != params.ell1 || ls.auth_path.len() != params.subtree_height
    }) {
        return VerifyReply::WireMalformed(FaultStage::SignatureFraming);
    }
    if verify_pq_hash_sig(suite, params, &pk, raw_msg, sig) {
        VerifyReply::Accept
    } else {
        VerifyReply::Reject
    }
}

/// Injective canonical 5-limb 56-bit Goldilocks packing for 32-byte digests (`[P1-02]`).
/// Eliminates the $2^{32}$-collision modulo-$p$ bias of 4-limb 64-bit reduction.
#[inline]
pub fn pack_digest32_to_goldilocks5(digest: &[u8; 32]) -> [Goldilocks; 5] {
    pack_bytes32_to_limbs56_canonical(digest)
}

/// Inverse canonical check unpacking 5 56-bit Goldilocks limbs (`limbs[0..5] < 2^56`, big-endian
/// 7-byte chunks with canonical `[0x01, 0x00, 0x00]` suffix in `limbs[4]`) back to an exact 32-byte
/// digest (`None` if any limb exceeds 56 bits or violates the domain suffix).
pub fn unpack_goldilocks5_to_digest32(limbs: &[Goldilocks; 5]) -> Option<[u8; 32]> {
    let mut buf = [0u8; 35];
    for i in 0..5 {
        let v = limbs[i].canonical();
        if (v >> 56) != 0 {
            return None;
        }
        let be = v.to_be_bytes();
        buf[7 * i..7 * (i + 1)].copy_from_slice(&be[1..8]);
    }
    if buf[32] != 0x01 || buf[33] != 0x00 || buf[34] != 0x00 {
        wipe_slice(&mut buf);
        return None;
    }
    let mut out = [0u8; 32];
    out.copy_from_slice(&buf[0..32]);
    wipe_slice(&mut buf);
    Some(out)
}

impl core::fmt::Display for EpochLatchError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl core::error::Error for EpochLatchError {}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;

    #[cfg(feature = "std")]
    #[test]
    fn persistent_fault_cache_verifies_all_layers_and_commits_atomically() {
        let dir = std::env::temp_dir().join(std::format!(
            "qsag-fault-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir(&dir).unwrap();
        let path = dir.join("cache");
        let params = PqHashParams::COMPACT_GOLDEN;
        let sk = PqSecretKey {
            sk_seed: [1; 32],
            sk_prf: [2; 32],
            pk_seed: [3; 32],
        };
        let pk = derive_public_key(Cshake256Suite, &params, &sk);
        let mut journal = FsFaultCacheJournal::create_new(&path, [4; 32]).unwrap();
        let sig = eval_single_sign_stateless_with_journal(
            Cshake256Suite,
            &params,
            &sk,
            &pk,
            b"journal",
            &[0; 32],
            100_000,
            &mut journal,
        )
        .unwrap();
        let checkpoint = journal.checkpoint();
        assert!(
            verify_before_release_with_journal(
                Cshake256Suite,
                &params,
                &pk,
                b"tampered",
                &sig,
                &mut journal
            )
            .is_err()
        );
        assert_eq!(journal.checkpoint(), checkpoint);
        drop(journal);
        let mut journal =
            FsFaultCacheJournal::open_existing_at_least(&path, [4; 32], checkpoint).unwrap();
        verify_before_release_with_journal(
            Cshake256Suite,
            &params,
            &pk,
            b"journal",
            &sig,
            &mut journal,
        )
        .unwrap();
        let mu = th_pre_hash(Cshake256Suite, &pk.pk_seed, &pk.pk_root, b"journal");
        let mut entries = Vec::new();
        assert!(verify_pq_hash_sig_collect(
            Cshake256Suite,
            &params,
            &pk,
            &mu,
            &sig,
            &mut entries
        ));
        assert_eq!(entries.len(), params.num_layers - 1);
        let key = cshake256_32(b"QSAG.TSW.FAULT.KEY/v1", &pk.to_wire_bytes());
        let checkpoint = journal.checkpoint();
        entries[0].root[0] ^= 1;
        assert!(journal.commit_verified(key, &entries).is_err());
        assert_eq!(journal.checkpoint(), checkpoint);
        entries[0].root[0] ^= 1;
        entries[0].tsw_ctr ^= 1;
        assert!(journal.commit_verified(key, &entries).is_err());
        // Conflicting duplicates in a new batch cannot partially commit.
        let mut duplicate = entries[0].clone();
        duplicate.root[0] ^= 1;
        assert!(
            journal
                .commit_verified([9; 32], &[entries[0].clone(), duplicate])
                .is_err()
        );
        assert_eq!(journal.checkpoint(), checkpoint);
        drop(journal);
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn test_stateless_tsw_roundtrip_hmsg_leaf_binding_and_upper_layer_determinism() {
        let sk = PqSecretKey {
            sk_seed: [0x11; 32],
            sk_prf: [0x22; 32],
            pk_seed: [0x33; 32],
        };
        let params = PqHashParams::COMPACT_GOLDEN;
        assert!(params.is_well_formed());
        let pk = derive_public_key(Cshake256Suite, &params, &sk);
        let sig1 = eval_single_sign_stateless(
            Cshake256Suite,
            &params,
            &sk,
            &pk,
            b"tsw-msg-1",
            &[0x44; 32],
            100_000,
        )
        .expect("stateless sign 1");
        assert!(verify_pq_hash_sig(
            Cshake256Suite,
            &params,
            &pk,
            b"tsw-msg-1",
            &sig1
        ));
        assert!(!verify_pq_hash_sig(
            Cshake256Suite,
            &params,
            &pk,
            b"tsw-msg-tampered",
            &sig1
        ));

        // Tampering with leaf_global_idx MUST be rejected by H_msg binding ([P0-03]).
        let mut forged_leaf = sig1.clone();
        forged_leaf.leaf_global_idx ^= 1;
        assert!(!verify_pq_hash_sig(
            Cshake256Suite,
            &params,
            &pk,
            b"tsw-msg-1",
            &forged_leaf
        ));

        // Upper-layer determinism ([P0-02]): two distinct messages landing in the same top-layer
        // kp index MUST produce bit-for-bit identical top-layer WOTS+C chains & tsw_ctr!
        let mut saw_same_top_kp = false;
        for nonce in 0..32u8 {
            let sig_other = eval_single_sign_stateless(
                Cshake256Suite,
                &params,
                &sk,
                &pk,
                &[b'M', nonce],
                &[nonce; 32],
                100_000,
            )
            .expect("stateless sign loop");
            let top_shift = (params.num_layers - 1) * params.subtree_height;
            if (sig_other.leaf_global_idx >> top_shift) == (sig1.leaf_global_idx >> top_shift)
                && sig_other.r_rand != sig1.r_rand
            {
                assert_eq!(
                    sig_other.layer_sigs[params.num_layers - 1],
                    sig1.layer_sigs[params.num_layers - 1],
                    "top-layer WOTS+C signature MUST be 100% deterministic and independent of r_rand"
                );
                saw_same_top_kp = true;
                break;
            }
        }
        assert!(
            saw_same_top_kp,
            "expected collision in 4-leaf top subtree within 32 trials"
        );

        let wire = sig1.to_wire_bytes(&params).unwrap();
        assert_eq!(&wire[0..5], b"QSAG\x01");
        let decoded = PqHashSig::from_wire_bytes(&params, &wire).unwrap();
        assert_eq!(decoded, sig1);
        assert_eq!(
            verify_pq_wire_envelope(
                Cshake256Suite,
                &params,
                &pk.to_wire_bytes(),
                b"tsw-msg-1",
                &PQ_WIRE_MAGIC,
                &sig1.r_rand,
                &decoded
            ),
            VerifyReply::Accept
        );
    }

    #[test]
    fn test_stateful_jorts_epoch_latch_retry_idempotence_and_batch_uniqueness() {
        let sk = PqSecretKey {
            sk_seed: [0x51; 32],
            sk_prf: [0x62; 32],
            pk_seed: [0x73; 32],
        };
        let params = PqHashParams::COMPACT_JORTS;
        assert!(params.is_well_formed());
        let pk = derive_public_key(Poseidon2Suite, &params, &sk);
        let mut latch = MonotonicEpochLatch::new(0);

        let sig0 = eval_single_sign_stateful(
            Poseidon2Suite,
            &params,
            &sk,
            &pk,
            &mut latch,
            b"block-vote-epoch-0",
            100_000,
        )
        .expect("epoch 0 sign");
        assert_eq!(sig0.leaf_global_idx, 0);
        assert!(verify_pq_hash_sig(
            Poseidon2Suite,
            &params,
            &pk,
            b"block-vote-epoch-0",
            &sig0
        ));

        // Crash-retry on SAME (epoch=0, msg) MUST produce bit-identical signature ([P0-04]).
        let sig0_retry = retry_single_sign_stateful(
            Poseidon2Suite,
            &params,
            &sk,
            &pk,
            &mut latch,
            0,
            b"block-vote-epoch-0",
            100_000,
        )
        .expect("idempotent retry");
        assert_eq!(sig0_retry, sig0);

        // Crash-retry on SAME epoch=0 with DIFFERENT msg MUST be refused!
        let equiv = retry_single_sign_stateful(
            Poseidon2Suite,
            &params,
            &sk,
            &pk,
            &mut latch,
            0,
            b"equivocating-fork-vote",
            100_000,
        );
        assert_eq!(equiv, Err(EpochLatchError::EquivocationRefused));

        let sig1 = eval_single_sign_stateful(
            Poseidon2Suite,
            &params,
            &sk,
            &pk,
            &mut latch,
            b"block-vote-epoch-1",
            100_000,
        )
        .expect("epoch 1 sign");
        assert_eq!(sig1.leaf_global_idx, 1);

        // Batch with distinct epochs passes; duplicate (pk, epoch) batch MUST be rejected!
        let valid_batch = vec![
            (pk, b"block-vote-epoch-0".as_slice(), sig0.clone()),
            (pk, b"block-vote-epoch-1".as_slice(), sig1),
        ];
        assert!(valid_jorts_batch(&params, &valid_batch));

        let replay_batch = vec![
            (pk, b"block-vote-epoch-0".as_slice(), sig0.clone()),
            (pk, b"block-vote-epoch-0".as_slice(), sig0),
        ];
        assert!(!valid_jorts_batch(&params, &replay_batch));
    }

    #[test]
    fn test_hybrid_pinned_sig_binds_identity_and_5limb_canonical_packing() {
        let sk2 = PqSecretKey {
            sk_seed: [0xA1; 32],
            sk_prf: [0xB2; 32],
            pk_seed: [0xC3; 32],
        };
        let params = PqHashParams::COMPACT_GOLDEN;
        let pk2 = derive_public_key(Cshake256Suite, &params, &sk2);
        let pk1 = b"aux-ed25519-mock-pk-bytes-32len!";

        let mock_sign1 = |m: &[u8]| cshake256_32(b"MOCK.S1", m);
        let mock_verify1 =
            |_pk1: &[u8], m: &[u8], s1: &[u8; 32]| ct_eq_bytes32(&cshake256_32(b"MOCK.S1", m), s1);

        let (id_commit, hsig) = sign_hybrid_pinned_stateless(
            Cshake256Suite,
            &params,
            pk1,
            mock_sign1,
            &sk2,
            &pk2,
            b"hybrid-payload",
            &[0x55; 32],
            100_000,
        )
        .expect("hybrid sign");

        assert!(verify_hybrid_pinned_sig(
            Cshake256Suite,
            &params,
            &id_commit,
            pk1,
            mock_verify1,
            b"hybrid-payload",
            &hsig
        ));
        // Stripped component sig2 MUST NOT verify as a standalone signature on raw msg ([P2-04])!
        assert!(!verify_pq_hash_sig(
            Cshake256Suite,
            &params,
            &pk2,
            b"hybrid-payload",
            &hsig.sig2
        ));

        let digest = [0xFFu8; 32];
        let limbs = pack_digest32_to_goldilocks5(&digest);
        assert_eq!(unpack_goldilocks5_to_digest32(&limbs), Some(digest));
    }

    #[test]
    fn test_extract_base_w_digits_checked_cross_byte_bitstream() {
        assert_eq!(
            extract_base_w_digits_checked(8, 2, &[0xe0]),
            Some(vec![7, 0])
        );
        assert_eq!(
            extract_base_w_digits_checked(8, 5, &[0, 0]),
            Some(vec![0; 5])
        );
        // 0b101_011_11 | 0b0_100_0000 -> digits 5, 3, 6, 4 in base-8 (3 bits MSB-first).
        assert_eq!(
            extract_base_w_digits_checked(8, 4, &[0b1010_1111, 0b0100_0000]),
            Some(vec![5, 3, 6, 4])
        );
        // Insufficient bits (3 * 3 = 9 > 8) returns None without panicking.
        assert_eq!(extract_base_w_digits_checked(8, 3, &[0xff]), None);
        // Non-dividing widths w = 32 (5 bits), 64 (6 bits), 128 (7 bits) span bytes cleanly.
        assert_eq!(
            extract_base_w_digits_checked(32, 3, &[0b1000_1010, 0b1011_1110]),
            Some(vec![17, 10, 31])
        );
        assert_eq!(
            extract_base_w_digits_checked(64, 2, &[0b1000_0111, 0b0011_0000]),
            Some(vec![33, 51])
        );
        assert_eq!(
            extract_base_w_digits_checked(128, 2, &[0b1000_0010, 0b1111_1100]),
            Some(vec![65, 63])
        );
    }
}
