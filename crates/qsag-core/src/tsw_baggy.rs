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
    let mask = w - 1;
    let mut out = Vec::with_capacity(ell1);
    if lg_w == 8 {
        for &b in digest_bytes.iter().take(ell1) {
            out.push(b as usize);
        }
    } else {
        let digits_per_byte = 8 / lg_w;
        for idx in 0..ell1 {
            let byte_idx = idx / digits_per_byte;
            let slot_in_byte = idx % digits_per_byte;
            let shift = (digits_per_byte - 1 - slot_in_byte) * lg_w;
            let b = digest_bytes[byte_idx] as usize;
            out.push((b >> shift) & mask);
        }
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

