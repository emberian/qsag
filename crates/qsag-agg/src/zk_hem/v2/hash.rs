//! Hashing of zk-Hem v2: 400-bit digests, the Fiat-Shamir transcript with a 400-bit chain
//! value, Merkle trees with Steiner-pruned multiproofs, and Stage-0 salts.
//!
//! Both profiles use the Keccak sponge of v1 with capacity 512 (cSHAKE256 or TurboSHAKE256)
//! and squeeze 50 bytes. Every use has its own customization string, distinct from all v1
//! strings, so no v2 hash input is a v1 hash input. Frames are unambiguous: a tree input starts
//! with a tag byte and has a length fixed by the tag and the public geometry; a transcript
//! input is a sequence of length-prefixed fields.

use alloc::collections::BTreeSet;
use alloc::vec;
use alloc::vec::Vec;

use super::field5::Fp5;
use super::params::{DIGEST_BYTES, EXT_BYTES, Profile, SALT_BYTES, TREE_NONCE_BYTES};
use crate::field::{Goldilocks, GoldilocksOps as _};
use crate::sponge::{
    cshake256_from_midstate_into, cshake256_static_midstate, turboshake256_from_midstate_into,
    turboshake256_static_midstate,
};

/// A Merkle digest or a transcript chain value.
pub type Digest = [u8; DIGEST_BYTES];

const TREE_CUSTOM: &[u8] = b"QSAG.ZKHEM2.TREE/v1";
const FS_CUSTOM: &[u8] = b"QSAG.ZKHEM2.FS/v1";
const TREE_MIDSTATE: [u64; 25] = cshake256_static_midstate(TREE_CUSTOM);
const FS_MIDSTATE: [u64; 25] = cshake256_static_midstate(FS_CUSTOM);
const TURBO_TREE_MIDSTATE: [u64; 25] = turboshake256_static_midstate(TREE_CUSTOM);
const TURBO_FS_MIDSTATE: [u64; 25] = turboshake256_static_midstate(FS_CUSTOM);

const TAG_NODE: u8 = 0x00;
const TAG_ROOT: u8 = 0x01;
const TAG_SALT: u8 = 0x02;
const TAG_LEAF_STAGE0: u8 = 0x10;
const TAG_LEAF_EXT: u8 = 0x12;

/// Largest tree depth a v2 verifier accepts.
pub const MAX_LOG_LEAVES: usize = 28;

/// The hash of a profile, in its two domains.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Hasher {
    turbo: bool,
    turbo_fs_domain: &'static [u64; 25],
}

impl Hasher {
    pub const fn new(profile: Profile) -> Self {
        Self {
            turbo: profile.uses_turboshake(),
            turbo_fs_domain: &TURBO_FS_MIDSTATE,
        }
    }

    #[inline]
    fn tree_into(self, input: &[u8], out: &mut [u8]) {
        if self.turbo {
            turboshake256_from_midstate_into(&TURBO_TREE_MIDSTATE, input, out);
        } else {
            cshake256_from_midstate_into(&TREE_MIDSTATE, input, out);
        }
    }

    #[inline]
    #[cfg(feature = "vulkan")]
    pub(crate) fn tree_midstate(self) -> &'static [u64; 25] {
        if self.turbo {
            &TURBO_TREE_MIDSTATE
        } else {
            &TREE_MIDSTATE
        }
    }
    fn tree(self, input: &[u8]) -> Digest {
        let mut out = [0u8; DIGEST_BYTES];
        self.tree_into(input, &mut out);
        out
    }

    #[inline]
    fn fs_into(self, input: &[u8], out: &mut [u8]) {
        if self.turbo {
            turboshake256_from_midstate_into(self.turbo_fs_domain, input, out);
        } else {
            cshake256_from_midstate_into(&FS_MIDSTATE, input, out);
        }
    }

    /// Internal node `node_idx` (heap numbering, the top node is 1): 105 bytes.
    #[inline]
    pub fn node(self, node_idx: u32, left: &Digest, right: &Digest) -> Digest {
        let mut buf = [0u8; 5 + 2 * DIGEST_BYTES];
        buf[0] = TAG_NODE;
        buf[1..5].copy_from_slice(&node_idx.to_le_bytes());
        buf[5..5 + DIGEST_BYTES].copy_from_slice(left);
        buf[5 + DIGEST_BYTES..].copy_from_slice(right);
        self.tree(&buf)
    }

    /// The commitment: the top node bound to the stage and the depth of its tree.
    #[inline]
    pub fn root(self, stage: u8, log_leaves: u8, top: &Digest) -> Digest {
        let mut buf = [0u8; 3 + DIGEST_BYTES];
        buf[0] = TAG_ROOT;
        buf[1] = stage;
        buf[2] = log_leaves;
        buf[3..].copy_from_slice(top);
        self.tree(&buf)
    }

    /// Salt of Stage-0 leaf `leaf_idx` from the prover's secret salt seed.
    #[inline]
    pub fn salt(self, salt_seed: &[u8; 32], leaf_idx: u32) -> [u8; SALT_BYTES] {
        let mut buf = [0u8; 37];
        buf[0] = TAG_SALT;
        buf[1..33].copy_from_slice(salt_seed);
        buf[33..].copy_from_slice(&leaf_idx.to_le_bytes());
        let mut out = [0u8; SALT_BYTES];
        self.tree_into(&buf, &mut out);
        qsag_asm::volatile_fill(&mut buf, 0u8);
        out
    }

    /// Stage-0 leaf: the per-tree 256-bit nonce, the per-leaf salt, the symbols of the table
    /// codeword on one fiber and the symbol of the mask codeword at the point below the fiber.
    ///
    /// Binding `tree_nonce` into every Stage-0 leaf domain-separates Stage-0 trees across
    /// proofs and split-share committers, eliminating the `|D'|` multi-proof salt birthday
    /// factor (cross-proof collision probability drops to `binom(P, 2) / 2^256`).
    pub fn leaf_stage0(
        self,
        tree_nonce: &[u8; TREE_NONCE_BYTES],
        leaf_idx: u32,
        salt: &[u8; SALT_BYTES],
        z: &[Goldilocks],
        r: Fp5,
    ) -> Digest {
        debug_assert!(z.len().is_power_of_two() && z.len() <= 64);
        let mut buf = [0u8; 6 + TREE_NONCE_BYTES + SALT_BYTES + 8 * 64 + EXT_BYTES];
        let header = 6 + TREE_NONCE_BYTES + SALT_BYTES;
        let used = header + 8 * z.len() + EXT_BYTES;
        buf[0] = TAG_LEAF_STAGE0;
        buf[1] = z.len().trailing_zeros() as u8;
        buf[2..6].copy_from_slice(&leaf_idx.to_le_bytes());
        buf[6..6 + TREE_NONCE_BYTES].copy_from_slice(tree_nonce);
        buf[6 + TREE_NONCE_BYTES..header].copy_from_slice(salt);
        let (zs, rs) = buf[header..used].split_at_mut(8 * z.len());
        for (dst, v) in zs.as_chunks_mut::<8>().0.iter_mut().zip(z) {
            *dst = v.to_le_bytes();
        }
        rs.copy_from_slice(&r.to_le_bytes());
        let out = self.tree(&buf[..used]);
        qsag_asm::volatile_fill(&mut buf, 0u8);
        out
    }

    /// Leaf of a later stage: the symbols of a challenge-field codeword on one fiber.
    pub fn leaf_ext(self, stage: u8, leaf_idx: u32, vals: &[Fp5]) -> Digest {
        debug_assert!(vals.len().is_power_of_two() && vals.len() <= 64);
        let mut buf = [0u8; 7 + EXT_BYTES * 64];
        let used = 7 + EXT_BYTES * vals.len();
        buf[0] = TAG_LEAF_EXT;
        buf[1] = stage;
        buf[2] = vals.len().trailing_zeros() as u8;
        buf[3..7].copy_from_slice(&leaf_idx.to_le_bytes());
        for (dst, v) in buf[7..used]
            .as_chunks_mut::<EXT_BYTES>()
            .0
            .iter_mut()
            .zip(vals)
        {
            *dst = v.to_le_bytes();
        }
        self.tree(&buf[..used])
    }
}

/// Hash operations used by the binary Canopy multiproof traversal.
pub trait CanopyHash<const N: usize>: Copy + Sync {
    fn node(self, index: u32, left: &[u8; N], right: &[u8; N]) -> [u8; N];
    fn root(self, stage: u8, depth: u8, top: &[u8; N]) -> [u8; N];
    fn pair_order(self, u: u64, hu: [u8; N], hs: [u8; N]) -> Option<([u8; N], [u8; N])>;
}

impl CanopyHash<DIGEST_BYTES> for Hasher {
    fn node(self, index: u32, left: &Digest, right: &Digest) -> Digest {
        self.node(index, left, right)
    }
    fn root(self, stage: u8, depth: u8, top: &Digest) -> Digest {
        self.root(stage, depth, top)
    }
    fn pair_order(self, u: u64, hu: Digest, hs: Digest) -> Option<(Digest, Digest)> {
        qsag_whir_verified::step_merkle_pair_order_400(u, 0, hu, hs).map(|p| (p.left, p.right))
    }
}

pub type MerkleTree = CanopyTree<DIGEST_BYTES>;

pub fn verify_multiproof(
    hasher: Hasher,
    stage: u8,
    depth: usize,
    root: &Digest,
    leaves: &[(usize, Digest)],
    siblings: &[Digest],
) -> bool {
    verify_canopy(hasher, stage, depth, root, leaves, siblings)
}

/// A Merkle tree over `2^log_leaves` leaf digests, all nodes kept (`nodes[1]` is the top node,
/// leaf `i` is `nodes[2^log_leaves + i]`).
pub struct CanopyTree<const N: usize> {
    log_leaves: usize,
    nodes: Vec<[u8; N]>,
    root: [u8; N],
}

impl<const N: usize> CanopyTree<N> {
    /// Build the tree of `stage` over `leaves`, whose number is a power of two.
    pub fn build(hasher: impl CanopyHash<N>, stage: u8, leaves: Vec<[u8; N]>) -> Self {
        let n = leaves.len();
        assert!(n.is_power_of_two() && n <= 1 << MAX_LOG_LEAVES);
        let log_leaves = n.trailing_zeros() as usize;
        let mut nodes = vec![[0u8; N]; n];
        nodes.extend(leaves);
        let mut width = n / 2;
        while width >= 1 {
            let (upper, lower) = nodes.split_at_mut(2 * width);
            let children = &lower[..2 * width];
            crate::pcs::fill_indexed(&mut upper[width..], |i| {
                hasher.node((width + i) as u32, &children[2 * i], &children[2 * i + 1])
            });
            width /= 2;
        }
        let root = hasher.root(stage, log_leaves as u8, &nodes[1.min(nodes.len() - 1)]);
        Self {
            log_leaves,
            nodes,
            root,
        }
    }

    #[cfg(feature = "vulkan")]
    pub(crate) fn from_heap(hasher: impl CanopyHash<N>, stage: u8, nodes: Vec<[u8; N]>) -> Self {
        let log_leaves = (nodes.len() / 2).trailing_zeros() as usize;
        let root = hasher.root(stage, log_leaves as u8, &nodes[1]);
        Self {
            log_leaves,
            nodes,
            root,
        }
    }
    pub fn root(&self) -> [u8; N] {
        self.root
    }

    pub fn log_leaves(&self) -> usize {
        self.log_leaves
    }

    /// Sibling digests outside the subtree spanned by `sorted_leaves` (strictly increasing),
    /// bottom-up and left to right: the order [`verify_multiproof`] consumes.
    pub fn open(&self, sorted_leaves: &[usize]) -> Vec<[u8; N]> {
        let n = 1usize << self.log_leaves;
        assert!(sorted_leaves.windows(2).all(|w| w[0] < w[1]));
        assert!(sorted_leaves.last().is_some_and(|&i| i < n));
        let mut active: Vec<usize> = sorted_leaves.iter().map(|&i| n + i).collect();
        let mut out = Vec::new();
        for _ in 0..self.log_leaves {
            let mut next = Vec::with_capacity(active.len());
            let mut k = 0;
            while k < active.len() {
                let u = active[k];
                if k + 1 < active.len() && active[k + 1] == (u ^ 1) {
                    k += 2;
                } else {
                    out.push(self.nodes[u ^ 1]);
                    k += 1;
                }
                next.push(u >> 1);
            }
            active = next;
        }
        out
    }
}

/// Check that `sorted_leaves` (strictly increasing indices with their leaf digests) are leaves
/// of the tree of `stage` and depth `log_leaves` committed to by `root`, consuming `siblings`
/// exactly.
pub(crate) fn verify_canopy<const N: usize>(
    hasher: impl CanopyHash<N>,
    stage: u8,
    log_leaves: usize,
    root: &[u8; N],
    sorted_leaves: &[(usize, [u8; N])],
    siblings: &[[u8; N]],
) -> bool {
    if log_leaves > MAX_LOG_LEAVES || sorted_leaves.is_empty() {
        return false;
    }
    let n = 1usize << log_leaves;
    if sorted_leaves.windows(2).any(|w| w[0].0 >= w[1].0)
        || sorted_leaves.last().is_some_and(|leaf| leaf.0 >= n)
    {
        return false;
    }
    let mut active: Vec<(usize, [u8; N])> =
        sorted_leaves.iter().map(|&(i, h)| (n + i, h)).collect();
    let mut cursor = 0usize;
    for _ in 0..log_leaves {
        let mut write = 0usize;
        let mut k = 0usize;
        while k < active.len() {
            let (u, hu) = active[k];
            let hs = if k + 1 < active.len() && active[k + 1].0 == (u ^ 1) {
                k += 2;
                active[k - 1].1
            } else {
                let Some(&supplied) = siblings.get(cursor) else {
                    return false;
                };
                cursor += 1;
                k += 1;
                supplied
            };
            let Some((left, right)) = hasher.pair_order(u as u64, hu, hs) else {
                return false;
            };
            active[write] = (u >> 1, hasher.node((u >> 1) as u32, &left, &right));
            write += 1;
        }
        active.truncate(write);
    }
    cursor == siblings.len()
        && matches!(active.as_slice(), [(1, top)] if hasher.root(stage, log_leaves as u8, top) == *root)
}

/// Number of siblings [`MerkleTree::open`] emits for `sorted_leaves`.
pub fn multiproof_len(log_leaves: usize, sorted_leaves: &[usize]) -> usize {
    let n = 1usize << log_leaves;
    let mut active: Vec<usize> = sorted_leaves.iter().map(|&i| n + i).collect();
    let mut count = 0;
    for _ in 0..log_leaves {
        let mut next = Vec::with_capacity(active.len());
        let mut k = 0;
        while k < active.len() {
            let u = active[k];
            if k + 1 < active.len() && active[k + 1] == (u ^ 1) {
                k += 2;
            } else {
                count += 1;
                k += 1;
            }
            next.push(u >> 1);
        }
        active = next;
    }
    count
}

fn push_field(frame: &mut Vec<u8>, field: &[u8]) {
    frame.extend_from_slice(&(field.len() as u64).to_le_bytes());
    frame.extend_from_slice(field);
}

fn frame(fields: &[&[u8]]) -> Vec<u8> {
    let mut out = Vec::with_capacity(fields.iter().map(|f| 8 + f.len()).sum());
    for f in fields {
        push_field(&mut out, f);
    }
    out
}

/// Fiat-Shamir transcript: a hash chain with a 400-bit chain value. Absorbing replaces the
/// chain value by the hash of (old value, label, payload); challenges are hashes of (chain
/// value, label, counter), the counter restarting at every absorb.
#[derive(Clone)]
pub struct Transcript {
    hasher: Hasher,
    chain: Digest,
    counter: u64,
    // Unlimited for the existing v2 channel. Public Hem charges every draw, including retries.
    remaining: Option<u16>,
}

impl Transcript {
    /// A transcript bound to the profile and to `binding`, the fields round 0 of the protocol
    /// lists.
    pub fn new(profile: Profile, binding: &[&[u8]]) -> Self {
        Self::init(Hasher::new(profile), profile.wire_tag(), binding)
    }

    pub(crate) fn turbo_domain(
        domain: &'static [u64; 25],
        tag: u8,
        binding: &[&[u8]],
        calls: u16,
    ) -> Self {
        let mut transcript = Self::init(
            Hasher {
                turbo: true,
                turbo_fs_domain: domain,
            },
            tag,
            binding,
        );
        transcript.remaining = Some(calls.saturating_sub(1));
        transcript
    }

    pub(crate) fn exhausted(&self) -> bool {
        self.remaining == Some(0)
    }

    fn charge(&mut self) -> bool {
        if let Some(left) = &mut self.remaining {
            if *left == 0 {
                return false;
            }
            *left -= 1;
        }
        true
    }

    fn init(hasher: Hasher, tag: u8, binding: &[&[u8]]) -> Self {
        let inner = frame(binding);
        let input = frame(&[b"INIT", &[tag], &inner]);
        let mut chain = [0u8; DIGEST_BYTES];
        hasher.fs_into(&input, &mut chain);
        Self {
            hasher,
            chain,
            counter: 0,
            remaining: None,
        }
    }

    pub fn hasher(&self) -> Hasher {
        self.hasher
    }

    pub fn absorb(&mut self, label: &[u8], payload: &[u8]) {
        if !self.charge() {
            return;
        }
        let input = frame(&[b"ABSORB", &self.chain, label, payload]);
        self.hasher.fs_into(&input, &mut self.chain);
        self.counter = 0;
    }

    pub fn absorb_fp5(&mut self, label: &[u8], val: Fp5) {
        self.absorb(label, &val.to_le_bytes());
    }

    pub fn absorb_fp5_slice(&mut self, label: &[u8], vals: &[Fp5]) {
        let mut bytes = Vec::with_capacity(EXT_BYTES * vals.len());
        for v in vals {
            bytes.extend_from_slice(&v.to_le_bytes());
        }
        self.absorb(label, &bytes);
    }

    fn squeeze_into(&mut self, kind: &[u8], label: &[u8], attempt: u64, out: &mut [u8]) -> bool {
        if !self.charge() {
            return false;
        }
        let input = frame(&[
            kind,
            &self.chain,
            label,
            &self.counter.to_le_bytes(),
            &attempt.to_le_bytes(),
        ]);
        self.hasher.fs_into(&input, out);
        true
    }

    /// A uniform base-field challenge: eight bytes, redrawn while they encode a value `>= p`.
    pub fn squeeze_base(&mut self, label: &[u8]) -> Goldilocks {
        let mut attempt = 0u64;
        loop {
            let mut raw = [0u8; 8];
            if !self.squeeze_into(b"SQUEEZE_F", label, attempt, &mut raw) {
                return Goldilocks::ONE;
            }
            if let Some(x) = Goldilocks::from_canonical_u64(u64::from_le_bytes(raw)) {
                self.counter += 1;
                return x;
            }
            attempt += 1;
        }
    }

    /// A uniform challenge in `F_{p^5}`: forty bytes, redrawn while any limb is `>= p`
    /// (probability below `2^-29.6` per draw), so an accepted value is exactly uniform.
    pub fn squeeze_fp5(&mut self, label: &[u8]) -> Fp5 {
        let mut attempt = 0u64;
        loop {
            let mut raw = [0u8; EXT_BYTES];
            if !self.squeeze_into(b"SQUEEZE_E", label, attempt, &mut raw) {
                return Fp5::ONE;
            }
            if let Some(x) = Fp5::from_le_bytes_canonical(raw) {
                self.counter += 1;
                return x;
            }
            attempt += 1;
        }
    }

    /// A uniform nonzero challenge.
    pub fn squeeze_fp5_nonzero(&mut self, label: &[u8]) -> Fp5 {
        loop {
            let x = self.squeeze_fp5(label);
            if !x.is_zero() {
                return x;
            }
        }
    }

    /// `min(count, num_groups)` distinct indices below `num_groups` (a power of two), sorted:
    /// uniform draws, repeated until enough distinct values have appeared.
    pub fn squeeze_distinct_indices(
        &mut self,
        label: &[u8],
        num_groups: usize,
        count: usize,
    ) -> Vec<usize> {
        assert!(num_groups.is_power_of_two());
        let target = count.min(num_groups);
        let groups_u64 = num_groups as u64;
        let mut set = BTreeSet::new();
        while set.len() < target {
            let mut raw = vec![0u8; 8 * (target - set.len())];
            if !self.squeeze_into(b"SQUEEZE_IDX", label, 0, &mut raw) {
                return (0..target).collect();
            }
            self.counter += 1;
            for word in raw.as_chunks::<8>().0 {
                let idx = qsag_whir_verified::canonical_query_group_idx(
                    u64::from_le_bytes(*word),
                    groups_u64,
                )
                .expect("power-of-two num_groups is non-zero") as usize;
                set.insert(idx);
            }
        }
        set.into_iter().collect()
    }

    /// The chain value.
    pub fn digest(&self) -> Digest {
        self.chain
    }
}

/// The verifier's side of the interaction as the prover and the verifier code see it: absorb
/// a prover message, draw a challenge. [`Transcript`] is the Fiat-Shamir instance; tests use
/// fixed coins to study the prover's messages as functions of the witness.
pub trait Channel {
    fn absorb(&mut self, label: &[u8], payload: &[u8]);
    fn squeeze_fp5(&mut self, label: &[u8]) -> Fp5;
    fn squeeze_distinct_indices(
        &mut self,
        label: &[u8],
        num_groups: usize,
        count: usize,
    ) -> Vec<usize>;

    fn absorb_fp5_slice(&mut self, label: &[u8], vals: &[Fp5]) {
        let mut bytes = Vec::with_capacity(EXT_BYTES * vals.len());
        for v in vals {
            bytes.extend_from_slice(&v.to_le_bytes());
        }
        self.absorb(label, &bytes);
    }

    fn squeeze_fp5_nonzero(&mut self, label: &[u8]) -> Fp5 {
        loop {
            let x = self.squeeze_fp5(label);
            if !x.is_zero() {
                return x;
            }
        }
    }
}

impl Channel for Transcript {
    fn absorb(&mut self, label: &[u8], payload: &[u8]) {
        Transcript::absorb(self, label, payload);
    }

    fn squeeze_fp5(&mut self, label: &[u8]) -> Fp5 {
        Transcript::squeeze_fp5(self, label)
    }

    fn squeeze_distinct_indices(
        &mut self,
        label: &[u8],
        num_groups: usize,
        count: usize,
    ) -> Vec<usize> {
        Transcript::squeeze_distinct_indices(self, label, num_groups, count)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn leaves(hasher: Hasher, n: usize) -> Vec<Digest> {
        (0..n)
            .map(|i| hasher.leaf_ext(1, i as u32, &[Fp5::from_u64(i as u64 + 1); 4]))
            .collect()
    }

    fn flip(d: &Digest, byte: usize) -> Digest {
        let mut out = *d;
        out[byte] ^= 1;
        out
    }

    #[test]
    fn profiles_and_domains_are_separated() {
        let c = Hasher::new(Profile::CshakeJohnson400);
        let t = Hasher::new(Profile::TurboShakeJohnson400);
        let (a, b) = ([1u8; DIGEST_BYTES], [2u8; DIGEST_BYTES]);
        assert_ne!(c.node(1, &a, &b), t.node(1, &a, &b));
        assert_ne!(c.node(1, &a, &b), c.node(2, &a, &b));
        assert_ne!(c.node(1, &a, &b), c.node(1, &b, &a));
        assert_ne!(c.root(0, 3, &a), c.root(1, 3, &a));
        assert_ne!(c.root(0, 3, &a), c.root(0, 4, &a));
        // A tree hash is not a transcript hash of the same bytes.
        let mut fs = [0u8; DIGEST_BYTES];
        let input = [7u8; 105];
        c.fs_into(&input, &mut fs);
        assert_ne!(c.tree(&input), fs);
        // The first 32 bytes are not a v1 canopy digest of the same input.
        let v1 = crate::sponge::cshake256_from_midstate_32(&crate::sponge::CANOPY_MIDSTATE, &input);
        assert_ne!(&c.tree(&input)[..32], &v1[..]);
    }

    #[test]
    fn leaf_digests_bind_every_field() {
        let h = Hasher::new(Profile::CshakeJohnson400);
        let z: Vec<Goldilocks> = (0..8).map(Goldilocks::from_u64_reduced).collect();
        let nonce = [0x42u8; TREE_NONCE_BYTES];
        let salt = [9u8; SALT_BYTES];
        let r = Fp5::from_u64(5);
        let base = h.leaf_stage0(&nonce, 3, &salt, &z, r);
        let mut nonce2 = nonce;
        nonce2[31] ^= 0x01;
        assert_ne!(base, h.leaf_stage0(&nonce2, 3, &salt, &z, r));
        assert_ne!(base, h.leaf_stage0(&nonce, 4, &salt, &z, r));
        let mut salt2 = salt;
        salt2[31] ^= 0x80;
        assert_ne!(base, h.leaf_stage0(&nonce, 3, &salt2, &z, r));
        for i in 0..8 {
            let mut z2 = z.clone();
            z2[i] += Goldilocks::ONE;
            assert_ne!(base, h.leaf_stage0(&nonce, 3, &salt, &z2, r));
        }
        assert_ne!(base, h.leaf_stage0(&nonce, 3, &salt, &z, r + Fp5::X.pow(4)));
        assert_ne!(base, h.leaf_stage0(&nonce, 3, &salt, &z[..4], r));

        let vals = [Fp5::from_u64(1), Fp5::X];
        let e = h.leaf_ext(1, 3, &vals);
        assert_ne!(e, h.leaf_ext(2, 3, &vals));
        assert_ne!(e, h.leaf_ext(1, 2, &vals));
        assert_ne!(e, h.leaf_ext(1, 3, &[Fp5::X, Fp5::from_u64(1)]));

        let seed = [3u8; 32];
        assert_ne!(h.salt(&seed, 0), h.salt(&seed, 1));
        assert_ne!(h.salt(&seed, 0), h.salt(&[4u8; 32], 0));
    }

    #[test]
    fn multiproof_roundtrip_and_tampering() {
        for profile in Profile::ALL {
            let h = Hasher::new(profile);
            for log_n in [0usize, 1, 3, 6] {
                let n = 1 << log_n;
                let lv = leaves(h, n);
                let tree = MerkleTree::build(h, 1, lv.clone());
                let sets: Vec<Vec<usize>> = vec![
                    vec![0],
                    vec![n - 1],
                    (0..n).collect(),
                    (0..n).step_by(3).collect(),
                    (0..n).filter(|i| i % 5 == 1 || i % 7 == 6).collect(),
                ];
                for set in sets.into_iter().filter(|s| !s.is_empty()) {
                    let sib = tree.open(&set);
                    assert_eq!(sib.len(), multiproof_len(log_n, &set));
                    let opened: Vec<(usize, Digest)> = set.iter().map(|&i| (i, lv[i])).collect();
                    assert!(verify_multiproof(h, 1, log_n, &tree.root(), &opened, &sib));
                    // Wrong stage, depth, root.
                    assert!(!verify_multiproof(h, 2, log_n, &tree.root(), &opened, &sib));
                    assert!(!verify_multiproof(
                        h,
                        1,
                        log_n + 1,
                        &tree.root(),
                        &opened,
                        &sib
                    ));
                    assert!(!verify_multiproof(
                        h,
                        1,
                        log_n,
                        &flip(&tree.root(), 49),
                        &opened,
                        &sib
                    ));
                    // A changed leaf digest.
                    let mut bad = opened.clone();
                    bad[0].1 = flip(&bad[0].1, 0);
                    assert!(!verify_multiproof(h, 1, log_n, &tree.root(), &bad, &sib));
                    // A leaf claimed at another index.
                    if n > 1 && set.len() == 1 {
                        let moved = [((set[0] + 1) % n, opened[0].1)];
                        assert!(!verify_multiproof(h, 1, log_n, &tree.root(), &moved, &sib));
                    }
                    // Each sibling changed, one missing, one extra.
                    for k in 0..sib.len() {
                        let mut s2 = sib.clone();
                        s2[k] = flip(&s2[k], 17);
                        assert!(!verify_multiproof(h, 1, log_n, &tree.root(), &opened, &s2));
                    }
                    if !sib.is_empty() {
                        assert!(!verify_multiproof(
                            h,
                            1,
                            log_n,
                            &tree.root(),
                            &opened,
                            &sib[..sib.len() - 1]
                        ));
                    }
                    let mut extra = sib.clone();
                    extra.push([0u8; DIGEST_BYTES]);
                    assert!(!verify_multiproof(
                        h,
                        1,
                        log_n,
                        &tree.root(),
                        &opened,
                        &extra
                    ));
                }
                // Unsorted or repeated indices are refused.
                if n >= 2 {
                    let two = [(1usize, lv[1]), (0usize, lv[0])];
                    assert!(!verify_multiproof(h, 1, log_n, &tree.root(), &two, &[]));
                    let rep = [(0usize, lv[0]), (0usize, lv[0])];
                    assert!(!verify_multiproof(h, 1, log_n, &tree.root(), &rep, &[]));
                }
            }
        }
    }

    #[test]
    fn full_opening_needs_no_siblings_and_root_depends_on_every_leaf() {
        let h = Hasher::new(Profile::TurboShakeJohnson400);
        let lv = leaves(h, 16);
        let tree = MerkleTree::build(h, 1, lv.clone());
        assert!(tree.open(&(0..16).collect::<Vec<_>>()).is_empty());
        assert_eq!(tree.open(&[5]).len(), 4);
        for i in 0..16 {
            let mut lv2 = lv.clone();
            lv2[i] = flip(&lv2[i], 3);
            assert_ne!(MerkleTree::build(h, 1, lv2).root(), tree.root());
        }
    }

    #[test]
    fn transcript_binds_order_labels_and_profile() {
        let bind: [&[u8]; 2] = [b"relation", b"statement"];
        let mut a = Transcript::new(Profile::CshakeJohnson400, &bind);
        let mut b = Transcript::new(Profile::TurboShakeJohnson400, &bind);
        assert_ne!(a.digest(), b.digest());
        // Field boundaries of the binding matter.
        let moved: [&[u8]; 2] = [b"relations", b"tatement"];
        assert_ne!(
            a.digest(),
            Transcript::new(Profile::CshakeJohnson400, &moved).digest()
        );
        b = a.clone();
        assert_eq!(a.squeeze_fp5(b"c"), b.squeeze_fp5(b"c"));
        // Successive challenges differ; labels separate.
        let x = a.squeeze_fp5(b"c");
        assert_ne!(x, a.squeeze_fp5(b"c"));
        let mut c = b.clone();
        assert_ne!(b.squeeze_fp5(b"c"), c.squeeze_fp5(b"d"));
        // Absorbing changes later challenges; label/payload boundaries matter.
        let (mut u, mut v) = (a.clone(), a.clone());
        u.absorb(b"ab", b"c");
        v.absorb(b"a", b"bc");
        assert_ne!(u.digest(), v.digest());
        assert_ne!(u.squeeze_base(b"x"), v.squeeze_base(b"x"));
        let (mut u, mut v) = (a.clone(), a.clone());
        u.absorb_fp5(b"m", Fp5::ONE);
        v.absorb_fp5(b"m", Fp5::X);
        assert_ne!(u.squeeze_fp5(b"x"), v.squeeze_fp5(b"x"));
        let (mut u, mut v) = (a.clone(), a.clone());
        u.absorb_fp5_slice(b"m", &[Fp5::ONE, Fp5::X]);
        v.absorb_fp5_slice(b"m", &[Fp5::X, Fp5::ONE]);
        assert_ne!(u.digest(), v.digest());
    }

    #[test]
    fn distinct_indices_are_sorted_distinct_and_in_range() {
        let mut t = Transcript::new(Profile::CshakeJohnson400, &[b"x"]);
        let idx = t.squeeze_distinct_indices(b"q", 1 << 10, 300);
        assert_eq!(idx.len(), 300);
        assert!(idx.windows(2).all(|w| w[0] < w[1]));
        assert!(idx.iter().all(|&i| i < 1 << 10));
        // More queries than fibers: every fiber.
        let all = t.squeeze_distinct_indices(b"q", 16, 300);
        assert_eq!(all, (0..16).collect::<Vec<_>>());
        // A different chain value gives a different set.
        let mut t2 = Transcript::new(Profile::CshakeJohnson400, &[b"y"]);
        assert_ne!(idx, t2.squeeze_distinct_indices(b"q", 1 << 10, 300));
        assert_ne!(t.squeeze_fp5_nonzero(b"n"), Fp5::ZERO);
    }

    #[test]
    fn squeezed_field_elements_spread_over_all_limbs() {
        let mut t = Transcript::new(Profile::TurboShakeJohnson400, &[b"x"]);
        let mut seen_high = [false; 5];
        for _ in 0..64 {
            let x = t.squeeze_fp5(b"c");
            for (k, limb) in x.to_limbs().iter().enumerate() {
                seen_high[k] |= limb.to_canonical_u64() >> 63 == 1;
            }
        }
        assert!(seen_high.iter().all(|&b| b));
        let b = t.squeeze_base(b"b");
        assert_ne!(b, t.squeeze_base(b"b"));
    }
}
