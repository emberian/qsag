//! The rehashed Ironwood note commitment tree.
//!
//! ZIP 2005 ("Repairing the note commitment Merkle tree"): `MerkleCRH^Orchard` is a
//! Sinsemilla hash, whose collision resistance rests on discrete logarithms, so a path in
//! the on-chain tree proves nothing against a quantum adversary. Because the tree is
//! public, every party can rebuild it over the same leaves with a collapsing hash, and
//! the Recovery Statement opens a path in that rebuilt tree. The ZIP also puts `rho` into
//! the leaf: `leaf = MerkleCRH(cm_x, rho)`.
//!
//! ZIP 2005 deliberately does not choose the hash ("No particular choice of post-quantum
//! proving system or commitment tree hash should be assumed"). This module is this
//! crate's instantiation, to be replaced by Zcash's once it is fixed:
//!
//! ```text
//! leaf(cm_x, rho)      = BLAKE2s-256(personal = "QsIwTre" || 0xff,  cm_x || rho)
//! node(h, left, right) = BLAKE2s-256(personal = "QsIwTre" || h,     left || right)
//! ```
//!
//! with `cm_x` and `rho` the 32-byte little-endian encodings that appear in an Action
//! (`cmx` of the output, `nullifier` of the same Action), `h` in `0..32` the height of the
//! children, depth 32 as on chain, positions as on chain, and the all-zero string for an
//! empty leaf. Each hash is one compression (the input is exactly one block), about
//! 21,000 rows. Security claim: position binding against quantum adversaries if BLAKE2s
//! is collapsing (Unruh 2016; Gunsing and Mennink 2022 for tree hashes, as cited by the
//! ZIP); that is an assumption about BLAKE2s, not something proved here.

use alloc::vec;
use alloc::vec::Vec;

use qsag_agg::zk_hem::relation::{ConstraintSystem, Lc};

use super::blake2::{blake2s_256, blake2s_256_block_gadget};

/// Depth of the tree.
pub const DEPTH: usize = 32;
/// An empty leaf.
pub const EMPTY_LEAF: [u8; 32] = [0; 32];

fn personal(tag: u8) -> [u8; 8] {
    let mut p = *b"QsIwTre\0";
    p[7] = tag;
    p
}

/// The leaf of a note: `cmx` and `rho` as they appear in its Action.
pub fn leaf_hash(cmx: &[u8; 32], rho: &[u8; 32]) -> [u8; 32] {
    blake2s_256(&personal(0xff), &[cmx, rho])
}

/// The parent of two nodes of height `height` (`0` for leaves).
pub fn node_hash(height: u8, left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    assert!((height as usize) < DEPTH);
    blake2s_256(&personal(height), &[left, right])
}

/// Roots of the empty subtrees of height `0..=32`.
pub fn empty_roots() -> [[u8; 32]; DEPTH + 1] {
    let mut out = [EMPTY_LEAF; DEPTH + 1];
    for h in 0..DEPTH {
        out[h + 1] = node_hash(h as u8, &out[h], &out[h]);
    }
    out
}

/// The root reached from `leaf` at `position` along `path` (siblings from the leaf up).
pub fn root_from_path(leaf: &[u8; 32], position: u32, path: &[[u8; 32]; DEPTH]) -> [u8; 32] {
    let mut node = *leaf;
    for (h, sibling) in path.iter().enumerate() {
        node = if (position >> h) & 1 == 0 {
            node_hash(h as u8, &node, sibling)
        } else {
            node_hash(h as u8, sibling, &node)
        };
    }
    node
}

/// An append-only tree that keeps only its frontier: enough for the root after each
/// append, as a chain follower needs for anchors.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Frontier {
    /// `left[h]` is the left sibling waiting at height `h`, if the node there is a right
    /// child in progress.
    left: [Option<[u8; 32]>; DEPTH],
    size: u64,
    /// The root, once all `2^32` positions are filled.
    full: Option<[u8; 32]>,
}

impl Default for Frontier {
    fn default() -> Self {
        Self::new()
    }
}

impl Frontier {
    pub fn new() -> Self {
        Self {
            left: [None; DEPTH],
            size: 0,
            full: None,
        }
    }

    /// Number of leaves appended.
    pub fn size(&self) -> u64 {
        self.size
    }

    /// Append a leaf; `false` when the tree is full.
    pub fn append(&mut self, leaf: &[u8; 32]) -> bool {
        if self.size >> DEPTH != 0 {
            return false;
        }
        let mut node = *leaf;
        let mut stored = false;
        for h in 0..DEPTH {
            if (self.size >> h) & 1 == 0 {
                self.left[h] = Some(node);
                stored = true;
                break;
            }
            node = node_hash(h as u8, &self.left[h].take().expect("left sibling"), &node);
        }
        if !stored {
            self.full = Some(node);
        }
        self.size += 1;
        true
    }

    /// The root with every position not yet appended empty.
    pub fn root(&self) -> [u8; 32] {
        if let Some(root) = self.full {
            return root;
        }
        let empty = empty_roots();
        // Walk the path of the next free position: where it is a right child the left
        // sibling is stored, elsewhere the right sibling is an empty subtree.
        let mut node = empty[0];
        let mut pending = false;
        for h in 0..DEPTH {
            let is_right = (self.size >> h) & 1 == 1;
            node = match (is_right, pending) {
                (true, true) => node_hash(h as u8, &self.left[h].expect("left sibling"), &node),
                (true, false) => {
                    pending = true;
                    node_hash(h as u8, &self.left[h].expect("left sibling"), &empty[h])
                }
                (false, true) => node_hash(h as u8, &node, &empty[h]),
                (false, false) => empty[h + 1],
            };
        }
        node
    }
}

/// The authentication path of `position` in the tree whose first leaves are `leaves` and
/// whose other positions are empty, with its root. `None` if `position` is not a listed
/// leaf. Recomputes the whole tree: for tests and small trees.
pub fn witness(leaves: &[[u8; 32]], position: u32) -> Option<([[u8; 32]; DEPTH], [u8; 32])> {
    if position as usize >= leaves.len() || leaves.len() as u64 > 1 << DEPTH {
        return None;
    }
    let empty = empty_roots();
    let mut level: Vec<[u8; 32]> = leaves.to_vec();
    let mut index = position as usize;
    let mut path = [EMPTY_LEAF; DEPTH];
    for h in 0..DEPTH {
        path[h] = level.get(index ^ 1).copied().unwrap_or(empty[h]);
        let mut next = vec![EMPTY_LEAF; level.len().div_ceil(2)];
        for (i, pair) in level.chunks(2).enumerate() {
            next[i] = node_hash(h as u8, &pair[0], pair.get(1).unwrap_or(&empty[h]));
        }
        level = next;
        index >>= 1;
    }
    Some((path, level[0]))
}

// ============================================================================
// Gadgets
// ============================================================================

/// [`leaf_hash`] over two 256-bit strings (least significant bit first within each byte).
pub fn leaf_hash_gadget(cs: &mut ConstraintSystem, cmx: &[Lc], rho: &[Lc]) -> Vec<Lc> {
    assert!(cmx.len() == 256 && rho.len() == 256);
    let block: Vec<Lc> = cmx.iter().chain(rho).cloned().collect();
    blake2s_256_block_gadget(cs, &personal(0xff), &block)
}

/// [`root_from_path`]: `position` is 32 Boolean bits (least significant first) and `path`
/// 32 siblings of 256 Boolean bits each.
pub fn root_gadget(
    cs: &mut ConstraintSystem,
    leaf: &[Lc],
    position: &[Lc],
    path: &[Vec<Lc>],
) -> Vec<Lc> {
    assert!(leaf.len() == 256 && position.len() == DEPTH && path.len() == DEPTH);
    let mut node = leaf.to_vec();
    for (h, (bit, sibling)) in position.iter().zip(path).enumerate() {
        assert_eq!(sibling.len(), 256);
        let mut block = Vec::with_capacity(512);
        let mut right = Vec::with_capacity(256);
        for (n, s) in node.iter().zip(sibling) {
            // left = bit ? sibling : node; right is the other one.
            let left = cs.select(bit, s, n);
            right.push(n.plus(s).minus(&left));
            block.push(left);
        }
        block.extend(right);
        node = blake2s_256_block_gadget(cs, &personal(h as u8), &block);
    }
    node
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hem::hash::{alloc_bits, bits_to_bytes};

    fn leaf(i: u32) -> [u8; 32] {
        leaf_hash(&[i as u8; 32], &[(i >> 8) as u8 ^ 0x5a; 32])
    }

    #[test]
    fn frontier_root_matches_recomputation() {
        let mut frontier = Frontier::new();
        assert_eq!(frontier.root(), empty_roots()[DEPTH]);
        let mut leaves = Vec::new();
        for i in 0..37u32 {
            leaves.push(leaf(i));
            assert!(frontier.append(&leaf(i)));
            let (path, root) = witness(&leaves, i).unwrap();
            assert_eq!(frontier.root(), root, "after {} leaves", i + 1);
            assert_eq!(root_from_path(&leaf(i), i, &path), root);
            // Every earlier leaf still opens to the new root, and to no other.
            let (old_path, old_root) = witness(&leaves, i / 2).unwrap();
            assert_eq!(old_root, root);
            assert_eq!(root_from_path(&leaf(i / 2), i / 2, &old_path), root);
            assert_ne!(root_from_path(&leaf(i / 2), i / 2 + 1, &old_path), root);
            assert_ne!(root_from_path(&leaf(i + 100), i / 2, &old_path), root);
        }
        assert!(witness(&leaves, 37).is_none());
    }

    #[test]
    fn hashes_are_domain_separated() {
        let (a, b) = ([1u8; 32], [2u8; 32]);
        assert_ne!(leaf_hash(&a, &b), node_hash(0, &a, &b));
        assert_ne!(node_hash(0, &a, &b), node_hash(1, &a, &b));
        assert_ne!(node_hash(0, &a, &b), node_hash(0, &b, &a));
        assert_ne!(empty_roots()[0], empty_roots()[1]);
    }

    #[test]
    fn gadgets_match_native() {
        let leaves: Vec<[u8; 32]> = (0..6).map(leaf).collect();
        let position = 5u32;
        let (path, root) = witness(&leaves, position).unwrap();
        let (cmx, rho) = ([5u8; 32], [0x5a; 32]);
        for (pos, ok) in [(position, true), (4, false)] {
            let mut cs = ConstraintSystem::new();
            let cmx_bits = alloc_bits(&mut cs, &cmx);
            let rho_bits = alloc_bits(&mut cs, &rho);
            let pos_bits = alloc_bits(&mut cs, &pos.to_le_bytes());
            let path_bits: Vec<Vec<Lc>> = path.iter().map(|s| alloc_bits(&mut cs, s)).collect();
            let rows0 = cs.num_rows();
            let leaf_bits = leaf_hash_gadget(&mut cs, &cmx_bits, &rho_bits);
            assert_eq!(bits_to_bytes(&cs, &leaf_bits), leaves[5].to_vec());
            let root_bits = root_gadget(&mut cs, &leaf_bits, &pos_bits, &path_bits);
            std::println!("leaf and 32-level path: {} rows", cs.num_rows() - rows0);
            assert_eq!(bits_to_bytes(&cs, &root_bits) == root.to_vec(), ok);
            let (shape, z) = cs.finish();
            assert!(shape.is_satisfied(&z));
        }
    }
}
