//! `PORS+FP`: a few-time signature over one Merkle tree, with forced pruning.
//!
//! * **Shape.** One tree of `2^tree_height` secret leaves per hypertree leaf. A signature
//!   reveals `reveal` *distinct* leaves and one deduplicated multiproof (an "Octopus") that
//!   authenticates all of them against the tree root. `FORS` spends `k` separate roots and
//!   `k` full paths; here paths merge wherever two revealed leaves share an ancestor.
//! * **Index selection.** The indices are read from the message XOF as `tree_height`-bit
//!   words; a word equal to an earlier one is skipped, so the subset is distinct by
//!   construction, and the result is sorted. See [`pors_fp_select`].
//! * **Forced pruning.** The number of multiproof nodes depends on how the subset clusters.
//!   A subset is accepted only if its multiproof has at most `max_auth_nodes` nodes; the
//!   signer counts the public message counter up until that holds. The verifier applies the
//!   same test, and a signature cannot carry more nodes than the bound.
//! * **Canonical multiproof.** [`octopus_positions`] fixes which nodes appear and in which
//!   order (leaf level first, left to right). [`pors_fp_root`] consumes exactly that
//!   sequence: one node too many, one too few, an unsorted or repeated index, all fail.
//!
//! ### What the bound in [`PorsFpParams::forgery_bits_milli`] says
//! After `g` signatures under one tree at most `g * reveal` leaves are public. A forgery
//! needs a message hash whose whole subset lies inside them. For one hash evaluation that
//! has probability at most `C(g * reveal, reveal) / C(2^tree_height, reveal)`: the pruning
//! test only removes subsets, for the forger as for the signer, so it does not enter. The
//! function returns `-log2` of that ratio. It is a per-query combinatorial bound in the
//! random-oracle model; it does not account for second-preimage attacks on the tree, for
//! the hypertree above, or for how often a hypertree leaf is reused.

use alloc::vec::Vec;

use crate::sponge::keccak::Cshake256Xof;
use crate::tsw_baggy::{
    AdrsKind, Cshake256Suite, HashAdrs, PqSecretKey, th_chain_f, th_node_h, th_secret_prf,
};
use crate::wipe::SecretVec;
use crate::wots_c::merkle_levels;

/// `PORS+FP` parameters.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PorsFpParams {
    /// Height of the tree; it has `2^tree_height` leaves.
    pub tree_height: usize,
    /// Distinct leaves revealed per signature (`k`).
    pub reveal: usize,
    /// Forced-pruning bound: most multiproof nodes a signature may carry (`m_max`).
    pub max_auth_nodes: usize,
}

impl PorsFpParams {
    /// 2048 leaves, 28 revealed, at most 128 multiproof nodes: 4,994 bytes at most, against
    /// 7,168 for the retired `FORS+C` layer, for the
    /// same number of leaves under MPC. About one subset in `2^10` passes the pruning test.
    pub const SHA3_128F: Self = Self {
        tree_height: 11,
        reveal: 28,
        max_auth_nodes: 128,
    };

    /// Small geometry for tests (about one subset in 16 passes).
    pub const TEST_SMALL: Self = Self {
        tree_height: 5,
        reveal: 6,
        max_auth_nodes: 9,
    };

    pub const fn is_well_formed(&self) -> bool {
        self.tree_height >= 1
            && self.tree_height <= 20
            && self.reveal >= 1
            && self.reveal <= 1024
            // At most half the leaves, so a skipped duplicate is never the likely draw.
            && self.reveal <= (1usize << self.tree_height) / 2
            && self.max_auth_nodes >= 1
            && self.max_auth_nodes <= self.reveal * self.tree_height
    }

    pub const fn leaves(&self) -> usize {
        1 << self.tree_height
    }

    /// Words [`pors_fp_select`] reads before it gives up on a counter.
    pub const fn draw_budget(&self) -> usize {
        2 * self.reveal + 32
    }

    /// Largest encoding of an opening: the secrets, a two-byte node count, the nodes.
    pub const fn opening_bytes_max(&self) -> usize {
        32 * self.reveal + 2 + 32 * self.max_auth_nodes
    }

    /// Lower bound, in thousandths of a bit, on `-log2` of the probability that one message
    /// hash selects only leaves revealed by `signatures` earlier signatures of the same tree
    /// (see the module documentation). `None` for malformed parameters or zero signatures.
    pub fn forgery_bits_milli(&self, signatures: u32) -> Option<u32> {
        if !self.is_well_formed() || signatures == 0 {
            return None;
        }
        let t = self.leaves() as u64;
        let k = self.reveal as u64;
        let covered = k.saturating_mul(u64::from(signatures)).min(t);
        let mut bits = 0u64;
        for i in 0..k {
            // Numerators rounded down, denominators rounded up.
            let num = log2_milli_floor(t - i);
            let den = log2_milli_floor(covered - i) + u64::from(!(covered - i).is_power_of_two());
            bits += num.saturating_sub(den);
        }
        u32::try_from(bits).ok()
    }
}

/// `floor(1000 * log2(x))` for `x >= 1`, by repeated squaring of the mantissa.
///
/// Kept out of line. Inlined into the loop of [`PorsFpParams::forgery_bits_milli`], the
/// twenty squarings become a chain in which every value feeds the next one twice, all
/// derived from the loop counter; LLVM's loop vectorizer walks that chain once per path
/// (`vputils::onlyFirstLaneUsed`), which took the thin-LTO test build past ten minutes.
#[inline(never)]
fn log2_milli_floor(x: u64) -> u64 {
    debug_assert!(x >= 1);
    let int = u64::from(63 - x.leading_zeros());
    let mut y = u128::from(x) << (63 - int);
    let mut frac = 0u64;
    for _ in 0..20 {
        y = (y * y) >> 63;
        frac <<= 1;
        if y >> 64 != 0 {
            frac |= 1;
            y >>= 1;
        }
    }
    1000 * int + ((1000 * frac) >> 20)
}

/// Positions `(height, index)` of the multiproof nodes of a strictly increasing index set,
/// in canonical order: heights ascending from the leaf level, indices ascending within one
/// height. `None` if `indices` is empty, not strictly increasing, or out of range.
pub fn octopus_positions(tree_height: usize, indices: &[u32]) -> Option<Vec<(u32, u32)>> {
    if tree_height > 31
        || indices.is_empty()
        || indices.windows(2).any(|w| w[0] >= w[1])
        || u64::from(indices[indices.len() - 1]) >= 1u64 << tree_height
    {
        return None;
    }
    let mut out = Vec::new();
    let mut cur = indices.to_vec();
    for level in 0..tree_height as u32 {
        let mut next = Vec::with_capacity(cur.len());
        let mut i = 0;
        while i < cur.len() {
            let x = cur[i];
            if x & 1 == 0 && cur.get(i + 1) == Some(&(x + 1)) {
                i += 2;
            } else {
                out.push((level, x ^ 1));
                i += 1;
            }
            next.push(x >> 1);
        }
        cur = next;
    }
    Some(out)
}

/// Read the index subset of one message counter from `xof`: successive big-endian 32-bit
/// words reduced to `tree_height` bits, skipping repeats, until `reveal` distinct values
/// are found; then sorted. `None` if the draw budget runs out or the subset's multiproof
/// exceeds `max_auth_nodes`, in which case the counter is not usable.
pub fn pors_fp_select(params: &PorsFpParams, xof: &mut Cshake256Xof) -> Option<Vec<u32>> {
    if !params.is_well_formed() {
        return None;
    }
    let mask = (1u32 << params.tree_height) - 1;
    let mut indices: Vec<u32> = Vec::with_capacity(params.reveal);
    for _ in 0..params.draw_budget() {
        let mut word = [0u8; 4];
        xof.squeeze(&mut word);
        let v = u32::from_be_bytes(word) & mask;
        if !indices.contains(&v) {
            indices.push(v);
            if indices.len() == params.reveal {
                break;
            }
        }
    }
    if indices.len() != params.reveal {
        return None;
    }
    indices.sort_unstable();
    let nodes = octopus_positions(params.tree_height, &indices)?.len();
    (nodes <= params.max_auth_nodes).then_some(indices)
}

/// The revealed secrets, in index order, and the canonical multiproof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PorsFpOpening {
    pub secrets: Vec<[u8; 32]>,
    pub auth: Vec<[u8; 32]>,
}

impl PorsFpOpening {
    /// `secrets || be16(auth.len()) || auth`.
    pub fn to_wire_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(32 * (self.secrets.len() + self.auth.len()) + 2);
        out.extend_from_slice(self.secrets.as_flattened());
        out.extend_from_slice(&(self.auth.len() as u16).to_be_bytes());
        out.extend_from_slice(self.auth.as_flattened());
        out
    }

    /// Inverse of [`Self::to_wire_bytes`]; returns the opening and the bytes it used. The
    /// node count must not exceed `max_auth_nodes`.
    pub fn from_wire_bytes(params: &PorsFpParams, raw: &[u8]) -> Option<(Self, usize)> {
        if !params.is_well_formed() {
            return None;
        }
        let secret_bytes = 32 * params.reveal;
        let count_bytes = raw.get(secret_bytes..secret_bytes + 2)?;
        let count = usize::from(u16::from_be_bytes([count_bytes[0], count_bytes[1]]));
        if count > params.max_auth_nodes {
            return None;
        }
        let used = secret_bytes + 2 + 32 * count;
        let auth_bytes = raw.get(secret_bytes + 2..used)?;
        let nodes = |bytes: &[u8]| bytes.as_chunks::<32>().0.to_vec();
        Some((
            Self {
                secrets: nodes(&raw[..secret_bytes]),
                auth: nodes(auth_bytes),
            },
            used,
        ))
    }
}

const fn pors_adrs(kind: AdrsKind, tree: u64, key_pair: u32, height: u32, index: u32) -> HashAdrs {
    HashAdrs {
        layer: 0,
        tree,
        kind,
        key_pair,
        chain_idx: height,
        hash_step: index,
    }
}

/// Address of the `PRF` call that derives leaf `leaf`'s secret.
pub const fn pors_prf_adrs(tree: u64, key_pair: u32, leaf: u32) -> HashAdrs {
    pors_adrs(AdrsKind::PorsPrf, tree, key_pair, 0, leaf)
}

/// Address of the `F` call that maps leaf `leaf`'s secret to its tree leaf.
pub const fn pors_leaf_adrs(tree: u64, key_pair: u32, leaf: u32) -> HashAdrs {
    pors_adrs(AdrsKind::PorsTree, tree, key_pair, 0, leaf)
}

/// Tree leaf of a revealed secret.
pub fn pors_leaf_hash(
    pk_seed: &[u8; 32],
    tree: u64,
    key_pair: u32,
    leaf: u32,
    secret: &[u8; 32],
) -> [u8; 32] {
    th_chain_f(
        Cshake256Suite,
        pk_seed,
        &pors_leaf_adrs(tree, key_pair, leaf),
        secret,
    )
}

/// Every level of the tree over `leaves` (leaf hashes), leaves first.
pub fn pors_levels(
    pk_seed: &[u8; 32],
    tree: u64,
    key_pair: u32,
    leaves: &[[u8; 32]],
) -> Vec<Vec<[u8; 32]>> {
    merkle_levels(pk_seed, 0, tree, AdrsKind::PorsTree, key_pair, leaves, 0)
}

/// The canonical multiproof of `indices` out of a full tree.
pub fn pors_fp_auth(
    params: &PorsFpParams,
    levels: &[Vec<[u8; 32]>],
    indices: &[u32],
) -> Option<Vec<[u8; 32]>> {
    if levels.len() != params.tree_height + 1 || levels[0].len() != params.leaves() {
        return None;
    }
    let positions = octopus_positions(params.tree_height, indices)?;
    (positions.len() <= params.max_auth_nodes).then(|| {
        positions
            .iter()
            .map(|&(height, index)| levels[height as usize][index as usize])
            .collect()
    })
}

/// Root implied by an opening of `indices`. `None` unless the parameters are well formed,
/// `indices` is strictly increasing with exactly `reveal` entries, there is one secret per
/// index, and `auth` is exactly the canonical multiproof with at most `max_auth_nodes`
/// nodes.
pub fn pors_fp_root(
    params: &PorsFpParams,
    pk_seed: &[u8; 32],
    tree: u64,
    key_pair: u32,
    indices: &[u32],
    opening: &PorsFpOpening,
) -> Option<[u8; 32]> {
    if !params.is_well_formed()
        || indices.len() != params.reveal
        || opening.secrets.len() != params.reveal
        || opening.auth.len() > params.max_auth_nodes
        || indices.windows(2).any(|w| w[0] >= w[1])
        || indices[indices.len() - 1] as usize >= params.leaves()
    {
        return None;
    }
    let mut cur: Vec<(u32, [u8; 32])> = indices
        .iter()
        .zip(&opening.secrets)
        .map(|(&leaf, secret)| (leaf, pors_leaf_hash(pk_seed, tree, key_pair, leaf, secret)))
        .collect();
    let mut auth = opening.auth.iter();
    for level in 0..params.tree_height as u32 {
        let mut next = Vec::with_capacity(cur.len());
        let mut i = 0;
        while i < cur.len() {
            let (x, node) = cur[i];
            let (left, right) = if x & 1 == 1 {
                i += 1;
                (*auth.next()?, node)
            } else if cur.get(i + 1).is_some_and(|n| n.0 == x + 1) {
                i += 2;
                (node, cur[i - 1].1)
            } else {
                i += 1;
                (node, *auth.next()?)
            };
            let adrs = pors_adrs(AdrsKind::PorsTree, tree, key_pair, level + 1, x >> 1);
            next.push((
                x >> 1,
                th_node_h(Cshake256Suite, pk_seed, &adrs, &left, &right),
            ));
        }
        cur = next;
    }
    (auth.next().is_none() && cur.len() == 1).then(|| cur[0].1)
}

/// Single-party reference: every leaf secret of one tree, and the tree over their hashes.
pub fn pors_reference_tree(
    params: &PorsFpParams,
    sk: &PqSecretKey,
    tree: u64,
    key_pair: u32,
) -> (SecretVec<[u8; 32]>, Vec<Vec<[u8; 32]>>) {
    let secrets = SecretVec::new(
        (0..params.leaves() as u32)
            .map(|leaf| {
                th_secret_prf(
                    Cshake256Suite,
                    &sk.pk_seed,
                    &sk.sk_seed,
                    &pors_prf_adrs(tree, key_pair, leaf),
                )
            })
            .collect::<Vec<[u8; 32]>>(),
    );
    let leaves: Vec<[u8; 32]> = secrets
        .iter()
        .enumerate()
        .map(|(leaf, s)| pors_leaf_hash(&sk.pk_seed, tree, key_pair, leaf as u32, s))
        .collect();
    let levels = pors_levels(&sk.pk_seed, tree, key_pair, &leaves);
    (secrets, levels)
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;

    fn sk() -> PqSecretKey {
        PqSecretKey {
            sk_seed: [7; 32],
            sk_prf: [8; 32],
            pk_seed: [9; 32],
        }
    }

    fn stream(ctr: u32) -> Cshake256Xof {
        let mut xof = Cshake256Xof::new(b"pors-fp-test");
        xof.absorb(&ctr.to_be_bytes());
        xof
    }

    /// First counter that passes the pruning test, with its subset.
    fn grind(params: &PorsFpParams) -> (u32, Vec<u32>) {
        (0u32..1 << 20)
            .find_map(|ctr| pors_fp_select(params, &mut stream(ctr)).map(|idx| (ctr, idx)))
            .unwrap()
    }

    fn open(params: &PorsFpParams, indices: &[u32]) -> (PorsFpOpening, [u8; 32]) {
        let (secrets, levels) = pors_reference_tree(params, &sk(), 3, 1);
        let opening = PorsFpOpening {
            secrets: indices.iter().map(|&i| secrets[i as usize]).collect(),
            auth: pors_fp_auth(params, &levels, indices).unwrap(),
        };
        (opening, levels[params.tree_height][0])
    }

    #[test]
    fn octopus_is_minimal_and_matches_a_brute_force_cover() {
        // Height 3: leaves 0 and 1 share a parent; 6 stands alone.
        assert_eq!(
            octopus_positions(3, &[0, 1, 6]),
            Some(vec![(0, 7), (1, 1), (1, 2)])
        );
        assert_eq!(
            octopus_positions(3, &[0, 1, 2, 3, 4, 5, 6, 7]),
            Some(vec![])
        );
        assert_eq!(
            octopus_positions(3, &[5]),
            Some(vec![(0, 4), (1, 3), (2, 0)])
        );
        for bad in [&[][..], &[1, 1], &[2, 1], &[8]] {
            assert_eq!(octopus_positions(3, bad), None);
        }
        // Against the definition: a node is needed iff it is not an ancestor-or-self of a
        // revealed leaf but its sibling is.
        for subset in 1u32..1 << 8 {
            let indices: Vec<u32> = (0..8).filter(|i| subset >> i & 1 == 1).collect();
            let on_path = |h: u32, i: u32| indices.iter().any(|&x| x >> h == i);
            let mut want = Vec::new();
            for h in 0..3 {
                for i in 0..8u32 >> h {
                    if !on_path(h, i) && on_path(h, i ^ 1) {
                        want.push((h, i));
                    }
                }
            }
            assert_eq!(octopus_positions(3, &indices), Some(want));
        }
    }

    #[test]
    fn selection_is_sorted_distinct_bounded_and_rejects_unpruned_subsets() {
        let params = PorsFpParams::TEST_SMALL;
        let (mut accepted, mut rejected_for_size) = (0, 0);
        for ctr in 0..2000 {
            match pors_fp_select(&params, &mut stream(ctr)) {
                Some(idx) => {
                    accepted += 1;
                    assert_eq!(idx.len(), params.reveal);
                    assert!(idx.windows(2).all(|w| w[0] < w[1]));
                    assert!(idx.iter().all(|&i| (i as usize) < params.leaves()));
                    let nodes = octopus_positions(params.tree_height, &idx).unwrap().len();
                    assert!(nodes <= params.max_auth_nodes);
                }
                None => {
                    // Same stream without the bound: the subset exists and is too wide.
                    let loose = PorsFpParams {
                        max_auth_nodes: params.reveal * params.tree_height,
                        ..params
                    };
                    let idx = pors_fp_select(&loose, &mut stream(ctr)).unwrap();
                    let nodes = octopus_positions(params.tree_height, &idx).unwrap().len();
                    assert!(nodes > params.max_auth_nodes);
                    rejected_for_size += 1;
                }
            }
        }
        // The bound is binding (most subsets fail it) and satisfiable.
        assert!(accepted > 20 && rejected_for_size > 5 * accepted);
    }

    #[test]
    fn opening_verifies_and_every_tampering_is_rejected() {
        let params = PorsFpParams::TEST_SMALL;
        let (_, indices) = grind(&params);
        let (opening, root) = open(&params, &indices);
        let pk_seed = sk().pk_seed;
        let check = |idx: &[u32], o: &PorsFpOpening| pors_fp_root(&params, &pk_seed, 3, 1, idx, o);
        assert_eq!(check(&indices, &opening), Some(root));
        assert!(opening.auth.len() <= params.max_auth_nodes);

        // Wrong secret, wrong node, wrong tree or key pair: another root.
        let mut bad = opening.clone();
        bad.secrets[2][0] ^= 1;
        assert_ne!(check(&indices, &bad), Some(root));
        let mut bad = opening.clone();
        bad.auth[0][31] ^= 1;
        assert_ne!(check(&indices, &bad), Some(root));
        assert_ne!(
            pors_fp_root(&params, &pk_seed, 4, 1, &indices, &opening),
            Some(root)
        );
        assert_ne!(
            pors_fp_root(&params, &pk_seed, 3, 2, &indices, &opening),
            Some(root)
        );

        // Not canonical: an extra node, a missing node, swapped nodes.
        let mut bad = opening.clone();
        bad.auth.push([0; 32]);
        assert_eq!(check(&indices, &bad), None);
        let mut bad = opening.clone();
        bad.auth.pop();
        assert_eq!(check(&indices, &bad), None);
        let mut bad = opening.clone();
        bad.auth.swap(0, 1);
        assert_ne!(check(&indices, &bad), Some(root));

        // Index sets that are not a sorted distinct subset of the right size.
        let mut unsorted = indices.clone();
        unsorted.swap(0, 1);
        assert_eq!(check(&unsorted, &opening), None);
        let mut repeated = indices.clone();
        repeated[1] = repeated[0];
        assert_eq!(check(&repeated, &opening), None);
        assert_eq!(check(&indices[1..], &opening), None);
        let mut out_of_range = indices.clone();
        *out_of_range.last_mut().unwrap() = params.leaves() as u32;
        assert_eq!(check(&out_of_range, &opening), None);
    }

    #[test]
    fn a_valid_multiproof_above_the_pruning_bound_is_rejected() {
        let params = PorsFpParams::TEST_SMALL;
        let loose = PorsFpParams {
            max_auth_nodes: params.reveal * params.tree_height,
            ..params
        };
        // A subset the bound excludes, opened honestly under the loose parameters.
        let indices = (0u32..)
            .find_map(|ctr| {
                let idx = pors_fp_select(&loose, &mut stream(ctr))?;
                (octopus_positions(params.tree_height, &idx)?.len() > params.max_auth_nodes)
                    .then_some(idx)
            })
            .unwrap();
        let (opening, root) = open(&loose, &indices);
        let pk_seed = sk().pk_seed;
        assert_eq!(
            pors_fp_root(&loose, &pk_seed, 3, 1, &indices, &opening),
            Some(root)
        );
        assert_eq!(
            pors_fp_root(&params, &pk_seed, 3, 1, &indices, &opening),
            None
        );
        let (_, levels) = pors_reference_tree(&params, &sk(), 3, 1);
        assert_eq!(pors_fp_auth(&params, &levels, &indices), None);
        // The wire decoder refuses the oversized count before allocating for it.
        assert!(PorsFpOpening::from_wire_bytes(&params, &opening.to_wire_bytes()).is_none());
    }

    #[test]
    fn wire_round_trip_and_truncation() {
        let params = PorsFpParams::TEST_SMALL;
        let (_, indices) = grind(&params);
        let (opening, _) = open(&params, &indices);
        let mut raw = opening.to_wire_bytes();
        assert!(raw.len() <= params.opening_bytes_max());
        raw.extend_from_slice(b"tail");
        let (back, used) = PorsFpOpening::from_wire_bytes(&params, &raw).unwrap();
        assert_eq!((back, used), (opening, raw.len() - 4));
        assert!(PorsFpOpening::from_wire_bytes(&params, &raw[..used - 1]).is_none());
    }

    #[test]
    fn parameter_checks_and_security_accounting() {
        assert!(PorsFpParams::SHA3_128F.is_well_formed());
        assert!(PorsFpParams::TEST_SMALL.is_well_formed());
        for bad in [
            PorsFpParams {
                tree_height: 0,
                ..PorsFpParams::TEST_SMALL
            },
            PorsFpParams {
                tree_height: 21,
                ..PorsFpParams::TEST_SMALL
            },
            PorsFpParams {
                reveal: 17,
                ..PorsFpParams::TEST_SMALL
            },
            PorsFpParams {
                reveal: 0,
                ..PorsFpParams::TEST_SMALL
            },
            PorsFpParams {
                max_auth_nodes: 0,
                ..PorsFpParams::TEST_SMALL
            },
            PorsFpParams {
                max_auth_nodes: 31,
                ..PorsFpParams::TEST_SMALL
            },
        ] {
            assert!(!bad.is_well_formed());
            assert_eq!(bad.forgery_bits_milli(1), None);
        }
        assert_eq!(log2_milli_floor(1), 0);
        assert_eq!(log2_milli_floor(1 << 40), 40_000);
        assert_eq!(log2_milli_floor(3), 1584);
        assert_eq!(log2_milli_floor(1000), 9965);

        // Exact values are 209.788, 157.024, 136.093 and 122.451 bits for one to four signatures
        // on one tree; the function rounds every term down and stays below them.
        let p = PorsFpParams::SHA3_128F;
        let bits: Vec<u32> = (1..=4)
            .map(|g| p.forgery_bits_milli(g).unwrap() / 1000)
            .collect();
        assert_eq!(bits, vec![209, 156, 136, 122]);
        assert!(
            bits.iter()
                .zip([209.788, 157.024, 136.093, 122.451])
                .all(|(lo, exact)| { f64::from(*lo) <= exact && exact - f64::from(*lo) < 2.0 })
        );
        assert_eq!(p.forgery_bits_milli(0), None);
        // Once every leaf is public nothing is left.
        assert_eq!(p.forgery_bits_milli(u32::MAX), Some(0));
        assert_eq!(p.opening_bytes_max(), 4994);
    }
}
