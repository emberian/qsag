//! Quorum-switching `Jorts`: stateful `(t, n)` threshold hash-based signatures whose one-time
//! leaves cannot be spent twice by switching between signer sets.
//!
//! One Merkle tree of height `h` certifies `2^h` one-time `WOTS+C` leaves under a single root.
//! The leaf scheme is `w = 4` with 128 chains over the full 256-bit digest, a fixed digit sum
//! of 192 and no checksum chains: a public counter is ground until the digits of
//! `SHAKE256(msg_hash || counter)` sum to 192 (about one counter in 32 does). Every hash is a
//! tweaked `SHAKE256`.
//!
//! A signer set never evaluates a hash on secret data online. Staging stores, for every chain
//! of every leaf, a sharing of each of the three secret chain states `y^(0), y^(1), y^(2)`
//! (`y^(3)` is the public chain end). Signing opens the share of `y^(d)` for the chain's digit
//! `d`, and whoever combines the openings hashes each node forward `3 - d` steps and compares
//! with the public chain end, so a wrong share is detected without any authenticated sharing.
//!
//! ### Mode QS-A: committee-partitioned `t`-of-`t` subtrees ([`CommitteePartitionedJorts`])
//! The leaves are split into `binom(n, t)` disjoint ranges, one per `t`-subset (committee) of
//! the custodians, and the chain states of a committee's leaves are shared additively
//! `t`-of-`t` among its members only. Any `t` online custodians are exactly one committee and
//! sign from that committee's range. With at most `t - 1` corrupted custodians every committee
//! contains an honest member; that member's durable latch binds each leaf to one digit vector,
//! and no other custodian set holds shares of that leaf. A leaf therefore cannot be signed
//! twice whatever set the corrupted custodians join next, and no assumption on `n` is needed.
//!
//! ### Mode QS-B: global tree with a latch certificate ([`BftShamirJorts`])
//! Every chain state is `(t, n)`-Shamir shared bytewise over `GF(2^8)`, with an independent
//! polynomial per chain step, so a custodian stores the same 12,288 bytes per leaf for every
//! `(t, n)`. A custodian opens its shares of a leaf only against a [`LatchCertificate`]: latch
//! acknowledgements of one binding from `q` custodians with `2q > n + f`. Two certificates for
//! one leaf share at least `f + 1` acknowledgers, hence an honest one, and an honest custodian
//! acknowledges one binding per leaf. This needs `n >= 3f + 1` to stay live.
//!
//! ### What this module is and is not
//! * The custodian types ([`CommitteeCustodian`], [`ShamirCustodian`]) hold one party's state
//!   and exchange plain message values; `crate::party_node` runs them over a wire transport,
//!   one party per thread. [`CommitteePartitionedJorts`] and [`BftShamirJorts`] drive all
//!   custodians in one process and exist for tests and measurements.
//! * [`stage_committee_partitioned`] and [`stage_bft_shamir`] are deterministic single-seed
//!   test and measurement helpers. In-process dealerless MPC staging and proactive
//!   share refresh are provided in [`crate::dealerless_staging`]
//!   ([`crate::dealerless_staging::stage_committee_partitioned_dealerless_mpc`],
//!   [`crate::dealerless_staging::stage_bft_shamir_dealerless_mpc`],
//!   [`crate::dealerless_staging::refresh_committee_shares`], and
//!   [`crate::dealerless_staging::refresh_bft_shamir_shares`]).
//! * A certificate is authenticated with one MAC per verifying custodian under pairwise keys.
//!   It convinces any custodian and nobody else.

use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

#[cfg(any(test, feature = "testing-ephemeral"))]
use qsag_core::belt_latch::MemoryWal;
use qsag_core::belt_latch::{BeltLatch, BeltLatchError, BeltLatchRecord, DurableWal};
use qsag_core::field::tower::{TowerGf256, lagrange_weights_zero_gf256};
use qsag_core::wipe::{SecretBuffer, SecretBytes, SecretVec};

use crate::hash::{SeedRng, h32, mac32, mac32_verify};

/// A 32-byte hash value or chain state.
pub type Node = [u8; 32];

/// Winternitz parameter.
pub const WOTS_W: usize = 4;
/// Hash steps from a chain's secret start to its public end.
pub const WOTS_STEPS: usize = WOTS_W - 1;
/// Chains per leaf: two bits of the 256-bit digest each.
pub const WOTS_CHAINS: usize = 128;
/// Required sum of the 128 digits.
pub const WOTS_TARGET_SUM: u32 = 192;
/// Largest counter tried while grinding.
pub const MAX_GRIND: u32 = 1 << 16;
/// A custodian refuses to bind an epoch more than this far above its high-water mark.
pub const MAX_WINDOW: u64 = 16;
/// Secret chain states stored per leaf and custodian (`y^(0), y^(1), y^(2)` of every chain).
pub const LEAF_SHARE_NODES: usize = WOTS_CHAINS * WOTS_STEPS;

const TAG_CHAIN: &[u8] = b"QSAG.QUORUM.CHAIN/v1";
const TAG_LEAF: &[u8] = b"QSAG.QUORUM.LEAF/v1";
const TAG_UNASSIGNED: &[u8] = b"QSAG.QUORUM.LEAF.UNASSIGNED/v1";
const TAG_NODE: &[u8] = b"QSAG.QUORUM.NODE/v1";
const TAG_MSG: &[u8] = b"QSAG.QUORUM.MSG/v1";
const TAG_DIGEST: &[u8] = b"QSAG.QUORUM.DIGEST/v1";
const TAG_BINDING: &[u8] = b"QSAG.QUORUM.BINDING/v1";
const TAG_ECHO_MAC: &[u8] = b"QSAG.QUORUM.ECHO.MAC/v1";
pub(crate) const TAG_PAIR_KEY: &[u8] = b"QSAG.QUORUM.PAIR.KEY/v1";
const TAG_STAGE_SK: &[u8] = b"QSAG.QUORUM.STAGE.SK/v1";
pub(crate) const TAG_STAGE_PK_SEED: &[u8] = b"QSAG.QUORUM.STAGE.PKSEED/v1";

/// Errors of the quorum-switching protocols.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum QuorumError {
    /// Parameters outside what the scheme supports; the string names the violated rule.
    InvalidConfig(&'static str),
    /// `2 * q <= n + f`: two quorums could intersect in corrupted custodians only.
    QuorumTooSmall { q: usize, n: usize, f: usize },
    /// The custodian holds no shares for this committee.
    NotCommitteeMember { party: usize, committee: usize },
    /// The signer set is not a committee of the layout.
    UnknownCommittee,
    /// The epoch is above the custodian's high-water mark by more than its window.
    EpochOutOfWindow { epoch: u64, next_epoch: u64 },
    /// The leaf range is used up.
    Exhausted,
    /// No counter below [`MAX_GRIND`] gave the target digit sum.
    GrindFailed,
    /// The durable latch refused (for example the epoch is bound to another message).
    Latch(BeltLatchError),
    /// No echo, or more than one, arrived from a committee member.
    MissingEcho { party: usize },
    /// An echo's MAC does not verify under the pairwise key.
    EchoMacInvalid { party: usize },
    /// A member's echo names another binding: two views of one epoch exist.
    SplitView { party: usize },
    /// A permit does not belong to the custodian's in-flight record.
    PermitMismatch,
    /// An opening is missing, duplicated, or from a custodian outside the signer set.
    BadOpeningSet,
    /// An opening has the wrong shape or names another leaf.
    MalformedOpening { party: usize },
    /// A reconstructed chain node does not hash forward to the public chain end.
    ChainVerifyFailed { chain: usize },
    /// Fewer distinct valid acknowledgements than the quorum.
    CertificateTooSmall { valid: usize, required: usize },
    /// The certificate certifies another leaf or binding than the one requested.
    CertificateBindingMismatch,
    /// Fewer than `t` openings.
    NotEnoughShares { have: usize, need: usize },
    /// Mandatory sign-then-verify or write-once codeword consistency failed before release.
    SignatureVerifyFailed,
}

impl From<BeltLatchError> for QuorumError {
    fn from(e: BeltLatchError) -> Self {
        Self::Latch(e)
    }
}

impl fmt::Display for QuorumError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidConfig(rule) => write!(f, "invalid quorum configuration: {rule}"),
            Self::QuorumTooSmall { q, n, f: faults } => write!(
                f,
                "quorum {q} is too small for n = {n}, f = {faults} (needs 2q > n + f)"
            ),
            Self::NotCommitteeMember { party, committee } => {
                write!(f, "custodian {party} is not in committee {committee}")
            }
            Self::UnknownCommittee => f.write_str("signer set is not a committee"),
            Self::EpochOutOfWindow { epoch, next_epoch } => {
                write!(f, "epoch {epoch} is outside the window above {next_epoch}")
            }
            Self::Exhausted => f.write_str("leaf range exhausted"),
            Self::GrindFailed => f.write_str("no counter reached the target digit sum"),
            Self::Latch(e) => write!(f, "latch refused: {e}"),
            Self::MissingEcho { party } => write!(f, "echo of custodian {party} missing"),
            Self::EchoMacInvalid { party } => write!(f, "echo MAC of custodian {party} invalid"),
            Self::SplitView { party } => {
                write!(f, "split view: custodian {party} bound another record")
            }
            Self::PermitMismatch => f.write_str("permit does not match the in-flight record"),
            Self::BadOpeningSet => f.write_str("openings do not match the signer set"),
            Self::MalformedOpening { party } => write!(f, "malformed opening of custodian {party}"),
            Self::ChainVerifyFailed { chain } => {
                write!(f, "chain {chain} does not reach its public end")
            }
            Self::CertificateTooSmall { valid, required } => write!(
                f,
                "latch certificate has {valid} valid acknowledgements, needs {required}"
            ),
            Self::CertificateBindingMismatch => {
                f.write_str("latch certificate is for another record")
            }
            Self::NotEnoughShares { have, need } => write!(f, "{have} openings, {need} needed"),
            Self::SignatureVerifyFailed => {
                f.write_str("signature failed verify-before-release consistency check")
            }
        }
    }
}

impl core::error::Error for QuorumError {}

// ---------------------------------------------------------------------------------------------
// WOTS+C leaf scheme and the Merkle tree
// ---------------------------------------------------------------------------------------------

/// Public key: one root for every committee and every leaf.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct QuorumPublicKey {
    pub pk_seed: Node,
    pub root: Node,
    pub height: u8,
}

/// A signature: the leaf, the grinding counter, one chain node per chain and the Merkle path.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QuorumJortsSig {
    pub leaf: u64,
    pub counter: u32,
    pub nodes: Vec<Node>,
    pub auth_path: Vec<Node>,
}

impl QuorumJortsSig {
    /// Encoded size: leaf index, counter, 128 nodes and the path.
    pub fn wire_bytes(&self) -> usize {
        8 + 4 + 32 * (self.nodes.len() + self.auth_path.len())
    }
}

/// One step of a chain: `y^(step + 1)` from `y^(step)`.
pub fn chain_step(pk_seed: &Node, leaf: u64, chain: u32, step: u32, input: &Node) -> Node {
    let mut adrs = [0u8; 16];
    adrs[..8].copy_from_slice(&leaf.to_be_bytes());
    adrs[8..12].copy_from_slice(&chain.to_be_bytes());
    adrs[12..].copy_from_slice(&step.to_be_bytes());
    h32(TAG_CHAIN, &[pk_seed, &adrs, input])
}

/// Hash `start = y^(from)` forward to `y^(to)`.
pub fn chain_walk(
    pk_seed: &Node,
    leaf: u64,
    chain: usize,
    from: usize,
    to: usize,
    start: &Node,
) -> Node {
    let mut value = *start;
    for step in from..to {
        value = chain_step(pk_seed, leaf, chain as u32, step as u32, &value);
    }
    value
}

/// Leaf hash over the 128 public chain ends.
pub fn leaf_hash(pk_seed: &Node, leaf: u64, ends: &[Node]) -> Node {
    h32(
        TAG_LEAF,
        &[pk_seed, &leaf.to_be_bytes(), ends.as_flattened()],
    )
}

/// Leaf value of a position that no committee owns. No chain exists for it, so no signature
/// can open it.
pub fn unassigned_leaf(pk_seed: &Node, leaf: u64) -> Node {
    h32(TAG_UNASSIGNED, &[pk_seed, &leaf.to_be_bytes()])
}

fn node_hash(pk_seed: &Node, level: u8, index: u64, left: &Node, right: &Node) -> Node {
    h32(
        TAG_NODE,
        &[pk_seed, &[level], &index.to_be_bytes(), left, right],
    )
}

fn merkle_levels(pk_seed: &Node, leaves: Vec<Node>) -> Vec<Vec<Node>> {
    let mut levels = vec![leaves];
    let mut level = 1u8;
    while levels.last().is_some_and(|l| l.len() > 1) {
        let prev = &levels[levels.len() - 1];
        let next: Vec<Node> = prev
            .as_chunks::<2>()
            .0
            .iter()
            .enumerate()
            .map(|(i, pair)| node_hash(pk_seed, level, i as u64, &pair[0], &pair[1]))
            .collect();
        levels.push(next);
        level += 1;
    }
    levels
}

fn root_from_path(pk_seed: &Node, leaf: u64, leaf_node: &Node, path: &[Node]) -> Node {
    let mut node = *leaf_node;
    let mut index = leaf;
    for (level, sibling) in path.iter().enumerate() {
        let (left, right) = if index & 1 == 0 {
            (&node, sibling)
        } else {
            (sibling, &node)
        };
        index >>= 1;
        node = node_hash(pk_seed, level as u8 + 1, index, left, right);
    }
    node
}

/// Hash of the message, bound to the key and to the leaf that signs it.
pub fn message_hash(pk: &QuorumPublicKey, leaf: u64, msg: &[u8]) -> Node {
    h32(TAG_MSG, &[&pk.pk_seed, &pk.root, &leaf.to_be_bytes(), msg])
}

/// The 128 base-4 digits selected by `counter`, or `None` if they do not sum to
/// [`WOTS_TARGET_SUM`]. Delegates codeword validation to `qsag_verified::VerifiedWotsC256Guard`.
pub fn digits_at(msg_hash: &Node, counter: u32) -> Option<Vec<u8>> {
    let digest = h32(TAG_DIGEST, &[msg_hash, &counter.to_be_bytes()]);
    qsag_verified::VerifiedWotsC256Guard::from_digest_verified(digest)
        .ok()
        .map(|guard| guard.digits().to_vec())
}

/// Smallest counter whose digits reach the target sum. The counter is public and the search
/// is deterministic, so every custodian derives the same record from `(leaf, msg)`.
pub fn grind(msg_hash: &Node) -> Option<(u32, Vec<u8>)> {
    (0..MAX_GRIND).find_map(|counter| digits_at(msg_hash, counter).map(|d| (counter, d)))
}

/// Everything a leaf is bound to when it signs: the message hash, the counter and the digits.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LeafRecord {
    pub leaf: u64,
    pub msg_hash: Node,
    pub counter: u32,
    pub digits: Vec<u8>,
}

impl LeafRecord {
    /// Derive the record of `msg` at `leaf` (grinds the counter).
    pub fn derive(pk: &QuorumPublicKey, leaf: u64, msg: &[u8]) -> Option<Self> {
        let msg_hash = message_hash(pk, leaf, msg);
        let (counter, digits) = grind(&msg_hash)?;
        Some(Self {
            leaf,
            msg_hash,
            counter,
            digits,
        })
    }

    /// Digest binding every field; this is what custodians echo, acknowledge and certify.
    pub fn binding(&self) -> Node {
        h32(
            TAG_BINDING,
            &[
                &self.leaf.to_be_bytes(),
                &self.msg_hash,
                &self.counter.to_be_bytes(),
                &self.digits,
            ],
        )
    }

    /// The counter in the latch's 32-byte salt field.
    fn salt(&self) -> Node {
        let mut salt = [0u8; 32];
        salt[..4].copy_from_slice(&self.counter.to_be_bytes());
        salt
    }

    fn from_latch(leaf: u64, rec: &BeltLatchRecord) -> Self {
        let mut counter = [0u8; 4];
        counter.copy_from_slice(&rec.retry_salt[..4]);
        Self {
            leaf,
            msg_hash: rec.msg_digest,
            counter: u32::from_be_bytes(counter),
            digits: rec.target_sum_digits.clone(),
        }
    }
}

/// Verify `sig` on `msg` under `pk`.
pub fn quorum_jorts_verify(pk: &QuorumPublicKey, msg: &[u8], sig: &QuorumJortsSig) -> bool {
    let height = usize::from(pk.height);
    if height == 0
        || height > 62
        || sig.nodes.len() != WOTS_CHAINS
        || sig.auth_path.len() != height
        || sig.leaf >= 1u64 << height
    {
        return false;
    }
    let msg_hash = message_hash(pk, sig.leaf, msg);
    let Some(digits) = digits_at(&msg_hash, sig.counter) else {
        return false;
    };
    let ends: Vec<Node> = sig
        .nodes
        .iter()
        .zip(&digits)
        .enumerate()
        .map(|(chain, (node, &digit))| {
            chain_walk(
                &pk.pk_seed,
                sig.leaf,
                chain,
                usize::from(digit),
                WOTS_STEPS,
                node,
            )
        })
        .collect();
    let leaf_node = leaf_hash(&pk.pk_seed, sig.leaf, &ends);
    qsag_verified::ct_eq_bytes32(
        &root_from_path(&pk.pk_seed, sig.leaf, &leaf_node, &sig.auth_path),
        &pk.root,
    )
}

/// Alias of [`quorum_jorts_verify`] for callers verifying dealerless or dealer-staged signatures.
pub use quorum_jorts_verify as verify_jorts_signature;

/// The public part of a staged key: the tree and the chain ends of every assigned leaf.
#[derive(Clone, Debug)]
pub struct QuorumTree {
    pk: QuorumPublicKey,
    levels: Vec<Vec<Node>>,
    chain_ends: BTreeMap<u64, Vec<Node>>,
}

impl QuorumTree {
    pub(crate) fn build(pk_seed: Node, height: u8, chain_ends: BTreeMap<u64, Vec<Node>>) -> Self {
        let leaves: Vec<Node> = (0..1u64 << height)
            .map(|leaf| match chain_ends.get(&leaf) {
                Some(ends) => leaf_hash(&pk_seed, leaf, ends),
                None => unassigned_leaf(&pk_seed, leaf),
            })
            .collect();
        let levels = merkle_levels(&pk_seed, leaves);
        let root = levels[usize::from(height)][0];
        Self {
            pk: QuorumPublicKey {
                pk_seed,
                root,
                height,
            },
            levels,
            chain_ends,
        }
    }

    pub fn public_key(&self) -> &QuorumPublicKey {
        &self.pk
    }

    /// Public chain ends of `leaf`, if a committee owns it.
    pub fn chain_ends(&self, leaf: u64) -> Option<&[Node]> {
        self.chain_ends.get(&leaf).map(Vec::as_slice)
    }

    /// Number of leaves that can sign.
    pub fn assigned_leaves(&self) -> usize {
        self.chain_ends.len()
    }

    pub fn auth_path(&self, leaf: u64) -> Vec<Node> {
        let mut index = leaf as usize;
        self.levels[..self.levels.len() - 1]
            .iter()
            .map(|level| {
                let sibling = level[index ^ 1];
                index >>= 1;
                sibling
            })
            .collect()
    }

    /// Check reconstructed chain nodes against the public chain ends, enforce canonical
    /// minimal grinding counter and full Merkle-root `Sign-Then-Verify`, and assemble the
    /// signature. A node that does not reach its chain end names the failing chain.
    fn finish_signature(
        &self,
        record: &LeafRecord,
        nodes: Vec<Node>,
    ) -> Result<QuorumJortsSig, QuorumError> {
        let height = usize::from(self.pk.height);
        if height == 0
            || height > 62
            || record.leaf >= (1u64 << height)
            || nodes.len() != WOTS_CHAINS
            || record.digits.len() != WOTS_CHAINS
            || self.levels.len() != height + 1
        {
            return Err(QuorumError::SignatureVerifyFailed);
        }
        let ends = self
            .chain_ends(record.leaf)
            .ok_or(QuorumError::InvalidConfig("leaf is not assigned"))?;
        if ends.len() != WOTS_CHAINS {
            return Err(QuorumError::SignatureVerifyFailed);
        }
        // Canonical minimal counter & codeword verification: blocks faulted grinding counters
        // `ctr' != ctr` that would otherwise pass public verification on the same `msg_hash`.
        let (canonical_ctr, canonical_digits) =
            grind(&record.msg_hash).ok_or(QuorumError::GrindFailed)?;
        if record.counter != canonical_ctr || record.digits != canonical_digits {
            return Err(QuorumError::SignatureVerifyFailed);
        }
        for (chain, (node, &digit)) in nodes.iter().zip(&record.digits).enumerate() {
            if usize::from(digit) > WOTS_STEPS {
                return Err(QuorumError::SignatureVerifyFailed);
            }
            let end = chain_walk(
                &self.pk.pk_seed,
                record.leaf,
                chain,
                usize::from(digit),
                WOTS_STEPS,
                node,
            );
            if !qsag_verified::ct_eq_bytes32(&end, &ends[chain]) {
                return Err(QuorumError::ChainVerifyFailed { chain });
            }
        }
        let mut index = record.leaf as usize;
        let mut auth_path = Vec::with_capacity(height);
        for level in &self.levels[..height] {
            let sibling = *level
                .get(index ^ 1)
                .ok_or(QuorumError::SignatureVerifyFailed)?;
            auth_path.push(sibling);
            index >>= 1;
        }
        let leaf_node = leaf_hash(&self.pk.pk_seed, record.leaf, ends);
        let recomputed_root = root_from_path(&self.pk.pk_seed, record.leaf, &leaf_node, &auth_path);
        if !qsag_verified::ct_eq_bytes32(&recomputed_root, &self.pk.root) {
            return Err(QuorumError::SignatureVerifyFailed);
        }
        Ok(QuorumJortsSig {
            leaf: record.leaf,
            counter: record.counter,
            nodes,
            auth_path,
        })
    }
}

/// One custodian's shares of the chain nodes a signature reveals: entry `i` is its share of
/// `y_i^(d_i)`, or zero where `d_i = 3` and the node is the public chain end.
#[derive(Clone, PartialEq, Eq)]
pub struct ShareOpening {
    pub party: usize,
    pub leaf: u64,
    pub shares: Vec<Node>,
}

/// Bytes of a [`ShareOpening`] on the wire: the leaf index and 128 shares.
pub const SHARE_OPENING_WIRE_BYTES: usize = 8 + 32 * WOTS_CHAINS;

fn select_shares(party: usize, record: &LeafRecord, leaf_shares: &[Node]) -> ShareOpening {
    let shares = record
        .digits
        .iter()
        .enumerate()
        .map(|(chain, &digit)| {
            if usize::from(digit) < WOTS_STEPS {
                leaf_shares[chain * WOTS_STEPS + usize::from(digit)]
            } else {
                [0u8; 32]
            }
        })
        .collect();
    ShareOpening {
        party,
        leaf: record.leaf,
        shares,
    }
}

fn check_opening(opening: &ShareOpening, record: &LeafRecord) -> Result<(), QuorumError> {
    if opening.leaf != record.leaf || opening.shares.len() != WOTS_CHAINS {
        return Err(QuorumError::MalformedOpening {
            party: opening.party,
        });
    }
    Ok(())
}

/// All `k`-subsets of `0..n` in lexicographic order.
pub fn combinations(n: usize, k: usize) -> Vec<Vec<usize>> {
    let mut out = Vec::new();
    if k > n {
        return out;
    }
    let mut current: Vec<usize> = (0..k).collect();
    loop {
        out.push(current.clone());
        let Some(pos) = (0..k).rev().find(|&i| current[i] < n - k + i) else {
            return out;
        };
        current[pos] += 1;
        for i in pos + 1..k {
            current[i] = current[i - 1] + 1;
        }
    }
}

/// Symmetric pairwise MAC keys derived from `seed`: entry `[i][j]` equals entry `[j][i]`.
/// Row `i` is what custodian `i` holds. A dealer stands in for a pairwise key agreement.
pub fn pairwise_mac_keys(seed: &Node, n: usize) -> Vec<Vec<Node>> {
    (0..n)
        .map(|i| {
            (0..n)
                .map(|j| {
                    let (lo, hi) = (i.min(j) as u64, i.max(j) as u64);
                    h32(TAG_PAIR_KEY, &[seed, &lo.to_be_bytes(), &hi.to_be_bytes()])
                })
                .collect()
        })
        .collect()
}

/// The four chain states of every chain of `leaf`: `(secret states, public ends)`.
fn stage_leaf_chains(seed: &Node, pk_seed: &Node, leaf: u64) -> (Vec<Node>, Vec<Node>) {
    let mut secrets = Vec::with_capacity(LEAF_SHARE_NODES);
    let mut ends = Vec::with_capacity(WOTS_CHAINS);
    for chain in 0..WOTS_CHAINS {
        let mut value = h32(
            TAG_STAGE_SK,
            &[seed, &leaf.to_be_bytes(), &(chain as u32).to_be_bytes()],
        );
        for step in 0..WOTS_STEPS {
            secrets.push(value);
            value = chain_step(pk_seed, leaf, chain as u32, step as u32, &value);
        }
        ends.push(value);
    }
    (secrets, ends)
}

fn latch_capacity_log2(leaves: u64) -> usize {
    (leaves.next_power_of_two().trailing_zeros() as usize).max(1)
}

fn window_check(epoch: u64, next_epoch: u64, replay: bool, window: u64) -> Result<(), QuorumError> {
    if !replay && epoch > next_epoch.saturating_add(window) {
        return Err(QuorumError::EpochOutOfWindow { epoch, next_epoch });
    }
    Ok(())
}

// ---------------------------------------------------------------------------------------------
// Mode QS-A: committee-partitioned t-of-t subtrees
// ---------------------------------------------------------------------------------------------

/// How the leaves are divided among the `binom(n, t)` committees.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CommitteeLayout {
    pub t: usize,
    pub n: usize,
    pub height: u8,
    committees: Vec<Vec<usize>>,
    leaves_per_committee: u64,
}

/// Maximum party count accepted by committee-partitioned quorum configurations.
pub const MAX_QUORUM_PARTIES: usize = 255;
/// Maximum custodian count mediated by `VerifiedBeltQuorumGuard` in Mode QS-B (`n <= 64`).
pub const MAX_SHAMIR_QUORUM_PARTIES: usize = 64;
/// Maximum enumerated committees; use `BftShamirJorts` for larger configurations.
pub const MAX_COMMITTEES: usize = 1024;
const MAX_STAGED_SHARE_BYTES: usize = 256 * 1024 * 1024;
pub(crate) fn check_staging_budget(height: u8, copies: usize) -> Result<(), QuorumError> {
    if height == 0
        || height > 10
        || (1usize << height)
            .checked_mul(copies)
            .and_then(|n| n.checked_mul(LEAF_SHARE_NODES * 32))
            .is_none_or(|bytes| bytes > MAX_STAGED_SHARE_BYTES)
    {
        return Err(QuorumError::InvalidConfig("staging memory budget exceeded"));
    }
    Ok(())
}

impl CommitteeLayout {
    pub fn new(t: usize, n: usize, height: u8) -> Result<Self, QuorumError> {
        if t < 2 || t > n || n > MAX_QUORUM_PARTIES {
            return Err(QuorumError::InvalidConfig("need 2 <= t <= n <= 255"));
        }
        if height == 0 || height > 30 {
            return Err(QuorumError::InvalidConfig("need 1 <= height <= 30"));
        }
        let mut count = 1usize;
        for k in 1..=t.min(n - t) {
            count = count
                .checked_mul(n - k + 1)
                .and_then(|v| v.checked_div(k))
                .filter(|&v| v <= MAX_COMMITTEES)
                .ok_or(QuorumError::InvalidConfig(
                    "too many committees; use BftShamirJorts",
                ))?;
        }
        let committees = combinations(n, t);
        let leaves_per_committee = (1u64 << height) / committees.len() as u64;
        if leaves_per_committee == 0 {
            return Err(QuorumError::InvalidConfig(
                "tree has fewer leaves than committees",
            ));
        }
        Ok(Self {
            t,
            n,
            height,
            committees,
            leaves_per_committee,
        })
    }

    /// The committees, each a sorted list of custodian indices.
    pub fn committees(&self) -> &[Vec<usize>] {
        &self.committees
    }

    pub fn leaves_per_committee(&self) -> u64 {
        self.leaves_per_committee
    }

    /// Index of the committee whose members are exactly `signers` (in any order).
    pub fn committee_index(&self, signers: &[usize]) -> Option<usize> {
        let mut sorted = signers.to_vec();
        sorted.sort_unstable();
        self.committees.iter().position(|c| *c == sorted)
    }

    /// Global leaf index of `epoch` in the range of `committee`.
    pub fn leaf_of(&self, committee: usize, epoch: u64) -> u64 {
        committee as u64 * self.leaves_per_committee + epoch
    }

    /// The committee that owns `leaf`, if any.
    pub fn committee_of_leaf(&self, leaf: u64) -> Option<usize> {
        let committee = (leaf / self.leaves_per_committee) as usize;
        (committee < self.committees.len()).then_some(committee)
    }
}

/// One custodian's sealed additive shares for one committee.
/// Raw shares are available only to this module's authorized signing ceremony.
///
/// ```compile_fail
/// use qsag_quorum::quorum_jorts::CommitteeShareStore;
/// fn duplicate(store: &CommitteeShareStore) -> CommitteeShareStore {
///     store.clone()
/// }
/// ```
///
/// ```compile_fail
/// use qsag_quorum::quorum_jorts::CommitteeShareStore;
/// fn expose(store: CommitteeShareStore) {
///     let _ = store.leaves;
/// }
/// ```
pub struct CommitteeShareStore {
    committee: usize,
    leaves: Vec<Vec<Node>>,
}

impl CommitteeShareStore {
    pub(crate) fn from_parts(committee: usize, leaves: Vec<Vec<Node>>) -> Self {
        Self { committee, leaves }
    }

    pub(crate) fn committee(&self) -> usize {
        self.committee
    }

    pub(crate) fn leaves_mut(&mut self) -> &mut [Vec<Node>] {
        &mut self.leaves
    }
}

/// What staging hands to one custodian.
pub struct CommitteePartyMaterial {
    pub party: usize,
    /// Pairwise MAC keys, indexed by peer.
    mac_keys: Vec<Node>,
    pub stores: Vec<CommitteeShareStore>,
}

impl CommitteePartyMaterial {
    pub(crate) fn from_parts(
        party: usize,
        mac_keys: Vec<Node>,
        stores: Vec<CommitteeShareStore>,
    ) -> Self {
        Self {
            party,
            mac_keys,
            stores,
        }
    }

    pub(crate) fn replace_mac_keys(&mut self, new_keys: Vec<Node>) {
        wipe_nodes(&mut self.mac_keys);
        self.mac_keys = new_keys;
    }
}

/// Output of [`stage_committee_partitioned`].
pub struct StagedCommitteeKeys {
    pub layout: CommitteeLayout,
    pub tree: Arc<QuorumTree>,
    pub parties: Vec<CommitteePartyMaterial>,
}

/// Dealer staging for Mode QS-A (see the module documentation for what a dealer stands for).
/// TRUSTED DEALER TEST/MEASUREMENT HELPER: centralizes all signing secrets.
pub fn stage_committee_partitioned(
    t: usize,
    n: usize,
    height: u8,
    seed: &Node,
) -> Result<StagedCommitteeKeys, QuorumError> {
    let layout = CommitteeLayout::new(t, n, height)?;
    check_staging_budget(height, t)?;
    let pk_seed = h32(TAG_STAGE_PK_SEED, &[seed]);
    let mut rng = SeedRng::new(seed, b"QS-A additive shares");
    let mac_keys = pairwise_mac_keys(seed, n);
    let mut parties: Vec<CommitteePartyMaterial> = (0..n)
        .map(|party| CommitteePartyMaterial {
            party,
            mac_keys: mac_keys[party].clone(),
            stores: Vec::new(),
        })
        .collect();
    let mut chain_ends = BTreeMap::new();
    for (committee, members) in layout.committees().iter().enumerate() {
        let mut stores: Vec<CommitteeShareStore> = members
            .iter()
            .map(|_| CommitteeShareStore {
                committee,
                leaves: Vec::new(),
            })
            .collect();
        for epoch in 0..layout.leaves_per_committee() {
            let leaf = layout.leaf_of(committee, epoch);
            let (secrets, ends) = stage_leaf_chains(seed, &pk_seed, leaf);
            chain_ends.insert(leaf, ends);
            let mut last = secrets;
            for store in &mut stores[..t - 1] {
                let mut share = vec![[0u8; 32]; LEAF_SHARE_NODES];
                rng.fill(share.as_flattened_mut());
                for (acc, s) in last.as_flattened_mut().iter_mut().zip(share.as_flattened()) {
                    *acc ^= s;
                }
                store.leaves.push(share);
            }
            stores[t - 1].leaves.push(last);
        }
        for (store, &member) in stores.into_iter().zip(members) {
            parties[member].stores.push(store);
        }
    }
    Ok(StagedCommitteeKeys {
        tree: Arc::new(QuorumTree::build(pk_seed, height, chain_ends)),
        layout,
        parties,
    })
}

/// A custodian's authenticated statement to one peer that it bound `binding` at `epoch`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LatchEcho {
    pub from: usize,
    pub committee: usize,
    pub epoch: u64,
    pub binding: Node,
    pub mac: Node,
}

fn echo_mac_parts(from: usize, to: usize, committee: usize, epoch: u64) -> [[u8; 8]; 4] {
    [
        (from as u64).to_be_bytes(),
        (to as u64).to_be_bytes(),
        (committee as u64).to_be_bytes(),
        epoch.to_be_bytes(),
    ]
}

/// Proof that a custodian bound a record and saw the same binding echoed, under valid MACs,
/// by every other member of the committee. Not `Clone`; only
/// [`CommitteeCustodian::verify_echoes`] creates one.
#[derive(Debug, PartialEq, Eq)]
pub struct CommitteePermit {
    party: usize,
    committee: usize,
    epoch: u64,
    binding: Node,
}

/// Per-leaf share nodes of one custodian.
type SecretLeaves = SecretVec<Vec<Node>>;
/// One pairwise MAC key per custodian.
type SecretMacKeys = SecretVec<Node>;

struct CommitteeSlot<W: DurableWal> {
    latch: BeltLatch<W>,
    leaves: SecretLeaves,
}

/// One custodian of Mode QS-A: its own shares, latches and MAC keys, nothing of its peers.
pub struct CommitteeCustodian<W: DurableWal> {
    party: usize,
    layout: CommitteeLayout,
    tree: Arc<QuorumTree>,
    mac_keys: SecretMacKeys,
    slots: BTreeMap<usize, CommitteeSlot<W>>,
    max_window: u64,
}

impl<W: DurableWal> CommitteeCustodian<W> {
    /// Build a custodian from its staged material. `wals` supplies one log per share store,
    /// in the order of `material.stores`.
    pub fn new(
        layout: CommitteeLayout,
        tree: Arc<QuorumTree>,
        mut material: CommitteePartyMaterial,
        wals: Vec<W>,
    ) -> Result<Self, QuorumError> {
        if wals.len() != material.stores.len() || material.mac_keys.len() != layout.n {
            return Err(QuorumError::InvalidConfig(
                "one log per committee and one MAC key per custodian",
            ));
        }
        let capacity = latch_capacity_log2(layout.leaves_per_committee());
        let mut slots = BTreeMap::new();
        for (mut store, wal) in core::mem::take(&mut material.stores).into_iter().zip(wals) {
            let latch = BeltLatch::recover(wal, capacity)?;
            slots.insert(
                store.committee,
                CommitteeSlot {
                    latch,
                    leaves: SecretBuffer(core::mem::take(&mut store.leaves)),
                },
            );
        }
        Ok(Self {
            party: material.party,
            layout,
            tree,
            mac_keys: SecretBuffer(core::mem::take(&mut material.mac_keys)),
            slots,
            max_window: MAX_WINDOW,
        })
    }

    pub fn party(&self) -> usize {
        self.party
    }

    pub fn layout(&self) -> &CommitteeLayout {
        &self.layout
    }

    pub fn tree(&self) -> &Arc<QuorumTree> {
        &self.tree
    }

    /// Committees this custodian holds shares for.
    pub fn committees(&self) -> impl Iterator<Item = usize> + '_ {
        self.slots.keys().copied()
    }

    /// Storage of one custodian in bytes of share material.
    pub fn share_bytes(&self) -> usize {
        self.slots
            .values()
            .map(|s| s.leaves.len() * LEAF_SHARE_NODES * 32)
            .sum()
    }

    /// Give the logs back, ordered by committee (a simulated restart or controlled shutdown).
    pub fn into_wals(self) -> Vec<W> {
        self.slots
            .into_values()
            .map(|s| s.latch.into_wal())
            .collect()
    }

    fn slot(&self, committee: usize) -> Result<&CommitteeSlot<W>, QuorumError> {
        self.slots
            .get(&committee)
            .ok_or(QuorumError::NotCommitteeMember {
                party: self.party,
                committee,
            })
    }

    pub(crate) fn slot_leaves_mut(
        &mut self,
        committee: usize,
    ) -> Result<&mut [Vec<Node>], QuorumError> {
        let party = self.party;
        self.slots
            .get_mut(&committee)
            .map(|s| s.leaves.0.as_mut_slice())
            .ok_or(QuorumError::NotCommitteeMember { party, committee })
    }

    pub(crate) fn replace_mac_keys(&mut self, new_keys: Vec<Node>) -> Result<(), QuorumError> {
        if new_keys.len() != self.layout.n {
            return Err(QuorumError::InvalidConfig(
                "one MAC key per custodian required",
            ));
        }
        self.mac_keys = SecretBuffer(new_keys);
        Ok(())
    }

    /// The custodian's high-water mark for `committee`.
    pub fn next_epoch(&self, committee: usize) -> Result<u64, QuorumError> {
        Ok(self.slot(committee)?.latch.next_epoch())
    }

    /// The record currently bound for `committee`, if any.
    pub fn in_flight(&self, committee: usize) -> Result<Option<LeafRecord>, QuorumError> {
        let slot = self.slot(committee)?;
        Ok(slot
            .latch
            .in_flight()
            .map(|rec| LeafRecord::from_latch(self.layout.leaf_of(committee, rec.epoch), rec)))
    }

    /// Derive the record of `msg` at `epoch` of `committee` and bind it durably. Refuses an
    /// epoch already bound to another record and one beyond the window above the high-water
    /// mark; an identical request replays the stored record.
    pub fn bind(
        &mut self,
        committee: usize,
        epoch: u64,
        msg: &[u8],
    ) -> Result<LeafRecord, QuorumError> {
        let party = self.party;
        let slot = self
            .slots
            .get_mut(&committee)
            .ok_or(QuorumError::NotCommitteeMember { party, committee })?;
        if epoch >= self.layout.leaves_per_committee {
            return Err(QuorumError::Exhausted);
        }
        let replay = slot.latch.in_flight().is_some_and(|r| r.epoch == epoch);
        window_check(epoch, slot.latch.next_epoch(), replay, self.max_window)?;
        let leaf = self.layout.leaf_of(committee, epoch);
        let record = LeafRecord::derive(self.tree.public_key(), leaf, msg)
            .ok_or(QuorumError::GrindFailed)?;
        slot.latch
            .bind(epoch, &record.msg_hash, &record.salt(), &record.digits)?;
        Ok(record)
    }

    /// The echo of the in-flight record of `committee`, authenticated for `peer`.
    pub fn echo_for(&self, committee: usize, peer: usize) -> Result<LatchEcho, QuorumError> {
        let record = self
            .in_flight(committee)?
            .ok_or(QuorumError::Latch(BeltLatchError::NothingBound))?;
        let key = self
            .mac_keys
            .get(peer)
            .ok_or(QuorumError::InvalidConfig("unknown peer"))?;
        let epoch = record.leaf - self.layout.leaf_of(committee, 0);
        let binding = record.binding();
        let parts = echo_mac_parts(self.party, peer, committee, epoch);
        let mac = mac32(
            key,
            TAG_ECHO_MAC,
            &[&parts[0], &parts[1], &parts[2], &parts[3], &binding],
        );
        Ok(LatchEcho {
            from: self.party,
            committee,
            epoch,
            binding,
            mac,
        })
    }

    /// Require exactly one echo from every other member of `committee`, each with a valid MAC
    /// and the binding of the local in-flight record.
    pub fn verify_echoes(
        &self,
        committee: usize,
        echoes: &[LatchEcho],
    ) -> Result<CommitteePermit, QuorumError> {
        let record = self
            .in_flight(committee)?
            .ok_or(QuorumError::Latch(BeltLatchError::NothingBound))?;
        let epoch = record.leaf - self.layout.leaf_of(committee, 0);
        let binding = record.binding();
        for &peer in self.layout.committees()[committee]
            .iter()
            .filter(|&&p| p != self.party)
        {
            let mut seen = echoes.iter().filter(|e| e.from == peer);
            let (Some(echo), None) = (seen.next(), seen.next()) else {
                return Err(QuorumError::MissingEcho { party: peer });
            };
            let parts = echo_mac_parts(peer, self.party, echo.committee, echo.epoch);
            if !mac32_verify(
                &self.mac_keys[peer],
                TAG_ECHO_MAC,
                &[&parts[0], &parts[1], &parts[2], &parts[3], &echo.binding],
                &echo.mac,
            ) {
                return Err(QuorumError::EchoMacInvalid { party: peer });
            }
            if echo.committee != committee || echo.epoch != epoch || echo.binding != binding {
                return Err(QuorumError::SplitView { party: peer });
            }
        }
        Ok(CommitteePermit {
            party: self.party,
            committee,
            epoch,
            binding,
        })
    }

    /// Open this custodian's additive shares of the nodes the permitted record reveals.
    pub fn open(&self, permit: &CommitteePermit) -> Result<ShareOpening, QuorumError> {
        let record = self
            .in_flight(permit.committee)?
            .ok_or(QuorumError::PermitMismatch)?;
        if permit.party != self.party
            || record.leaf != self.layout.leaf_of(permit.committee, permit.epoch)
            || record.binding() != permit.binding
        {
            return Err(QuorumError::PermitMismatch);
        }
        let slot = self.slot(permit.committee)?;
        Ok(select_shares(
            self.party,
            &record,
            &slot.leaves[permit.epoch as usize],
        ))
    }
}

/// Combine the additive openings of every member of a committee into a signature. Each
/// reconstructed node is hashed forward to its public chain end.
pub fn combine_additive(
    tree: &QuorumTree,
    record: &LeafRecord,
    members: &[usize],
    openings: &[ShareOpening],
) -> Result<QuorumJortsSig, QuorumError> {
    let ends = tree
        .chain_ends(record.leaf)
        .ok_or(QuorumError::InvalidConfig("leaf is not assigned"))?;
    if openings.len() != members.len() {
        return Err(QuorumError::BadOpeningSet);
    }
    let mut nodes = vec![[0u8; 32]; WOTS_CHAINS];
    for &member in members {
        let mut found = openings.iter().filter(|o| o.party == member);
        let (Some(opening), None) = (found.next(), found.next()) else {
            return Err(QuorumError::BadOpeningSet);
        };
        check_opening(opening, record)?;
        for (acc, s) in nodes
            .as_flattened_mut()
            .iter_mut()
            .zip(opening.shares.as_flattened())
        {
            *acc ^= s;
        }
    }
    for (chain, &digit) in record.digits.iter().enumerate() {
        if usize::from(digit) == WOTS_STEPS {
            nodes[chain] = ends[chain];
        }
    }
    tree.finish_signature(record, nodes)
}

/// All custodians of Mode QS-A driven in one process (tests and measurements; see the module
/// documentation).
/// QS-A is committee-revealing partitioned custody: disjoint leaf ranges reveal
/// the signing committee as `floor(leaf_idx / leaves_per_committee)` among the
/// binomial(n, t) committees. It does not provide signer-set privacy.
pub struct CommitteePartitionedJorts<W: DurableWal> {
    pub layout: CommitteeLayout,
    pub tree: Arc<QuorumTree>,
    pub custodians: Vec<CommitteeCustodian<W>>,
    ots_release_cache: BTreeMap<u64, (Node, u32)>,
}

#[cfg(any(test, feature = "testing-ephemeral"))]
impl CommitteePartitionedJorts<MemoryWal> {
    /// Stage a key with volatile logs (restricted to tests and `testing-ephemeral`).
    pub fn stage(t: usize, n: usize, height: u8, seed: &Node) -> Result<Self, QuorumError> {
        Self::stage_durable(t, n, height, seed, |_party, store_count| {
            vec![MemoryWal::new(); store_count]
        })
    }

    /// Build from pre-staged (e.g. dealerless MPC) committee keys with volatile logs.
    pub fn from_staged(staged: StagedCommitteeKeys) -> Result<Self, QuorumError> {
        Self::from_staged_durable(staged, |_party, store_count| {
            vec![MemoryWal::new(); store_count]
        })
    }
}

impl<W: DurableWal> CommitteePartitionedJorts<W> {
    /// Build from pre-staged (e.g. dealerless MPC) committee keys with caller-provisioned logs.
    pub fn from_staged_durable(
        staged: StagedCommitteeKeys,
        mut make_wals: impl FnMut(usize, usize) -> Vec<W>,
    ) -> Result<Self, QuorumError> {
        if staged.parties.len() != staged.layout.n {
            return Err(QuorumError::InvalidConfig("party count mismatch"));
        }
        let custodians = staged
            .parties
            .into_iter()
            .map(|material| {
                let wals = make_wals(material.party, material.stores.len());
                CommitteeCustodian::new(staged.layout.clone(), staged.tree.clone(), material, wals)
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self {
            layout: staged.layout,
            tree: staged.tree,
            custodians,
            ots_release_cache: BTreeMap::new(),
        })
    }

    /// Stage a key with caller-provisioned durable logs (one per committee slot per party).
    pub fn stage_durable(
        t: usize,
        n: usize,
        height: u8,
        seed: &Node,
        make_wals: impl FnMut(usize, usize) -> Vec<W>,
    ) -> Result<Self, QuorumError> {
        let staged = stage_committee_partitioned(t, n, height, seed)?;
        Self::from_staged_durable(staged, make_wals)
    }
    pub fn public_key(&self) -> &QuorumPublicKey {
        self.tree.public_key()
    }

    /// The next epoch every member of `committee` can still bind.
    pub fn next_epoch(&self, committee: usize) -> Result<u64, QuorumError> {
        let mut epoch = 0;
        for &member in &self.layout.committees()[committee] {
            epoch = epoch.max(self.custodians[member].next_epoch(committee)?);
        }
        Ok(epoch)
    }

    /// Sign `msg` with exactly the `t` custodians in `online`, at their committee's next
    /// free epoch.
    pub fn sign(&mut self, online: &[usize], msg: &[u8]) -> Result<QuorumJortsSig, QuorumError> {
        let committee = self
            .layout
            .committee_index(online)
            .ok_or(QuorumError::UnknownCommittee)?;
        let epoch = self.next_epoch(committee)?;
        self.sign_at(committee, epoch, msg)
    }

    /// Sign `msg` at a chosen epoch of `committee`.
    pub fn sign_at(
        &mut self,
        committee: usize,
        epoch: u64,
        msg: &[u8],
    ) -> Result<QuorumJortsSig, QuorumError> {
        let members = self.layout.committees()[committee].clone();
        let mut record = None;
        for &member in &members {
            record = Some(self.custodians[member].bind(committee, epoch, msg)?);
        }
        let record = record.ok_or(QuorumError::InvalidConfig("empty committee"))?;
        let mut openings = Vec::with_capacity(members.len());
        for &member in &members {
            let echoes = members
                .iter()
                .filter(|&&peer| peer != member)
                .map(|&peer| self.custodians[peer].echo_for(committee, member))
                .collect::<Result<Vec<_>, _>>()?;
            let permit = self.custodians[member].verify_echoes(committee, &echoes)?;
            openings.push(self.custodians[member].open(&permit)?);
        }
        let sig = combine_additive(&self.tree, &record, &members, &openings)?;
        if let Some((prev_hash, prev_ctr)) = self.ots_release_cache.get(&sig.leaf)
            && (!qsag_verified::ct_eq_bytes32(prev_hash, &record.msg_hash)
                || *prev_ctr != sig.counter)
        {
            return Err(QuorumError::SignatureVerifyFailed);
        }
        if !quorum_jorts_verify(self.public_key(), msg, &sig) {
            return Err(QuorumError::SignatureVerifyFailed);
        }
        self.ots_release_cache
            .insert(sig.leaf, (record.msg_hash, sig.counter));
        Ok(sig)
    }
}

// ---------------------------------------------------------------------------------------------
// Mode QS-B: global tree, (t, n) Shamir shares, latch certificate
// ---------------------------------------------------------------------------------------------

/// Parameters of Mode QS-B: `t` shares reconstruct, at most `f` custodians are corrupted, and
/// `q` acknowledgements certify a leaf.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct QuorumConfig {
    t: usize,
    n: usize,
    f: usize,
    q: usize,
}

impl QuorumConfig {
    /// The configuration with the smallest safe quorum, `q = floor((n + f) / 2) + 1`.
    pub fn new(t: usize, n: usize, f: usize) -> Result<Self, QuorumError> {
        let sum = n
            .checked_add(f)
            .ok_or(QuorumError::InvalidConfig("quorum parameter overflow"))?;
        Self::with_quorum(t, n, f, sum / 2 + 1)
    }

    /// The tightest configuration for threshold `t`: `f = t - 1` corrupted custodians among
    /// `n = 3t - 2` (`n <= MAX_SHAMIR_QUORUM_PARTIES`).
    pub fn tight(t: usize) -> Result<Self, QuorumError> {
        if t == 0 || t > MAX_SHAMIR_QUORUM_PARTIES || 3 * t - 2 > MAX_SHAMIR_QUORUM_PARTIES {
            return Err(QuorumError::InvalidConfig("need 1 <= t and 1 <= n <= 64"));
        }
        Self::new(t, 3 * t - 2, t - 1)
    }

    /// A configuration with an explicit quorum. Rejected unless `n <= 64` (the
    /// `VerifiedBeltQuorumGuard` mediation bound), `2q > n + f` (any two quorums
    /// share an honest custodian), `q <= n - f` (the honest custodians alone form a quorum),
    /// `f < t` (the corrupted custodians cannot reconstruct) and `t <= n - f`.
    pub fn with_quorum(t: usize, n: usize, f: usize, q: usize) -> Result<Self, QuorumError> {
        if n == 0 || n > MAX_SHAMIR_QUORUM_PARTIES || t == 0 || t > n || f >= n || q > n {
            return Err(QuorumError::InvalidConfig("need 1 <= t and 1 <= n <= 64"));
        }
        // Production uses global BFT liveness, not the safety-only committee mode.
        if !qsag_verified::validate_belt_quorum_config(n as u32, t as u32, f as u32, q as u32, true)
        {
            if 2 * q <= n + f {
                return Err(QuorumError::QuorumTooSmall { q, n, f });
            }
            return Err(QuorumError::InvalidConfig(
                "invalid global BFT quorum configuration",
            ));
        }
        Ok(Self { t, n, f, q })
    }

    pub fn threshold(&self) -> usize {
        self.t
    }

    pub fn parties(&self) -> usize {
        self.n
    }

    pub fn max_faults(&self) -> usize {
        self.f
    }

    pub fn quorum(&self) -> usize {
        self.q
    }
}

/// What staging hands to one custodian of Mode QS-B. Like [`CommitteeShareStore`], the
/// shares and MAC keys can only be moved into a [`ShamirCustodian`]: they are neither
/// readable nor duplicable from outside this module.
///
/// ```compile_fail
/// use qsag_quorum::quorum_jorts::ShamirPartyMaterial;
/// fn duplicate(material: &ShamirPartyMaterial) -> ShamirPartyMaterial {
///     material.clone()
/// }
/// ```
///
/// ```compile_fail
/// use qsag_quorum::quorum_jorts::ShamirPartyMaterial;
/// fn expose(material: ShamirPartyMaterial) {
///     let _ = &material.leaves;
/// }
/// ```
///
/// ```compile_fail
/// use qsag_quorum::quorum_jorts::ShamirPartyMaterial;
/// fn expose(material: ShamirPartyMaterial) {
///     let _ = &material.mac_keys;
/// }
/// ```
pub struct ShamirPartyMaterial {
    pub party: usize,
    /// Pairwise MAC keys indexed by peer; the custodian's own index holds a private key.
    mac_keys: Vec<Node>,
    /// `leaves[leaf][3 * chain + step]`: this custodian's Shamir share of each chain state.
    leaves: Vec<Vec<Node>>,
}

impl ShamirPartyMaterial {
    pub(crate) fn from_parts(party: usize, mac_keys: Vec<Node>, leaves: Vec<Vec<Node>>) -> Self {
        Self {
            party,
            mac_keys,
            leaves,
        }
    }

    pub(crate) fn leaves_mut(&mut self) -> &mut [Vec<Node>] {
        &mut self.leaves
    }

    pub(crate) fn replace_mac_keys(&mut self, new_keys: Vec<Node>) {
        wipe_nodes(&mut self.mac_keys);
        self.mac_keys = new_keys;
    }
}

/// Output of [`stage_bft_shamir`].
pub struct StagedShamirKeys {
    pub cfg: QuorumConfig,
    pub tree: Arc<QuorumTree>,
    pub parties: Vec<ShamirPartyMaterial>,
}

pub(crate) fn shamir_point(party: usize) -> TowerGf256 {
    TowerGf256(party as u8 + 1)
}

/// Branchless, LUT-free multiplication in the protocol's Wiedemann tower basis.
/// Using an AES-polynomial Russian-peasant multiplier here would change the field encoding.
pub(crate) fn gf256_mul_ct(a: u8, b: u8) -> u8 {
    TowerGf256(a).mul(TowerGf256(b)).0
}

/// Dealer staging for Mode QS-B. Every byte of every chain state gets its own random
/// polynomial of degree `t - 1`; custodian `p` receives its value at `p + 1`.
/// TRUSTED DEALER TEST/MEASUREMENT HELPER: centralizes all signing secrets.
pub fn stage_bft_shamir(
    cfg: QuorumConfig,
    height: u8,
    seed: &Node,
) -> Result<StagedShamirKeys, QuorumError> {
    if height == 0 || height > 10 {
        return Err(QuorumError::InvalidConfig("need 1 <= height <= 10"));
    }
    check_staging_budget(height, cfg.n)?;
    let pk_seed = h32(TAG_STAGE_PK_SEED, &[seed]);
    let mut rng = SeedRng::new(seed, b"QS-B Shamir coefficients");
    let mac_keys = pairwise_mac_keys(seed, cfg.n);
    // powers[p][k] multiplies by (p + 1)^(k + 1).
    let powers: Vec<Vec<u8>> = (0..cfg.n)
        .map(|p| {
            let x = shamir_point(p);
            let mut acc = TowerGf256::ONE;
            (1..cfg.t)
                .map(|_| {
                    acc = acc.mul(x);
                    acc.0
                })
                .collect()
        })
        .collect();
    let mut parties: Vec<ShamirPartyMaterial> = (0..cfg.n)
        .map(|party| ShamirPartyMaterial {
            party,
            mac_keys: mac_keys[party].clone(),
            leaves: Vec::new(),
        })
        .collect();
    let mut chain_ends = BTreeMap::new();
    let secret_bytes = LEAF_SHARE_NODES * 32;
    let mut coeffs = vec![0u8; secret_bytes * (cfg.t - 1)];
    for leaf in 0..1u64 << height {
        let (secrets, ends) = stage_leaf_chains(seed, &pk_seed, leaf);
        chain_ends.insert(leaf, ends);
        rng.fill(&mut coeffs);
        let flat = secrets.as_flattened();
        for (p, party) in parties.iter_mut().enumerate() {
            let mut share = vec![[0u8; 32]; LEAF_SHARE_NODES];
            for (b, out) in share.as_flattened_mut().iter_mut().enumerate() {
                let mut acc = flat[b];
                for (k, power) in powers[p].iter().enumerate() {
                    acc ^= gf256_mul_ct(*power, coeffs[b * (cfg.t - 1) + k]);
                }
                *out = acc;
            }
            party.leaves.push(share);
        }
    }
    qsag_asm::volatile_fill(&mut coeffs, 0);
    core::hint::black_box(coeffs.as_mut_slice());
    Ok(StagedShamirKeys {
        cfg,
        tree: Arc::new(QuorumTree::build(pk_seed, height, chain_ends)),
        parties,
    })
}

/// A custodian's acknowledgement that it bound `binding` at `leaf`, with one MAC per
/// custodian so that any of them can check it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LatchAck {
    pub from: usize,
    pub leaf: u64,
    pub binding: Node,
    pub macs: Vec<Node>,
}

/// Acknowledgements of one binding at one leaf. Valid for a custodian when at least `q` of
/// them, from distinct custodians, carry a MAC that custodian can verify.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LatchCertificate {
    pub leaf: u64,
    pub binding: Node,
    pub acks: Vec<LatchAck>,
}

impl LatchCertificate {
    /// Collect the acknowledgements that name `record`.
    pub fn assemble(record: &LeafRecord, acks: impl IntoIterator<Item = LatchAck>) -> Self {
        let binding = record.binding();
        Self {
            leaf: record.leaf,
            binding,
            acks: acks
                .into_iter()
                .filter(|a| a.leaf == record.leaf && a.binding == binding)
                .collect(),
        }
    }
}

type SecretWalKey = SecretBytes<32>;

fn belt_guard_key_commit(pk: &QuorumPublicKey, party: usize) -> Node {
    h32(
        b"QSAG.QUORUM.BELT_GUARD/v1",
        &[&pk.pk_seed, &pk.root, &(party as u64).to_be_bytes()],
    )
}

fn belt_wal_receipt_digest(epoch: u64, binding: &Node) -> Node {
    h32(
        b"QSAG.QUORUM.WAL_RECEIPT/v1",
        &[&epoch.to_be_bytes(), binding],
    )
}

fn build_verified_belt_guard(
    cfg: QuorumConfig,
    pk: &QuorumPublicKey,
    party: usize,
    mac_keys: &[Node],
    max_window: u64,
    next_epoch: u64,
    in_flight: Option<&BeltLatchRecord>,
) -> Result<(qsag_verified::VerifiedBeltQuorumGuard, SecretWalKey), QuorumError> {
    let guard_key_commit = belt_guard_key_commit(pk, party);
    let mut custodian_keys = [[0u8; 32]; 64];
    for (i, slot) in custodian_keys.iter_mut().take(cfg.n).enumerate() {
        *slot = mac_keys[i];
    }
    let wal_key: SecretWalKey = SecretBuffer(h32(
        b"QSAG.QUORUM.BELT_WAL_KEY/v1",
        &[&mac_keys[party], &guard_key_commit],
    ));
    let initial_next = match in_flight {
        Some(prev) => prev.epoch,
        None => next_epoch,
    };
    let guard_res = qsag_verified::VerifiedBeltQuorumGuard::new_validated(
        cfg.n as u32,
        cfg.t as u32,
        cfg.f as u32,
        cfg.q as u32,
        true,
        initial_next,
        max_window,
        guard_key_commit,
        custodian_keys,
        *wal_key,
    );
    for slot in &mut custodian_keys {
        qsag_asm::volatile_fill(slot, 0);
    }
    let mut guard =
        guard_res.map_err(|_| QuorumError::InvalidConfig("invalid verified belt quorum"))?;
    if let Some(prev) = in_flight {
        let prev_binding = LeafRecord::from_latch(prev.epoch, prev).binding();
        let prev_receipt = belt_wal_receipt_digest(prev.epoch, &prev_binding);
        let prev_tag = qsag_verified::wal_receipt_tag(
            &wal_key,
            &guard_key_commit,
            prev.epoch,
            &prev_binding,
            &prev_receipt,
        );
        let (next_guard, res) =
            guard.propose_or_retry_epoch(prev.epoch, prev_binding, prev_receipt, prev_tag);
        guard = next_guard;
        if res.is_err() {
            return Err(QuorumError::Latch(BeltLatchError::WalPoisoned));
        }
    }
    Ok((guard, wal_key))
}

/// One custodian of Mode QS-B: its Shamir shares, its latch, its persistent extracted
/// `VerifiedBeltQuorumGuard`, and its pairwise MAC keys.
pub struct ShamirCustodian<W: DurableWal> {
    party: usize,
    cfg: QuorumConfig,
    tree: Arc<QuorumTree>,
    mac_keys: SecretMacKeys,
    latch: BeltLatch<W>,
    leaves: SecretLeaves,
    max_window: u64,
    verified_guard: Option<qsag_verified::VerifiedBeltQuorumGuard>,
    wal_receipt_key: SecretWalKey,
    last_authorized_grant: Option<qsag_verified::BeltAuthorizationGrant>,
    guard_poisoned: bool,
}

impl<W: DurableWal> ShamirCustodian<W> {
    pub fn new(
        cfg: QuorumConfig,
        tree: Arc<QuorumTree>,
        mut material: ShamirPartyMaterial,
        wal: W,
    ) -> Result<Self, QuorumError> {
        if material.mac_keys.len() != cfg.n || material.party >= cfg.n {
            return Err(QuorumError::InvalidConfig("one MAC key per custodian"));
        }
        let latch = BeltLatch::recover(wal, latch_capacity_log2(material.leaves.len() as u64))?;
        let mac_keys = SecretBuffer(core::mem::take(&mut material.mac_keys));
        let (verified_guard, wal_receipt_key) = build_verified_belt_guard(
            cfg,
            tree.public_key(),
            material.party,
            &mac_keys,
            MAX_WINDOW,
            latch.next_epoch(),
            latch.in_flight(),
        )?;
        Ok(Self {
            party: material.party,
            cfg,
            tree,
            mac_keys,
            latch,
            leaves: SecretBuffer(core::mem::take(&mut material.leaves)),
            max_window: MAX_WINDOW,
            verified_guard: Some(verified_guard),
            wal_receipt_key,
            last_authorized_grant: None,
            guard_poisoned: false,
        })
    }

    pub fn party(&self) -> usize {
        self.party
    }

    pub fn config(&self) -> &QuorumConfig {
        &self.cfg
    }

    pub fn tree(&self) -> &Arc<QuorumTree> {
        &self.tree
    }

    pub fn next_epoch(&self) -> u64 {
        self.latch.next_epoch()
    }

    /// Storage of this custodian in bytes of share material.
    pub fn share_bytes(&self) -> usize {
        self.leaves.len() * LEAF_SHARE_NODES * 32
    }

    pub fn into_wal(self) -> W {
        self.latch.into_wal()
    }

    pub(crate) fn leaves_mut(&mut self) -> &mut [Vec<Node>] {
        &mut self.leaves.0
    }

    fn is_guard_poisoned(&self) -> bool {
        self.guard_poisoned || self.verified_guard.as_ref().is_none_or(|g| g.is_poisoned())
    }

    pub(crate) fn replace_mac_keys(&mut self, new_keys: Vec<Node>) -> Result<(), QuorumError> {
        if new_keys.len() != self.cfg.n {
            return Err(QuorumError::InvalidConfig(
                "one MAC key per custodian required",
            ));
        }
        let was_poisoned = self.is_guard_poisoned();
        let (mut next_guard, next_wal_key) = build_verified_belt_guard(
            self.cfg,
            self.tree.public_key(),
            self.party,
            &new_keys,
            self.max_window,
            self.latch.next_epoch(),
            self.latch.in_flight(),
        )?;
        if was_poisoned {
            let (poisoned_guard, _) =
                next_guard.propose_or_retry_epoch(0, [0u8; 32], [0u8; 32], [0u8; 32]);
            next_guard = poisoned_guard;
            self.guard_poisoned = true;
            self.last_authorized_grant = None;
        }
        self.mac_keys = SecretBuffer(new_keys);
        self.verified_guard = Some(next_guard);
        self.wal_receipt_key = next_wal_key;
        Ok(())
    }

    fn derive(&self, leaf: u64, msg: &[u8]) -> Result<LeafRecord, QuorumError> {
        if leaf >= self.leaves.len() as u64 {
            return Err(QuorumError::Exhausted);
        }
        LeafRecord::derive(self.tree.public_key(), leaf, msg).ok_or(QuorumError::GrindFailed)
    }

    fn bind(&mut self, record: &LeafRecord) -> Result<(), QuorumError> {
        let replay = self
            .latch
            .in_flight()
            .is_some_and(|r| r.epoch == record.leaf);
        window_check(
            record.leaf,
            self.latch.next_epoch(),
            replay,
            self.max_window,
        )?;
        self.latch.bind(
            record.leaf,
            &record.msg_hash,
            &record.salt(),
            &record.digits,
        )?;
        Ok(())
    }

    fn step_persistent_guard_epoch(
        &mut self,
        leaf: u64,
        binding: Node,
        bind_ok: bool,
    ) -> Result<(), QuorumError> {
        let Some(guard) = self.verified_guard.take() else {
            self.guard_poisoned = true;
            self.last_authorized_grant = None;
            return Err(QuorumError::Latch(BeltLatchError::WalPoisoned));
        };
        let guard_commit = guard.guard_key_commit();
        let receipt_digest = belt_wal_receipt_digest(leaf, &binding);
        let receipt_tag = if bind_ok {
            qsag_verified::wal_receipt_tag(
                &self.wal_receipt_key.0,
                &guard_commit,
                leaf,
                &binding,
                &receipt_digest,
            )
        } else {
            [0u8; 32]
        };
        if let Some(prev_grant) = &self.last_authorized_grant
            && (prev_grant.authorized_epoch != leaf
                || !qsag_verified::ct_eq_bytes32(&prev_grant.msg_tag, &binding))
        {
            self.last_authorized_grant = None;
        }
        let (next_guard, prop_res) =
            guard.propose_or_retry_epoch(leaf, binding, receipt_digest, receipt_tag);
        let poisoned = next_guard.is_poisoned();
        self.verified_guard = Some(next_guard);
        if poisoned {
            self.guard_poisoned = true;
            self.last_authorized_grant = None;
        }
        match prop_res {
            Ok(()) => Ok(()),
            Err(qsag_verified::BeltAuthError::InvalidWalReceipt) => {
                Err(QuorumError::Latch(BeltLatchError::WalPoisoned))
            }
            Err(_) => Err(QuorumError::Latch(BeltLatchError::EpochAlreadyBound)),
        }
    }

    /// Bind the record of `msg` at `leaf` durably and acknowledge it to every custodian
    /// using `qsag_verified::custodian_ack_tag` directly on the wire.
    pub fn ack(&mut self, leaf: u64, msg: &[u8]) -> Result<(LeafRecord, LatchAck), QuorumError> {
        if self.is_guard_poisoned() {
            return Err(QuorumError::Latch(BeltLatchError::WalPoisoned));
        }
        let record = self.derive(leaf, msg)?;
        let binding = record.binding();
        if let Err(err) = self.bind(&record) {
            if matches!(err, QuorumError::Latch(BeltLatchError::WalPoisoned)) {
                let _ = self.step_persistent_guard_epoch(record.leaf, binding, false);
                self.guard_poisoned = true;
            }
            return Err(err);
        }
        self.step_persistent_guard_epoch(record.leaf, binding, true)?;
        let pk = self.tree.public_key();
        let macs = (0..self.cfg.n)
            .map(|to| {
                let recipient_guard_commit = belt_guard_key_commit(pk, to);
                qsag_verified::custodian_ack_tag(
                    &self.mac_keys[to],
                    &recipient_guard_commit,
                    leaf,
                    &binding,
                    self.party as u8,
                )
            })
            .collect();
        let ack = LatchAck {
            from: self.party,
            leaf,
            binding,
            macs,
        };
        Ok((record, ack))
    }

    /// Count the acknowledgements of `cert` this custodian can verify (distinct custodians,
    /// the certificate's leaf and binding, a valid MAC for this custodian) and require a
    /// quorum of them.
    pub fn verify_certificate(&self, cert: &LatchCertificate) -> Result<usize, QuorumError> {
        let valid_acks = self.verified_certificate_acks(cert);
        let valid = valid_acks.len();
        // The second condition restates the configuration invariant at the point of use.
        if valid < self.cfg.q || 2 * valid <= self.cfg.n + self.cfg.f {
            return Err(QuorumError::CertificateTooSmall {
                valid,
                required: self.cfg.q,
            });
        }
        Ok(valid)
    }

    fn verified_certificate_acks(&self, cert: &LatchCertificate) -> Vec<(u8, [u8; 32])> {
        let my_guard_commit = belt_guard_key_commit(self.tree.public_key(), self.party);
        let mut seen = vec![false; self.cfg.n];
        let mut acks = Vec::new();
        for ack in &cert.acks {
            if ack.from >= self.cfg.n
                || seen[ack.from]
                || ack.leaf != cert.leaf
                || ack.binding != cert.binding
                || ack.macs.len() != self.cfg.n
            {
                continue;
            }
            let expected = qsag_verified::custodian_ack_tag(
                &self.mac_keys[ack.from],
                &my_guard_commit,
                ack.leaf,
                &ack.binding,
                ack.from as u8,
            );
            if qsag_verified::ct_eq_bytes32(&expected, &ack.macs[self.party]) {
                seen[ack.from] = true;
                acks.push((ack.from as u8, ack.macs[self.party]));
            }
        }
        acks
    }

    /// Gate QS-B share release through the persistent `qsag_verified::VerifiedBeltQuorumGuard`
    /// (`n <= 64`), feeding untrusted wire `LatchAck` tags directly into `record_custodian_ack`
    /// without caller-side tag re-synthesis and latching sticky poison on equivocation or WAL fault.
    fn authorize_via_verified_belt_guard(
        &mut self,
        record: &LeafRecord,
        wire_acks: &[(u8, [u8; 32])],
    ) -> Result<(), QuorumError> {
        let binding = record.binding();
        self.step_persistent_guard_epoch(record.leaf, binding, true)?;

        let Some(mut guard) = self.verified_guard.take() else {
            self.guard_poisoned = true;
            self.last_authorized_grant = None;
            return Err(QuorumError::Latch(BeltLatchError::WalPoisoned));
        };

        for &(custodian_id, wire_tag) in wire_acks {
            let (next_guard, ack_res) =
                guard.record_custodian_ack(record.leaf, binding, custodian_id, wire_tag);
            guard = next_guard;
            if ack_res.is_err() {
                let poisoned = guard.is_poisoned();
                self.verified_guard = Some(guard);
                if poisoned {
                    self.guard_poisoned = true;
                    self.last_authorized_grant = None;
                }
                return Err(QuorumError::CertificateBindingMismatch);
            }
        }

        if matches!(
            guard.phase(),
            qsag_verified::pants_and_quorum_guards::BeltQuorumPhase::SharesAuthorized
        ) {
            self.verified_guard = Some(guard);
            let Some(grant) = self.last_authorized_grant.as_ref() else {
                self.guard_poisoned = true;
                return Err(QuorumError::CertificateBindingMismatch);
            };
            if grant.authorized_epoch != record.leaf
                || !qsag_verified::ct_eq_bytes32(&grant.msg_tag, &binding)
                || (grant.certified_acks as usize) < self.cfg.q
            {
                return Err(QuorumError::CertificateBindingMismatch);
            }
            return Ok(());
        }

        let (next_guard, auth_res) = guard.authorize_shares(record.leaf, binding);
        let poisoned = next_guard.is_poisoned();
        self.verified_guard = Some(next_guard);
        if poisoned {
            self.guard_poisoned = true;
            self.last_authorized_grant = None;
        }
        let grant = auth_res.map_err(|_| QuorumError::CertificateTooSmall {
            valid: wire_acks.len(),
            required: self.cfg.q,
        })?;
        if grant.authorized_epoch != record.leaf
            || !qsag_verified::ct_eq_bytes32(&grant.msg_tag, &binding)
            || (grant.certified_acks as usize) < self.cfg.q
        {
            return Err(QuorumError::CertificateBindingMismatch);
        }
        self.last_authorized_grant = Some(grant);
        Ok(())
    }

    /// Open this custodian's Shamir shares of the nodes that the record of `msg` at `leaf`
    /// reveals. Requires a valid certificate for exactly that record, and binds the record
    /// in the local latch and persistent `VerifiedBeltQuorumGuard` first, so a custodian
    /// that already bound the leaf to another record refuses and permanently poisons.
    pub fn open(
        &mut self,
        leaf: u64,
        msg: &[u8],
        cert: &LatchCertificate,
    ) -> Result<ShareOpening, QuorumError> {
        if self.is_guard_poisoned() {
            return Err(QuorumError::Latch(BeltLatchError::WalPoisoned));
        }
        let record = self.derive(leaf, msg)?;
        let binding = record.binding();
        if cert.leaf != leaf || cert.binding != binding {
            return Err(QuorumError::CertificateBindingMismatch);
        }
        self.verify_certificate(cert)?;
        let wire_acks = self.verified_certificate_acks(cert);
        let bind_res = self.bind(&record);
        if let Err(err) = bind_res {
            let is_wal_io_or_equivocation = matches!(
                err,
                QuorumError::Latch(BeltLatchError::WalPoisoned | BeltLatchError::EpochAlreadyBound)
            );
            if is_wal_io_or_equivocation {
                let _ = self.step_persistent_guard_epoch(
                    record.leaf,
                    binding,
                    !matches!(err, QuorumError::Latch(BeltLatchError::WalPoisoned)),
                );
                self.guard_poisoned = true;
                self.last_authorized_grant = None;
            }
            return Err(err);
        }
        self.authorize_via_verified_belt_guard(&record, &wire_acks)?;
        Ok(select_shares(
            self.party,
            &record,
            &self.leaves[leaf as usize],
        ))
    }
}

fn interpolate_nodes(openings: &[&ShareOpening]) -> Option<Vec<Node>> {
    let points: Vec<TowerGf256> = openings.iter().map(|o| shamir_point(o.party)).collect();
    let weights = lagrange_weights_zero_gf256(&points)?;
    let mut nodes = vec![[0u8; 32]; WOTS_CHAINS];
    for (opening, weight) in openings.iter().zip(&weights) {
        for (acc, &s) in nodes
            .as_flattened_mut()
            .iter_mut()
            .zip(opening.shares.as_flattened())
        {
            *acc ^= gf256_mul_ct(weight.0, s);
        }
    }
    Some(nodes)
}

fn shamir_candidates<'a>(
    cfg: &QuorumConfig,
    record: &LeafRecord,
    openings: &'a [ShareOpening],
) -> Result<Vec<&'a ShareOpening>, QuorumError> {
    let mut distinct: Vec<&ShareOpening> = Vec::new();
    for opening in openings {
        check_opening(opening, record)?;
        if opening.party >= cfg.n || distinct.iter().any(|o| o.party == opening.party) {
            return Err(QuorumError::BadOpeningSet);
        }
        distinct.push(opening);
    }
    if distinct.len() < cfg.t {
        return Err(QuorumError::NotEnoughShares {
            have: distinct.len(),
            need: cfg.t,
        });
    }
    distinct.sort_by_key(|o| o.party);
    Ok(distinct)
}

fn shamir_signature(
    tree: &QuorumTree,
    record: &LeafRecord,
    subset: &[&ShareOpening],
) -> Result<QuorumJortsSig, QuorumError> {
    let ends = tree
        .chain_ends(record.leaf)
        .ok_or(QuorumError::InvalidConfig("leaf is not assigned"))?;
    let mut nodes = interpolate_nodes(subset).ok_or(QuorumError::BadOpeningSet)?;
    for (chain, &digit) in record.digits.iter().enumerate() {
        if usize::from(digit) == WOTS_STEPS {
            nodes[chain] = ends[chain];
        }
    }
    tree.finish_signature(record, nodes)
}

/// Reconstruct from the `t` lowest-numbered openings. A wrong share makes a chain miss its
/// public end and is reported as [`QuorumError::ChainVerifyFailed`].
pub fn combine_shamir(
    cfg: &QuorumConfig,
    tree: &QuorumTree,
    record: &LeafRecord,
    openings: &[ShareOpening],
) -> Result<QuorumJortsSig, QuorumError> {
    let distinct = shamir_candidates(cfg, record, openings)?;
    shamir_signature(tree, record, &distinct[..cfg.t])
}

/// Like [`combine_shamir`], but with more than `t` openings it searches for a `t`-subset
/// whose reconstruction verifies and returns, next to the signature, the custodians whose
/// openings contradict it. The search visits `binom(openings, t)` subsets at worst.
pub fn combine_shamir_robust(
    cfg: &QuorumConfig,
    tree: &QuorumTree,
    record: &LeafRecord,
    openings: &[ShareOpening],
) -> Result<(QuorumJortsSig, Vec<usize>), QuorumError> {
    let distinct = shamir_candidates(cfg, record, openings)?;
    let mut last_error = QuorumError::BadOpeningSet;
    let mut count = 1usize;
    for k in 1..=cfg.t.min(distinct.len() - cfg.t) {
        count = count
            .checked_mul(distinct.len() - k + 1)
            .and_then(|n| n.checked_div(k))
            .filter(|&n| n <= MAX_COMMITTEES)
            .ok_or(QuorumError::InvalidConfig(
                "robust reconstruction subset budget exceeded",
            ))?;
    }
    for subset in combinations(distinct.len(), cfg.t) {
        let chosen: Vec<&ShareOpening> = subset.iter().map(|&i| distinct[i]).collect();
        match shamir_signature(tree, record, &chosen) {
            Ok(sig) => {
                let mut blamed = Vec::new();
                for (i, other) in distinct.iter().enumerate() {
                    if subset.contains(&i) {
                        continue;
                    }
                    // Swap the outsider in for one member; a consistent share reconstructs
                    // the same verified nodes.
                    let mut probe = chosen.clone();
                    probe[0] = other;
                    if shamir_signature(tree, record, &probe).is_err() {
                        blamed.push(other.party);
                    }
                }
                return Ok((sig, blamed));
            }
            Err(e) => last_error = e,
        }
    }
    Err(last_error)
}

/// All custodians of Mode QS-B driven in one process (tests and measurements; see the module
/// documentation).
/// QS-B uses quorum-independent leaf allocation from one global tree. A leaf
/// index does not encode the signing committee as it does in QS-A.
pub struct BftShamirJorts<W: DurableWal> {
    pub cfg: QuorumConfig,
    pub tree: Arc<QuorumTree>,
    pub custodians: Vec<ShamirCustodian<W>>,
    ots_release_cache: BTreeMap<u64, (Node, u32)>,
}

#[cfg(any(test, feature = "testing-ephemeral"))]
impl BftShamirJorts<MemoryWal> {
    /// Stage a key with volatile logs (restricted to tests and `testing-ephemeral`).
    pub fn stage(cfg: QuorumConfig, height: u8, seed: &Node) -> Result<Self, QuorumError> {
        Self::stage_durable(cfg, height, seed, |_party| MemoryWal::new())
    }

    /// Build from pre-staged (e.g. dealerless MPC) Shamir keys with volatile logs.
    pub fn from_staged(staged: StagedShamirKeys) -> Result<Self, QuorumError> {
        Self::from_staged_durable(staged, |_party| MemoryWal::new())
    }
}

impl<W: DurableWal> BftShamirJorts<W> {
    /// Build from pre-staged (e.g. dealerless MPC) Shamir keys with caller-provisioned logs.
    pub fn from_staged_durable(
        staged: StagedShamirKeys,
        mut make_wal: impl FnMut(usize) -> W,
    ) -> Result<Self, QuorumError> {
        if staged.parties.len() != staged.cfg.n {
            return Err(QuorumError::InvalidConfig("party count mismatch"));
        }
        let cfg = staged.cfg;
        let custodians = staged
            .parties
            .into_iter()
            .map(|material| {
                let wal = make_wal(material.party);
                ShamirCustodian::new(cfg, staged.tree.clone(), material, wal)
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self {
            cfg,
            tree: staged.tree,
            custodians,
            ots_release_cache: BTreeMap::new(),
        })
    }

    /// Stage a key with caller-provisioned durable logs (one per custodian).
    pub fn stage_durable(
        cfg: QuorumConfig,
        height: u8,
        seed: &Node,
        make_wal: impl FnMut(usize) -> W,
    ) -> Result<Self, QuorumError> {
        let staged = stage_bft_shamir(cfg, height, seed)?;
        Self::from_staged_durable(staged, make_wal)
    }
    pub fn public_key(&self) -> &QuorumPublicKey {
        self.tree.public_key()
    }

    /// Collect acknowledgements of `msg` at `leaf` from `ackers`; custodians that refuse are
    /// skipped. Returns `None` if nobody acknowledged.
    pub fn certify(
        &mut self,
        ackers: &[usize],
        leaf: u64,
        msg: &[u8],
    ) -> Option<(LeafRecord, LatchCertificate)> {
        let mut record = None;
        let mut acks = Vec::new();
        for &p in ackers {
            if let Ok((rec, ack)) = self.custodians[p].ack(leaf, msg) {
                record = Some(rec);
                acks.push(ack);
            }
        }
        let record = record?;
        let cert = LatchCertificate::assemble(&record, acks);
        Some((record, cert))
    }

    /// Sign `msg` at the next leaf free at every custodian in `online`: all of them
    /// acknowledge, and the `t` lowest-numbered open.
    pub fn sign(&mut self, online: &[usize], msg: &[u8]) -> Result<QuorumJortsSig, QuorumError> {
        let leaf = online
            .iter()
            .map(|&p| self.custodians[p].next_epoch())
            .max()
            .ok_or(QuorumError::BadOpeningSet)?;
        let mut openers = online.to_vec();
        openers.sort_unstable();
        openers.truncate(self.cfg.t);
        self.sign_at(online, &openers, leaf, msg)
    }

    /// Sign `msg` at `leaf` with acknowledgements from `ackers` and openings from `openers`.
    pub fn sign_at(
        &mut self,
        ackers: &[usize],
        openers: &[usize],
        leaf: u64,
        msg: &[u8],
    ) -> Result<QuorumJortsSig, QuorumError> {
        let (record, cert) =
            self.certify(ackers, leaf, msg)
                .ok_or(QuorumError::CertificateTooSmall {
                    valid: 0,
                    required: self.cfg.q,
                })?;
        let openings = openers
            .iter()
            .map(|&p| self.custodians[p].open(leaf, msg, &cert))
            .collect::<Result<Vec<_>, _>>()?;
        let sig = combine_shamir(&self.cfg, &self.tree, &record, &openings)?;
        if let Some((prev_hash, prev_ctr)) = self.ots_release_cache.get(&sig.leaf)
            && (!qsag_verified::ct_eq_bytes32(prev_hash, &record.msg_hash)
                || *prev_ctr != sig.counter)
        {
            return Err(QuorumError::SignatureVerifyFailed);
        }
        if !quorum_jorts_verify(self.public_key(), msg, &sig) {
            return Err(QuorumError::SignatureVerifyFailed);
        }
        self.ots_release_cache
            .insert(sig.leaf, (record.msg_hash, sig.counter));
        Ok(sig)
    }
}

fn wipe_nodes(nodes: &mut [Node]) {
    for node in nodes {
        qsag_core::wipe::wipe_bytes32(node);
    }
}
impl Drop for CommitteeShareStore {
    fn drop(&mut self) {
        for leaf in &mut self.leaves {
            wipe_nodes(leaf);
        }
    }
}
impl Drop for CommitteePartyMaterial {
    fn drop(&mut self) {
        wipe_nodes(&mut self.mac_keys);
    }
}
#[cfg(test)]
impl ShamirPartyMaterial {
    /// A second copy of one custodian's shares, as a corrupted custodian would hold.
    pub(crate) fn duplicate_for_test(&self) -> Self {
        Self {
            party: self.party,
            mac_keys: self.mac_keys.clone(),
            leaves: self.leaves.clone(),
        }
    }
}
impl Drop for ShamirPartyMaterial {
    fn drop(&mut self) {
        wipe_nodes(&mut self.mac_keys);
        for leaf in &mut self.leaves {
            wipe_nodes(leaf);
        }
    }
}
macro_rules! redacted_debug {
    ($($ty:ty),*) => { $(
        impl core::fmt::Debug for $ty {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                f.write_str(concat!(stringify!($ty), "([REDACTED])"))
            }
        }
    )* };
}
redacted_debug!(
    ShareOpening,
    CommitteeShareStore,
    CommitteePartyMaterial,
    ShamirPartyMaterial
);

impl Drop for ShareOpening {
    fn drop(&mut self) {
        wipe_nodes(&mut self.shares);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const SEED: Node = [0x5a; 32];

    #[test]
    fn digits_use_the_full_digest_and_grinding_is_short() {
        let pk = QuorumPublicKey {
            pk_seed: [1; 32],
            root: [2; 32],
            height: 4,
        };
        let mut total = 0u64;
        for i in 0..64u8 {
            let record = LeafRecord::derive(&pk, 3, &[i]).unwrap();
            assert_eq!(record.digits.len(), WOTS_CHAINS);
            assert!(record.digits.iter().all(|&d| d < 4));
            assert_eq!(
                record.digits.iter().map(|&d| u32::from(d)).sum::<u32>(),
                WOTS_TARGET_SUM
            );
            assert_eq!(
                digits_at(&record.msg_hash, record.counter),
                Some(record.digits.clone())
            );
            for earlier in 0..record.counter {
                assert_eq!(digits_at(&record.msg_hash, earlier), None);
            }
            total += u64::from(record.counter) + 1;
        }
        // One counter in about 32 has digit sum 192; 64 samples average well below 64 tries.
        assert!(total / 64 < 64, "mean grinding length {}", total / 64);
        // The digits are the 2-bit groups of the digest, most significant first.
        let record = LeafRecord::derive(&pk, 5, b"layout").unwrap();
        let digest = h32(
            TAG_DIGEST,
            &[&record.msg_hash, &record.counter.to_be_bytes()],
        );
        let raw: Vec<u8> = digest
            .iter()
            .flat_map(|b| [(b >> 6) & 3, (b >> 4) & 3, (b >> 2) & 3, b & 3])
            .collect();
        assert_eq!(record.digits, raw);
    }

    #[test]
    fn combinations_are_lexicographic_and_complete() {
        assert_eq!(combinations(3, 2), vec![vec![0, 1], vec![0, 2], vec![1, 2]]);
        assert_eq!(combinations(5, 3).len(), 10);
        assert_eq!(combinations(7, 4).len(), 35);
        assert_eq!(combinations(4, 4), vec![vec![0, 1, 2, 3]]);
        assert!(combinations(2, 3).is_empty());
    }

    #[test]
    fn committee_layout_partitions_the_leaves() {
        for (t, n, height, committees) in [(2, 3, 4u8, 3usize), (3, 5, 6, 10), (4, 7, 7, 35)] {
            let layout = CommitteeLayout::new(t, n, height).unwrap();
            assert_eq!(layout.committees().len(), committees);
            let per = layout.leaves_per_committee();
            assert_eq!(per, (1u64 << height) / committees as u64);
            let mut owner = BTreeMap::new();
            for c in 0..committees {
                for e in 0..per {
                    assert!(owner.insert(layout.leaf_of(c, e), c).is_none());
                    assert_eq!(layout.committee_of_leaf(layout.leaf_of(c, e)), Some(c));
                }
            }
            assert!(owner.keys().all(|&leaf| leaf < 1u64 << height));
        }
        assert!(CommitteeLayout::new(3, 5, 3).is_err());
        assert!(CommitteeLayout::new(1, 5, 6).is_err());
        assert!(CommitteeLayout::new(6, 5, 6).is_err());
    }

    #[test]
    fn two_of_three_committees_sign_and_verify_under_one_root() {
        let mut jorts = CommitteePartitionedJorts::stage(2, 3, 4, &SEED).unwrap();
        let pk = *jorts.public_key();
        let mut leaves = Vec::new();
        for online in [[0usize, 1], [0, 2], [1, 2], [1, 0]] {
            let msg = [online[0] as u8, online[1] as u8, leaves.len() as u8];
            let sig = jorts.sign(&online, &msg).unwrap();
            assert!(quorum_jorts_verify(&pk, &msg, &sig));
            assert!(!quorum_jorts_verify(&pk, b"other", &sig));
            assert_eq!(sig.nodes.len(), 128);
            assert_eq!(sig.wire_bytes(), 12 + 4096 + 32 * 4);
            leaves.push(sig.leaf);
        }
        // Committee {0,1} advanced to its second leaf; the others used their first.
        assert_eq!(leaves, vec![0, 5, 10, 1]);
    }

    #[test]
    fn signature_tampering_is_rejected() {
        let mut jorts = CommitteePartitionedJorts::stage(2, 3, 3, &SEED).unwrap();
        let pk = *jorts.public_key();
        let sig = jorts.sign(&[0, 2], b"msg").unwrap();
        assert!(quorum_jorts_verify(&pk, b"msg", &sig));
        let mut bad = sig.clone();
        bad.nodes[17][0] ^= 1;
        assert!(!quorum_jorts_verify(&pk, b"msg", &bad));
        let mut bad = sig.clone();
        bad.auth_path[1][31] ^= 0x80;
        assert!(!quorum_jorts_verify(&pk, b"msg", &bad));
        let mut bad = sig.clone();
        bad.counter += 1;
        assert!(!quorum_jorts_verify(&pk, b"msg", &bad));
        let mut bad = sig.clone();
        bad.leaf ^= 1;
        assert!(!quorum_jorts_verify(&pk, b"msg", &bad));
        let mut bad = sig.clone();
        bad.nodes.pop();
        assert!(!quorum_jorts_verify(&pk, b"msg", &bad));
        let mut other = pk;
        other.root[0] ^= 1;
        assert!(!quorum_jorts_verify(&other, b"msg", &sig));
        // An unassigned position has no chains: the last leaves of the tree are filler.
        assert_eq!(jorts.tree.assigned_leaves(), 6);
        assert_eq!(jorts.tree.chain_ends(7), None);
    }

    #[test]
    fn additive_shares_are_held_by_committee_members_only() {
        let staged = stage_committee_partitioned(3, 5, 6, &SEED).unwrap();
        for material in &staged.parties {
            // binom(4, 2) committees contain a given custodian.
            assert_eq!(material.stores.len(), 6);
            for store in &material.stores {
                assert!(staged.layout.committees()[store.committee].contains(&material.party));
                assert_eq!(store.leaves.len(), 6);
                assert!(store.leaves.iter().all(|l| l.len() == LEAF_SHARE_NODES));
            }
        }
        // The shares of a committee xor to chain states that reach the public ends, and
        // any two of the three do not.
        let committee = staged
            .layout
            .committee_index(&[1, 2, 4])
            .expect("a committee");
        let leaf = staged.layout.leaf_of(committee, 2);
        let pk_seed = staged.tree.public_key().pk_seed;
        let ends = staged.tree.chain_ends(leaf).unwrap();
        let shares: Vec<&Vec<Node>> = [1usize, 2, 4]
            .iter()
            .map(|&p| {
                let store = staged.parties[p]
                    .stores
                    .iter()
                    .find(|s| s.committee == committee)
                    .unwrap();
                &store.leaves[2]
            })
            .collect();
        for chain in [0usize, 63, 127] {
            for step in 0..WOTS_STEPS {
                let idx = chain * WOTS_STEPS + step;
                let mut full = [0u8; 32];
                let mut partial = [0u8; 32];
                for (k, share) in shares.iter().enumerate() {
                    for (acc, byte) in full.iter_mut().zip(share[idx]) {
                        *acc ^= byte;
                    }
                    if k < 2 {
                        for (acc, byte) in partial.iter_mut().zip(share[idx]) {
                            *acc ^= byte;
                        }
                    }
                }
                assert_eq!(
                    chain_walk(&pk_seed, leaf, chain, step, WOTS_STEPS, &full),
                    ends[chain]
                );
                assert_ne!(
                    chain_walk(&pk_seed, leaf, chain, step, WOTS_STEPS, &partial),
                    ends[chain]
                );
            }
        }
    }

    #[test]
    fn committee_latch_replays_refuses_rebinding_and_enforces_the_window() {
        let mut jorts = CommitteePartitionedJorts::stage(2, 3, 8, &SEED).unwrap();
        let c = jorts.layout.committee_index(&[0, 1]).unwrap();
        let first = jorts.custodians[0].bind(c, 0, b"m1").unwrap();
        assert_eq!(jorts.custodians[0].bind(c, 0, b"m1").unwrap(), first);
        assert_eq!(
            jorts.custodians[0].bind(c, 0, b"m2"),
            Err(QuorumError::Latch(BeltLatchError::EpochAlreadyBound))
        );
        // Skipping forward inside the window is allowed and burns the skipped epochs.
        jorts.custodians[0].bind(c, 1 + MAX_WINDOW, b"m3").unwrap();
        assert_eq!(
            jorts.custodians[0].bind(c, 0, b"m1"),
            Err(QuorumError::Latch(BeltLatchError::EpochConsumed))
        );
        let next = jorts.custodians[0].next_epoch(c).unwrap();
        assert_eq!(
            jorts.custodians[0].bind(c, next + MAX_WINDOW + 1, b"m4"),
            Err(QuorumError::EpochOutOfWindow {
                epoch: next + MAX_WINDOW + 1,
                next_epoch: next
            })
        );
        assert_eq!(
            jorts.custodians[0].bind(c, jorts.layout.leaves_per_committee(), b"m5"),
            Err(QuorumError::Exhausted)
        );
        // Custodian 2 is not in committee {0, 1}.
        assert_eq!(
            jorts.custodians[2].bind(c, 0, b"m1"),
            Err(QuorumError::NotCommitteeMember {
                party: 2,
                committee: c
            })
        );
    }

    #[test]
    fn committee_latch_survives_a_restart() {
        let mut staged = stage_committee_partitioned(2, 3, 4, &SEED).unwrap();
        let material = staged.parties.remove(0);
        let wals = vec![MemoryWal::new(); material.stores.len()];
        let mut custodian =
            CommitteeCustodian::new(staged.layout.clone(), staged.tree.clone(), material, wals)
                .unwrap();
        let c = staged.layout.committee_index(&[0, 2]).unwrap();
        let record = custodian.bind(c, 1, b"before the crash").unwrap();
        let wals = custodian.into_wals();
        // Simulate loading the original sealed material from trusted provisioning.
        let material = stage_committee_partitioned(2, 3, 4, &SEED)
            .unwrap()
            .parties
            .remove(0);
        let mut restarted =
            CommitteeCustodian::new(staged.layout.clone(), staged.tree.clone(), material, wals)
                .unwrap();
        assert_eq!(restarted.in_flight(c).unwrap(), Some(record.clone()));
        assert_eq!(restarted.bind(c, 1, b"before the crash").unwrap(), record);
        assert_eq!(
            restarted.bind(c, 1, b"after the crash"),
            Err(QuorumError::Latch(BeltLatchError::EpochAlreadyBound))
        );
        assert_eq!(
            restarted.bind(c, 0, b"older epoch"),
            Err(QuorumError::Latch(BeltLatchError::EpochConsumed))
        );
    }

    #[test]
    fn echo_checks_catch_missing_forged_and_conflicting_echoes() {
        let mut jorts = CommitteePartitionedJorts::stage(3, 5, 6, &SEED).unwrap();
        let c = jorts.layout.committee_index(&[0, 1, 2]).unwrap();
        for p in [0usize, 1] {
            jorts.custodians[p].bind(c, 0, b"agreed").unwrap();
        }
        jorts.custodians[2].bind(c, 0, b"something else").unwrap();
        let e10 = jorts.custodians[1].echo_for(c, 0).unwrap();
        let e20 = jorts.custodians[2].echo_for(c, 0).unwrap();
        assert_eq!(
            jorts.custodians[0].verify_echoes(c, &[e10]),
            Err(QuorumError::MissingEcho { party: 2 })
        );
        assert_eq!(
            jorts.custodians[0].verify_echoes(c, &[e10, e10, e20]),
            Err(QuorumError::MissingEcho { party: 1 })
        );
        assert_eq!(
            jorts.custodians[0].verify_echoes(c, &[e10, e20]),
            Err(QuorumError::SplitView { party: 2 })
        );
        // Custodian 2 cannot repair its echo: changing the binding breaks the MAC, and an
        // echo it made for custodian 1 does not verify at custodian 0.
        let mut forged = e20;
        forged.binding = e10.binding;
        assert_eq!(
            jorts.custodians[0].verify_echoes(c, &[e10, forged]),
            Err(QuorumError::EchoMacInvalid { party: 2 })
        );
        let e21 = jorts.custodians[2].echo_for(c, 1).unwrap();
        assert_eq!(
            jorts.custodians[0].verify_echoes(c, &[e10, e21]),
            Err(QuorumError::EchoMacInvalid { party: 2 })
        );
        // A reflected echo (custodian 0's own echo to 1, relabelled) does not verify either.
        let mut reflected = jorts.custodians[0].echo_for(c, 1).unwrap();
        reflected.from = 1;
        assert_eq!(
            jorts.custodians[0].verify_echoes(c, &[reflected, e20]),
            Err(QuorumError::EchoMacInvalid { party: 1 })
        );
    }

    #[test]
    fn permits_open_only_the_record_they_were_issued_for() {
        let mut jorts = CommitteePartitionedJorts::stage(2, 3, 4, &SEED).unwrap();
        let c = jorts.layout.committee_index(&[0, 1]).unwrap();
        for p in [0usize, 1] {
            jorts.custodians[p].bind(c, 0, b"first").unwrap();
        }
        let echo = jorts.custodians[1].echo_for(c, 0).unwrap();
        let permit = jorts.custodians[0].verify_echoes(c, &[echo]).unwrap();
        let opening = jorts.custodians[0].open(&permit).unwrap();
        assert_eq!(opening.shares.len(), WOTS_CHAINS);
        // The custodian moves on; the old permit no longer opens anything.
        jorts.custodians[0].bind(c, 1, b"second").unwrap();
        assert_eq!(
            jorts.custodians[0].open(&permit),
            Err(QuorumError::PermitMismatch)
        );
        // A permit of custodian 0 is useless at custodian 1.
        assert_eq!(
            jorts.custodians[1].open(&permit),
            Err(QuorumError::PermitMismatch)
        );
    }

    #[test]
    fn additive_combination_detects_a_flipped_share() {
        let mut jorts = CommitteePartitionedJorts::stage(3, 5, 6, &SEED).unwrap();
        let members = [0usize, 2, 3];
        let c = jorts.layout.committee_index(&members).unwrap();
        let mut record = None;
        for &p in &members {
            record = Some(jorts.custodians[p].bind(c, 0, b"msg").unwrap());
        }
        let record = record.unwrap();
        let mut openings = Vec::new();
        for &p in &members {
            let echoes: Vec<LatchEcho> = members
                .iter()
                .filter(|&&q| q != p)
                .map(|&q| jorts.custodians[q].echo_for(c, p).unwrap())
                .collect();
            let permit = jorts.custodians[p].verify_echoes(c, &echoes).unwrap();
            openings.push(jorts.custodians[p].open(&permit).unwrap());
        }
        let sig = combine_additive(&jorts.tree, &record, &members, &openings).unwrap();
        assert!(quorum_jorts_verify(jorts.public_key(), b"msg", &sig));
        let chain = record.digits.iter().position(|&d| d < 3).unwrap();
        let mut bad = openings.clone();
        bad[1].shares[chain][5] ^= 0x10;
        assert_eq!(
            combine_additive(&jorts.tree, &record, &members, &bad),
            Err(QuorumError::ChainVerifyFailed { chain })
        );
        assert_eq!(
            combine_additive(&jorts.tree, &record, &members, &openings[..2]),
            Err(QuorumError::BadOpeningSet)
        );
        let mut dup = openings.clone();
        dup[2] = dup[1].clone();
        assert_eq!(
            combine_additive(&jorts.tree, &record, &members, &dup),
            Err(QuorumError::BadOpeningSet)
        );
    }

    /// Regression for quorum-switching equivocation in `(3, 5)`: custodians 3 and 4 are
    /// corrupted and try to spend one leaf twice, first with custodian 0, then with
    /// custodian 1.
    #[test]
    fn three_of_five_committees_block_quorum_switching_double_signing() {
        let mut jorts = CommitteePartitionedJorts::stage(3, 5, 6, &SEED).unwrap();
        let pk = *jorts.public_key();
        let c034 = jorts.layout.committee_index(&[0, 3, 4]).unwrap();
        let c134 = jorts.layout.committee_index(&[1, 3, 4]).unwrap();
        assert_ne!(c034, c134);

        // First signature: {0, 3, 4} sign M1 on their leaf.
        let sig1 = jorts.sign(&[0, 3, 4], b"M1").unwrap();
        assert!(quorum_jorts_verify(&pk, b"M1", &sig1));
        let leaf = sig1.leaf;
        assert_eq!(jorts.layout.committee_of_leaf(leaf), Some(c034));

        // Attack 1: the corrupted pair asks custodian 1 to sign M2 on that leaf. Custodian 1
        // holds no share of it: its only stores are for its own committees.
        let epoch = leaf - jorts.layout.leaf_of(c034, 0);
        assert_eq!(
            jorts.custodians[1].bind(c034, epoch, b"M2"),
            Err(QuorumError::NotCommitteeMember {
                party: 1,
                committee: c034
            })
        );

        // Attack 2: go back to custodian 0 with M2 for the same leaf. Its latch refuses.
        assert_eq!(
            jorts.custodians[0].bind(c034, epoch, b"M2"),
            Err(QuorumError::Latch(BeltLatchError::EpochAlreadyBound))
        );

        // Attack 3: the corrupted pair opens its own shares for M2's digits and fills in
        // custodian 0's share with what it saw during the M1 signing. Wherever the digits of
        // M2 differ from M1's, custodian 0 never opened the needed share.
        let record2 = LeafRecord::derive(&pk, leaf, b"M2").unwrap();
        let record1 = LeafRecord::derive(&pk, leaf, b"M1").unwrap();
        assert_ne!(record1.digits, record2.digits);
        let staged = stage_committee_partitioned(3, 5, 6, &SEED).unwrap();
        let store_of = |p: usize| {
            staged.parties[p]
                .stores
                .iter()
                .find(|s| s.committee == c034)
                .unwrap()
                .leaves[epoch as usize]
                .clone()
        };
        let corrupt3 = select_shares(3, &record2, &store_of(3));
        let corrupt4 = select_shares(4, &record2, &store_of(4));
        // What custodian 0 revealed for M1 (the adversary's view of its shares).
        let seen0 = select_shares(0, &record1, &store_of(0));
        let replayed0 = ShareOpening {
            party: 0,
            leaf,
            shares: seen0.shares.clone(),
        };
        let forged = combine_additive(
            &jorts.tree,
            &record2,
            &[0, 3, 4],
            &[replayed0, corrupt3, corrupt4],
        );
        assert!(matches!(forged, Err(QuorumError::ChainVerifyFailed { .. })));

        // Attack 4: {1, 3, 4} is a committee too, but it signs from its own range, so the
        // result is a signature on a different leaf, not a second use of `leaf`.
        let sig2 = jorts.sign(&[1, 3, 4], b"M2").unwrap();
        assert!(quorum_jorts_verify(&pk, b"M2", &sig2));
        assert_ne!(sig2.leaf, leaf);
        assert_eq!(jorts.layout.committee_of_leaf(sig2.leaf), Some(c134));
        // No signature on M2 exists for the first leaf: re-labelling does not verify.
        let mut relabelled = sig2.clone();
        relabelled.leaf = leaf;
        assert!(!quorum_jorts_verify(&pk, b"M2", &relabelled));
    }

    /// `(3, 5)` stays live with any two custodians offline: the three that remain are a
    /// committee, and all ten signatures verify under the one root on distinct leaves.
    #[test]
    fn three_of_five_signs_with_any_two_custodians_offline() {
        let mut jorts = CommitteePartitionedJorts::stage(3, 5, 6, &SEED).unwrap();
        let pk = *jorts.public_key();
        let mut used = alloc::collections::BTreeSet::new();
        for offline in combinations(5, 2) {
            let online: Vec<usize> = (0..5).filter(|p| !offline.contains(p)).collect();
            let msg = [offline[0] as u8, offline[1] as u8];
            let sig = jorts.sign(&online, &msg).unwrap();
            assert!(quorum_jorts_verify(&pk, &msg, &sig), "offline {offline:?}");
            assert!(used.insert(sig.leaf));
        }
        assert_eq!(used.len(), 10);
        // Two custodians are not a committee, and four must name which three sign.
        assert_eq!(
            jorts.sign(&[0, 1], b"x"),
            Err(QuorumError::UnknownCommittee)
        );
        assert_eq!(
            jorts.sign(&[0, 1, 2, 3], b"x"),
            Err(QuorumError::UnknownCommittee)
        );
    }

    #[test]
    fn quorum_config_rejects_unsafe_and_dead_parameters() {
        for (t, n, f, q) in [(2, 4, 1, 3), (3, 7, 2, 5), (4, 10, 3, 7), (7, 19, 6, 13)] {
            let cfg = QuorumConfig::new(t, n, f).unwrap();
            assert_eq!(cfg.quorum(), q);
            assert!(2 * q > n + f);
        }
        for t in 1..=20usize {
            let cfg = QuorumConfig::tight(t).unwrap();
            assert_eq!(
                (cfg.parties(), cfg.max_faults()),
                (3 * t - 2, t - 1),
                "t = {t}"
            );
            // The smallest safe quorum is also the largest live one: exactly n - f.
            assert_eq!(cfg.quorum(), cfg.parties() - cfg.max_faults());
            assert!(matches!(
                QuorumConfig::with_quorum(t, 3 * t - 2, t - 1, cfg.quorum() - 1),
                Err(QuorumError::QuorumTooSmall { .. }) | Err(QuorumError::InvalidConfig(_))
            ));
        }
        assert_eq!(QuorumConfig::tight(3), QuorumConfig::new(3, 7, 2));
        assert!(QuorumConfig::tight(0).is_err());
        assert_eq!(
            QuorumConfig::with_quorum(3, 7, 2, 4),
            Err(QuorumError::QuorumTooSmall { q: 4, n: 7, f: 2 })
        );
        assert!(QuorumConfig::with_quorum(3, 7, 2, 5).is_ok());
        // A quorum the honest custodians cannot reach alone.
        assert!(matches!(
            QuorumConfig::with_quorum(3, 7, 2, 6),
            Err(QuorumError::InvalidConfig(_))
        ));
        assert!(matches!(
            QuorumConfig::new(3, 6, 2),
            Err(QuorumError::InvalidConfig(_))
        ));
        assert!(matches!(
            QuorumConfig::new(2, 7, 2),
            Err(QuorumError::InvalidConfig(_))
        ));
        assert!(matches!(
            QuorumConfig::new(6, 7, 2),
            Err(QuorumError::InvalidConfig(_))
        ));
        assert!(QuorumConfig::tight(22).is_ok()); // n = 64
        assert!(matches!(
            QuorumConfig::tight(23),
            Err(QuorumError::InvalidConfig(_))
        ));
        assert!(matches!(
            QuorumConfig::with_quorum(22, 65, 21, 44),
            Err(QuorumError::InvalidConfig(_))
        ));
    }

    fn shamir_3_of_7() -> BftShamirJorts<MemoryWal> {
        BftShamirJorts::stage(QuorumConfig::new(3, 7, 2).unwrap(), 3, &SEED).unwrap()
    }

    /// The staged material of [`shamir_3_of_7`] again (staging is deterministic).
    fn staged_3_of_7() -> StagedShamirKeys {
        stage_bft_shamir(QuorumConfig::new(3, 7, 2).unwrap(), 3, &SEED).unwrap()
    }

    /// An acknowledgement by a corrupted custodian: it has custodian `p`'s keys and no
    /// latch to hold it back, so it acknowledges any record at any leaf.
    fn rogue_ack(staged: &StagedShamirKeys, p: usize, leaf: u64, msg: &[u8]) -> LatchAck {
        let mut rogue = ShamirCustodian::new(
            staged.cfg,
            staged.tree.clone(),
            staged.parties[p].duplicate_for_test(),
            MemoryWal::new(),
        )
        .unwrap();
        rogue.ack(leaf, msg).unwrap().1
    }

    #[test]
    fn shamir_storage_is_independent_of_the_threshold() {
        for (t, n, f) in [(2usize, 4usize, 1usize), (3, 7, 2), (4, 10, 3)] {
            let jorts = BftShamirJorts::stage(QuorumConfig::new(t, n, f).unwrap(), 2, &SEED)
                .expect("staging");
            for custodian in &jorts.custodians {
                assert_eq!(custodian.share_bytes(), 4 * 12_288);
            }
        }
    }

    #[test]
    fn shamir_signs_with_any_quorum_and_any_openers() {
        let mut jorts = shamir_3_of_7();
        let pk = *jorts.public_key();
        let sig = jorts.sign(&[0, 1, 2, 3, 4], b"a").unwrap();
        assert!(quorum_jorts_verify(&pk, b"a", &sig));
        assert_eq!(sig.leaf, 0);
        // Another quorum, two custodians of the first one offline.
        let sig = jorts.sign(&[2, 3, 4, 5, 6], b"b").unwrap();
        assert!(quorum_jorts_verify(&pk, b"b", &sig));
        assert_eq!(sig.leaf, 1);
        // Custodians that were offline for a leaf catch up inside the window; the openers
        // need not be the lowest-numbered ones.
        let sig = jorts
            .sign_at(&[0, 1, 4, 5, 6], &[6, 1, 4], 2, b"c")
            .unwrap();
        assert!(quorum_jorts_verify(&pk, b"c", &sig));
        // All seven may acknowledge.
        let sig = jorts.sign(&[0, 1, 2, 3, 4, 5, 6], b"d").unwrap();
        assert!(quorum_jorts_verify(&pk, b"d", &sig));
        assert_eq!(sig.leaf, 3);
    }

    /// Regression for quorum switching in `(3, 7, f = 2)` with `q = 5`: custodians 5 and 6
    /// are corrupted and acknowledge everything.
    #[test]
    fn three_of_seven_blocks_corrupt_quorum_switching() {
        let mut jorts = shamir_3_of_7();
        let pk = *jorts.public_key();
        let sig1 = jorts
            .sign_at(&[0, 1, 2, 5, 6], &[0, 1, 2], 0, b"M1")
            .unwrap();
        assert!(quorum_jorts_verify(&pk, b"M1", &sig1));

        // The corrupted pair switches to the custodians that were not asked before. Only
        // {3, 4, 5, 6} acknowledge M2 at leaf 0; custodians 0, 1, 2 refuse.
        for p in [0usize, 1, 2] {
            assert_eq!(
                jorts.custodians[p].ack(0, b"M2").unwrap_err(),
                QuorumError::Latch(BeltLatchError::EpochAlreadyBound)
            );
        }
        let staged = staged_3_of_7();
        let (record2, honest2) = jorts.certify(&[0, 1, 2, 3, 4], 0, b"M2").unwrap();
        assert_eq!(honest2.acks.len(), 2);
        let mut acks2 = honest2.acks.clone();
        acks2.push(rogue_ack(&staged, 5, 0, b"M2"));
        acks2.push(rogue_ack(&staged, 6, 0, b"M2"));
        let cert2 = LatchCertificate::assemble(&record2, acks2);
        assert_eq!(cert2.acks.len(), 4);
        // Four acknowledgements are not a quorum: 2 * 4 <= 7 + 2. No honest custodian
        // opens, including 3 and 4, who did bind M2.
        for custodian in &mut jorts.custodians[..5] {
            assert_eq!(
                custodian.open(0, b"M2", &cert2),
                Err(QuorumError::CertificateTooSmall {
                    valid: 4,
                    required: 5
                })
            );
        }

        // Padding the certificate does not help: a duplicate acknowledgement is counted
        // once, an acknowledgement of M1 is for another binding, and a MAC made up for an
        // honest custodian does not verify.
        let (_, cert1) = jorts.certify(&[5, 6], 0, b"M1").unwrap();
        let mut padded = cert2.clone();
        padded.acks.push(cert2.acks[0].clone());
        padded.acks.push(cert1.acks[0].clone());
        let mut invented = cert2.acks[0].clone();
        invented.from = 0;
        padded.acks.push(invented);
        assert_eq!(
            jorts.custodians[3].open(0, b"M2", &padded),
            Err(QuorumError::CertificateTooSmall {
                valid: 4,
                required: 5
            })
        );
        // A certificate for M1 cannot be presented for M2.
        let (_, good1) = jorts.certify(&[0, 1, 2, 5, 6], 0, b"M1").unwrap();
        assert_eq!(good1.acks.len(), 5);
        assert_eq!(
            jorts.custodians[3].open(0, b"M2", &good1),
            Err(QuorumError::CertificateBindingMismatch)
        );
        // ... and custodian 3, having bound M2, will not open M1 even with its certificate.
        assert_eq!(
            jorts.custodians[3].open(0, b"M1", &good1),
            Err(QuorumError::Latch(BeltLatchError::EpochAlreadyBound))
        );

        // The corrupted pair alone holds two shares of a degree-2 sharing. Whatever third
        // share they invent, the chains do not verify.
        let mut openings: Vec<ShareOpening> = [5usize, 6]
            .iter()
            .map(|&p| select_shares(p, &record2, &staged.parties[p].leaves[0]))
            .collect();
        openings.push(ShareOpening {
            party: 3,
            leaf: 0,
            shares: vec![[0x42; 32]; WOTS_CHAINS],
        });
        assert!(matches!(
            combine_shamir(&jorts.cfg, &jorts.tree, &record2, &openings),
            Err(QuorumError::ChainVerifyFailed { .. })
        ));
    }

    /// The same attack against a quorum of four succeeds, which is why `q = 4` is rejected:
    /// {0, 1, 5, 6} and {2, 3, 5, 6} intersect in corrupted custodians only.
    #[test]
    fn a_quorum_of_four_of_seven_would_be_double_signed() {
        assert_eq!(
            QuorumConfig::with_quorum(3, 7, 2, 4),
            Err(QuorumError::QuorumTooSmall { q: 4, n: 7, f: 2 })
        );
        let mut jorts = shamir_3_of_7();
        let pk = *jorts.public_key();
        let staged = staged_3_of_7();
        let (rec1, cert1) = jorts.certify(&[0, 1, 5, 6], 0, b"M1").unwrap();
        let (rec2, honest2) = jorts.certify(&[2, 3], 0, b"M2").unwrap();
        let mut acks2 = honest2.acks;
        acks2.push(rogue_ack(&staged, 5, 0, b"M2"));
        acks2.push(rogue_ack(&staged, 6, 0, b"M2"));
        let cert2 = LatchCertificate::assemble(&rec2, acks2);
        assert_eq!((cert1.acks.len(), cert2.acks.len()), (4, 4));
        // The real custodians reject both four-acknowledgement certificates.
        assert!(matches!(
            jorts.custodians[0].open(0, b"M1", &cert1),
            Err(QuorumError::CertificateTooSmall { .. })
        ));
        assert!(matches!(
            jorts.custodians[2].open(0, b"M2", &cert2),
            Err(QuorumError::CertificateTooSmall { .. })
        ));
        // Custodians that accepted four acknowledgements would hand over the shares below,
        // and two signatures on one leaf would exist.
        let open = |p: usize, rec: &LeafRecord| select_shares(p, rec, &staged.parties[p].leaves[0]);
        let sig1 = combine_shamir(
            &jorts.cfg,
            &jorts.tree,
            &rec1,
            &[open(0, &rec1), open(5, &rec1), open(6, &rec1)],
        )
        .unwrap();
        let sig2 = combine_shamir(
            &jorts.cfg,
            &jorts.tree,
            &rec2,
            &[open(2, &rec2), open(5, &rec2), open(6, &rec2)],
        )
        .unwrap();
        assert_eq!(sig1.leaf, sig2.leaf);
        assert!(quorum_jorts_verify(&pk, b"M1", &sig1));
        assert!(quorum_jorts_verify(&pk, b"M2", &sig2));
    }

    #[test]
    fn flipped_shamir_shares_fail_the_chain_check_and_are_attributed() {
        let mut jorts = shamir_3_of_7();
        let pk = *jorts.public_key();
        let (record, cert) = jorts.certify(&[0, 1, 2, 3, 4], 0, b"msg").unwrap();
        let mut openings: Vec<ShareOpening> = [0usize, 1, 2, 3, 4]
            .iter()
            .map(|&p| jorts.custodians[p].open(0, b"msg", &cert).unwrap())
            .collect();
        let sig = combine_shamir(&jorts.cfg, &jorts.tree, &record, &openings).unwrap();
        assert!(quorum_jorts_verify(&pk, b"msg", &sig));
        // Any three custodians reconstruct the same signature.
        let other = combine_shamir(&jorts.cfg, &jorts.tree, &record, &openings[2..]).unwrap();
        assert_eq!(other, sig);

        let chain = record.digits.iter().position(|&d| d < 3).unwrap();
        openings[1].shares[chain][0] ^= 1;
        assert_eq!(
            combine_shamir(&jorts.cfg, &jorts.tree, &record, &openings[..3]),
            Err(QuorumError::ChainVerifyFailed { chain })
        );
        // With spare openings the bad one is identified and the signature still comes out.
        let (robust, blamed) =
            combine_shamir_robust(&jorts.cfg, &jorts.tree, &record, &openings).unwrap();
        assert_eq!(robust, sig);
        assert_eq!(blamed, vec![1]);
        // With exactly t openings there is nothing to fall back on.
        assert_eq!(
            combine_shamir_robust(&jorts.cfg, &jorts.tree, &record, &openings[..3]),
            Err(QuorumError::ChainVerifyFailed { chain })
        );
        assert_eq!(
            combine_shamir(&jorts.cfg, &jorts.tree, &record, &openings[..2]),
            Err(QuorumError::NotEnoughShares { have: 2, need: 3 })
        );
    }

    /// Nothing about `y^(k)` for `k < d` leaves a custodian. Two stagings share every chain
    /// (same secrets) but the test rewrites, in one of them, each custodian's shares of the
    /// states below the opened digit: the openings are identical byte for byte. And the two
    /// corrupted custodians' own shares of an unopened state are consistent with every value
    /// of it.
    #[test]
    fn shamir_openings_do_not_depend_on_lower_chain_states() {
        let cfg = QuorumConfig::new(3, 7, 2).unwrap();
        let staged = stage_bft_shamir(cfg, 2, &SEED).unwrap();
        let pk = *staged.tree.public_key();
        let record = LeafRecord::derive(&pk, 1, b"msg").unwrap();
        assert!(record.digits.iter().any(|&d| d > 0));
        for party in [0usize, 3, 6] {
            let original = &staged.parties[party].leaves[1];
            let mut rewritten = original.clone();
            let mut touched = 0usize;
            for (chain, &digit) in record.digits.iter().enumerate() {
                for step in 0..usize::from(digit).min(WOTS_STEPS) {
                    rewritten[chain * WOTS_STEPS + step] = [0xEE; 32];
                    touched += 1;
                }
            }
            assert!(touched > 0);
            assert_eq!(
                select_shares(party, &record, original),
                select_shares(party, &record, &rewritten)
            );
        }

        // Custodians 5 and 6 hold two points of a degree-2 polynomial per byte. For every
        // candidate secret byte there is exactly one such polynomial through both shares,
        // so their view assigns the same weight to all 256 values.
        let chain = record.digits.iter().position(|&d| d > 0).unwrap();
        let idx = chain * WOTS_STEPS; // y^(0) of a chain opened at a later step
        let (s5, s6) = (
            staged.parties[5].leaves[1][idx][0],
            staged.parties[6].leaves[1][idx][0],
        );
        let (x5, x6) = (shamir_point(5), shamir_point(6));
        let mut consistent = 0usize;
        for candidate in 0..=255u8 {
            // Solve a1, a2 from p(x) = candidate + a1 x + a2 x^2 at the two points.
            let r5 = TowerGf256(s5).add(TowerGf256(candidate));
            let r6 = TowerGf256(s6).add(TowerGf256(candidate));
            let det = x5.mul(x6.mul(x6)).add(x6.mul(x5.mul(x5)));
            let det_inv = det.inv().expect("distinct non-zero points");
            let a1 = r5.mul(x6.mul(x6)).add(r6.mul(x5.mul(x5))).mul(det_inv);
            let a2 = r5.mul(x6).add(r6.mul(x5)).mul(det_inv);
            let eval = |x: TowerGf256| TowerGf256(candidate).add(a1.mul(x)).add(a2.mul(x.mul(x)));
            if eval(x5).0 == s5 && eval(x6).0 == s6 {
                consistent += 1;
            }
        }
        assert_eq!(consistent, 256);

        // The independent polynomials per step matter: the shares of consecutive states of
        // one chain are unrelated, and three of them still reconstruct each state.
        let secret_of = |step: usize| {
            let openings: Vec<ShareOpening> = [0usize, 1, 2]
                .iter()
                .map(|&p| ShareOpening {
                    party: p,
                    leaf: 1,
                    shares: vec![staged.parties[p].leaves[1][idx + step]; WOTS_CHAINS],
                })
                .collect();
            let refs: Vec<&ShareOpening> = openings.iter().collect();
            interpolate_nodes(&refs).unwrap()[0]
        };
        let (y0, y1) = (secret_of(0), secret_of(1));
        assert_eq!(
            chain_step(&pk.pk_seed, 1, chain as u32, 0, &y0),
            y1,
            "state 1 is one hash step above state 0"
        );
    }

    #[test]
    fn shamir_window_and_restart_behave_like_the_committee_latch() {
        let cfg = QuorumConfig::new(2, 4, 1).unwrap();
        let mut staged = stage_bft_shamir(cfg, 6, &SEED).unwrap();
        // Staging is deterministic in the seed: a restart is handed the same material again.
        let material = stage_bft_shamir(cfg, 6, &SEED).unwrap().parties.remove(0);
        let mut custodian = ShamirCustodian::new(
            cfg,
            staged.tree.clone(),
            staged.parties.remove(0),
            MemoryWal::new(),
        )
        .unwrap();
        let (record, _) = custodian.ack(2, b"m").unwrap();
        assert_eq!(
            custodian.ack(3 + MAX_WINDOW + 1, b"far").unwrap_err(),
            QuorumError::EpochOutOfWindow {
                epoch: 3 + MAX_WINDOW + 1,
                next_epoch: 3
            }
        );
        assert_eq!(
            custodian.ack(64, b"beyond").unwrap_err(),
            QuorumError::Exhausted
        );
        let wal = custodian.into_wal();
        let mut restarted = ShamirCustodian::new(cfg, staged.tree.clone(), material, wal).unwrap();
        assert_eq!(restarted.ack(2, b"m").unwrap().0, record);
        assert_eq!(
            restarted.ack(2, b"other").unwrap_err(),
            QuorumError::Latch(BeltLatchError::EpochAlreadyBound)
        );
        assert_eq!(
            restarted.ack(1, b"older").unwrap_err(),
            QuorumError::Latch(BeltLatchError::EpochConsumed)
        );
    }
}
#[cfg(test)]
mod bounds_tests {
    use super::*;
    #[test]
    fn rejects_excessive_combinations_before_enumeration() {
        assert!(stage_committee_partitioned(2, 3, 30, &[0; 32]).is_err());
        assert!(stage_bft_shamir(QuorumConfig::tight(2).unwrap(), 30, &[0; 32]).is_err());
        assert!(CommitteeLayout::new(32, 64, 30).is_err());
        assert!(CommitteeLayout::new(2, usize::MAX, 30).is_err());
        assert!(CommitteeLayout::new(2, 46, 30).is_err());
        assert_eq!(
            CommitteeLayout::new(2, 45, 30).unwrap().committees().len(),
            990
        );
    }
}

#[cfg(test)]
mod verified_config_parity {
    use super::*;
    #[test]
    fn global_bft_validator_parity() {
        for n in 0..=16 {
            for t in 0..=17 {
                for f in 0..=17 {
                    for q in 0..=17 {
                        assert_eq!(
                            QuorumConfig::with_quorum(t, n, f, q).is_ok(),
                            qsag_verified::validate_belt_quorum_config(
                                n as u32, t as u32, f as u32, q as u32, true
                            )
                        );
                    }
                }
            }
        }
        // The extracted safety-only mode permits a unanimous committee without global liveness.
        assert!(qsag_verified::validate_belt_quorum_config(
            3, 2, 1, 3, false
        ));
        assert!(QuorumConfig::with_quorum(2, 3, 1, 3).is_err());
        assert!(QuorumConfig::with_quorum(4, 7, 0, 4).is_ok());
        assert!(QuorumConfig::with_quorum(5, 7, 0, 4).is_err());
    }

    #[test]
    fn verify_before_release_blocks_tree_sibling_grind_counter_and_ots_cache_faults() {
        let mut jorts = CommitteePartitionedJorts::stage(2, 3, 3, &[0x44; 32]).unwrap();
        let valid = jorts.sign(&[0, 1], b"honest-0").unwrap();
        assert!(quorum_jorts_verify(jorts.public_key(), b"honest-0", &valid));

        // 1. Non-minimal grinding counter `ctr' > ctr` that ALSO sums to 192 is rejected
        //    by `finish_signature` before any signature can be released.
        let leaf = valid.leaf;
        let msg_hash = message_hash(jorts.public_key(), leaf, b"honest-0");
        let second_valid = ((valid.counter + 1)..MAX_GRIND)
            .find_map(|c| digits_at(&msg_hash, c).map(|d| (c, d)))
            .expect("second valid counter exists within 65536");
        let non_minimal_record = LeafRecord {
            leaf,
            msg_hash,
            counter: second_valid.0,
            digits: second_valid.1,
        };
        assert_eq!(
            jorts
                .tree
                .finish_signature(&non_minimal_record, valid.nodes.clone()),
            Err(QuorumError::SignatureVerifyFailed)
        );

        // 2. Transient RAM bit-flip in a Merkle sibling node inside `QuorumTree::levels`
        //    deterministically aborts `finish_signature` instead of releasing a broken path.
        let canonical_record = LeafRecord {
            leaf,
            msg_hash,
            counter: valid.counter,
            digits: digits_at(&msg_hash, valid.counter).unwrap(),
        };
        let mut corrupted_tree = (*jorts.tree).clone();
        corrupted_tree.levels[0][(leaf as usize) ^ 1][0] ^= 0x01;
        assert_eq!(
            corrupted_tree.finish_signature(&canonical_record, valid.nodes.clone()),
            Err(QuorumError::SignatureVerifyFailed)
        );

        // 3. Write-once `ots_release_cache` blocks releasing a second `(msg_hash, ctr)` on a leaf.
        let next_leaf = jorts.layout.leaf_of(0, 1);
        jorts
            .ots_release_cache
            .insert(next_leaf, ([0xEE; 32], 9999));
        assert_eq!(
            jorts.sign_at(0, 1, b"conflict"),
            Err(QuorumError::SignatureVerifyFailed)
        );
    }

    #[test]
    fn shamir_custodian_verified_belt_guard_permits_idempotent_retry_and_poisons_on_equivocation() {
        let cfg = QuorumConfig::tight(2).unwrap(); // t=2, n=4, f=1, q=3
        let staged = stage_bft_shamir(cfg, 2, &[0x71; 32]).unwrap();
        let tree = staged.tree.clone();
        let mut custodians: Vec<ShamirCustodian<qsag_core::belt_latch::MemoryWal>> = staged
            .parties
            .into_iter()
            .map(|p| {
                ShamirCustodian::new(
                    cfg,
                    tree.clone(),
                    p,
                    qsag_core::belt_latch::MemoryWal::new(),
                )
                .unwrap()
            })
            .collect();

        let msg_a = b"qs-b-primary";
        let msg_b = b"qs-b-conflicting";
        // Parties 0, 1, 2 ack `msg_a` at leaf 0 (`q = 3` quorum); party 3 acks `msg_b` at leaf 0!
        let mut acks_a = Vec::new();
        let mut rec_a = None;
        for c in &mut custodians[..3] {
            let (rec, ack) = c.ack(0, msg_a).unwrap();
            rec_a = Some(rec);
            acks_a.push(ack);
        }
        let cert_a = LatchCertificate::assemble(&rec_a.unwrap(), acks_a);
        let _ = custodians[3].ack(0, msg_b).unwrap();

        // Idempotent retry of `open(0, msg_a, &cert_a)` on custodian 0 succeeds cleanly via VerifiedBeltQuorumGuard.
        let open1 = custodians[0].open(0, msg_a, &cert_a).unwrap();
        let open2 = custodians[0].open(0, msg_a, &cert_a).unwrap();
        assert_eq!(open1, open2);

        // Custodian 3 already bound `msg_b` at leaf 0; presenting `cert_a` triggers conflicting-epoch
        // refusal AND permanently poisons custodian 3's VerifiedBeltQuorumGuard latch!
        assert!(matches!(
            custodians[3].open(0, msg_a, &cert_a),
            Err(QuorumError::Latch(BeltLatchError::EpochAlreadyBound))
        ));
        assert!(custodians[3].guard_poisoned);
        assert!(matches!(
            custodians[3].ack(1, b"later-epoch"),
            Err(QuorumError::Latch(BeltLatchError::WalPoisoned))
        ));
    }
}
