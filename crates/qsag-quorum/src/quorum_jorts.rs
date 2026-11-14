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
//! * Staging ([`stage_committee_partitioned`], [`stage_bft_shamir`]) is a dealer: it derives
//!   every chain from one seed and hands out shares. In a deployment that role is a
//!   multi-party computation; nothing here replaces it.
//! * A certificate is authenticated with one MAC per verifying custodian under pairwise keys.
//!   It convinces any custodian and nobody else.

use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use qsag_core::belt_latch::{BeltLatch, BeltLatchError, BeltLatchRecord, DurableWal, MemoryWal};
use qsag_core::field::tower::{TowerGf256, lagrange_weights_zero_gf256};

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
const TAG_ACK_MAC: &[u8] = b"QSAG.QUORUM.ACK.MAC/v1";
const TAG_PAIR_KEY: &[u8] = b"QSAG.QUORUM.PAIR.KEY/v1";
const TAG_STAGE_SK: &[u8] = b"QSAG.QUORUM.STAGE.SK/v1";
const TAG_STAGE_PK_SEED: &[u8] = b"QSAG.QUORUM.STAGE.PKSEED/v1";

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
/// [`WOTS_TARGET_SUM`].
pub fn digits_at(msg_hash: &Node, counter: u32) -> Option<Vec<u8>> {
    let digest = h32(TAG_DIGEST, &[msg_hash, &counter.to_be_bytes()]);
    let mut digits = Vec::with_capacity(WOTS_CHAINS);
    let mut sum = 0u32;
    for byte in digest {
        for shift in [6u8, 4, 2, 0] {
            let digit = (byte >> shift) & 3;
            sum += u32::from(digit);
            digits.push(digit);
        }
    }
    (sum == WOTS_TARGET_SUM).then_some(digits)
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
    root_from_path(&pk.pk_seed, sig.leaf, &leaf_node, &sig.auth_path) == pk.root
}

/// The public part of a staged key: the tree and the chain ends of every assigned leaf.
#[derive(Clone, Debug)]
pub struct QuorumTree {
    pk: QuorumPublicKey,
    levels: Vec<Vec<Node>>,
    chain_ends: BTreeMap<u64, Vec<Node>>,
}

impl QuorumTree {
    fn build(pk_seed: Node, height: u8, chain_ends: BTreeMap<u64, Vec<Node>>) -> Self {
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

    /// Check reconstructed chain nodes against the public chain ends and assemble the
    /// signature. A node that does not reach its chain end names the failing chain.
    fn finish_signature(
        &self,
        record: &LeafRecord,
        nodes: Vec<Node>,
    ) -> Result<QuorumJortsSig, QuorumError> {
        let ends = self
            .chain_ends(record.leaf)
            .ok_or(QuorumError::InvalidConfig("leaf is not assigned"))?;
        for (chain, (node, &digit)) in nodes.iter().zip(&record.digits).enumerate() {
            let end = chain_walk(
                &self.pk.pk_seed,
                record.leaf,
                chain,
                usize::from(digit),
                WOTS_STEPS,
                node,
            );
            if end != ends[chain] {
                return Err(QuorumError::ChainVerifyFailed { chain });
            }
        }
        Ok(QuorumJortsSig {
            leaf: record.leaf,
            counter: record.counter,
            nodes,
            auth_path: self.auth_path(record.leaf),
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

/// Maximum party count accepted by quorum configurations.
pub const MAX_QUORUM_PARTIES: usize = 255;
/// Maximum enumerated committees; use `BftShamirJorts` for larger configurations.
pub const MAX_COMMITTEES: usize = 1024;
const MAX_STAGED_SHARE_BYTES: usize = 256 * 1024 * 1024;
fn check_staging_budget(height: u8, copies: usize) -> Result<(), QuorumError> {
    if height == 0 || height > 10 || (1usize << height).checked_mul(copies)
        .and_then(|n| n.checked_mul(LEAF_SHARE_NODES * 32))
        .is_none_or(|bytes| bytes > MAX_STAGED_SHARE_BYTES) {
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

/// What staging hands to one custodian.
pub struct CommitteePartyMaterial {
    pub party: usize,
    /// Pairwise MAC keys, indexed by peer.
    mac_keys: Vec<Node>,
    pub stores: Vec<CommitteeShareStore>,
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

struct SecretLeaves(Vec<Vec<Node>>);
impl core::ops::Deref for SecretLeaves {
    type Target = [Vec<Node>];
    fn deref(&self) -> &Self::Target { &self.0 }
}
impl Drop for SecretLeaves {
    fn drop(&mut self) {
        for leaf in &mut self.0 { wipe_nodes(leaf); }
    }
}

struct SecretMacKeys(Vec<Node>);
impl core::ops::Deref for SecretMacKeys {
    type Target = [Node];
    fn deref(&self) -> &Self::Target { &self.0 }
}
impl Drop for SecretMacKeys {
    fn drop(&mut self) { wipe_nodes(&mut self.0); }
}

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
                    leaves: SecretLeaves(core::mem::take(&mut store.leaves)),
                },
            );
        }
        Ok(Self {
            party: material.party,
            layout,
            tree,
            mac_keys: SecretMacKeys(core::mem::take(&mut material.mac_keys)),
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

    /// The custodian's high-water mark for `committee`.
    pub fn next_epoch(&self, committee: usize) -> Result<u64, QuorumError> {
        Ok(self
            .slot(committee)?
            .latch
            .next_epoch())
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
        let replay = slot
            .latch
            .in_flight()
            .is_some_and(|r| r.epoch == epoch);
        window_check(
            epoch,
            slot.latch.next_epoch(),
            replay,
            self.max_window,
        )?;
        let leaf = self.layout.leaf_of(committee, epoch);
        let record = LeafRecord::derive(self.tree.public_key(), leaf, msg)
            .ok_or(QuorumError::GrindFailed)?;
        slot.latch.bind(
            epoch,
            &record.msg_hash,
            &record.salt(),
            &record.digits,
        )?;
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
}

impl CommitteePartitionedJorts<MemoryWal> {
    /// Stage a key with volatile logs.
    pub fn stage(t: usize, n: usize, height: u8, seed: &Node) -> Result<Self, QuorumError> {
        let staged = stage_committee_partitioned(t, n, height, seed)?;
        let custodians = staged
            .parties
            .into_iter()
            .map(|material| {
                let wals = vec![MemoryWal::new(); material.stores.len()];
                CommitteeCustodian::new(staged.layout.clone(), staged.tree.clone(), material, wals)
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self {
            layout: staged.layout,
            tree: staged.tree,
            custodians,
        })
    }
}

impl<W: DurableWal> CommitteePartitionedJorts<W> {
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
        combine_additive(&self.tree, &record, &members, &openings)
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
    /// `n = 3t - 2`.
    pub fn tight(t: usize) -> Result<Self, QuorumError> {
        if t == 0 || t > MAX_QUORUM_PARTIES {
            return Err(QuorumError::InvalidConfig("need 1 <= t and 1 <= n <= 255"));
        }
        Self::new(t, 3 * t - 2, t - 1)
    }

    /// A configuration with an explicit quorum. Rejected unless `2q > n + f` (any two quorums
    /// share an honest custodian), `q <= n - f` (the honest custodians alone form a quorum),
    /// `f < t` (the corrupted custodians cannot reconstruct) and `t <= n - f`.
    pub fn with_quorum(t: usize, n: usize, f: usize, q: usize) -> Result<Self, QuorumError> {
        if n == 0 || n > MAX_QUORUM_PARTIES || t == 0 || t > n || f >= n || q > n {
            return Err(QuorumError::InvalidConfig("need 1 <= t and 1 <= n <= 255"));
        }
        if f >= t {
            return Err(QuorumError::InvalidConfig(
                "need f < t: f shares must not reconstruct",
            ));
        }
        if n < 3 * f + 1 {
            return Err(QuorumError::InvalidConfig("need n >= 3f + 1"));
        }
        if t > n - f {
            return Err(QuorumError::InvalidConfig(
                "need t <= n - f: honest custodians must reconstruct",
            ));
        }
        if 2 * q <= n + f {
            return Err(QuorumError::QuorumTooSmall { q, n, f });
        }
        if q > n - f {
            return Err(QuorumError::InvalidConfig(
                "need q <= n - f: honest custodians must certify",
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

/// What staging hands to one custodian of Mode QS-B.
#[derive(Clone)]
pub struct ShamirPartyMaterial {
    pub party: usize,
    /// Pairwise MAC keys indexed by peer; the custodian's own index holds a private key.
    pub mac_keys: Vec<Node>,
    /// `leaves[leaf][3 * chain + step]`: this custodian's Shamir share of each chain state.
    pub leaves: Vec<Vec<Node>>,
}

/// Output of [`stage_bft_shamir`].
pub struct StagedShamirKeys {
    pub cfg: QuorumConfig,
    pub tree: Arc<QuorumTree>,
    pub parties: Vec<ShamirPartyMaterial>,
}

fn shamir_point(party: usize) -> TowerGf256 {
    TowerGf256(party as u8 + 1)
}

/// Branchless, LUT-free multiplication in the protocol's Wiedemann tower basis.
/// Using an AES-polynomial Russian-peasant multiplier here would change the field encoding.
fn gf256_mul_ct(a: u8, b: u8) -> u8 {
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
