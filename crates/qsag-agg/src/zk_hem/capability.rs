//! Privacy-preserving batched bearer capabilities and `SortedRevocationTree` interval
//! non-membership as a hiding `zk-Hem` relation (`#![no_std]` + `alloc`).
//!
//! Each slot `b` in a batch of `B >= 1` capabilities proves in zero knowledge:
//!
//! 1. **Root capability issuance (`issuer_root`)**:
//!    `mint_leaf = compute_mint_leaf(token_id, audience, enrollment_tag)` where
//!    `enrollment_tag` commits to `(root_tag, final_tag, actual_hops)`.
//!    authenticates at a hidden index under `issuer_root` without revealing `token_id`,
//!    `root_tag`, or the issuance leaf position.
//! 2. **Issuer-enrolled conjunctive caveats (`0..=max_hops` caveats)**:
//!    Starting from `tag_0 = root_tag`, each active hop `h` advances the chained MAC tag
//!    `tag_{h+1} = sponge12(tag_h || [kind] || payload[0..4] || [CAP_STEP_TAG, h])[0..4]`
//!    and enforces its conjunctive predicate (`ExpiresAt`, `NotBefore`, `Resource`, `Actions`,
//!    `MaxAmount`) against the verifier's trusted [`CapabilityRequest`], terminating at the
//!    bearer's hidden `final_tag` and emitting a deterministic per-context nullifier
//!    `presentation_tag = sponge12(final_tag || token_id || context_digest || [CAP_PRESENT_TAG])[0..4]`.
//! 3. **`SortedRevocationTree` adjacent-leaf interval non-membership (`revocation_root`)**:
//!    Witnesses an adjacent pair `(revoked_lo, revoked_hi)` at consecutive leaf indices
//!    `(idx, idx + 1)` (`idx < 2^D - 1`) in the sorted Poseidon2 Merkle tree under
//!    `(revocation_root, revocation_epoch)` and enforces strict 256-bit canonical field-limb
//!    inequalities `revoked_lo < token_id < revoked_hi` (plus `token_id[b - 1] < token_id[b]`
//!    across batched slots so a batch of `B` capabilities cannot replay duplicates).

//!
//! # Delegation boundary
//! This relation requires the bearer to know the chain's root secret. A root-only
//! enrollment therefore cannot support non-escalatable offline macaroon delegation:
//! the bearer could remove caveats and recompute the presentation. Enrollment here
//! binds the exact chain, and `attenuate` evolves the root secret irreversibly. The
//! authority must enroll the resulting `mint_leaf` before that capability is usable.
//! Do not give a delegate an ancestor capability or its root secret. True offline
//! delegation requires an additional recursive proof or signature-chain construction.

use alloc::vec;
use alloc::vec::Vec;
use core::cmp::Ordering;

use super::protocol::{self, ZkHemError, ZkHemProof};
use super::relation::{ConstraintSystem, Lc, Shape, poseidon2_perm, sponge12, sponge12_native};
use crate::field::{GOLDILOCKS_PRIME, Goldilocks};
use crate::pcs::WhirSecurityRegime;
use crate::sponge::{POSEIDON2_CONST_IV, cshake256_32, poseidon2_compress12_ff};

type F = Goldilocks;

/// Full-width 256-bit algebraic digest (`4` canonical `Goldilocks` limbs).
pub type Digest = [F; 4];

/// Full-width 256-bit capability identifier ordered lexicographically (`[0]` most significant).
pub type TokenId = [F; 4];

/// Maximum supported delegation/attenuation hops per capability (`8`).
pub const MAX_CAP_HOPS: usize = 8;

/// Maximum capabilities proven together in one batch relation (`32`).
pub const MAX_CAP_BATCH: usize = 32;

/// Default Merkle depth of the issued-capability directory (`4,096` capabilities).
pub const DEFAULT_ISSUER_DEPTH: usize = 12;

/// Default Merkle depth of [`SortedRevocationTree`] (`65,536` leaves).
pub const DEFAULT_REVOCATION_DEPTH: usize = 16;

/// Canonical 8-byte wire magic for [`ZkCapabilityBatchProof`].
pub const CAPABILITY_WIRE_MAGIC: &[u8; 8] = b"QSAGCAP1";

/// Strict lower sentinel `[0, 0, 0, 0]` at index `0` of every [`SortedRevocationTree`].
pub const SENTINEL_MIN_ID: TokenId = [F::ZERO; 4];

/// Strict upper sentinel `[p - 1, p - 1, p - 1, p - 1]` padding the tail of every [`SortedRevocationTree`].
pub const SENTINEL_MAX_ID: TokenId = [F::from_u64_reduced(GOLDILOCKS_PRIME - 1); 4];

const CAP_ROOT_TAG_DOM: u64 = 0x4341_5052_4F4F_5431; // "CAPROOT1"
const CAP_MINT_LEAF_TAG: u64 = 0x4341_504D_4C45_4631; // "CAPMLEF1"
const CAP_MINT_NODE_TAG: u64 = 0x4341_504D_4E4F_4431; // "CAPMNOD1"
const CAP_STEP_TAG_DOM: u64 = 0x4341_5053_5445_5031; // "CAPSTEP1"
const CAP_PRESENT_TAG_DOM: u64 = 0x4341_5050_5245_5331; // "CAPPRES1"
const REV_LEAF_TAG: u64 = 0x5245_564C_4541_4631; // "REVLEAF1"
const REV_NODE_TAG: u64 = 0x5245_564E_4F44_4531; // "REVNODE1"

#[inline]
fn f(x: u64) -> F {
    F::from_u64_reduced(x)
}

#[inline]
fn first4(st: [F; 12]) -> Digest {
    [st[0], st[1], st[2], st[3]]
}

#[inline]
fn first4_lc(st: &[Lc; 12]) -> [Lc; 4] {
    core::array::from_fn(|i| st[i].clone())
}

/// Canonical lexicographic total order on 256-bit `TokenId`s (`[0]` most significant limb).
#[inline]
pub fn cmp_token_id(a: &TokenId, b: &TokenId) -> Ordering {
    for i in 0..4 {
        match a[i].to_canonical_u64().cmp(&b[i].to_canonical_u64()) {
            Ordering::Equal => continue,
            non_eq => return non_eq,
        }
    }
    Ordering::Equal
}

#[inline]
fn is_usable_token_id(id: &TokenId) -> bool {
    cmp_token_id(&SENTINEL_MIN_ID, id) == Ordering::Less
        && cmp_token_id(id, &SENTINEL_MAX_ID) == Ordering::Less
}

/// Domain-separated 4-limb digest of the verifier's fresh challenge `context`.
pub fn context_digest(context: &[u8]) -> Digest {
    let raw = cshake256_32(b"QSAG.ZKHEM.CAP.CTX/v1", context);
    core::array::from_fn(|i| {
        let mut word = [0u8; 8];
        word.copy_from_slice(&raw[8 * i..8 * (i + 1)]);
        f(u64::from_le_bytes(word))
    })
}

/// Static parameters fixing the public `Shape` of a batched capability presentation relation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CapabilityParams {
    /// Number of distinct capabilities verified together (`1..=MAX_CAP_BATCH`).
    pub batch_size: usize,
    /// Maximum caveat attenuation hops per capability (`1..=MAX_CAP_HOPS`).
    pub max_hops: usize,
    /// Depth of the issued-capability Merkle directory (`1..=20`).
    pub issuer_depth: usize,
    /// Depth of the [`SortedRevocationTree`] (`1..=20`).
    pub revocation_depth: usize,
}

impl Default for CapabilityParams {
    fn default() -> Self {
        Self {
            batch_size: 1,
            max_hops: MAX_CAP_HOPS,
            issuer_depth: DEFAULT_ISSUER_DEPTH,
            revocation_depth: DEFAULT_REVOCATION_DEPTH,
        }
    }
}

impl CapabilityParams {
    #[inline]
    pub fn valid(self) -> bool {
        (1..=MAX_CAP_BATCH).contains(&self.batch_size)
            && (1..=MAX_CAP_HOPS).contains(&self.max_hops)
            && (1..=20).contains(&self.issuer_depth)
            && (1..=20).contains(&self.revocation_depth)
    }
}

/// Errors returned by capability issuance, attenuation, revocation lookup, or `zk-Hem` proving.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CapabilityZkError {
    InvalidParams,
    SentinelTokenIdReserved,
    TooManyCaveats,
    RevocationTreeFull,
    TokenRevoked,
    InvalidIssuerOpening,
    InvalidRevocationWitness,
    InvalidTag,
    CaveatDenied,
    UnsortedOrDuplicateBatch,
    BatchLengthMismatch,
    StatementMismatch,
    Proof(ZkHemError),
}

/// Conjunctive first-party capability caveats matching `qsag_policy::macaroon::Caveat`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CapCaveat {
    /// Requires `request.now < expires_at` (`kind = 1`).
    ExpiresAt(u64),
    /// Requires `request.now >= not_before` (`kind = 2`).
    NotBefore(u64),
    /// Requires `request.resource == resource` (`kind = 3`).
    Resource(Digest),
    /// Requires `(request.actions & !allowed_mask) == 0` (`kind = 4`).
    Actions(u64),
    /// Requires `request.amount <= max_amount` (`kind = 5`).
    MaxAmount(u128),
}

impl CapCaveat {
    #[inline]
    fn encode_words(&self) -> (u64, [F; 4]) {
        match *self {
            Self::ExpiresAt(t) => (1, [f(t >> 32), f(t & 0xFFFF_FFFF), F::ZERO, F::ZERO]),
            Self::NotBefore(t) => (2, [f(t >> 32), f(t & 0xFFFF_FFFF), F::ZERO, F::ZERO]),
            Self::Resource(res) => (3, res),
            Self::Actions(mask) => (4, [f(mask >> 32), f(mask & 0xFFFF_FFFF), F::ZERO, F::ZERO]),
            Self::MaxAmount(max) => (
                5,
                [
                    f((max >> 96) as u64),
                    f(((max >> 64) & 0xFFFF_FFFF) as u64),
                    f(((max >> 32) & 0xFFFF_FFFF) as u64),
                    f((max & 0xFFFF_FFFF) as u64),
                ],
            ),
        }
    }

    #[inline]
    pub fn allows(&self, req: &CapabilityRequest) -> bool {
        match *self {
            Self::ExpiresAt(t) => req.now < t,
            Self::NotBefore(t) => req.now >= t,
            Self::Resource(res) => res == req.resource,
            Self::Actions(mask) => (req.actions & !mask) == 0,
            Self::MaxAmount(max) => req.amount <= max,
        }
    }
}

/// Verifier-supplied request facts checked conjunctively against every active caveat.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CapabilityRequest {
    pub audience: Digest,
    pub resource: Digest,
    pub actions: u64,
    pub amount: u128,
    pub now: u64,
}

#[inline]
fn compute_root_tag(issuer_key: &Digest, token_id: &TokenId, audience: &Digest) -> Digest {
    let mut msg = Vec::with_capacity(13);
    msg.extend_from_slice(issuer_key);
    msg.extend_from_slice(token_id);
    msg.extend_from_slice(audience);
    msg.push(f(CAP_ROOT_TAG_DOM));
    let st = sponge12_native(&msg);
    qsag_asm::volatile_fill(&mut msg, F::ZERO);
    first4(st)
}

/// Low-level directory leaf hash. The third argument is an enrollment commitment,
/// not a raw chain root; use [`BearerCapability::mint_leaf`] to bind the policy.
#[inline]
pub fn compute_mint_leaf(token_id: &TokenId, audience: &Digest, root_tag: &Digest) -> Digest {
    let mut msg = Vec::with_capacity(13);
    msg.extend_from_slice(token_id);
    msg.extend_from_slice(audience);
    msg.extend_from_slice(root_tag);
    msg.push(f(CAP_MINT_LEAF_TAG));
    let st = sponge12_native(&msg);
    qsag_asm::volatile_fill(&mut msg, F::ZERO);
    first4(st)
}

#[inline]
fn chain_step_native(prev_tag: &Digest, caveat: &CapCaveat, hop: usize) -> Digest {
    let (kind, payload) = caveat.encode_words();
    chain_step_raw_native(prev_tag, kind, &payload, hop)
}

#[inline]
fn chain_step_raw_native(prev_tag: &Digest, kind: u64, payload: &[F; 4], hop: usize) -> Digest {
    let mut msg = Vec::with_capacity(11);
    msg.extend_from_slice(prev_tag);
    msg.push(f(kind));
    msg.extend_from_slice(payload);
    msg.push(f(CAP_STEP_TAG_DOM));
    msg.push(f(hop as u64));
    let st = sponge12_native(&msg);
    qsag_asm::volatile_fill(&mut msg, F::ZERO);
    first4(st)
}

#[inline]
pub fn compute_presentation_tag(final_tag: &Digest, token_id: &TokenId, ctx: &Digest) -> Digest {
    let mut msg = Vec::with_capacity(13);
    msg.extend_from_slice(final_tag);
    msg.extend_from_slice(token_id);
    msg.extend_from_slice(ctx);
    msg.push(f(CAP_PRESENT_TAG_DOM));
    let st = sponge12_native(&msg);
    qsag_asm::volatile_fill(&mut msg, F::ZERO);
    first4(st)
}

/// Bearer capability with issuer-enrolled caveats and secret zeroization.
///
/// The bearer knows `root_tag`; Rust field privacy is not a cryptographic boundary.
/// Every changed policy requires enrollment of its new [`Self::mint_leaf`].
#[derive(Clone, PartialEq, Eq)]
pub struct BearerCapability {
    token_id: TokenId,
    audience: Digest,
    root_tag: Digest,
    caveats: Vec<CapCaveat>,
    final_tag: Digest,
}

impl core::fmt::Debug for BearerCapability {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("BearerCapability")
            .field("audience", &self.audience)
            .field("num_caveats", &self.caveats.len())
            .field("token_id", &"[REDACTED]")
            .field("root_tag", &"[REDACTED]")
            .field("final_tag", &"[REDACTED]")
            .finish()
    }
}

impl Drop for BearerCapability {
    fn drop(&mut self) {
        qsag_asm::volatile_fill(&mut self.token_id, F::ZERO);
        qsag_asm::volatile_fill(&mut self.root_tag, F::ZERO);
        qsag_asm::volatile_fill(&mut self.final_tag, F::ZERO);
    }
}

impl BearerCapability {
    /// Mint a fresh root capability from an authority's secret `issuer_key`.
    pub fn issue(
        issuer_key: &Digest,
        token_id: TokenId,
        audience: Digest,
    ) -> Result<Self, CapabilityZkError> {
        if !is_usable_token_id(&token_id) {
            return Err(CapabilityZkError::SentinelTokenIdReserved);
        }
        let root_tag = compute_root_tag(issuer_key, &token_id, &audience);
        Ok(Self {
            token_id,
            audience,
            root_tag,
            caveats: Vec::new(),
            final_tag: root_tag,
        })
    }

    /// Add a restriction and irreversibly evolve the enrollment secret.
    ///
    /// Requires no issuer key locally, but the authority must enroll the new
    /// [`Self::mint_leaf`] before presentation. This is not offline delegation.
    /// Transfer only the resulting capability, never a saved ancestor copy.
    pub fn attenuate(&mut self, caveat: CapCaveat) -> Result<(), CapabilityZkError> {
        if self.caveats.len() >= MAX_CAP_HOPS {
            return Err(CapabilityZkError::TooManyCaveats);
        }
        let hop = self.caveats.len();
        let mut next_root = chain_step_native(&self.final_tag, &caveat, hop);
        qsag_asm::volatile_fill(&mut self.root_tag, F::ZERO);
        qsag_asm::volatile_fill(&mut self.final_tag, F::ZERO);
        self.root_tag = next_root;
        qsag_asm::volatile_fill(&mut next_root, F::ZERO);
        self.caveats.push(caveat);
        self.final_tag = self.root_tag;
        for (hop, caveat) in self.caveats.iter().enumerate() {
            self.final_tag = chain_step_native(&self.final_tag, caveat, hop);
        }
        Ok(())
    }

    #[inline]
    pub fn token_id(&self) -> &TokenId {
        &self.token_id
    }

    #[inline]
    pub fn audience(&self) -> &Digest {
        &self.audience
    }

    #[inline]
    pub fn caveats(&self) -> &[CapCaveat] {
        &self.caveats
    }

    /// Commitment to the exact current policy, to be approved by the issuer.
    #[inline]
    pub fn mint_leaf(&self) -> Digest {
        let mut msg = Vec::with_capacity(10);
        msg.extend_from_slice(&self.root_tag);
        msg.extend_from_slice(&self.final_tag);
        msg.push(f(self.caveats.len() as u64));
        msg.push(f(CAP_MINT_LEAF_TAG));
        let mut enrollment_tag = first4(sponge12_native(&msg));
        let leaf = compute_mint_leaf(&self.token_id, &self.audience, &enrollment_tag);
        qsag_asm::volatile_fill(&mut msg, F::ZERO);
        qsag_asm::volatile_fill(&mut enrollment_tag, F::ZERO);
        leaf
    }

    #[inline]
    pub fn presentation_tag(&self, context: &[u8]) -> Digest {
        compute_presentation_tag(&self.final_tag, &self.token_id, &context_digest(context))
    }

    /// Standalone native verification of the tag chain and all caveats against `request`.
    pub fn verify_native(&self, request: &CapabilityRequest) -> Result<(), CapabilityZkError> {
        if self.audience != request.audience {
            return Err(CapabilityZkError::CaveatDenied);
        }
        let mut running = self.root_tag;
        for (hop, caveat) in self.caveats.iter().enumerate() {
            running = chain_step_native(&running, caveat, hop);
        }
        let tag_ok = running == self.final_tag;
        qsag_asm::volatile_fill(&mut running, F::ZERO);
        if !tag_ok {
            return Err(CapabilityZkError::InvalidTag);
        }
        for caveat in &self.caveats {
            if !caveat.allows(request) {
                return Err(CapabilityZkError::CaveatDenied);
            }
        }
        Ok(())
    }
}

// ============================================================================
// Issued-Capability Directory & SortedRevocationTree
// ============================================================================

#[inline]
fn mint_node_native(left: &Digest, right: &Digest, level: usize) -> Digest {
    poseidon2_compress12_ff(
        *left,
        *right,
        [
            f(CAP_MINT_NODE_TAG),
            f(level as u64),
            F::ZERO,
            f(POSEIDON2_CONST_IV),
        ],
    )
}

/// Poseidon2 Merkle accumulator of issued capability root commitments (`mint_leaf`s).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CapabilityIssuerDirectory {
    depth: usize,
    levels: Vec<Vec<Digest>>,
}

impl CapabilityIssuerDirectory {
    pub fn new(depth: usize, mint_leaves: &[Digest]) -> Result<Self, CapabilityZkError> {
        if !(1..=20).contains(&depth) || mint_leaves.len() > (1usize << depth) {
            return Err(CapabilityZkError::InvalidParams);
        }
        let mut leaves = mint_leaves.to_vec();
        leaves.resize(1usize << depth, [F::ZERO; 4]);
        let mut levels = vec![leaves];
        for level in 0..depth {
            let next = levels[level]
                .as_chunks::<2>()
                .0
                .iter()
                .map(|pair| mint_node_native(&pair[0], &pair[1], level))
                .collect();
            levels.push(next);
        }
        Ok(Self { depth, levels })
    }

    #[inline]
    pub fn depth(&self) -> usize {
        self.depth
    }

    #[inline]
    pub fn root(&self) -> Digest {
        self.levels[self.depth][0]
    }

    pub fn opening(&self, index: usize) -> Option<Vec<Digest>> {
        if index >= (1usize << self.depth) {
            return None;
        }
        Some(
            (0..self.depth)
                .map(|level| self.levels[level][(index >> level) ^ 1])
                .collect(),
        )
    }

    pub fn verify_opening(&self, index: usize, leaf: &Digest, siblings: &[Digest]) -> bool {
        if index >= (1usize << self.depth) || siblings.len() != self.depth {
            return false;
        }
        let mut node = *leaf;
        for (level, sib) in siblings.iter().enumerate() {
            let (left, right) = if ((index >> level) & 1) == 1 {
                (sib, &node)
            } else {
                (&node, sib)
            };
            node = mint_node_native(left, right, level);
        }
        node == self.root()
    }
}

#[inline]
fn rev_leaf_native(id: &TokenId) -> Digest {
    first4(sponge12_native(&[
        id[0],
        id[1],
        id[2],
        id[3],
        f(REV_LEAF_TAG),
    ]))
}

#[inline]
fn rev_node_tweak(level: usize, epoch: u64) -> [F; 4] {
    [
        f(REV_NODE_TAG),
        f(level as u64),
        f(epoch & 0xFFFF_FFFF),
        f(epoch >> 32) + f(POSEIDON2_CONST_IV),
    ]
}

#[inline]
fn rev_node_native(left: &Digest, right: &Digest, level: usize, epoch: u64) -> Digest {
    poseidon2_compress12_ff(*left, *right, rev_node_tweak(level, epoch))
}

/// Adjacent-leaf non-membership witness in a [`SortedRevocationTree`]:
/// authenticates `leaf[left_index] == revoked_lo` and `leaf[left_index + 1] == revoked_hi`
/// with `revoked_lo < token_id < revoked_hi`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RevocationNonMembershipWitness {
    pub left_index: usize,
    pub revoked_lo: TokenId,
    pub path_lo: Vec<Digest>,
    pub revoked_hi: TokenId,
    pub path_hi: Vec<Digest>,
}

impl Drop for RevocationNonMembershipWitness {
    fn drop(&mut self) {
        qsag_asm::volatile_fill(&mut self.revoked_lo, F::ZERO);
        qsag_asm::volatile_fill(&mut self.revoked_hi, F::ZERO);
        for d in &mut self.path_lo {
            qsag_asm::volatile_fill(d, F::ZERO);
        }
        for d in &mut self.path_hi {
            qsag_asm::volatile_fill(d, F::ZERO);
        }
    }
}

/// Sorted Poseidon2 Merkle tree over revoked `TokenId`s (`SENTINEL_MIN_ID` at leaf `0`,
/// strictly sorted revoked IDs at `1..=m`, and `SENTINEL_MAX_ID` padding `m + 1 .. 2^depth`),
/// enabling $O(\log N)$ adjacent-neighbor interval non-membership proofs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SortedRevocationTree {
    depth: usize,
    epoch: u64,
    revoked_count: usize,
    leaves: Vec<TokenId>,
    levels: Vec<Vec<Digest>>,
}

impl SortedRevocationTree {
    pub fn new(
        depth: usize,
        epoch: u64,
        revoked_ids: &[TokenId],
    ) -> Result<Self, CapabilityZkError> {
        if !(1..=20).contains(&depth) {
            return Err(CapabilityZkError::InvalidParams);
        }
        if revoked_ids.iter().any(|id| !is_usable_token_id(id)) {
            return Err(CapabilityZkError::SentinelTokenIdReserved);
        }
        let mut sorted = revoked_ids.to_vec();
        sorted.sort_by(cmp_token_id);
        sorted.dedup();
        let capacity = 1usize << depth;
        // Reserve index `0` for `SENTINEL_MIN_ID` and at least index `m + 1` for `SENTINEL_MAX_ID`.
        if sorted.len() + 2 > capacity {
            return Err(CapabilityZkError::RevocationTreeFull);
        }
        let revoked_count = sorted.len();
        let mut leaves = Vec::with_capacity(capacity);
        leaves.push(SENTINEL_MIN_ID);
        leaves.extend_from_slice(&sorted);
        leaves.resize(capacity, SENTINEL_MAX_ID);

        let leaf_hashes: Vec<Digest> = leaves.iter().map(rev_leaf_native).collect();
        let mut levels = vec![leaf_hashes];
        for level in 0..depth {
            let next = levels[level]
                .as_chunks::<2>()
                .0
                .iter()
                .map(|pair| rev_node_native(&pair[0], &pair[1], level, epoch))
                .collect();
            levels.push(next);
        }
        Ok(Self {
            depth,
            epoch,
            revoked_count,
            leaves,
            levels,
        })
    }

    #[inline]
    pub fn depth(&self) -> usize {
        self.depth
    }

    #[inline]
    pub fn epoch(&self) -> u64 {
        self.epoch
    }

    #[inline]
    pub fn revoked_count(&self) -> usize {
        self.revoked_count
    }

    #[inline]
    pub fn root(&self) -> Digest {
        self.levels[self.depth][0]
    }

    pub fn is_revoked(&self, token_id: &TokenId) -> bool {
        if !is_usable_token_id(token_id) {
            return true;
        }
        self.leaves[1..=self.revoked_count]
            .binary_search_by(|probe| cmp_token_id(probe, token_id))
            .is_ok()
    }

    fn path(&self, index: usize) -> Vec<Digest> {
        (0..self.depth)
            .map(|level| self.levels[level][(index >> level) ^ 1])
            .collect()
    }

    /// Construct an adjacent-leaf interval non-membership witness `(revoked_lo, revoked_hi)`
    /// proving `revoked_lo < token_id < revoked_hi` at consecutive indices `(idx, idx + 1)`.
    pub fn prove_non_membership(
        &self,
        token_id: &TokenId,
    ) -> Result<RevocationNonMembershipWitness, CapabilityZkError> {
        if !is_usable_token_id(token_id) {
            return Err(CapabilityZkError::SentinelTokenIdReserved);
        }
        let active_span = &self.leaves[..=self.revoked_count + 1];
        match active_span.binary_search_by(|probe| cmp_token_id(probe, token_id)) {
            Ok(_) => Err(CapabilityZkError::TokenRevoked),
            Err(ins) => {
                debug_assert!((1..=self.revoked_count + 1).contains(&ins));
                let left_index = ins - 1;
                let right_index = ins;
                let revoked_lo = self.leaves[left_index];
                let revoked_hi = self.leaves[right_index];
                debug_assert_eq!(cmp_token_id(&revoked_lo, token_id), Ordering::Less);
                debug_assert_eq!(cmp_token_id(token_id, &revoked_hi), Ordering::Less);
                Ok(RevocationNonMembershipWitness {
                    left_index,
                    revoked_lo,
                    path_lo: self.path(left_index),
                    revoked_hi,
                    path_hi: self.path(right_index),
                })
            }
        }
    }

    /// Standalone native verification of an interval non-membership witness against `self.root()`.
    pub fn verify_non_membership_native(
        &self,
        token_id: &TokenId,
        w: &RevocationNonMembershipWitness,
    ) -> bool {
        if w.left_index >= (1usize << self.depth) - 1
            || w.path_lo.len() != self.depth
            || w.path_hi.len() != self.depth
            || cmp_token_id(&w.revoked_lo, token_id) != Ordering::Less
            || cmp_token_id(token_id, &w.revoked_hi) != Ordering::Less
        {
            return false;
        }
        let check_path = |idx: usize, key: &TokenId, path: &[Digest]| -> bool {
            let mut node = rev_leaf_native(key);
            for (level, sib) in path.iter().enumerate() {
                let (l, r) = if ((idx >> level) & 1) == 1 {
                    (sib, &node)
                } else {
                    (&node, sib)
                };
                node = rev_node_native(l, r, level, self.epoch);
            }
            node == self.root()
        };
        check_path(w.left_index, &w.revoked_lo, &w.path_lo)
            && check_path(w.left_index + 1, &w.revoked_hi, &w.path_hi)
    }
}

// ============================================================================
// Public Statement, Witness & In-Circuit Gadgets
// ============================================================================

/// One capability witness bundle fed into [`CapabilityRelation::prove`].
#[derive(Clone)]
pub struct CapabilityPresentationInput {
    pub capability: BearerCapability,
    pub issuer_index: usize,
    pub issuer_siblings: Vec<Digest>,
    pub non_membership: RevocationNonMembershipWitness,
}

/// Public statement of a batched capability + non-revocation `zk-Hem` proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CapabilityBatchStatement {
    pub issuer_root: Digest,
    pub revocation_root: Digest,
    pub revocation_epoch: u64,
    pub request: CapabilityRequest,
    /// Per-capability unlinkable presentation nullifiers, ordered by hidden `token_id`.
    pub presentation_tags: Vec<Digest>,
}

impl CapabilityBatchStatement {
    /// Canonicalize and sort `inputs` by `token_id` and derive the corresponding public statement.
    pub fn prepare_sorted(
        issuer_root: Digest,
        revocation_root: Digest,
        revocation_epoch: u64,
        request: CapabilityRequest,
        inputs: &mut [CapabilityPresentationInput],
        context: &[u8],
    ) -> Result<Self, CapabilityZkError> {
        if inputs.is_empty() || inputs.len() > MAX_CAP_BATCH {
            return Err(CapabilityZkError::BatchLengthMismatch);
        }
        inputs.sort_by(|a, b| cmp_token_id(a.capability.token_id(), b.capability.token_id()));
        for pair in inputs.windows(2) {
            if cmp_token_id(pair[0].capability.token_id(), pair[1].capability.token_id())
                != Ordering::Less
            {
                return Err(CapabilityZkError::UnsortedOrDuplicateBatch);
            }
        }
        let ctx = context_digest(context);
        let presentation_tags = inputs
            .iter()
            .map(|item| {
                compute_presentation_tag(
                    &item.capability.final_tag,
                    &item.capability.token_id,
                    &ctx,
                )
            })
            .collect();
        Ok(Self {
            issuer_root,
            revocation_root,
            revocation_epoch,
            request,
            presentation_tags,
        })
    }
}

fn public_inputs_vec(st: &CapabilityBatchStatement, context: &[u8]) -> Vec<F> {
    let ctx = context_digest(context);
    let mut out = Vec::with_capacity(92 + 4 * st.presentation_tags.len());
    out.extend_from_slice(&st.issuer_root);
    out.extend_from_slice(&st.revocation_root);
    out.push(f(st.revocation_epoch & 0xFFFF_FFFF));
    out.push(f(st.revocation_epoch >> 32));
    out.extend_from_slice(&st.request.audience);
    out.extend_from_slice(&st.request.resource);
    for t in 0..64 {
        out.push(f((st.request.actions >> t) & 1));
    }
    out.push(f((st.request.amount >> 96) as u64));
    out.push(f(((st.request.amount >> 64) & 0xFFFF_FFFF) as u64));
    out.push(f(((st.request.amount >> 32) & 0xFFFF_FFFF) as u64));
    out.push(f((st.request.amount & 0xFFFF_FFFF) as u64));
    out.push(f(st.request.now >> 32));
    out.push(f(st.request.now & 0xFFFF_FFFF));
    out.extend_from_slice(&ctx);
    for tag in &st.presentation_tags {
        out.extend_from_slice(tag);
    }
    out
}

#[derive(Clone)]
struct HopSlot {
    active: bool,
    kind: u64,
    payload: [F; 4],
}

#[derive(Clone)]
struct CapSlot {
    token_id: TokenId,
    root_tag: Digest,
    final_tag: Digest,
    hops: Vec<HopSlot>,
    issuer_index: usize,
    issuer_siblings: Vec<Digest>,
    rev_left_index: usize,
    revoked_lo: TokenId,
    path_lo: Vec<Digest>,
    revoked_hi: TokenId,
    path_hi: Vec<Digest>,
}

impl Drop for CapSlot {
    fn drop(&mut self) {
        qsag_asm::volatile_fill(&mut self.token_id, F::ZERO);
        qsag_asm::volatile_fill(&mut self.root_tag, F::ZERO);
        qsag_asm::volatile_fill(&mut self.final_tag, F::ZERO);
        qsag_asm::volatile_fill(&mut self.revoked_lo, F::ZERO);
        qsag_asm::volatile_fill(&mut self.revoked_hi, F::ZERO);
        for hop in &mut self.hops {
            qsag_asm::volatile_fill(&mut hop.payload, F::ZERO);
        }
    }
}

impl CapSlot {
    fn placeholder(params: CapabilityParams) -> Self {
        Self {
            token_id: [F::ZERO, F::ZERO, F::ZERO, F::ONE],
            root_tag: [F::ZERO; 4],
            final_tag: [F::ZERO; 4],
            hops: vec![
                HopSlot {
                    active: false,
                    kind: 0,
                    payload: [F::ZERO; 4],
                };
                params.max_hops
            ],
            issuer_index: 0,
            issuer_siblings: vec![[F::ZERO; 4]; params.issuer_depth],
            rev_left_index: 0,
            revoked_lo: SENTINEL_MIN_ID,
            path_lo: vec![[F::ZERO; 4]; params.revocation_depth],
            revoked_hi: SENTINEL_MAX_ID,
            path_hi: vec![[F::ZERO; 4]; params.revocation_depth],
        }
    }

    fn from_input(
        params: CapabilityParams,
        item: &CapabilityPresentationInput,
    ) -> Result<Self, CapabilityZkError> {
        if item.capability.caveats.len() > params.max_hops
            || item.issuer_siblings.len() != params.issuer_depth
            || item.issuer_index >= (1usize << params.issuer_depth)
            || item.non_membership.path_lo.len() != params.revocation_depth
            || item.non_membership.path_hi.len() != params.revocation_depth
            || item.non_membership.left_index >= (1usize << params.revocation_depth) - 1
        {
            return Err(CapabilityZkError::InvalidParams);
        }
        let mut hops = Vec::with_capacity(params.max_hops);
        for caveat in &item.capability.caveats {
            let (kind, payload) = caveat.encode_words();
            hops.push(HopSlot {
                active: true,
                kind,
                payload,
            });
        }
        hops.resize(
            params.max_hops,
            HopSlot {
                active: false,
                kind: 0,
                payload: [F::ZERO; 4],
            },
        );
        Ok(Self {
            token_id: item.capability.token_id,
            root_tag: item.capability.root_tag,
            final_tag: item.capability.final_tag,
            hops,
            issuer_index: item.issuer_index,
            issuer_siblings: item.issuer_siblings.clone(),
            rev_left_index: item.non_membership.left_index,
            revoked_lo: item.non_membership.revoked_lo,
            path_lo: item.non_membership.path_lo.clone(),
            revoked_hi: item.non_membership.revoked_hi,
            path_hi: item.non_membership.path_hi.clone(),
        })
    }
}

fn alloc4(cs: &mut ConstraintSystem, v: &Digest) -> [Lc; 4] {
    core::array::from_fn(|i| cs.alloc(v[i]).into())
}

fn alloc_bits(cs: &mut ConstraintSystem, value: u64, n: usize) -> Vec<Lc> {
    (0..n)
        .map(|t| {
            let bit: Lc = cs.alloc(f((value >> t) & 1)).into();
            cs.enforce_boolean(&bit);
            bit
        })
        .collect()
}

fn pack_bits(bits: &[Lc]) -> Lc {
    let parts: Vec<(F, &Lc)> = bits
        .iter()
        .enumerate()
        .map(|(t, b)| (f(1u64 << t), b))
        .collect();
    Lc::combine(&parts)
}

/// Unique canonical `< p` 64-bit Boolean decomposition (`bits[0..64]` LSB-first) plus
/// its MSB-first 32-bit halves `(hi32, lo32)` (`0 <= hi32, lo32 < 2^32`).
fn canonical_bits_and_halves32(cs: &mut ConstraintSystem, value: &Lc) -> (Vec<Lc>, Lc, Lc) {
    let raw = cs.eval(value).to_canonical_u64();
    let bits = alloc_bits(cs, raw, 64);
    cs.enforce_equal(&pack_bits(&bits), value);
    let mut high_ones = bits[32].clone();
    for bit in &bits[33..] {
        high_ones = cs.mul(&high_ones, bit).into();
    }
    let lo32 = pack_bits(&bits[..32]);
    let hi32 = pack_bits(&bits[32..64]);
    cs.enforce_mul(high_ones, lo32.clone(), Lc::zero());
    (bits, hi32, lo32)
}

/// Decompose a 4-limb `Digest` (`[0]` MSB limb) into eight 32-bit MSB-to-LSB halves (`< 2^32`),
/// enforcing canonical `< p` representation on all four `Goldilocks` limbs.
fn canonical_digest_halves8(cs: &mut ConstraintSystem, limbs: &[Lc; 4]) -> [Lc; 8] {
    let mut out: [Lc; 8] = core::array::from_fn(|_| Lc::zero());
    for i in 0..4 {
        let (_, hi32, lo32) = canonical_bits_and_halves32(cs, &limbs[i]);
        out[2 * i] = hi32;
        out[2 * i + 1] = lo32;
    }
    out
}

fn select4(cs: &mut ConstraintSystem, bit: &Lc, on_one: &[Lc; 4], on_zero: &[Lc; 4]) -> [Lc; 4] {
    core::array::from_fn(|i| cs.select(bit, &on_one[i], &on_zero[i]))
}

fn enforce_equal4(cs: &mut ConstraintSystem, a: &[Lc; 4], b: &[Lc; 4]) {
    for (x, y) in a.iter().zip(b) {
        cs.enforce_equal(x, y);
    }
}

fn compress12_ff_gadget(
    cs: &mut ConstraintSystem,
    in0: &[Lc; 4],
    in1: &[Lc; 4],
    tweak: &[Lc; 4],
) -> [Lc; 4] {
    let mut st: [Lc; 12] = core::array::from_fn(|i| match i {
        0..=3 => in0[i].clone(),
        4..=7 => in1[i - 4].clone(),
        _ => tweak[i - 8].clone(),
    });
    poseidon2_perm(cs, &mut st);
    core::array::from_fn(|i| {
        st[i]
            .plus(&in0[i])
            .plus(&in1[i].scaled(F::TWO))
            .plus(&tweak[i].scaled(f(4)))
    })
}

/// Enforce `a < b` (when `allow_eq == false`) or `a <= b` (when `allow_eq == true`) over
/// `K` MSB-to-LSB 32-bit limbs (`0 <= a_j, b_j < 2^32`), gated by Boolean `gate`.
///
/// Soundness:
/// - `win[0..K]` (and optional `is_eq`) are Booleans summing to `gate in {0, 1}` (`K + 1 <= 9 < p`),
///   forcing exact one-hot selection when `gate == 1` and all-zero when `gate == 0`.
/// - Prefix indicators force `a_j == b_j` at every limb more significant than the winning limb `j*`
///   (and at all limbs when `is_eq == 1`).
/// - At `j*`, `b_{j*} - a_{j*} - 1` lies in `[-(2^32), 2^32 - 2]` over `Z`, which cannot wrap
///   modulo `p = 2^64 - 2^32 + 1`; decomposing `chosen_diff` into 32 Booleans proves `a_{j*} < b_{j*}`.
fn enforce_gated_cmp_limbs32(
    cs: &mut ConstraintSystem,
    gate: &Lc,
    a: &[Lc],
    b: &[Lc],
    allow_eq: bool,
) {
    assert_eq!(a.len(), b.len());
    let k = a.len();
    assert!((1..=8).contains(&k));

    // Keep the Boolean gate precondition local, including for future callers.
    cs.enforce_boolean(gate);
    let gate_on = cs.eval(gate).to_canonical_u64() == 1;
    let mut first_diff = None;
    for j in 0..k {
        if cs.eval(&a[j]) != cs.eval(&b[j]) {
            first_diff = Some(j);
            break;
        }
    }

    let win: Vec<Lc> = (0..k)
        .map(|j| {
            let bit_val = u64::from(gate_on && first_diff == Some(j));
            let w: Lc = cs.alloc(f(bit_val)).into();
            cs.enforce_boolean(&w);
            w
        })
        .collect();

    let is_eq = if allow_eq {
        let eq_val = u64::from(gate_on && first_diff.is_none());
        let eq_lc: Lc = cs.alloc(f(eq_val)).into();
        cs.enforce_boolean(&eq_lc);
        eq_lc
    } else {
        Lc::zero()
    };

    let sum_selectors = win.iter().fold(is_eq.clone(), |acc, w| acc.plus(w));
    cs.enforce_equal(&sum_selectors, gate);

    let prefix_limit = if allow_eq { k } else { k - 1 };
    for j in 0..prefix_limit {
        let must_eq = win[j + 1..].iter().fold(is_eq.clone(), |acc, w| acc.plus(w));
        cs.enforce_mul(must_eq, a[j].minus(&b[j]), Lc::zero());
    }

    let mut chosen_diff = Lc::zero();
    for j in 0..k {
        let diff_minus_one = b[j].minus(&a[j]).plus_const(F::ZERO - F::ONE);
        let term: Lc = cs.mul(&win[j], &diff_minus_one).into();
        chosen_diff = chosen_diff.plus(&term);
    }

    // Witness the non-negative 32-bit integer value when honest (`0` if unsatisfied so shape stays fixed).
    let diff_u64 = match (gate_on, first_diff) {
        (true, Some(j)) => {
            let av = cs.eval(&a[j]).to_canonical_u64();
            let bv = cs.eval(&b[j]).to_canonical_u64();
            bv.saturating_sub(av.saturating_add(1))
        }
        _ => 0,
    };
    let diff_bits = alloc_bits(cs, diff_u64, 32);
    cs.enforce_equal(&pack_bits(&diff_bits), &chosen_diff);
}

/// Both indices are bounded integers; the field equality cannot wrap at 2^depth.
fn adjacent_index_bits(cs: &mut ConstraintSystem, left: usize, depth: usize) -> (Vec<Lc>, Vec<Lc>) {
    let lo = alloc_bits(cs, left as u64, depth);
    let right = (left as u64).saturating_add(1).min((1u64 << depth) - 1);
    let hi = alloc_bits(cs, right, depth);
    cs.enforce_equal(&pack_bits(&hi), &pack_bits(&lo).plus_const(F::ONE));
    (lo, hi)
}

#[allow(clippy::too_many_arguments)]
fn slot_gadget(
    cs: &mut ConstraintSystem,
    params: CapabilityParams,
    slot: &CapSlot,
    issuer_root: &[Lc; 4],
    revocation_root: &[Lc; 4],
    rev_epoch_lo32: &Lc,
    rev_epoch_hi32: &Lc,
    req_audience: &[Lc; 4],
    req_resource: &[Lc; 4],
    req_actions_bits: &[Lc],
    req_amount_limbs32: &[Lc; 4],
    req_now_limbs32: &[Lc; 2],
    ctx_digest: &[Lc; 4],
    want_pres_tag: &[Lc; 4],
) -> [Lc; 8] {
    let token_id = alloc4(cs, &slot.token_id);
    let token_halves = canonical_digest_halves8(cs, &token_id);
    let root_tag = alloc4(cs, &slot.root_tag);
    let final_tag = alloc4(cs, &slot.final_tag);

    // 2. Poseidon2 sponge macaroon attenuation (`0..=params.max_hops`) & conjunctive caveat checks.
    let mut cur_tag = root_tag.clone();
    let mut actual_hops = Lc::zero();
    let mut prev_active: Option<Lc> = None;
    for (hop_idx, hop) in slot.hops.iter().enumerate() {
        let active: Lc = cs.alloc(f(u64::from(hop.active))).into();
        cs.enforce_boolean(&active);
        actual_hops = actual_hops.plus(&active);
        if let Some(prev) = &prev_active {
            cs.enforce_mul(
                active.clone(),
                Lc::constant(F::ONE).minus(prev),
                Lc::zero(),
            );
        }
        prev_active = Some(active.clone());

        // Exact one-hot caveat kind selector `s[0..5]` for kinds `1..=5` when `active == 1`.
        let selectors: [Lc; 5] = core::array::from_fn(|k| {
            let v = u64::from(hop.active && hop.kind == (k as u64 + 1));
            let s: Lc = cs.alloc(f(v)).into();
            cs.enforce_boolean(&s);
            s
        });
        let sel_sum = selectors.iter().fold(Lc::zero(), |acc, s| acc.plus(s));
        cs.enforce_equal(&sel_sum, &active);

        let kind_lc = Lc::combine(&[
            (f(1), &selectors[0]),
            (f(2), &selectors[1]),
            (f(3), &selectors[2]),
            (f(4), &selectors[3]),
            (f(5), &selectors[4]),
        ]);

        let payload = alloc4(cs, &hop.payload);
        let mut p_bits_all: Vec<Vec<Lc>> = Vec::with_capacity(4);
        let mut p_hi32: [Lc; 4] = core::array::from_fn(|_| Lc::zero());
        let mut p_lo32: [Lc; 4] = core::array::from_fn(|_| Lc::zero());
        for i in 0..4 {
            let (bits, hi, lo) = canonical_bits_and_halves32(cs, &payload[i]);
            p_bits_all.push(bits);
            p_hi32[i] = hi;
            p_lo32[i] = lo;
        }

        // Enforce canonical 32-bit packing for `u64` kinds (`1, 2, 4`) and `u128` kind (`5`).
        let is_u64_kind = selectors[0].plus(&selectors[1]).plus(&selectors[3]);
        cs.enforce_mul(is_u64_kind.clone(), p_hi32[0].clone(), Lc::zero());
        cs.enforce_mul(is_u64_kind.clone(), p_hi32[1].clone(), Lc::zero());
        cs.enforce_mul(is_u64_kind.clone(), payload[2].clone(), Lc::zero());
        cs.enforce_mul(is_u64_kind, payload[3].clone(), Lc::zero());
        for hi in &p_hi32 {
            cs.enforce_mul(selectors[4].clone(), hi.clone(), Lc::zero());
        }

        // Kind 1 (`ExpiresAt(t)`): `request.now < t`.
        enforce_gated_cmp_limbs32(
            cs,
            &selectors[0],
            req_now_limbs32,
            &[p_lo32[0].clone(), p_lo32[1].clone()],
            false,
        );
        // Kind 2 (`NotBefore(t)`): `t <= request.now`.
        enforce_gated_cmp_limbs32(
            cs,
            &selectors[1],
            &[p_lo32[0].clone(), p_lo32[1].clone()],
            req_now_limbs32,
            true,
        );
        // Kind 3 (`Resource(res)`): `res == request.resource`.
        for i in 0..4 {
            cs.enforce_mul(
                selectors[2].clone(),
                payload[i].minus(&req_resource[i]),
                Lc::zero(),
            );
        }
        // Kind 4 (`Actions(mask)`): `(request.actions & !mask) == 0`.
        let mut forbidden_sum = Lc::zero();
        for t in 0..64 {
            let mask_bit = if t < 32 {
                &p_bits_all[1][t]
            } else {
                &p_bits_all[0][t - 32]
            };
            let bad: Lc = cs
                .mul(&req_actions_bits[t], &Lc::constant(F::ONE).minus(mask_bit))
                .into();
            forbidden_sum = forbidden_sum.plus(&bad);
        }
        cs.enforce_mul(selectors[3].clone(), forbidden_sum, Lc::zero());
        // Kind 5 (`MaxAmount(max)`): `request.amount <= max`.
        enforce_gated_cmp_limbs32(cs, &selectors[4], req_amount_limbs32, &p_lo32, true);

        // Chained Poseidon2 tag step: `next_tag = sponge12(cur_tag || kind || payload || [CAP_STEP_TAG, hop])[0..4]`.
        let mut step_msg: Vec<Lc> = Vec::with_capacity(11);
        step_msg.extend_from_slice(&cur_tag);
        step_msg.push(kind_lc);
        step_msg.extend_from_slice(&payload);
        step_msg.push(Lc::constant(f(CAP_STEP_TAG_DOM)));
        step_msg.push(Lc::constant(f(hop_idx as u64)));
        let stepped = first4_lc(&sponge12(cs, &step_msg));
        cur_tag = select4(cs, &active, &stepped, &cur_tag);
    }
    enforce_equal4(cs, &cur_tag, &final_tag);

    // Exact policy membership under `issuer_root`, including the secret root and chain length.
    let mut enrollment_msg = Vec::with_capacity(10);
    enrollment_msg.extend_from_slice(&root_tag);
    enrollment_msg.extend_from_slice(&final_tag);
    enrollment_msg.push(actual_hops);
    enrollment_msg.push(Lc::constant(f(CAP_MINT_LEAF_TAG)));
    let enrollment_tag = first4_lc(&sponge12(cs, &enrollment_msg));
    let mut mint_msg: Vec<Lc> = Vec::with_capacity(13);
    mint_msg.extend_from_slice(&token_id);
    mint_msg.extend_from_slice(req_audience);
    mint_msg.extend_from_slice(&enrollment_tag);
    mint_msg.push(Lc::constant(f(CAP_MINT_LEAF_TAG)));
    let mut mint_node = first4_lc(&sponge12(cs, &mint_msg));

    let iss_idx_bits = alloc_bits(cs, slot.issuer_index as u64, params.issuer_depth);
    for (level, bit) in iss_idx_bits.iter().enumerate() {
        let sib = alloc4(cs, &slot.issuer_siblings[level]);
        let left = select4(cs, bit, &sib, &mint_node);
        let right: [Lc; 4] =
            core::array::from_fn(|i| mint_node[i].plus(&sib[i]).minus(&left[i]));
        let tweak = [
            Lc::constant(f(CAP_MINT_NODE_TAG)),
            Lc::constant(f(level as u64)),
            Lc::zero(),
            Lc::constant(f(POSEIDON2_CONST_IV)),
        ];
        mint_node = compress12_ff_gadget(cs, &left, &right, &tweak);
    }
    enforce_equal4(cs, &mint_node, issuer_root);



    // 3. Presentation nullifier binding `(final_tag, token_id, context_digest)`.
    let mut pres_msg: Vec<Lc> = Vec::with_capacity(13);
    pres_msg.extend_from_slice(&final_tag);
    pres_msg.extend_from_slice(&token_id);
    pres_msg.extend_from_slice(ctx_digest);
    pres_msg.push(Lc::constant(f(CAP_PRESENT_TAG_DOM)));
    let computed_pres = first4_lc(&sponge12(cs, &pres_msg));
    enforce_equal4(cs, &computed_pres, want_pres_tag);

    // 4. `SortedRevocationTree` adjacent-leaf interval non-membership:
    //    `idx_hi == idx_lo + 1 < 2^D`, both authenticate to `revocation_root`, and
    //    `revoked_lo < token_id < revoked_hi`.
    let (idx_lo_bits, idx_hi_bits) =
        adjacent_index_bits(cs, slot.rev_left_index, params.revocation_depth);

    let revoked_lo = alloc4(cs, &slot.revoked_lo);
    let revoked_hi = alloc4(cs, &slot.revoked_hi);
    let lo_halves = canonical_digest_halves8(cs, &revoked_lo);
    let hi_halves = canonical_digest_halves8(cs, &revoked_hi);

    let one = Lc::constant(F::ONE);
    enforce_gated_cmp_limbs32(cs, &one, &lo_halves, &token_halves, false);
    enforce_gated_cmp_limbs32(cs, &one, &token_halves, &hi_halves, false);

    let check_rev_path = |cs: &mut ConstraintSystem,
                          leaf_key: &[Lc; 4],
                          idx_bits: &[Lc],
                          siblings: &[Digest]| {
        let mut leaf_msg: Vec<Lc> = Vec::with_capacity(5);
        leaf_msg.extend_from_slice(leaf_key);
        leaf_msg.push(Lc::constant(f(REV_LEAF_TAG)));
        let mut node = first4_lc(&sponge12(cs, &leaf_msg));
        for (level, bit) in idx_bits.iter().enumerate() {
            let sib = alloc4(cs, &siblings[level]);
            let left = select4(cs, bit, &sib, &node);
            let right: [Lc; 4] = core::array::from_fn(|i| node[i].plus(&sib[i]).minus(&left[i]));
            let tweak = [
                Lc::constant(f(REV_NODE_TAG)),
                Lc::constant(f(level as u64)),
                rev_epoch_lo32.clone(),
                rev_epoch_hi32.plus_const(f(POSEIDON2_CONST_IV)),
            ];
            node = compress12_ff_gadget(cs, &left, &right, &tweak);
        }
        enforce_equal4(cs, &node, revocation_root);
    };
    check_rev_path(cs, &revoked_lo, &idx_lo_bits, &slot.path_lo);
    check_rev_path(cs, &revoked_hi, &idx_hi_bits, &slot.path_hi);

    token_halves
}

fn populate(
    cs: &mut ConstraintSystem,
    params: CapabilityParams,
    statement: &CapabilityBatchStatement,
    context: &[u8],
    slots: &[CapSlot],
) {
    assert_eq!(slots.len(), params.batch_size);
    assert_eq!(statement.presentation_tags.len(), params.batch_size);

    let pub_lcs: Vec<Lc> = public_inputs_vec(statement, context)
        .into_iter()
        .map(|v| cs.public_input(v).into())
        .collect();

    let issuer_root: [Lc; 4] = core::array::from_fn(|i| pub_lcs[i].clone());
    let revocation_root: [Lc; 4] = core::array::from_fn(|i| pub_lcs[4 + i].clone());
    let rev_epoch_lo32 = &pub_lcs[8];
    let rev_epoch_hi32 = &pub_lcs[9];
    let req_audience: [Lc; 4] = core::array::from_fn(|i| pub_lcs[10 + i].clone());
    let req_resource: [Lc; 4] = core::array::from_fn(|i| pub_lcs[14 + i].clone());
    let req_actions_bits = &pub_lcs[18..82];
    let req_amount_limbs32: [Lc; 4] = core::array::from_fn(|i| pub_lcs[82 + i].clone());
    let req_now_limbs32: [Lc; 2] = [pub_lcs[86].clone(), pub_lcs[87].clone()];
    let ctx_digest: [Lc; 4] = core::array::from_fn(|i| pub_lcs[88 + i].clone());
    let pres_tags_base = 92;

    let one = Lc::constant(F::ONE);
    let mut prev_token_halves: Option<[Lc; 8]> = None;
    for (b, slot) in slots.iter().enumerate() {
        let want_pres: [Lc; 4] =
            core::array::from_fn(|i| pub_lcs[pres_tags_base + 4 * b + i].clone());
        let token_halves = slot_gadget(
            cs,
            params,
            slot,
            &issuer_root,
            &revocation_root,
            rev_epoch_lo32,
            rev_epoch_hi32,
            &req_audience,
            &req_resource,
            req_actions_bits,
            &req_amount_limbs32,
            &req_now_limbs32,
            &ctx_digest,
            &want_pres,
        );
        if let Some(prev) = &prev_token_halves {
            // Strictly increasing `token_id` across slots forbids duplicate capability replay.
            enforce_gated_cmp_limbs32(cs, &one, prev, &token_halves, false);
        }
        prev_token_halves = Some(token_halves);
    }
}

/// Self-delimiting wire wrapper (`b"QSAGCAP1"`) around a hiding [`ZkHemProof`] for [`CapabilityRelation`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ZkCapabilityBatchProof {
    pub proof: ZkHemProof,
}

// Allocation-free framing pass: the shared PCS decoder has absolute vector caps,
// but some vectors reserve before checking the remaining bytes. Keep this wrapper's
// allocation proportional to the supplied wire. Semantic/canonical checks remain in
// the shared decoder. Move this pass into that decoder when its write cone is available.
fn capability_wire_fits(bytes: &[u8], shape: &Shape, regime: WhirSecurityRegime) -> Option<()> {
    fn skip(bytes: &mut &[u8], n: usize) -> Option<()> {
        *bytes = bytes.get(n..)?;
        Some(())
    }
    fn count(bytes: &mut &[u8]) -> Option<usize> {
        let n = u32::from_le_bytes(bytes.get(..4)?.try_into().ok()?) as usize;
        skip(bytes, 4)?;
        Some(n)
    }
    fn vector(bytes: &mut &[u8], width: usize) -> Option<()> {
        let n = count(bytes)?;
        skip(bytes, n.checked_mul(width)?)
    }
    let layout = protocol::Layout::new(shape, regime)?;
    let mut rest = bytes;
    // Commitment, two mask sums, row values, four companion claims, sumchecks.
    let words = 9usize
        .checked_add(shape.log_rows.checked_mul(protocol::ROW_DEGREE + 1)?)?
        .checked_add(layout.var_bits.checked_mul(protocol::COL_DEGREE + 1)?)?;
    skip(&mut rest, 33usize.checked_add(words.checked_mul(32)?)?)?;
    skip(&mut rest, 64)?; // stage-0 OOD evaluations
    let folds = count(&mut rest)?;
    skip(&mut rest, folds.checked_mul(5 * 32 + 8)?)?; // quartic polys + nonces
    let layers = count(&mut rest)?;
    // Each layer consumes at least a commitment, two OOD values and a nonce.
    if layers > rest.len() / (33 + 64 + 8) {
        return None;
    }
    for _ in 0..layers {
        skip(&mut rest, 33 + 64 + 8)?;
        vector(&mut rest, 32)?; // opened Ext4 values
        vector(&mut rest, 32)?; // Merkle siblings
    }
    vector(&mut rest, 32)?; // terminal coefficients
    skip(&mut rest, 8)?; // PoW nonce
    vector(&mut rest, 16)?; // salts
    vector(&mut rest, 8)?; // round-0 base field values
    vector(&mut rest, 32)?; // round-0 Merkle siblings
    rest.is_empty().then_some(())
}

impl ZkCapabilityBatchProof {
    pub fn to_bytes(&self) -> Vec<u8> {
        let inner = self.proof.to_bytes();
        let mut out = Vec::with_capacity(CAPABILITY_WIRE_MAGIC.len() + inner.len());
        out.extend_from_slice(CAPABILITY_WIRE_MAGIC);
        out.extend_from_slice(&inner);
        out
    }

    /// Strict canonical wire decoder; rejects wrong magic, non-canonical limbs, or trailing bytes.
    pub fn from_bytes(
        bytes: &[u8],
        relation: &CapabilityRelation,
        regime: WhirSecurityRegime,
    ) -> Option<Self> {
        if bytes.get(..8)? != CAPABILITY_WIRE_MAGIC {
            return None;
        }
        let inner = bytes.get(8..)?;
        capability_wire_fits(inner, &relation.shape, regime)?;
        let proof = ZkHemProof::from_bytes(inner, &relation.shape, regime)?;
        // Preserve strict wrapper canonicality even if the inner codec evolves.
        if proof.to_bytes() != inner {
            return None;
        }
        Some(Self { proof })
    }
}

/// Precompiled witness-independent `zk-Hem` relation for `(batch_size, max_hops, issuer_depth, revocation_depth)`.
#[derive(Clone, Debug)]
pub struct CapabilityRelation {
    params: CapabilityParams,
    shape: Shape,
}

impl CapabilityRelation {
    pub fn new(params: CapabilityParams) -> Result<Self, CapabilityZkError> {
        if !params.valid() {
            return Err(CapabilityZkError::InvalidParams);
        }
        let dummy_statement = CapabilityBatchStatement {
            issuer_root: [F::ZERO; 4],
            revocation_root: [F::ZERO; 4],
            revocation_epoch: 0,
            request: CapabilityRequest {
                audience: [F::ZERO; 4],
                resource: [F::ZERO; 4],
                actions: 0,
                amount: 0,
                now: 0,
            },
            presentation_tags: vec![[F::ZERO; 4]; params.batch_size],
        };
        let slots = vec![CapSlot::placeholder(params); params.batch_size];
        let mut cs = ConstraintSystem::new();
        populate(&mut cs, params, &dummy_statement, b"", &slots);
        let (shape, mut z) = cs.finish();
        qsag_asm::volatile_fill(&mut z, F::ZERO);
        Ok(Self { params, shape })
    }

    #[inline]
    pub fn params(&self) -> CapabilityParams {
        self.params
    }

    #[inline]
    pub fn shape(&self) -> &Shape {
        &self.shape
    }

    fn statement_bytes(&self, context: &[u8]) -> Vec<u8> {
        let mut out = b"QSAG.ZKHEM.CAPABILITY.BATCH/v1".to_vec();
        out.extend_from_slice(CAPABILITY_WIRE_MAGIC);
        // Relation revision 2 enrolls the exact policy and requires reissuance.
        out.extend_from_slice(&2u32.to_le_bytes());
        for n in [
            self.params.batch_size as u64,
            self.params.max_hops as u64,
            self.params.issuer_depth as u64,
            self.params.revocation_depth as u64,
            context.len() as u64,
        ] {
            out.extend_from_slice(&n.to_le_bytes());
        }
        out.extend_from_slice(context);
        out
    }

    fn validate_and_build_slots(
        &self,
        statement: &CapabilityBatchStatement,
        inputs: &[CapabilityPresentationInput],
        context: &[u8],
    ) -> Result<Vec<CapSlot>, CapabilityZkError> {
        if inputs.len() != self.params.batch_size
            || statement.presentation_tags.len() != self.params.batch_size
        {
            return Err(CapabilityZkError::BatchLengthMismatch);
        }
        for pair in inputs.windows(2) {
            if cmp_token_id(pair[0].capability.token_id(), pair[1].capability.token_id())
                != Ordering::Less
            {
                return Err(CapabilityZkError::UnsortedOrDuplicateBatch);
            }
        }
        let ctx = context_digest(context);
        let mut slots = Vec::with_capacity(self.params.batch_size);
        for (item, want_pres) in inputs.iter().zip(&statement.presentation_tags) {
            item.capability.verify_native(&statement.request)?;
            let got_pres = compute_presentation_tag(
                &item.capability.final_tag,
                &item.capability.token_id,
                &ctx,
            );
            if got_pres != *want_pres {
                return Err(CapabilityZkError::StatementMismatch);
            }
            // Verify issuer directory path natively.
            if item.issuer_index >= (1usize << self.params.issuer_depth)
                || item.issuer_siblings.len() != self.params.issuer_depth
            {
                return Err(CapabilityZkError::InvalidIssuerOpening);
            }
            let mut mint_node = item.capability.mint_leaf();
            for (level, sib) in item.issuer_siblings.iter().enumerate() {
                let (l, r) = if ((item.issuer_index >> level) & 1) == 1 {
                    (sib, &mint_node)
                } else {
                    (&mint_node, sib)
                };
                mint_node = mint_node_native(l, r, level);
            }
            if mint_node != statement.issuer_root {
                return Err(CapabilityZkError::InvalidIssuerOpening);
            }

            // Verify SortedRevocationTree non-membership natively.
            let nm = &item.non_membership;
            if nm.left_index >= (1usize << self.params.revocation_depth) - 1
                || nm.path_lo.len() != self.params.revocation_depth
                || nm.path_hi.len() != self.params.revocation_depth
                || cmp_token_id(&nm.revoked_lo, item.capability.token_id()) != Ordering::Less
                || cmp_token_id(item.capability.token_id(), &nm.revoked_hi) != Ordering::Less
            {
                return Err(CapabilityZkError::InvalidRevocationWitness);
            }
            for (idx, key, path) in [
                (nm.left_index, &nm.revoked_lo, &nm.path_lo),
                (nm.left_index + 1, &nm.revoked_hi, &nm.path_hi),
            ] {
                let mut node = rev_leaf_native(key);
                for (level, sib) in path.iter().enumerate() {
                    let (l, r) = if ((idx >> level) & 1) == 1 {
                        (sib, &node)
                    } else {
                        (&node, sib)
                    };
                    node = rev_node_native(l, r, level, statement.revocation_epoch);
                }
                if node != statement.revocation_root {
                    return Err(CapabilityZkError::InvalidRevocationWitness);
                }
            }

            slots.push(CapSlot::from_input(self.params, item)?);
        }
        Ok(slots)
    }

    /// Prove a batch of capabilities (`inputs` sorted in strictly ascending order of `token_id`).
    pub fn prove(
        &self,
        statement: &CapabilityBatchStatement,
        inputs: &[CapabilityPresentationInput],
        context: &[u8],
        regime: WhirSecurityRegime,
        seed: &[u8; 32],
    ) -> Result<ZkCapabilityBatchProof, CapabilityZkError> {
        let slots = self.validate_and_build_slots(statement, inputs, context)?;
        let mut cs = ConstraintSystem::witness_only();
        populate(&mut cs, self.params, statement, context, &slots);
        let assignment = cs
            .finish_assignment(&self.shape)
            .ok_or(CapabilityZkError::InvalidParams)?;
        let proof = protocol::prove(
            &self.shape,
            assignment,
            &self.statement_bytes(context),
            regime,
            seed,
        )
        .map_err(CapabilityZkError::Proof)?;
        Ok(ZkCapabilityBatchProof { proof })
    }

    /// Verify a batched capability + non-revocation proof against `statement` and `context`.
    pub fn verify(
        &self,
        statement: &CapabilityBatchStatement,
        context: &[u8],
        regime: WhirSecurityRegime,
        proof: &ZkCapabilityBatchProof,
    ) -> bool {
        if statement.presentation_tags.len() != self.params.batch_size {
            return false;
        }
        protocol::verify(
            &self.shape,
            &public_inputs_vec(statement, context),
            &self.statement_bytes(context),
            regime,
            &proof.proof,
        )
    }
}

#[cfg(all(test, feature = "std"))]
mod tests {
    use super::*;

    fn id(w0: u64, w1: u64, w2: u64, w3: u64) -> TokenId {
        [f(w0), f(w1), f(w2), f(w3)]
    }

    struct BatchFixture {
        params: CapabilityParams,
        relation: CapabilityRelation,
        rev_tree: SortedRevocationTree,
        statement: CapabilityBatchStatement,
        inputs: Vec<CapabilityPresentationInput>,
    }

    fn build_fixture(batch_size: usize, max_hops: usize, iss_d: usize, rev_d: usize) -> BatchFixture {
        let params = CapabilityParams {
            batch_size,
            max_hops,
            issuer_depth: iss_d,
            revocation_depth: rev_d,
        };
        let relation = CapabilityRelation::new(params).unwrap();
        let issuer_key = [
            f(0x0A11_CE01),
            f(0x0A11_CE02),
            f(0x0A11_CE03),
            f(0x0A11_CE04),
        ];
        let audience = [f(10), f(20), f(30), f(40)];
        let resource = [f(901), f(902), f(903), f(904)];
        let request = CapabilityRequest {
            audience,
            resource,
            actions: 0b0011,
            amount: 500,
            now: 1_700_000_000,
        };

        // Revoked tokens bracket every honest token in the sorted tree.
        let revoked = vec![
            id(0, 0, 0, 100),
            id(0, 0, 0, 250),
            id(0, 0, 0, 500),
            id(0, 0, 1, 10),
        ];
        let rev_tree = SortedRevocationTree::new(rev_d, 42, &revoked).unwrap();

        let mut caps = Vec::with_capacity(batch_size);
        let mut mint_leaves = Vec::with_capacity(batch_size + 2);
        mint_leaves.push([f(77); 4]); // padding distractor leaf at index 0
        for b in 0..batch_size {
            let tid = id(0, 0, 0, 110 + (b as u64) * 7);
            assert!(!rev_tree.is_revoked(&tid));
            let mut cap = BearerCapability::issue(&issuer_key, tid, audience).unwrap();
            cap.attenuate(CapCaveat::Resource(resource)).unwrap();
            cap.attenuate(CapCaveat::NotBefore(1_600_000_000)).unwrap();
            if max_hops >= 3 {
                cap.attenuate(CapCaveat::ExpiresAt(1_800_000_000)).unwrap();
            }
            if max_hops >= 4 {
                cap.attenuate(CapCaveat::Actions(0b0111)).unwrap();
            }
            if max_hops >= 5 {
                cap.attenuate(CapCaveat::MaxAmount(1_000 + b as u128)).unwrap();
            }
            mint_leaves.push(cap.mint_leaf());
            caps.push((1 + b, cap));
        }

        let directory = CapabilityIssuerDirectory::new(iss_d, &mint_leaves).unwrap();
        let mut inputs: Vec<CapabilityPresentationInput> = caps
            .into_iter()
            .map(|(iss_idx, cap)| {
                let nm = rev_tree.prove_non_membership(cap.token_id()).unwrap();
                assert!(rev_tree.verify_non_membership_native(cap.token_id(), &nm));
                CapabilityPresentationInput {
                    issuer_index: iss_idx,
                    issuer_siblings: directory.opening(iss_idx).unwrap(),
                    capability: cap,
                    non_membership: nm,
                }
            })
            .collect();

        let statement = CapabilityBatchStatement::prepare_sorted(
            directory.root(),
            rev_tree.root(),
            rev_tree.epoch(),
            request,
            &mut inputs,
            b"challenge-ctx-v1",
        )
        .unwrap();

        BatchFixture {
            params,
            relation,
            rev_tree,
            statement,
            inputs,
        }
    }

    fn synthesize_raw(
        params: CapabilityParams,
        statement: &CapabilityBatchStatement,
        context: &[u8],
        slots: &[CapSlot],
    ) -> (Shape, Vec<F>) {
        let mut cs = ConstraintSystem::new();
        populate(&mut cs, params, statement, context, slots);
        cs.finish()
    }

    fn set_bit(z: &mut [F], bit: &Lc, value: F) {
        assert_eq!(bit.terms().len(), 1);
        let (index, coeff) = bit.terms()[0];
        assert_eq!(coeff, F::ONE);
        z[index as usize] = value;
    }

    #[test]
    fn canonical_decomposition_rejects_mod_p_aliases_and_non_boolean_bits() {
        for raw in [GOLDILOCKS_PRIME, GOLDILOCKS_PRIME + 1, u64::MAX] {
            let mut cs = ConstraintSystem::new();
            let value: Lc = cs.alloc(f(raw)).into();
            let (bits, _, _) = canonical_bits_and_halves32(&mut cs, &value);
            let after_products = cs.alloc(F::ZERO).index();
            let (shape, mut z) = cs.finish();
            assert!(shape.is_satisfied(&z));
            for (i, bit) in bits.iter().enumerate() {
                set_bit(&mut z, bit, f((raw >> i) & 1));
            }
            // Recompute every high-ones multiplication as a malicious prover would;
            // these aliases must fail the canonicality row, not stale intermediates.
            z[after_products - 31..after_products].fill(F::ONE);
            assert!(!shape.is_satisfied(&z), "alias {raw}");
        }
        let mut cs = ConstraintSystem::new();
        let (bits, _, _) = canonical_bits_and_halves32(&mut cs, &Lc::constant(f(2)));
        let (shape, mut z) = cs.finish();
        set_bit(&mut z, &bits[0], f(2));
        set_bit(&mut z, &bits[1], F::ZERO); // packing still equals 2
        assert!(!shape.is_satisfied(&z));
    }

    #[test]
    fn comparator_rejects_bit_flips_multiple_winners_and_non_boolean_gate() {
        let mut cs = ConstraintSystem::new();
        let gate: Lc = cs.alloc(F::ONE).into();
        let a = [Lc::zero(), Lc::zero()];
        let b = [Lc::zero(), Lc::constant(f(2))];
        enforce_gated_cmp_limbs32(&mut cs, &gate, &a, &b, false);
        let (shape, z) = cs.finish();
        assert!(shape.is_satisfied(&z));
        for index in 1..shape.mask_var_base {
            let mut forged = z.clone();
            forged[index] += F::ONE;
            assert!(!shape.is_satisfied(&forged), "unbound comparator cell {index}");
        }
        let mut forged = z;
        forged[1] = f(2); // gate
        forged[2] = F::ONE; // win[0]
        forged[3] = F::ONE; // win[1]
        forged[4] = F::ZERO - F::ONE; // win[0] * (b[0] - a[0] - 1)
        forged[5] = F::ONE; // win[1] * (b[1] - a[1] - 1)
        forged[6..38].fill(F::ZERO); // sum of differences is zero
        assert!(!shape.is_satisfied(&forged)); // only gate Booleanity blocks this

        for allow_eq in [false, true] {
            for gate in [0, 1] {
                for (a, b) in [(0, 0), (0, u32::MAX), (u32::MAX, 0), (7, 8)] {
                    let mut cs = ConstraintSystem::new();
                    enforce_gated_cmp_limbs32(&mut cs, &Lc::constant(f(gate)),
                        &[Lc::constant(f(a as u64))], &[Lc::constant(f(b as u64))], allow_eq);
                    let (shape, z) = cs.finish();
                    assert_eq!(shape.is_satisfied(&z), gate == 0 || a < b || (allow_eq && a == b));
                }
            }
        }
    }

    #[test]
    fn adjacent_indices_reject_nonadjacency_wraparound_and_native_overflow() {
        for left in [0, 2, 6, 7] {
            let mut cs = ConstraintSystem::new();
            let (_, hi) = adjacent_index_bits(&mut cs, left, 3);
            let (shape, z) = cs.finish();
            assert_eq!(shape.is_satisfied(&z), left < 7);
            for right in 0..8 {
                let mut forged = z.clone();
                for (i, bit) in hi.iter().enumerate() {
                    set_bit(&mut forged, bit, f((right >> i) & 1));
                }
                assert_eq!(shape.is_satisfied(&forged), right == (left + 1) as u64);
            }
        }
        let fx = build_fixture(1, 2, 2, 3);
        for index in [usize::MAX, (1 << 3) - 1] {
            let mut inputs = fx.inputs.clone();
            inputs[0].non_membership.left_index = index;
            assert!(!fx.rev_tree.verify_non_membership_native(
                inputs[0].capability.token_id(), &inputs[0].non_membership));
            assert!(CapSlot::from_input(fx.params, &inputs[0]).is_err());
            assert!(fx.relation.validate_and_build_slots(&fx.statement, &inputs, b"challenge-ctx-v1").is_err());
        }
        for depth in [0, 21, usize::MAX] {
            assert!(SortedRevocationTree::new(depth, 0, &[]).is_err());
        }
        for sentinel in [SENTINEL_MIN_ID, SENTINEL_MAX_ID] {
            assert!(SortedRevocationTree::new(2, 0, &[sentinel]).is_err());
        }
        assert!(SortedRevocationTree::new(1, 0, &[id(0, 0, 0, 1)]).is_err());
        let empty = SortedRevocationTree::new(1, u64::MAX, &[]).unwrap();
        assert!(!empty.is_revoked(&id(0, 0, 0, 1)));
        for size in [0, MAX_CAP_BATCH + 1] {
            assert!(CapabilityRelation::new(CapabilityParams { batch_size: size, ..fx.params }).is_err());
        }
    }

    #[test]
    fn stripping_and_retagging_caveats_cannot_open_enrolled_policy() {
        let fx = build_fixture(1, 5, 2, 3);
        for keep in 0..5 {
            let mut forged = fx.inputs.clone();
            let cap = &mut forged[0].capability;
            cap.caveats.truncate(keep);
            cap.final_tag = cap.root_tag;
            for (hop, caveat) in cap.caveats.iter().enumerate() {
                cap.final_tag = chain_step_native(&cap.final_tag, caveat, hop);
            }
            // The attacker can choose a matching presentation: this passed the old relation.
            cap.verify_native(&fx.statement.request).unwrap();
            let statement = CapabilityBatchStatement::prepare_sorted(
                fx.statement.issuer_root, fx.statement.revocation_root, fx.statement.revocation_epoch,
                fx.statement.request, &mut forged, b"challenge-ctx-v1").unwrap();
            assert_eq!(fx.relation.validate_and_build_slots(&statement, &forged, b"challenge-ctx-v1").err(),
                Some(CapabilityZkError::InvalidIssuerOpening));
            let slots = [CapSlot::from_input(fx.params, &forged[0]).unwrap()];
            let (shape, z) = synthesize_raw(fx.params, &statement, b"challenge-ctx-v1", &slots);
            assert!(!shape.is_satisfied(&z));
        }
        let mut cap = BearerCapability::issue(&[f(9); 4], id(0, 0, 0, 1), [f(3); 4]).unwrap();
        let ancestor = cap.clone();
        cap.attenuate(CapCaveat::Actions(1)).unwrap();
        assert_ne!(ancestor.root_tag, cap.root_tag);
        assert_ne!(ancestor.mint_leaf(), cap.mint_leaf());
        cap.caveats.clear();
        cap.final_tag = cap.root_tag;
        assert_ne!(ancestor.mint_leaf(), cap.mint_leaf());
    }

    fn check_caveat_boundary(caveat: CapCaveat, request: CapabilityRequest) {
        let params = CapabilityParams { batch_size: 1, max_hops: 2, issuer_depth: 1, revocation_depth: 1 };
        let mut cap = BearerCapability::issue(&[f(9); 4], id(0, 0, 0, 1), request.audience).unwrap();
        cap.attenuate(caveat).unwrap();
        let directory = CapabilityIssuerDirectory::new(1, &[cap.mint_leaf()]).unwrap();
        let tree = SortedRevocationTree::new(1, 0, &[]).unwrap();
        let nm = tree.prove_non_membership(cap.token_id()).unwrap();
        let mut inputs = [CapabilityPresentationInput { capability: cap, issuer_index: 0,
            issuer_siblings: directory.opening(0).unwrap(), non_membership: nm }];
        let statement = CapabilityBatchStatement::prepare_sorted(directory.root(), tree.root(), 0,
            request, &mut inputs, b"boundary").unwrap();
        let mut slots = [CapSlot::from_input(params, &inputs[0]).unwrap()];
        // An inactive hop may contain any canonical payload, including values > 2^32.
        slots[0].hops[1].payload = SENTINEL_MAX_ID;
        let (shape, z) = synthesize_raw(params, &statement, b"boundary", &slots);
        assert_eq!(shape.is_satisfied(&z), caveat.allows(&request), "{caveat:?}, {request:?}");
    }

    #[test]
    fn caveat_integer_boundaries_actions_and_inactive_hops() {
        let mut req = CapabilityRequest { audience: [f(3); 4], resource: [f(4); 4], actions: 0, amount: 0, now: 0 };
        for max in [0, (1u128 << 32) - 1, 1u128 << 32, 1u128 << 64, 1u128 << 96, u128::MAX] {
            for amount in [max.saturating_sub(1), max, max.saturating_add(1), u128::MAX] {
                req.amount = amount;
                check_caveat_boundary(CapCaveat::MaxAmount(max), req);
            }
        }
        for bound in [0, 1u64 << 32, GOLDILOCKS_PRIME, u64::MAX] {
            for now in [bound.saturating_sub(1), bound, bound.saturating_add(1)] {
                req.now = now;
                check_caveat_boundary(CapCaveat::ExpiresAt(bound), req);
                check_caveat_boundary(CapCaveat::NotBefore(bound), req);
            }
        }
        for allowed in [0, 1, 1u64 << 32, 1u64 << 63, u64::MAX] {
            for actions in [allowed, !allowed, u64::MAX] {
                req.actions = actions;
                check_caveat_boundary(CapCaveat::Actions(allowed), req);
            }
        }
        check_caveat_boundary(CapCaveat::Resource(req.resource), req);
        check_caveat_boundary(CapCaveat::Resource([F::ZERO; 4]), req);
    }

    #[test]
    fn zero_through_eight_hops_and_overlong_attenuation() {
        let params = CapabilityParams { batch_size: 1, max_hops: MAX_CAP_HOPS,
            issuer_depth: 1, revocation_depth: 1 };
        let relation = CapabilityRelation::new(params).unwrap();
        let request = CapabilityRequest { audience: [f(3); 4], resource: [f(4); 4],
            actions: 1, amount: u128::MAX, now: u64::MAX };
        let tree = SortedRevocationTree::new(1, 0, &[]).unwrap();
        let mut cap = BearerCapability::issue(&[f(9); 4], id(0, 0, 0, 1), request.audience).unwrap();
        for hops in 0..=MAX_CAP_HOPS {
            let directory = CapabilityIssuerDirectory::new(1, &[cap.mint_leaf()]).unwrap();
            let mut inputs = [CapabilityPresentationInput { capability: cap.clone(), issuer_index: 0,
                issuer_siblings: directory.opening(0).unwrap(),
                non_membership: tree.prove_non_membership(cap.token_id()).unwrap() }];
            let statement = CapabilityBatchStatement::prepare_sorted(directory.root(), tree.root(), 0,
                request, &mut inputs, b"hops").unwrap();
            let slots = relation.validate_and_build_slots(&statement, &inputs, b"hops").unwrap();
            let (shape, z) = synthesize_raw(params, &statement, b"hops", &slots);
            assert_eq!(&shape, relation.shape());
            assert!(shape.is_satisfied(&z));
            if hops < MAX_CAP_HOPS { cap.attenuate(CapCaveat::Actions(1)).unwrap(); }
        }
        let saved = cap.clone();
        assert_eq!(cap.attenuate(CapCaveat::Actions(0)), Err(CapabilityZkError::TooManyCaveats));
        assert_eq!(cap, saved);
    }

    #[test]
    fn raw_numeric_payload_overflow_is_rejected_even_with_matching_enrollment() {
        let params = CapabilityParams { batch_size: 1, max_hops: 1, issuer_depth: 1, revocation_depth: 1 };
        let request = CapabilityRequest { audience: [f(3); 4], resource: [f(4); 4], actions: 0, amount: 0, now: 0 };
        let tree = SortedRevocationTree::new(1, 0, &[]).unwrap();
        // Commit to a deliberately malformed numeric payload, so enrollment and tag
        // constraints succeed; only the numeric range constraints can reject it.
        for kind in [1, 2, 4, 5] {
            let mut slot = CapSlot::placeholder(params);
            slot.root_tag = [f(9); 4];
            slot.hops[0] = HopSlot { active: true, kind, payload: [f(1u64 << 32), F::ZERO, F::ZERO, F::ZERO] };
            if kind == 1 { slot.hops[0].payload[1] = F::ONE; }
            slot.final_tag = chain_step_raw_native(&slot.root_tag, kind, &slot.hops[0].payload, 0);
            let mut msg = slot.root_tag.to_vec();
            msg.extend_from_slice(&slot.final_tag);
            msg.extend_from_slice(&[F::ONE, f(CAP_MINT_LEAF_TAG)]);
            let enrollment = first4(sponge12_native(&msg));
            let leaf = compute_mint_leaf(&slot.token_id, &request.audience, &enrollment);
            let directory = CapabilityIssuerDirectory::new(1, &[leaf]).unwrap();
            slot.issuer_siblings = directory.opening(0).unwrap();
            let nm = tree.prove_non_membership(&slot.token_id).unwrap();
            slot.path_lo = nm.path_lo.clone();
            slot.path_hi = nm.path_hi.clone();
            let statement = CapabilityBatchStatement { issuer_root: directory.root(), revocation_root: tree.root(),
                revocation_epoch: 0, request, presentation_tags: vec![compute_presentation_tag(
                    &slot.final_tag, &slot.token_id, &context_digest(b"range"))] };
            let (shape, z) = synthesize_raw(params, &statement, b"range", &[slot]);
            assert!(!shape.is_satisfied(&z), "kind {kind}");
        }
    }

    #[test]
    fn sorted_revocation_tree_proves_absent_and_rejects_revoked_and_sentinels() {
        let r0 = id(0, 0, 0, 50);
        let r1 = id(0, 0, 5, 0);
        let r2 = id(1, 0, 0, 0);
        let tree = SortedRevocationTree::new(4, 9, &[r2, r0, r1, r0]).unwrap();
        assert_eq!(tree.revoked_count(), 3);

        for revoked in [SENTINEL_MIN_ID, r0, r1, r2, SENTINEL_MAX_ID] {
            assert!(tree.is_revoked(&revoked));
            assert!(tree.prove_non_membership(&revoked).is_err());
        }

        for absent in [
            id(0, 0, 0, 1),
            id(0, 0, 0, 49),
            id(0, 0, 0, 51),
            id(0, 0, 4, u64::MAX - (1u64 << 32)),
            id(2, 0, 0, 0),
        ] {
            assert!(!tree.is_revoked(&absent));
            let w = tree.prove_non_membership(&absent).unwrap();
            assert!(tree.verify_non_membership_native(&absent, &w));
            assert!(!tree.verify_non_membership_native(&w.revoked_lo, &w));
            assert!(!tree.verify_non_membership_native(&w.revoked_hi, &w));
        }
    }

    #[test]
    fn circuit_rejects_revoked_token_equal_to_lo_or_hi_and_tampered_caveat_chains() {
        let fx = build_fixture(2, 5, 4, 5);
        let honest_slots: Vec<CapSlot> = fx
            .inputs
            .iter()
            .map(|inp| CapSlot::from_input(fx.params, inp).unwrap())
            .collect();
        let (shape, z) = synthesize_raw(fx.params, &fx.statement, b"challenge-ctx-v1", &honest_slots);
        assert_eq!(&shape, fx.relation.shape());
        assert!(shape.is_satisfied(&z));

        // 1. Revoked boundary attack (`token_id == revoked_lo` or `token_id == revoked_hi`):
        //    even if a cheating prover witnesses an issuer-enrolled capability whose `token_id`
        //    equals `revoked_lo`, the strict `<` gadget in `Shape` must reject!
        let mut eq_lo = honest_slots.clone();
        eq_lo[0].revoked_lo = eq_lo[0].token_id;
        let (s_bad, z_bad) = synthesize_raw(fx.params, &fx.statement, b"challenge-ctx-v1", &eq_lo);
        assert_eq!(&s_bad, fx.relation.shape());
        assert!(!s_bad.is_satisfied(&z_bad));

        let mut swapped = honest_slots.clone();
        let lo = swapped[0].revoked_lo;
        swapped[0].revoked_lo = swapped[0].revoked_hi;
        swapped[0].revoked_hi = lo;
        let (_, bad) = synthesize_raw(fx.params, &fx.statement, b"challenge-ctx-v1", &swapped);
        assert!(!shape.is_satisfied(&bad));
        let mut wrong_path = honest_slots.clone();
        wrong_path[0].path_hi[0][0] += F::ONE;
        let (_, bad) = synthesize_raw(fx.params, &fx.statement, b"challenge-ctx-v1", &wrong_path);
        assert!(!shape.is_satisfied(&bad));

        let mut eq_hi = honest_slots.clone();
        eq_hi[0].revoked_hi = eq_hi[0].token_id;
        let (_, z_bad) = synthesize_raw(fx.params, &fx.statement, b"challenge-ctx-v1", &eq_hi);
        assert!(!shape.is_satisfied(&z_bad));

        //Also check high-level API refusal when `token_id` is in `SortedRevocationTree`:
        assert!(fx.rev_tree.is_revoked(&id(0, 0, 0, 100)));
        assert_eq!(
            fx.rev_tree.prove_non_membership(&id(0, 0, 0, 100)).unwrap_err(),
            CapabilityZkError::TokenRevoked
        );
        let mut tampered_nm = fx.inputs.clone();
        tampered_nm[0].non_membership.revoked_lo = *tampered_nm[0].capability.token_id();
        assert_eq!(
            fx.relation
                .prove(
                    &fx.statement,
                    &tampered_nm,
                    b"challenge-ctx-v1",
                    WhirSecurityRegime::Poseidon2Cdhz25ZeroPowQrom128,
                    &[7; 32],
                )
                .unwrap_err(),
            CapabilityZkError::InvalidRevocationWitness
        );

        // 2. Tampered caveat chain: dropping or altering an intermediate caveat breaks `cur_tag == final_tag`.
        let mut dropped_caveat = honest_slots.clone();
        dropped_caveat[0].hops[2].active = false;
        dropped_caveat[0].hops[2].kind = 0;
        dropped_caveat[0].hops[2].payload = [F::ZERO; 4];
        dropped_caveat[0].hops[3].active = false;
        dropped_caveat[0].hops[3].kind = 0;
        dropped_caveat[0].hops[4].active = false;
        dropped_caveat[0].hops[4].kind = 0;
        let (_, z_bad) =
            synthesize_raw(fx.params, &fx.statement, b"challenge-ctx-v1", &dropped_caveat);
        assert!(!shape.is_satisfied(&z_bad));

        let mut bad_chain_input = fx.inputs.clone();
        bad_chain_input[0].capability.caveats[0] = CapCaveat::ExpiresAt(u64::MAX);
        assert_eq!(
            fx.relation
                .prove(
                    &fx.statement,
                    &bad_chain_input,
                    b"challenge-ctx-v1",
                    WhirSecurityRegime::Poseidon2Cdhz25ZeroPowQrom128,
                    &[7; 32],
                )
                .unwrap_err(),
            CapabilityZkError::InvalidTag
        );

        // 3. Expired / exceeded-amount / disallowed-action request is rejected both natively and in-circuit.
        let mut expired_stmt = fx.statement.clone();
        expired_stmt.request.now = 1_800_000_000; // `ExpiresAt(1_800_000_000)` requires strict `now < t`!
        let (_, z_bad) =
            synthesize_raw(fx.params, &expired_stmt, b"challenge-ctx-v1", &honest_slots);
        assert!(!shape.is_satisfied(&z_bad));

        let mut over_amt = fx.statement.clone();
        over_amt.request.amount = 1_001; // slot 0 has `MaxAmount(1_000)`!
        let (_, z_bad) = synthesize_raw(fx.params, &over_amt, b"challenge-ctx-v1", &honest_slots);
        assert!(!shape.is_satisfied(&z_bad));

        let mut bad_act = fx.statement.clone();
        bad_act.request.actions = 0b1001; // bit 3 not in `0b0111`!
        let (_, z_bad) = synthesize_raw(fx.params, &bad_act, b"challenge-ctx-v1", &honest_slots);
        assert!(!shape.is_satisfied(&z_bad));

        // 4. Duplicate capability in batch (`token_id[0] == token_id[1]`) is rejected in-circuit.
        let dup_slots = vec![honest_slots[0].clone(), honest_slots[0].clone()];
        let mut dup_stmt = fx.statement.clone();
        dup_stmt.presentation_tags[1] = dup_stmt.presentation_tags[0];
        let (_, z_bad) = synthesize_raw(fx.params, &dup_stmt, b"challenge-ctx-v1", &dup_slots);
        assert!(!shape.is_satisfied(&z_bad));
    }

    #[test]
    fn batched_capability_proof_roundtrips_and_verifies() {
        let regime = WhirSecurityRegime::Poseidon2Cdhz25JohnsonQrom128;
        let fx = build_fixture(2, 5, 6, 8);
        let proof = fx
            .relation
            .prove(&fx.statement, &fx.inputs, b"challenge-ctx-v1", regime, &[33; 32])
            .unwrap();
        let bytes = proof.to_bytes();
        let decoded = ZkCapabilityBatchProof::from_bytes(&bytes, &fx.relation, regime).unwrap();
        assert_eq!(decoded, proof);
        assert_eq!(decoded.to_bytes(), bytes);
        assert!(fx.relation.verify(&fx.statement, b"challenge-ctx-v1", regime, &decoded));

        // Trailing byte and wrong magic are rejected.
        let mut trailing = bytes.clone();
        trailing.push(0);
        assert!(ZkCapabilityBatchProof::from_bytes(&trailing, &fx.relation, regime).is_none());
        for cut in (0..bytes.len()).step_by(997).chain([bytes.len() - 1]) {
            assert!(ZkCapabilityBatchProof::from_bytes(&bytes[..cut], &fx.relation, regime).is_none());
        }
        for word in [GOLDILOCKS_PRIME, GOLDILOCKS_PRIME + 1, u64::MAX] {
            let mut alias = bytes.clone();
            alias[41..49].copy_from_slice(&word.to_le_bytes()); // first Ext4 limb
            assert!(ZkCapabilityBatchProof::from_bytes(&alias, &fx.relation, regime).is_none());
        }
        let layout = protocol::Layout::new(fx.relation.shape(), regime).unwrap();
        let fold_count = 8 + 33 + 32 * (9 + fx.relation.shape().log_rows * (protocol::ROW_DEGREE + 1)
            + layout.var_bits * (protocol::COL_DEGREE + 1)) + 64;
        let mut huge_count = bytes[..fold_count + 4].to_vec();
        huge_count[fold_count..].copy_from_slice(&u32::MAX.to_le_bytes());
        assert!(ZkCapabilityBatchProof::from_bytes(&huge_count, &fx.relation, regime).is_none());
        let mut tampered = bytes.clone();
        tampered[8] ^= 1; // canonical commitment mutation must fail verification
        let tampered = ZkCapabilityBatchProof::from_bytes(&tampered, &fx.relation, regime).unwrap();
        assert!(!fx.relation.verify(&fx.statement, b"challenge-ctx-v1", regime, &tampered));
        let mut wrong_magic = bytes;
        wrong_magic[7] ^= 1;
        assert!(ZkCapabilityBatchProof::from_bytes(&wrong_magic, &fx.relation, regime).is_none());

        // Every public statement component is bound, including full-width integers.
        for component in 0..8 {
            let mut changed = fx.statement.clone();
            match component {
                0 => changed.issuer_root[0] += F::ONE,
                1 => changed.request.audience[0] += F::ONE,
                2 => changed.request.resource[0] += F::ONE,
                3 => changed.request.actions ^= 1u64 << 63,
                4 => changed.request.amount ^= 1u128 << 127,
                5 => changed.request.now ^= 1u64 << 63,
                6 => changed.revocation_epoch ^= 1u64 << 63,
                _ => changed.presentation_tags.swap(0, 1),
            }
            assert!(!fx.relation.verify(&changed, b"challenge-ctx-v1", regime, &decoded));
        }
        // Statement and context mutations fail verification.
        assert!(!fx.relation.verify(&fx.statement, b"challenge-ctx-v2", regime, &decoded));
        let mut wrong_rev = fx.statement.clone();
        wrong_rev.revocation_root[0] += F::ONE;
        assert!(!fx.relation.verify(&wrong_rev, b"challenge-ctx-v1", regime, &decoded));
        let mut wrong_epoch = fx.statement.clone();
        wrong_epoch.revocation_epoch += 1;
        assert!(!fx.relation.verify(&wrong_epoch, b"challenge-ctx-v1", regime, &decoded));
        let mut wrong_nullifier = fx.statement.clone();
        wrong_nullifier.presentation_tags[1][2] += F::ONE;
        assert!(!fx.relation.verify(&wrong_nullifier, b"challenge-ctx-v1", regime, &decoded));
    }

    #[test]
    #[ignore = "measurement: run with --ignored --nocapture"]
    fn bench_zk_capability_batch() {
        for (batch_size, max_hops, iss_d, rev_d) in [
            (1usize, MAX_CAP_HOPS, DEFAULT_ISSUER_DEPTH, DEFAULT_REVOCATION_DEPTH),
            (2usize, 4, 8, 12),
            (4usize, MAX_CAP_HOPS, DEFAULT_ISSUER_DEPTH, DEFAULT_REVOCATION_DEPTH),
        ] {
            for regime in [
                WhirSecurityRegime::BciksJohnsonQrom128,
                WhirSecurityRegime::Poseidon2Cdhz25JohnsonQrom128,
            ] {
                let fx = build_fixture(batch_size, max_hops, iss_d, rev_d);
                let shape = fx.relation.shape();
                let layout = protocol::Layout::new(shape, regime).unwrap();
                let median = |mut v: Vec<f64>| {
                    v.sort_by(f64::total_cmp);
                    v[v.len() / 2]
                };
                let mut prove_ms = Vec::new();
                let mut proof = None;
                for run in 0..3u8 {
                    let t = std::time::Instant::now();
                    proof = Some(
                        fx.relation
                            .prove(
                                &fx.statement,
                                &fx.inputs,
                                b"challenge-ctx-v1",
                                regime,
                                &[40 + run; 32],
                            )
                            .unwrap(),
                    );
                    prove_ms.push(t.elapsed().as_secs_f64() * 1e3);
                }
                let proof = proof.unwrap();
                let bytes = proof.to_bytes();
                let time_verify = || {
                    median(
                        (0..5)
                            .map(|_| {
                                let t = std::time::Instant::now();
                                let decoded =
                                    ZkCapabilityBatchProof::from_bytes(&bytes, &fx.relation, regime)
                                        .unwrap();
                                assert!(fx.relation.verify(
                                    &fx.statement,
                                    b"challenge-ctx-v1",
                                    regime,
                                    &decoded
                                ));
                                t.elapsed().as_secs_f64() * 1e3
                            })
                            .collect(),
                    )
                };
                let verify_all = time_verify();
                let verify_one = crate::with_worker_limit(1, time_verify);
                std::println!(
                    "ZKHEM_CAPABILITY batch={batch_size} regime={regime:?} sbox_rows={} \
                     rows=2^{} vars={} cells=2^{} blind_cells={} proof_bytes={} \
                     proof_kib={:.2} prove_ms_median={:.1} verify_ms_all_workers={verify_all:.2} \
                     verify_ms_1_worker={verify_one:.2} workers={}",
                    shape.num_sbox,
                    shape.log_rows,
                    shape.num_vars,
                    layout.log_cells,
                    layout.blind_cells,
                    bytes.len(),
                    bytes.len() as f64 / 1024.0,
                    median(prove_ms),
                    crate::parallel_workers(),
                );
            }
        }
    }
}
