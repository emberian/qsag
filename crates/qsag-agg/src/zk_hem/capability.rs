//! Privacy-preserving batched bearer capabilities and `SortedRevocationTree` interval
//! non-membership as a hiding `zk-Hem` relation (`#![no_std]` + `alloc`).
//!
//! Each slot `b` in a batch of `B >= 1` capabilities proves in zero knowledge:
//!
//! 1. **Root capability issuance (`issuer_root`)**:
//!    `mint_leaf = sponge12(token_id || audience || root_tag || [CAP_MINT_LEAF_TAG])[0..4]`
//!    authenticates at a hidden index under `issuer_root` without revealing `token_id`,
//!    `root_tag`, or the issuance leaf position.
//! 2. **Conjunctive Poseidon2 macaroon attenuation (`0..=max_hops` caveats)**:
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

/// Bearer capability with Poseidon2 sponge-chained caveat attenuation and secret zeroization.
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

    /// Offline attenuation by any holder without knowing `issuer_key`.
    pub fn attenuate(&mut self, caveat: CapCaveat) -> Result<(), CapabilityZkError> {
        if self.caveats.len() >= MAX_CAP_HOPS {
            return Err(CapabilityZkError::TooManyCaveats);
        }
        let hop = self.caveats.len();
        self.final_tag = chain_step_native(&self.final_tag, &caveat, hop);
        self.caveats.push(caveat);
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

    #[inline]
    pub fn mint_leaf(&self) -> Digest {
        compute_mint_leaf(&self.token_id, &self.audience, &self.root_tag)
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
        if w.left_index + 1 >= (1usize << self.depth)
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
