//! Batched presentation of issuer-enrolled bearer capabilities with `SortedRevocationTree`
//! interval non-membership, as a committed-mask `zk-Hem` relation (`#![no_std]` + `alloc`).
//!
//! Witness privacy and knowledge soundness are those of the masking protocol, summarised
//! on [`v2::prove`] and stated in `crates/qsag-agg/SECURITY.md`. A presentation reveals
//! its public inputs. The scoped relation also reveals a tag per slot.
//! [`UnlinkableCapabilityRelation`] omits the tag and consumes a verifier-issued challenge. The constraints below specify the relation being checked.
//!
//! # Capability model
//!
//! A capability is `(token_id, audience, root_tag, caveats)`. Its tag chain is
//! `tag_0 = root_tag`,
//! `tag_{h+1} = sponge12(tag_h || [kind_h] || payload_h || [CAP_STEP_TAG_DOM, h])[0..4]`,
//! and `final_tag = tag_n` for `n` caveats. Its directory leaf is
//!
//! `mint_leaf = sponge12(token_id || audience || root_tag || final_tag || [n, CAP_MINT_LEAF_TAG])[0..4]`.
//!
//! The authority that publishes `issuer_root` decides which leaves exist. A capability is
//! presentable exactly when its own leaf is in the directory: the leaf commits to the caveat
//! count and to `final_tag`, hence to the whole caveat list.
//!
//! [`BearerCapability::attenuate`] is deterministic and needs no issuer key. It replaces
//! `root_tag` by a one-way image of the parent's `final_tag` and the new caveat, then
//! recomputes the chain. The result has a new leaf, which the authority must enroll before
//! it can be presented. The authority recomputes that leaf itself from `issuer_key` and
//! `(token_id, audience, caveats)` with [`BearerCapability::issue`] and `attenuate`, so it
//! never has to accept a leaf it cannot interpret.
//!
//! What a holder of an attenuated capability gets:
//! - It cannot drop or change a caveat. Any other caveat list gives a leaf that is not
//!   enrolled.
//! - It cannot open an ancestor's leaf. That needs the ancestor's `root_tag`, a preimage of
//!   its own under `sponge12`.
//! - The lineage shares one `token_id`: one revocation entry revokes all of it, and one
//!   batch cannot contain two members of it.
//!
//! For offline delegation, [`DelegatedBearerCapability`] authenticates every attenuation
//! with an ephemeral Poseidon2 WOTS+C key. [`DelegatedCapabilityRelation`] verifies the
//! chain and possession of its terminal secret using the same masking protocol. Only the
//! initial key is enrolled; later hops need no contact with the issuer. The registered mode above
//! remains available for smaller presentation circuits.
//!
//! # Relation
//!
//! Each slot `b` of a batch of `B >= 1` capabilities constrains:
//!
//! 1. **Caveats.** For a witnessed `n <= max_hops`, the first `n` hops are active. Each active
//!    hop advances the tag chain and enforces its predicate (`ExpiresAt`, `NotBefore`,
//!    `Resource`, `Actions`, `MaxAmount`) against the verifier's [`CapabilityRequest`]. The
//!    chain ends at the witnessed `final_tag`.
//! 2. **Enrollment.** `mint_leaf`, computed from the witnessed `token_id`, `root_tag`,
//!    `final_tag` and `n` and from the request's public `audience`, opens at a witnessed index
//!    under `issuer_root`.
//! 3. **Presentation tag.** The public
//!    `presentation_tag = sponge12(final_tag || token_id || context_digest || [CAP_PRESENT_TAG_DOM])[0..4]`
//!    is a deterministic per-context nullifier of the capability.
//! 4. **Non-revocation.** Adjacent leaves `(revoked_lo, revoked_hi)` at indices
//!    `(idx, idx + 1)`, `idx + 1 < 2^D`, open under `(revocation_root, revocation_epoch)`,
//!    and `revoked_lo < token_id < revoked_hi` as 256-bit integers over canonical limbs.
//!
//! Across slots, `token_id[b - 1] < token_id[b]`, so a batch cannot repeat a capability.

use alloc::vec;
use alloc::vec::Vec;
use core::cmp::Ordering;

use qsag_agg::field::{GOLDILOCKS_PRIME, Goldilocks};
use qsag_agg::sponge::{POSEIDON2_CONST_IV, cshake256_32, poseidon2_compress12_ff};
use qsag_agg::zk_hem::relation::{
    ConstraintSystem, Lc, Shape, poseidon2_perm, sponge12, sponge12_native,
};
use qsag_agg::zk_hem::v2::params::Profile;
use qsag_agg::zk_hem::v2::protocol::{self as v2, ZkHemV2Error, ZkHemV2Proof};

mod offline;
mod unlinkable;
pub use offline::{
    DelegatedBearerCapability, DelegatedCapabilityRelation, DelegatedPresentationInput,
};

pub use unlinkable::{
    CapabilityChallenge, UnlinkableCapabilityPresentation, UnlinkableCapabilityRelation,
    UnlinkableCapabilityStatement, VerifierChallengeLedger,
};

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
pub use qsag_agg::zk_hem::capability::CAPABILITY_WIRE_MAGIC;

/// Strict lower sentinel `[0, 0, 0, 0]` at index `0` of every [`SortedRevocationTree`].
pub const SENTINEL_MIN_ID: TokenId = [F::ZERO; 4];

/// Strict upper sentinel `[p - 1, p - 1, p - 1, p - 1]` padding the tail of every [`SortedRevocationTree`].
pub const SENTINEL_MAX_ID: TokenId = [F::from_u64_reduced(GOLDILOCKS_PRIME - 1); 4];

const CAP_ROOT_TAG_DOM: u64 = 0x4341_5052_4F4F_5431; // "CAPROOT1"
const CAP_CHILD_ROOT_DOM: u64 = 0x4341_5043_4849_4C31; // "CAPCHIL1"
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
    let raw = cshake256_32(qsag_agg::zk_hem::capability::CONTEXT_DOMAIN, context);
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
    Proof(ZkHemV2Error),
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

/// Directory leaf of the capability `(token_id, audience, root_tag)` whose `hops` caveats
/// chain `root_tag` to `final_tag`.
#[inline]
fn mint_leaf_native(
    token_id: &TokenId,
    audience: &Digest,
    root_tag: &Digest,
    final_tag: &Digest,
    hops: usize,
) -> Digest {
    let mut msg = Vec::with_capacity(18);
    msg.extend_from_slice(token_id);
    msg.extend_from_slice(audience);
    msg.extend_from_slice(root_tag);
    msg.extend_from_slice(final_tag);
    msg.push(f(hops as u64));
    msg.push(f(CAP_MINT_LEAF_TAG));
    let st = sponge12_native(&msg);
    qsag_asm::volatile_fill(&mut msg, F::ZERO);
    first4(st)
}

#[inline]
fn chain_step_native(prev_tag: &Digest, caveat: &CapCaveat, hop: usize) -> Digest {
    let (kind, payload) = caveat.encode_words();
    caveat_step_native(CAP_STEP_TAG_DOM, prev_tag, kind, &payload, hop)
}

/// Root of the capability obtained by adding `caveat` as caveat number `hop` to a
/// capability whose chain ends at `parent_final`.
#[inline]
fn child_root_native(parent_final: &Digest, caveat: &CapCaveat, hop: usize) -> Digest {
    let (kind, payload) = caveat.encode_words();
    caveat_step_native(CAP_CHILD_ROOT_DOM, parent_final, kind, &payload, hop)
}

#[inline]
fn caveat_step_native(
    domain: u64,
    prev_tag: &Digest,
    kind: u64,
    payload: &[F; 4],
    hop: usize,
) -> Digest {
    let mut msg = Vec::with_capacity(11);
    msg.extend_from_slice(prev_tag);
    msg.push(f(kind));
    msg.extend_from_slice(payload);
    msg.push(f(domain));
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

/// Bearer capability: whoever holds it can present it once its [`Self::mint_leaf`] is
/// enrolled. `token_id`, `root_tag` and `final_tag` are secret and wiped on drop.
#[derive(Clone)]
pub struct BearerCapability {
    token_id: TokenId,
    audience: Digest,
    root_tag: Digest,
    caveats: Vec<CapCaveat>,
    final_tag: Digest,
}

impl BearerCapability {
    /// The secret words in a fixed byte layout, for a constant-time comparison.
    fn secret_bytes(&self) -> [u8; 96] {
        let mut out = [0u8; 96];
        let words = self
            .token_id
            .iter()
            .chain(&self.root_tag)
            .chain(&self.final_tag);
        for (chunk, word) in out.as_chunks_mut::<8>().0.iter_mut().zip(words) {
            *chunk = word.to_le_bytes();
        }
        out
    }
}

/// The secret words (`token_id`, `root_tag`, `final_tag`) are compared in constant time and
/// as one block, so neither the position nor the count of matching words affects timing.
/// The audience and the caveats are compared ordinarily.
impl PartialEq for BearerCapability {
    fn eq(&self, other: &Self) -> bool {
        let (mut mine, mut theirs) = (self.secret_bytes(), other.secret_bytes());
        let secrets_equal = qsag_asm::ct_eq_bytes(&mine, &theirs);
        qsag_asm::volatile_fill(&mut mine, 0);
        qsag_asm::volatile_fill(&mut theirs, 0);
        secrets_equal & (self.audience == other.audience) & (self.caveats == other.caveats)
    }
}
impl Eq for BearerCapability {}

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
    /// Mint a capability without caveats from the authority's secret `issuer_key`.
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

    /// Add a caveat. `root_tag` becomes a one-way image of the previous `final_tag` and
    /// `caveat`, so the result cannot open the leaf of the capability it came from.
    ///
    /// Needs no issuer key, but the result has a new [`Self::mint_leaf`] and cannot be
    /// presented until the authority enrolls it (see the module documentation).
    pub fn attenuate(&mut self, caveat: CapCaveat) -> Result<(), CapabilityZkError> {
        if self.caveats.len() >= MAX_CAP_HOPS {
            return Err(CapabilityZkError::TooManyCaveats);
        }
        let hop = self.caveats.len();
        let mut next_root = child_root_native(&self.final_tag, &caveat, hop);
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

    /// Directory leaf the authority enrolls for this capability and its exact caveat list.
    #[inline]
    pub fn mint_leaf(&self) -> Digest {
        mint_leaf_native(
            &self.token_id,
            &self.audience,
            &self.root_tag,
            &self.final_tag,
            self.caveats.len(),
        )
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

/// Poseidon2 Merkle accumulator of the enrolled capability leaves (`mint_leaf`s).
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
    /// Deterministic per-context presentation nullifiers, ordered by witnessed `token_id`.
    /// Equal contexts for the same capability produce equal tags; unlinkability across
    /// contexts rests on the tag derivation, which `crates/qsag-agg/SECURITY.md` does not analyse.
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
    delegation: Option<offline::DelegationSlot>,
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
        // The openings locate the holder's leaf; `RevocationNonMembershipWitness` erases
        // its copies of the same paths.
        for path in [
            &mut self.issuer_siblings,
            &mut self.path_lo,
            &mut self.path_hi,
        ] {
            for node in path.iter_mut() {
                qsag_asm::volatile_fill(node, F::ZERO);
            }
        }
    }
}

impl CapSlot {
    fn placeholder(params: CapabilityParams) -> Self {
        Self {
            delegation: None,
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
            delegation: None,
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
        let must_eq = win[j + 1..]
            .iter()
            .fold(is_eq.clone(), |acc, w| acc.plus(w));
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
    want_pres_tag: Option<&[Lc; 4]>,
) -> [Lc; 8] {
    let token_id = alloc4(cs, &slot.token_id);
    let token_halves = canonical_digest_halves8(cs, &token_id);
    let root_tag = alloc4(cs, &slot.root_tag);
    let final_tag = alloc4(cs, &slot.final_tag);

    // 1. Caveats: an active prefix of hops, each advancing the tag chain and enforcing its
    //    predicate against the request.
    let mut cur_tag = root_tag.clone();
    let mut actual_hops = Lc::zero();
    let mut prev_active: Option<Lc> = None;
    for (hop_idx, hop) in slot.hops.iter().enumerate() {
        let active: Lc = cs.alloc(f(u64::from(hop.active))).into();
        cs.enforce_boolean(&active);
        actual_hops = actual_hops.plus(&active);
        if let Some(prev) = &prev_active {
            cs.enforce_mul(active.clone(), Lc::constant(F::ONE).minus(prev), Lc::zero());
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
        step_msg.push(kind_lc.clone());
        step_msg.extend_from_slice(&payload);
        step_msg.push(Lc::constant(f(CAP_STEP_TAG_DOM)));
        step_msg.push(Lc::constant(f(hop_idx as u64)));
        let stepped = first4_lc(&sponge12(cs, &step_msg));
        cur_tag = if let Some(delegation) = &slot.delegation {
            offline::hop_gadget(
                cs,
                &active,
                &cur_tag,
                &token_id,
                req_audience,
                &kind_lc,
                &payload,
                hop_idx,
                &delegation.hops[hop_idx],
            )
        } else {
            select4(cs, &active, &stepped, &cur_tag)
        };
    }
    enforce_equal4(cs, &cur_tag, &final_tag);
    if let Some(delegation) = &slot.delegation {
        let terminal_pk = offline::secret_public_gadget(cs, &delegation.secret);
        enforce_equal4(cs, &terminal_pk, &final_tag);
    }

    // 2. Enrollment: the leaf binding `(token_id, audience, root_tag, final_tag, hops)` opens
    //    under `issuer_root`.
    let mut mint_msg: Vec<Lc> = Vec::with_capacity(18);
    mint_msg.extend_from_slice(&token_id);
    mint_msg.extend_from_slice(req_audience);
    mint_msg.extend_from_slice(&root_tag);
    if slot.delegation.is_some() {
        mint_msg.push(Lc::constant(f(offline::MINT_DOMAIN)));
    } else {
        mint_msg.extend_from_slice(&final_tag);
        mint_msg.push(actual_hops);
        mint_msg.push(Lc::constant(f(CAP_MINT_LEAF_TAG)));
    }
    let mut mint_node = first4_lc(&sponge12(cs, &mint_msg));

    let iss_idx_bits = alloc_bits(cs, slot.issuer_index as u64, params.issuer_depth);
    for (level, bit) in iss_idx_bits.iter().enumerate() {
        let sib = alloc4(cs, &slot.issuer_siblings[level]);
        let left = select4(cs, bit, &sib, &mint_node);
        let right: [Lc; 4] = core::array::from_fn(|i| mint_node[i].plus(&sib[i]).minus(&left[i]));
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
    if let Some(want_pres_tag) = want_pres_tag {
        let mut pres_msg: Vec<Lc> = Vec::with_capacity(13);
        pres_msg.extend_from_slice(&final_tag);
        pres_msg.extend_from_slice(&token_id);
        pres_msg.extend_from_slice(ctx_digest);
        pres_msg.push(Lc::constant(f(CAP_PRESENT_TAG_DOM)));
        let computed_pres = first4_lc(&sponge12(cs, &pres_msg));
        enforce_equal4(cs, &computed_pres, want_pres_tag);
    }

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

    let check_rev_path =
        |cs: &mut ConstraintSystem, leaf_key: &[Lc; 4], idx_bits: &[Lc], siblings: &[Digest]| {
            let mut leaf_msg: Vec<Lc> = Vec::with_capacity(5);
            leaf_msg.extend_from_slice(leaf_key);
            leaf_msg.push(Lc::constant(f(REV_LEAF_TAG)));
            let mut node = first4_lc(&sponge12(cs, &leaf_msg));
            for (level, bit) in idx_bits.iter().enumerate() {
                let sib = alloc4(cs, &siblings[level]);
                let left = select4(cs, bit, &sib, &node);
                let right: [Lc; 4] =
                    core::array::from_fn(|i| node[i].plus(&sib[i]).minus(&left[i]));
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
    assert!(
        statement.presentation_tags.is_empty()
            || statement.presentation_tags.len() == params.batch_size
    );

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
        let want_pres = statement
            .presentation_tags
            .get(b)
            .map(|_| core::array::from_fn(|i| pub_lcs[pres_tags_base + 4 * b + i].clone()));
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
            want_pres.as_ref(),
        );
        if let Some(prev) = &prev_token_halves {
            // Strictly increasing `token_id` across slots forbids duplicate capability replay.
            enforce_gated_cmp_limbs32(cs, &one, prev, &token_halves, false);
        }
        prev_token_halves = Some(token_halves);
    }
}

/// Self-delimiting wire wrapper (`b"QSAGCAP1"`) around a `zk-Hem v2` [`ZkHemV2Proof`]
/// for [`CapabilityRelation`].
#[derive(Clone, Debug, PartialEq, Eq)]
