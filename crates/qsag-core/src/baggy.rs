//! `Baggy`: stateless 2-of-3 threshold hash-based signatures (`WOTS+C` `w = 4`, `v = 128`, `T = 192`,
//! `FORS+C`, hypertree) on the 256-lane replicated engine, with the `Waistband` top-layer
//! cache.
//!
//! ### Structure
//! A hypertree of `d` layers of height-`h'` subtrees over `WOTS+C` leaves ([`crate::wots_c`]);
//! the bottom leaf signs the public key of a `FORS+C` instance with `k - 1` trees of height
//! `a`. `FORS+C` grinds a public counter until the index of the `k`-th tree is zero and omits
//! that tree. All secret values derive from the shared `sk_seed`; only values that belong in
//! a signature, or chain endpoints and leaf hashes that are public-key material, are opened.
//!
//! ### Three phases ([`baggy_sign_mpc`])
//! 1. **Randomiser.** `opt_rand = PRF(sk_prf, mu)` stays shared and keys
//!    `R = PRF(opt_rand, mu)`; both are evaluated under MPC, verified at their own barrier,
//!    and only `R` is opened. `R` therefore depends on the shared key and the message alone:
//!    a signer that aborts after seeing `R` gets the same `R`, and the same leaf and FORS
//!    indices, on every retry.
//! 2. **All-layer sweep.** `R` fixes every address, so the FORS leaves and the chains of
//!    every subtree on the path are evaluated together, level by level: one `PRF` level and
//!    three `F` levels in total, however many layers there are.
//! 3. **Cut.** One barrier verifies every gate of phase 2. Then chain endpoints and FORS leaf
//!    hashes are opened (first round), the subtree roots and the digits they imply are
//!    computed in public, and the selected chain nodes are opened (second round). Upper-layer
//!    leaves always sign the same child root, so they always reveal the same digits.
//!
//! ### `Waistband`
//! [`WaistbandCache`] stores, for the top `L` layers, the public leaves of subtrees and the
//! (deterministic) `WOTS+C` signatures of their leaves on child roots, with authentication
//! paths. A cached signature removes that layer from the sweep entirely; cached leaves
//! reduce a layer to the 128 chains of its signing leaf. The cache can be filled eagerly
//! ([`WaistbandCache::precompute`], cost `sum_{j <= L} 2^{h' j}` subtree sweeps) or lazily as
//! signatures pass through it. Everything in it is public.
//!
//! A cached value decides which message an uncached layer above it signs, so a wrong value
//! could make a static `WOTS+C` key open a second codeword. Three checks stand in front of
//! every chain-node opening:
//! * **Identity.** A cache is bound to one [`BaggyKeyBinding`] (`pk_seed`, `pk_root` and a
//!   digest of every [`BaggyParams`] field) and is refused under any other, before any MPC
//!   work.
//! * **Entry authentication.** Each cached signature carries the child root it signed and
//!   the subtree root it reconstructs to, both taken from a signature path that verified up
//!   to `pk_root`; each cached leaf set carries its subtree root. Before the sweep,
//!   [`baggy_sign_mpc`] re-verifies every cached entry on the path against its stored roots,
//!   checks that adjacent cached entries agree and that the top one ends in `pk_root`, and
//!   aborts with [`BaggyError::CacheEntryUnauthenticated`] otherwise. A layer above a cached
//!   entry signs the stored root, never one recomputed from the entry's signature.
//! * **First-signed record.** A [`FirstSignedLedger`] holds, per static key
//!   `(layer, tree, key_pair)`, the digit vector it first opened. It is consulted and
//!   written before every chain-node opening round; a different vector is refused
//!   ([`BaggyError::StaticKeyDigitsConflict`]). An uncached layer whose message comes from
//!   the cache is opened only if the ledger already holds its vector
//!   ([`BaggyError::CacheUnanchored`] otherwise): the stored roots detect an entry that was
//!   damaged, but an entry and its stored roots rewritten together are consistent with each
//!   other, and only the ledger distinguishes that case.
//!
//! What this does not cover: the cache lives in process memory and has no secret-keyed
//! integrity tag; the guarantee against a writer that can rewrite it coherently rests on the
//! ledger, and so on the ledger being durable and being the same one for the life of the
//! key. [`MemoryFirstSigned`] is not durable. The binding is a public value checked by the
//! signing function, and [`baggy_keygen_mpc`] records its identity in the key shares, which
//! every later call compares (see [`BaggyKeyBinding`]).
//!
//! ### Limits that are stated, not solved
//! * The number of signatures per key is bounded by the few-time security of `FORS+C` at the
//!   chosen `(k, a, h)`; [`BaggyParams::SHA3_128F`] reuses the tree geometry of
//!   [`crate::tsw_baggy::PqHashParams::BAGGY_TSW_128F`], which that preset sizes for `2^16`
//!   signatures. The layer signatures use the 128-chain `WOTS+C` encoding of a full
//!   256-bit digest ([`crate::wots_c::WotsCParams::V128`]).
//! * `BaggyPoseidon2` is the existing authenticated-share Poseidon2 engine under this suite's
//!   name; it does not run on the 256-lane engine.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::fmt;

use crate::keccak_mpc::TSW_SUITE_MIDSTATE;
use crate::rss256::{Rss256Engine, Rss256Error, SharedState256, active_lane_mask};
use crate::sponge::keccak::{SHAKE256_RATE_BYTES, cshake256_32, encode_multi_frame};
use crate::tsw_baggy::{
    AdrsKind, Cshake256Suite, HashAdrs, PqSecretKey, extract_bit_window_checked,
    fors_leaf_hash_from_secret, fors_secret_leaf, th_call, th_call_secret, th_pre_hash,
    th_preimage, th_tweak_tl, walk_merkle_auth_path,
};
use crate::wots_c::{
    DigestGrinder, LaneSpec, Sweep, WOTS_STEPS, WotsCParams, merkle_auth_path, merkle_levels,
    wots_c_digest_adrs, wots_c_leaf, wots_c_recover_pk, wots_c_reference_leaf,
    wots_c_reference_nodes,
};

/// Role tags of the `Baggy` suite.
pub const TAG_BAGGY_OPT_RAND: &[u8] = b"QSAG.BAGGY.OPTRAND/v1";
pub const TAG_BAGGY_R: &[u8] = b"QSAG.BAGGY.R/v1";
pub const TAG_BAGGY_HMSG: &[u8] = b"QSAG.BAGGY.HMSG/v1";
pub const TAG_BAGGY_DIGEST: &[u8] = b"QSAG.BAGGY.DIGEST/v1";
pub const TAG_BAGGY_PARAMS: &[u8] = b"QSAG.BAGGY.PARAMS/v1";
pub const TAG_BAGGY_KEY_ID: &[u8] = b"QSAG.BAGGY.KEYID/v1";

/// Marker for the `SHAKE`-based suite.
#[derive(Clone, Copy, Debug)]
pub struct BaggySha3;

/// Marker for the algebraic suite; its parameters are
/// [`crate::tsw_baggy::PqHashParams::BAGGY_TSW_128F`] over the Poseidon2 hash.
#[derive(Clone, Copy, Debug)]
pub struct BaggyPoseidon2;

pub use crate::poseidon2_mpc::{
    sign_stateless_tsw_poseidon2_mpc as sign_baggy_poseidon2_mpc,
    sign_stateless_tsw_poseidon2_mpc_cached as sign_baggy_poseidon2_mpc_cached,
};

/// `Baggy` parameters.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BaggyParams {
    pub wots: WotsCParams,
    /// Height `h'` of every subtree.
    pub subtree_height: usize,
    /// Layers `d`.
    pub num_layers: usize,
    /// FORS trees `k`, counting the omitted one.
    pub fors_trees: usize,
    /// FORS tree height `a`.
    pub fors_height: usize,
    /// Bound on each public grind.
    pub max_grind: u32,
}

impl BaggyParams {
    /// `h = 32`, `d = 16`, `h' = 2`, `k = 33`, `a = 6`: 73,828-byte signatures.
    pub const SHA3_128F: Self = Self {
        wots: WotsCParams::V128,
        subtree_height: 2,
        num_layers: 16,
        fors_trees: 33,
        fors_height: 6,
        max_grind: 1 << 26,
    };

    /// Small geometry for tests.
    pub const TEST_SMALL: Self = Self {
        wots: WotsCParams::V128,
        subtree_height: 2,
        num_layers: 3,
        fors_trees: 5,
        fors_height: 3,
        max_grind: 1 << 26,
    };

    pub const fn total_height(&self) -> usize {
        self.subtree_height * self.num_layers
    }

    pub const fn is_well_formed(&self) -> bool {
        self.wots.is_well_formed()
            && self.subtree_height >= 1
            && self.subtree_height <= 8
            && self.num_layers >= 1
            && self.total_height() <= 62
            && self.fors_trees >= 2
            && self.fors_height >= 1
            && self.fors_height <= 16
            && self.fors_trees * self.fors_height + self.total_height() <= 256
    }

    /// FORS trees that appear in a signature.
    pub const fn signed_fors_trees(&self) -> usize {
        self.fors_trees - 1
    }

    pub const fn sig_bytes(&self) -> usize {
        32 + 4
            + self.signed_fors_trees() * (32 + 32 * self.fors_height)
            + self.num_layers * (4 + 32 * self.wots.chains + 32 * self.subtree_height)
    }

    /// Domain-separated digest of every field. Two parameter sets that differ anywhere,
    /// including in `wots.chains` or `wots.target_sum` (which a public key does not commit
    /// to), have different digests.
    pub fn digest(&self) -> [u8; 32] {
        // Exhaustive patterns: a field added to either struct fails to compile here until
        // it is hashed too.
        let Self {
            wots,
            subtree_height,
            num_layers,
            fors_trees,
            fors_height,
            max_grind,
        } = *self;
        let WotsCParams {
            chains,
            zero_digits,
            target_sum,
        } = wots;
        let word = |v: usize| (v as u64).to_be_bytes();
        cshake256_32(
            TAG_BAGGY_PARAMS,
            &encode_multi_frame(&[
                &word(chains),
                &word(zero_digits),
                &word(target_sum),
                &word(subtree_height),
                &word(num_layers),
                &word(fors_trees),
                &word(fors_height),
                &u64::from(max_grind).to_be_bytes(),
            ]),
        )
    }

    const fn subtree_leaves(&self) -> usize {
        1 << self.subtree_height
    }

    /// Leaf index and tree index of the path at `layer`.
    const fn path_at(&self, leaf_idx: u64, layer: usize) -> (u32, u64) {
        let shifted = leaf_idx >> (self.subtree_height * layer);
        (
            (shifted & ((1 << self.subtree_height) - 1)) as u32,
            shifted >> self.subtree_height,
        )
    }
}

/// Public key.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BaggyPublicKey {
    pub pk_seed: [u8; 32],
    pub pk_root: [u8; 32],
}

/// Identity of one signing key: `pk_seed`, `pk_root` and the digest of the parameters it was
/// generated under. [`baggy_keygen_mpc`] produces it; the signer stores it next to its key
/// shares and passes the stored value to [`baggy_sign_mpc`], which refuses to run unless it
/// agrees with the engine's `pk_seed`, the supplied public key and the supplied parameters.
/// [`WaistbandCache`] and the keys of the [`FirstSignedLedger`] are bound to it.
///
/// Bound: a signing call cannot proceed with a `pk_root` or with parameters (any field)
/// other than those recorded here. [`baggy_keygen_mpc`] also records [`Self::identity`] in
/// the engine's key shares (once; a different identity is refused), and every later call
/// requires the shares to carry the identity of the binding it is given. A binding rebuilt
/// from a changed public key or changed parameters therefore does not match shares that
/// went through key generation, and shares that carry no identity sign nothing. The record
/// lives in the key-share values: a deployment that stores shares must store it with them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BaggyKeyBinding {
    pk_seed: [u8; 32],
    pk_root: [u8; 32],
    params_digest: [u8; 32],
}

impl BaggyKeyBinding {
    /// Binding of `pk` under `params`. Meant to be called once, when the key is generated
    /// or imported, and stored.
    pub fn new(params: &BaggyParams, pk: &BaggyPublicKey) -> Self {
        Self {
            pk_seed: pk.pk_seed,
            pk_root: pk.pk_root,
            params_digest: params.digest(),
        }
    }

    pub fn pk_seed(&self) -> &[u8; 32] {
        &self.pk_seed
    }

    pub fn pk_root(&self) -> &[u8; 32] {
        &self.pk_root
    }

    pub fn params_digest(&self) -> &[u8; 32] {
        &self.params_digest
    }

    /// Whether this is the binding of exactly `pk` under exactly `params`.
    pub fn matches(&self, params: &BaggyParams, pk: &BaggyPublicKey) -> bool {
        *self == Self::new(params, pk)
    }

    /// Single digest of the three fields; names the key in a [`StaticKeyId`].
    pub fn identity(&self) -> [u8; 32] {
        cshake256_32(
            TAG_BAGGY_KEY_ID,
            &encode_multi_frame(&[&self.pk_seed, &self.pk_root, &self.params_digest]),
        )
    }
}

/// One `WOTS+C` key of the hypertree of one signing key. Every such key signs a value fixed
/// by the signing key alone (a child subtree root, or at layer 0 a FORS public key).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct StaticKeyId {
    /// [`BaggyKeyBinding::identity`] of the signing key.
    pub identity: [u8; 32],
    pub layer: u32,
    pub tree: u64,
    pub key_pair: u32,
}

/// The digit vector a static key opened first.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FirstSignedRecord {
    pub key: StaticKeyId,
    pub digits: Vec<u8>,
}

/// Failure of a [`FirstSignedLedger`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FirstSignedError {
    /// The write or its sync did not complete.
    Io,
    /// A stored record exists but does not decode.
    Corrupt,
    /// A record for the key exists with other digits; nothing was written.
    Conflict,
}

/// Durable map `static key -> first-signed digits`.
///
/// Contract with the signer: before any round that opens chain nodes of a static key, the
/// signer reads the key's record; if there is one it must equal the digits about to be
/// opened, and if there is none the signer calls [`FirstSignedLedger::sync_record`] and
/// opens only after it returned `Ok`. A record is never replaced or removed. An
/// implementation that loses records (a restart of a volatile one, a restored backup)
/// removes the protection for the lost keys.
pub trait FirstSignedLedger {
    /// Gate the first secret-derived output of a ceremony. Durable implementations
    /// require a journal permit even when every first-signed entry is already cached.
    fn begin_release(&mut self, _key: &[u8; 32], _ceremony: &[u8; 32], _codeword: &[u8; 32]) -> Result<(), FirstSignedError> { Err(FirstSignedError::Io) }

    /// The record of `key`; `Ok(None)` only if none was ever stored.
    fn first_signed(&self, key: &StaticKeyId) -> Result<Option<Vec<u8>>, FirstSignedError>;

    /// Store all of `records` and return only once they would survive a power loss. A record
    /// whose key is already stored with the same digits is a no-op; with other digits the
    /// call fails with [`FirstSignedError::Conflict`]. On any error nothing may be assumed
    /// about what was written, and the signer does not open.
    fn sync_record(&mut self, records: &[FirstSignedRecord]) -> Result<(), FirstSignedError>;
}

/// Volatile [`FirstSignedLedger`] for tests and for hosts that supply durability one level
/// up. It does not survive a restart: after one, every key can open a first vector again.
#[derive(Clone, Debug, Default)]
pub struct MemoryFirstSigned {
    records: BTreeMap<StaticKeyId, Vec<u8>>,
    syncs: u64,
    fail_next: bool,
}

impl MemoryFirstSigned {
    pub fn new() -> Self {
        Self::default()
    }

    /// Keys with a record.
    pub fn len(&self) -> usize {
        self.records.len()
    }

    pub fn is_empty(&self) -> bool {
        self.records.is_empty()
    }

    /// Number of successful [`FirstSignedLedger::sync_record`] calls.
    pub fn sync_count(&self) -> u64 {
        self.syncs
    }

    /// Make the next [`FirstSignedLedger::sync_record`] fail without storing anything.
    pub fn fail_next_sync(&mut self) {
        self.fail_next = true;
    }
}

impl FirstSignedLedger for MemoryFirstSigned {
    fn begin_release(&mut self, _key: &[u8; 32], _ceremony: &[u8; 32], _codeword: &[u8; 32]) -> Result<(), FirstSignedError> { Ok(()) }
    fn first_signed(&self, key: &StaticKeyId) -> Result<Option<Vec<u8>>, FirstSignedError> {
        Ok(self.records.get(key).cloned())
    }

    fn sync_record(&mut self, records: &[FirstSignedRecord]) -> Result<(), FirstSignedError> {
        if self.fail_next {
            self.fail_next = false;
            return Err(FirstSignedError::Io);
        }
        if records
            .iter()
            .any(|r| self.records.get(&r.key).is_some_and(|d| *d != r.digits))
        {
            return Err(FirstSignedError::Conflict);
        }
        for r in records {
            self.records.insert(r.key, r.digits.clone());
        }
        self.syncs += 1;
        Ok(())
    }
}

/// Authenticated durable first-signed records. Retain `checkpoint()` independently
/// before opening signing material; supply it on recovery to reject rollback.
#[cfg(feature = "std")]
pub struct FsFirstSignedLedger(crate::durable_ledger::Ledger, Option<crate::ceremony_journal::CeremonyReservation>);
#[cfg(feature = "std")]
impl FsFirstSignedLedger {
    /// Consume a committed journal permit for the next signing or precomputation attempt.
    /// Bind key_id to BaggyKeyBinding::identity(), ceremony_id to the engine session,
    /// and epoch_or_codeword to baggy_msg_digest (or precompute_release_binding).
    pub fn authorize_release(&mut self, journal: &crate::ceremony_journal::FsCeremonyJournal,
        permit: crate::ceremony_journal::CeremonyReleasePermit) -> Result<(), FirstSignedError> {
        self.1 = None;
        self.1 = Some(journal.consume_release(permit).map_err(|_| FirstSignedError::Io)?);
        Ok(())
    }

    pub fn provision_genesis(path: impl Into<std::path::PathBuf>, key: [u8; 32]) -> Result<Self, FirstSignedError> {
        crate::durable_ledger::Ledger::create(path, key, b"QSAG.FIRST_SIGNED.V1").map(|ledger| Self(ledger, None)).map_err(|_| FirstSignedError::Io)
    }
    pub fn open_existing(path: impl Into<std::path::PathBuf>, key: [u8; 32], checkpoint: crate::LedgerCheckpoint) -> Result<Self, FirstSignedError> {
        crate::durable_ledger::Ledger::open(path, key, b"QSAG.FIRST_SIGNED.V1", checkpoint).map(|ledger| Self(ledger, None)).map_err(|_| FirstSignedError::Corrupt)
    }
    pub fn checkpoint(&self) -> crate::LedgerCheckpoint { self.0.checkpoint() }
    fn key(key: &StaticKeyId) -> Vec<u8> {
        let mut out = key.identity.to_vec();
        out.extend_from_slice(&key.layer.to_le_bytes());
        out.extend_from_slice(&key.tree.to_le_bytes());
        out.extend_from_slice(&key.key_pair.to_le_bytes());
        out
    }
}
#[cfg(feature = "std")]
impl FirstSignedLedger for FsFirstSignedLedger {
    fn begin_release(&mut self, key: &[u8; 32], ceremony: &[u8; 32], codeword: &[u8; 32]) -> Result<(), FirstSignedError> {
        let r = self.1.take().ok_or(FirstSignedError::Io)?;
        if r.key_id != *key || r.ceremony_id != *ceremony || r.epoch_or_codeword != *codeword { return Err(FirstSignedError::Conflict); }
        Ok(())
    }

    fn first_signed(&self, key: &StaticKeyId) -> Result<Option<Vec<u8>>, FirstSignedError> {
        Ok(self.0.read().map_err(|_| FirstSignedError::Corrupt)?.get(&Self::key(key)).cloned())
    }
    fn sync_record(&mut self, records: &[FirstSignedRecord]) -> Result<(), FirstSignedError> {
        let mut stored = self.0.read().map_err(|_| FirstSignedError::Corrupt)?;
        for r in records {
            let key = Self::key(&r.key);
            if stored.get(&key).is_some_and(|d| *d != r.digits) { return Err(FirstSignedError::Conflict); }
            stored.insert(key, r.digits.clone());
        }
        self.0.commit(&stored).map_err(|_| FirstSignedError::Io)
    }
}

/// One revealed FORS secret with its root-first authentication path.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BaggyForsOpening {
    pub secret: [u8; 32],
    pub auth: Vec<[u8; 32]>,
}

/// One hypertree layer: `WOTS+C` signature on the node below and the path to the subtree root.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BaggyLayerSig {
    pub ctr: u32,
    pub chains: Vec<[u8; 32]>,
    pub auth: Vec<[u8; 32]>,
}

/// Signature.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BaggySig {
    pub r: [u8; 32],
    pub msg_ctr: u32,
    pub fors: Vec<BaggyForsOpening>,
    pub layers: Vec<BaggyLayerSig>,
}

/// Errors of `Baggy`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BaggyError {
    InvalidParameters,
    /// A public grind found no valid counter below `max_grind`.
    GrindExhausted,
    Engine(Rss256Error),
    /// A cached entry does not fit the path it was looked up for.
    CacheInconsistent,
    /// The assembled signature did not verify; it is not released.
    SelfCheckFailed,
    /// The [`BaggyKeyBinding`] does not match the engine's `pk_seed`, the public key or the
    /// parameters of this call. Raised before any MPC work.
    KeyBindingMismatch,
    /// The cache is bound to another key or other parameters. Raised before any MPC work.
    CacheIdentityMismatch,
    /// A cached entry on the signing path does not verify against its stored roots, or does
    /// not agree with its neighbours or with `pk_root`. No chain node was opened.
    CacheEntryUnauthenticated,
    /// An uncached layer would sign a root that only the cache vouches for, and the ledger
    /// holds no first-signed record for that layer's key. No chain node was opened.
    CacheUnanchored,
    /// The key already opened a different digit vector. No chain node was opened.
    StaticKeyDigitsConflict {
        layer: u32,
        tree: u64,
        key_pair: u32,
    },
    /// The first-signed ledger failed; no chain node was opened.
    FirstSigned(FirstSignedError),
}

impl From<FirstSignedError> for BaggyError {
    fn from(e: FirstSignedError) -> Self {
        Self::FirstSigned(e)
    }
}

impl From<Rss256Error> for BaggyError {
    fn from(e: Rss256Error) -> Self {
        Self::Engine(e)
    }
}

impl fmt::Display for BaggyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidParameters => f.write_str("invalid Baggy parameters"),
            Self::GrindExhausted => f.write_str("no valid counter within the grind bound"),
            Self::Engine(e) => write!(f, "engine: {e}"),
            Self::CacheInconsistent => f.write_str("Waistband entry inconsistent with the path"),
            Self::SelfCheckFailed => f.write_str("assembled signature failed verification"),
            Self::KeyBindingMismatch => {
                f.write_str("key binding does not match engine, public key or parameters")
            }
            Self::CacheIdentityMismatch => {
                f.write_str("Waistband cache is bound to another key or parameter set")
            }
            Self::CacheEntryUnauthenticated => {
                f.write_str("Waistband entry failed authentication")
            }
            Self::CacheUnanchored => {
                f.write_str("cached root has no first-signed record for the layer above")
            }
            Self::StaticKeyDigitsConflict {
                layer,
                tree,
                key_pair,
            } => write!(
                f,
                "key (layer {layer}, tree {tree}, leaf {key_pair}) already opened other digits"
            ),
            Self::FirstSigned(e) => write!(f, "first-signed ledger: {e:?}"),
        }
    }
}

impl core::error::Error for BaggyError {}

/// Message digest bound to the public key.
pub fn baggy_msg_digest(pk: &BaggyPublicKey, msg: &[u8]) -> [u8; 32] {
    th_pre_hash(Cshake256Suite, &pk.pk_seed, &pk.pk_root, msg)
}

/// Rate block and secret offset of `th_call(tag, [], ZERO, [secret32, mu])`.
fn keyed_mu_frame(tag: &[u8], mu: &[u8; 32]) -> ([u8; SHAKE256_RATE_BYTES], usize) {
    let pre = th_preimage(tag, &[], &HashAdrs::ZERO, &[&[0u8; 32], mu]);
    assert!(pre.len() < SHAKE256_RATE_BYTES);
    let mut frame = [0u8; SHAKE256_RATE_BYTES];
    frame[..pre.len()].copy_from_slice(&pre);
    frame[pre.len()] = 0x04;
    frame[SHAKE256_RATE_BYTES - 1] ^= 0x80;
    (frame, pre.len() - 33 - 32)
}

/// FORS indices and hypertree leaf index selected by a message hash, if the omitted tree's
/// index is zero.
fn parse_hmsg(params: &BaggyParams, hash: &[u8; 32]) -> Option<(Vec<u32>, u64)> {
    let (k, a) = (params.fors_trees, params.fors_height);
    let mut idxs = Vec::with_capacity(k - 1);
    for j in 0..k {
        let idx = extract_bit_window_checked(hash, j * a, a)? as u32;
        if j == k - 1 {
            if idx != 0 {
                return None;
            }
        } else {
            idxs.push(idx);
        }
    }
    let leaf = extract_bit_window_checked(hash, k * a, params.total_height())?;
    Some((idxs, leaf))
}

fn hmsg(pk: &BaggyPublicKey, r: &[u8; 32], mu: &[u8; 32], ctr: u32) -> [u8; 32] {
    let adrs = HashAdrs {
        kind: AdrsKind::ForsRoots,
        hash_step: ctr,
        ..HashAdrs::ZERO
    };
    th_call(
        Cshake256Suite,
        TAG_BAGGY_HMSG,
        &pk.pk_seed,
        &adrs,
        &[r, &pk.pk_root, mu],
    )
}

/// Smallest message counter whose hash satisfies the `FORS+C` constraint.
fn grind_hmsg(
    params: &BaggyParams,
    pk: &BaggyPublicKey,
    r: &[u8; 32],
    mu: &[u8; 32],
) -> Option<(u32, Vec<u32>, u64)> {
    (0..params.max_grind).find_map(|ctr| {
        parse_hmsg(params, &hmsg(pk, r, mu, ctr)).map(|(idxs, leaf)| (ctr, idxs, leaf))
    })
}

fn fors_pk(pk_seed: &[u8; 32], tree: u64, key_pair: u32, roots: &[[u8; 32]]) -> [u8; 32] {
    let adrs = HashAdrs {
        layer: 0,
        tree,
        kind: AdrsKind::ForsRoots,
        key_pair,
        chain_idx: 0,
        hash_step: 0,
    };
    th_tweak_tl(Cshake256Suite, pk_seed, &adrs, roots)
}

fn layer_grinder(
    pk_seed: &[u8; 32],
    layer: usize,
    tree: u64,
    key_pair: u32,
    node: &[u8; 32],
) -> DigestGrinder {
    DigestGrinder::new(
        TAG_BAGGY_DIGEST,
        pk_seed,
        &wots_c_digest_adrs(layer as u32, tree, key_pair),
        node,
    )
}

/// Subtree root implied by a layer signature on `node`.
fn layer_root(
    params: &BaggyParams,
    pk_seed: &[u8; 32],
    layer: usize,
    tree: u64,
    key_pair: u32,
    node: &[u8; 32],
    sig: &BaggyLayerSig,
) -> Option<[u8; 32]> {
    if sig.auth.len() != params.subtree_height || sig.ctr >= params.max_grind {
        return None;
    }
    let digits =
        layer_grinder(pk_seed, layer, tree, key_pair, node).digits_at(&params.wots, sig.ctr)?;
    let leaf = wots_c_recover_pk(
        &params.wots,
        pk_seed,
        layer as u32,
        tree,
        key_pair,
        &digits,
        &sig.chains,
    )?;
    walk_merkle_auth_path(
        Cshake256Suite,
        pk_seed,
        layer as u32,
        tree,
        AdrsKind::Tree,
        0,
        params.subtree_height,
        0,
        key_pair as usize,
        leaf,
        &sig.auth,
    )
}

/// Verify a `Baggy` signature.
pub fn baggy_verify(params: &BaggyParams, pk: &BaggyPublicKey, msg: &[u8], sig: &BaggySig) -> bool {
    verified_path(params, pk, msg, sig).is_some()
}

/// The nodes of a valid signature's path: entry 0 is the FORS public key, entry `l + 1` the
/// root of the layer-`l` subtree, and the last one equals `pk_root`. `None` if the
/// signature does not verify.
fn verified_path(
    params: &BaggyParams,
    pk: &BaggyPublicKey,
    msg: &[u8],
    sig: &BaggySig,
) -> Option<Vec<[u8; 32]>> {
    if !params.is_well_formed()
        || sig.fors.len() != params.signed_fors_trees()
        || sig.layers.len() != params.num_layers
        || sig.msg_ctr >= params.max_grind
    {
        return None;
    }
    let mu = baggy_msg_digest(pk, msg);
    let (idxs, leaf_idx) = parse_hmsg(params, &hmsg(pk, &sig.r, &mu, sig.msg_ctr))?;
    let (kp0, tree0) = params.path_at(leaf_idx, 0);
    let mut roots = Vec::with_capacity(idxs.len());
    for (j, (idx, opening)) in idxs.iter().zip(&sig.fors).enumerate() {
        let leaf = fors_leaf_hash_from_secret(
            Cshake256Suite,
            &pk.pk_seed,
            tree0,
            kp0,
            j as u32,
            *idx,
            &opening.secret,
        );
        roots.push(walk_merkle_auth_path(
            Cshake256Suite,
            &pk.pk_seed,
            0,
            tree0,
            AdrsKind::ForsTree,
            kp0,
            params.fors_height,
            j,
            *idx as usize,
            leaf,
            &opening.auth,
        )?);
    }
    let mut nodes = Vec::with_capacity(params.num_layers + 1);
    nodes.push(fors_pk(&pk.pk_seed, tree0, kp0, &roots));
    for (layer, layer_sig) in sig.layers.iter().enumerate() {
        let (kp, tree) = params.path_at(leaf_idx, layer);
        let root = layer_root(params, &pk.pk_seed, layer, tree, kp, &nodes[layer], layer_sig)?;
        nodes.push(root);
    }
    (nodes[params.num_layers] == pk.pk_root).then_some(nodes)
}

/// Single-party reference: public key from the top subtree.
pub fn baggy_reference_keygen(params: &BaggyParams, sk: &PqSecretKey) -> BaggyPublicKey {
    let top = (params.num_layers - 1) as u32;
    let leaves: Vec<[u8; 32]> = (0..params.subtree_leaves() as u32)
        .map(|kp| wots_c_reference_leaf(&params.wots, sk, top, 0, kp))
        .collect();
    let levels = merkle_levels(&sk.pk_seed, top, 0, AdrsKind::Tree, 0, &leaves, 0);
    BaggyPublicKey {
        pk_seed: sk.pk_seed,
        pk_root: levels[params.subtree_height][0],
    }
}

/// Single-party reference signature (tests and known-answer comparisons).
pub fn baggy_reference_sign(
    params: &BaggyParams,
    sk: &PqSecretKey,
    pk: &BaggyPublicKey,
    msg: &[u8],
) -> Option<BaggySig> {
    let mu = baggy_msg_digest(pk, msg);
    let opt_rand = th_call_secret(
        Cshake256Suite,
        TAG_BAGGY_OPT_RAND,
        &[],
        &HashAdrs::ZERO,
        &[&sk.sk_prf, &mu],
    );
    let r = th_call_secret(
        Cshake256Suite,
        TAG_BAGGY_R,
        &[],
        &HashAdrs::ZERO,
        &[&opt_rand, &mu],
    );
    let (msg_ctr, idxs, leaf_idx) = grind_hmsg(params, pk, &r, &mu)?;
    let (kp0, tree0) = params.path_at(leaf_idx, 0);
    let mut fors = Vec::with_capacity(idxs.len());
    let mut roots = Vec::with_capacity(idxs.len());
    for (j, idx) in idxs.iter().enumerate() {
        let secrets: Vec<[u8; 32]> = (0..1u32 << params.fors_height)
            .map(|leaf| fors_secret_leaf(Cshake256Suite, sk, tree0, kp0, j as u32, leaf))
            .collect();
        let leaves: Vec<[u8; 32]> = secrets
            .iter()
            .enumerate()
            .map(|(leaf, s)| {
                fors_leaf_hash_from_secret(
                    Cshake256Suite,
                    &pk.pk_seed,
                    tree0,
                    kp0,
                    j as u32,
                    leaf as u32,
                    s,
                )
            })
            .collect();
        let levels = merkle_levels(&pk.pk_seed, 0, tree0, AdrsKind::ForsTree, kp0, &leaves, j);
        roots.push(levels[params.fors_height][0]);
        fors.push(BaggyForsOpening {
            secret: secrets[*idx as usize],
            auth: merkle_auth_path(&levels, *idx as usize),
        });
    }
    let mut node = fors_pk(&pk.pk_seed, tree0, kp0, &roots);
    let mut layers = Vec::with_capacity(params.num_layers);
    for layer in 0..params.num_layers {
        let (kp, tree) = params.path_at(leaf_idx, layer);
        let leaves: Vec<[u8; 32]> = (0..params.subtree_leaves() as u32)
            .map(|l| wots_c_reference_leaf(&params.wots, sk, layer as u32, tree, l))
            .collect();
        let levels = merkle_levels(&pk.pk_seed, layer as u32, tree, AdrsKind::Tree, 0, &leaves, 0);
        let (ctr, digits) =
            layer_grinder(&pk.pk_seed, layer, tree, kp, &node).grind(&params.wots, params.max_grind)?;
        layers.push(BaggyLayerSig {
            ctr,
            chains: wots_c_reference_nodes(&params.wots, sk, layer as u32, tree, kp, &digits),
            auth: merkle_auth_path(&levels, kp as usize),
        });
        node = levels[params.subtree_height][0];
    }
    Some(BaggySig {
        r,
        msg_ctr,
        fors,
        layers,
    })
}

/// A cached layer signature with the two roots it connects. Both roots are taken from a
/// path that verified up to `pk_root` when the entry was created and are not updated after.
#[derive(Clone, Debug)]
struct CachedSig {
    sig: BaggyLayerSig,
    /// The value the signature signs: the root of the subtree below.
    child_root: [u8; 32],
    /// The root of the subtree the signing leaf belongs to.
    layer_root: [u8; 32],
}

/// The cached public leaves of one subtree and the root they hash to.
#[derive(Clone, Debug)]
struct CachedLeaves {
    leaves: Vec<[u8; 32]>,
    root: [u8; 32],
}

/// `Waistband`: public cache of top-layer subtree leaves and leaf signatures, bound to one
/// [`BaggyKeyBinding`]. A fresh cache is unbound and binds to the key it first stores an
/// entry for; from then on every use under another key or parameter set is refused.
#[derive(Clone, Debug, Default)]
pub struct WaistbandCache {
    top_layers: usize,
    max_entries: usize,
    bound: Option<BaggyKeyBinding>,
    leaves: BTreeMap<(u32, u64), CachedLeaves>,
    sigs: BTreeMap<(u32, u64, u32), CachedSig>,
    hits: u64,
    misses: u64,
}

impl WaistbandCache {
    /// Cache the top `top_layers` layers, holding at most `max_entries` signatures and as
    /// many leaf sets. `top_layers = 0` disables the cache.
    pub fn new(top_layers: usize, max_entries: usize) -> Self {
        Self {
            top_layers,
            max_entries,
            ..Self::default()
        }
    }

    pub fn disabled() -> Self {
        Self::default()
    }

    pub fn top_layers(&self) -> usize {
        self.top_layers
    }

    pub fn sig_entries(&self) -> usize {
        self.sigs.len()
    }

    pub fn leaf_entries(&self) -> usize {
        self.leaves.len()
    }

    /// Layer signatures served from the cache so far.
    pub fn hits(&self) -> u64 {
        self.hits
    }

    /// Covered layers that had to be evaluated because nothing was cached.
    pub fn misses(&self) -> u64 {
        self.misses
    }

    fn covers(&self, params: &BaggyParams, layer: usize) -> bool {
        layer + self.top_layers >= params.num_layers
    }

    /// The key this cache is bound to; `None` while it has stored nothing.
    pub fn binding(&self) -> Option<&BaggyKeyBinding> {
        self.bound.as_ref()
    }

    fn check_identity(&self, binding: &BaggyKeyBinding) -> Result<(), BaggyError> {
        match &self.bound {
            Some(bound) if bound != binding => Err(BaggyError::CacheIdentityMismatch),
            _ => Ok(()),
        }
    }

    /// Called after [`Self::check_identity`] and before the first entry is stored. A
    /// disabled cache stores nothing and stays unbound.
    fn bind(&mut self, binding: &BaggyKeyBinding) {
        if self.top_layers > 0 {
            self.bound = Some(*binding);
        }
    }

    fn insert_leaves(&mut self, layer: usize, tree: u64, set: CachedLeaves) {
        if self.leaves.len() < self.max_entries {
            self.leaves.insert((layer as u32, tree), set);
        }
    }

    fn insert_sig(&mut self, layer: usize, tree: u64, key_pair: u32, entry: CachedSig) {
        if self.sigs.len() < self.max_entries {
            self.sigs.insert((layer as u32, tree, key_pair), entry);
        }
    }

    /// Journal codeword binding for this cache precomputation.
    pub fn precompute_release_binding(&self, binding: &BaggyKeyBinding) -> [u8; 32] {
        cshake256_32(b"QSAG.BAGGY.PRECOMPUTE.RELEASE/v1", &encode_multi_frame(&[
            &binding.identity(), &(self.top_layers as u64).to_le_bytes()]))
    }

    /// Fill every signature of the top `top_layers` layers eagerly (distributed-key-ceremony
    /// time). Requires `top_layers < num_layers`: the bottom layer signs message-dependent
    /// FORS keys and cannot be precomputed. Sweeps `sum_{j <= L} 2^{h' j}` subtrees.
    ///
    /// Refused before any MPC work if `binding` does not match the engine, `pk` and `params`
    /// or if the cache is bound to another identity. Every digit vector is checked against
    /// `ledger` and recorded there before the chain-node opening round, and every entry is
    /// verified against the swept subtree roots before it is stored.
    pub fn precompute<L: FirstSignedLedger + ?Sized>(
        &mut self,
        engine: &mut Rss256Engine,
        params: &BaggyParams,
        pk: &BaggyPublicKey,
        binding: &BaggyKeyBinding,
        ledger: &mut L,
    ) -> Result<(), BaggyError> {
        let (d, hp, chains) = (params.num_layers, params.subtree_height, params.wots.chains);
        if !params.is_well_formed() || self.top_layers == 0 || self.top_layers >= d {
            return Err(BaggyError::InvalidParameters);
        }
        check_key_binding(engine, params, pk, binding)?;
        self.check_identity(binding)?;
        let lowest = d - 1 - self.top_layers;
        if hp * self.top_layers > 16 {
            return Err(BaggyError::InvalidParameters);
        }
        ledger.begin_release(&binding.identity(), engine.session_id(), &self.precompute_release_binding(binding))?;
        // Every subtree of the covered layers, plus the layer below for their child roots.
        let mut subtrees: Vec<(usize, u64)> = Vec::new();
        for layer in (lowest..d).rev() {
            for tree in 0..1u64 << (hp * (d - 1 - layer)) {
                subtrees.push((layer, tree));
            }
        }
        let per_tree = params.subtree_leaves() * chains;
        let mut lanes = Vec::with_capacity(subtrees.len() * per_tree);
        for &(layer, tree) in &subtrees {
            for kp in 0..params.subtree_leaves() as u32 {
                for c in 0..chains as u32 {
                    lanes.push(LaneSpec::wots(layer as u32, tree, kp, c));
                }
            }
        }
        let sweep = Sweep::evaluate(engine, &pk.pk_seed, lanes, WOTS_STEPS as u8)?;
        engine.check()?;
        engine.mark_open_round();
        let picks: Vec<(usize, u8)> =
            (0..sweep.lane_count()).map(|l| (l, WOTS_STEPS as u8)).collect();
        let endpoints = sweep.open_positions(engine, &picks)?;
        let mut levels: BTreeMap<(usize, u64), Vec<Vec<[u8; 32]>>> = BTreeMap::new();
        for (i, &(layer, tree)) in subtrees.iter().enumerate() {
            let leaves: Vec<[u8; 32]> = endpoints[i * per_tree..(i + 1) * per_tree]
                .chunks_exact(chains)
                .enumerate()
                .map(|(kp, ends)| wots_c_leaf(&pk.pk_seed, layer as u32, tree, kp as u32, ends))
                .collect();
            levels.insert(
                (layer, tree),
                merkle_levels(&pk.pk_seed, layer as u32, tree, AdrsKind::Tree, 0, &leaves, 0),
            );
        }
        if levels[&(d - 1, 0)][hp][0] != pk.pk_root {
            return Err(BaggyError::CacheInconsistent);
        }
        // Digits of every covered leaf on its child root (a root of a subtree swept above,
        // so verified at the barrier), then one opening round for all.
        let identity = binding.identity();
        let mut records: Vec<FirstSignedRecord> = Vec::new();
        let mut jobs: Vec<(usize, u64, u32, u32, [u8; 32])> = Vec::new();
        let mut node_picks: Vec<(usize, u8)> = Vec::new();
        for (i, &(layer, tree)) in subtrees.iter().enumerate() {
            if layer == lowest {
                continue;
            }
            for kp in 0..params.subtree_leaves() as u32 {
                let child_root = levels[&(layer - 1, (tree << hp) | u64::from(kp))][hp][0];
                let (ctr, digits) = layer_grinder(&pk.pk_seed, layer, tree, kp, &child_root)
                    .grind(&params.wots, params.max_grind)
                    .ok_or(BaggyError::GrindExhausted)?;
                let key = StaticKeyId {
                    identity,
                    layer: layer as u32,
                    tree,
                    key_pair: kp,
                };
                admit_digits(ledger, key, digits.clone(), false, &mut records)?;
                let lane0 = i * per_tree + kp as usize * chains;
                node_picks.extend(digits.iter().enumerate().map(|(c, dg)| (lane0 + c, *dg)));
                jobs.push((layer, tree, kp, ctr, child_root));
            }
        }
        if !records.is_empty() {
            ledger.sync_record(&records)?;
        }
        engine.mark_open_round();
        let nodes = sweep.open_positions(engine, &node_picks)?;
        let mut entries = Vec::with_capacity(jobs.len());
        for (job, chain_nodes) in jobs.iter().zip(nodes.chunks_exact(chains)) {
            let &(layer, tree, kp, ctr, child_root) = job;
            let tree_levels = &levels[&(layer, tree)];
            let sig = BaggyLayerSig {
                ctr,
                chains: chain_nodes.to_vec(),
                auth: merkle_auth_path(tree_levels, kp as usize),
            };
            let root = tree_levels[hp][0];
            if layer_root(params, &pk.pk_seed, layer, tree, kp, &child_root, &sig) != Some(root) {
                return Err(BaggyError::SelfCheckFailed);
            }
            entries.push((
                layer,
                tree,
                kp,
                CachedSig {
                    sig,
                    child_root,
                    layer_root: root,
                },
            ));
        }
        self.bind(binding);
        for (layer, tree, kp, entry) in entries {
            self.insert_sig(layer, tree, kp, entry);
        }
        for (&(layer, tree), tree_levels) in &levels {
            if layer > lowest {
                self.insert_leaves(
                    layer,
                    tree,
                    CachedLeaves {
                        leaves: tree_levels[0].clone(),
                        root: tree_levels[hp][0],
                    },
                );
            }
        }
        Ok(())
    }
}

/// The binding must be that of `pk` under `params`, `pk` must belong to the engine's key,
/// and the engine's key shares must carry the same identity: they are bound to it by
/// [`baggy_keygen_mpc`], so a binding rebuilt for other parameters or another root does not
/// match shares that went through key generation, and unbound shares sign nothing.
fn check_key_binding(
    engine: &Rss256Engine,
    params: &BaggyParams,
    pk: &BaggyPublicKey,
    binding: &BaggyKeyBinding,
) -> Result<(), BaggyError> {
    if !binding.matches(params, pk) || pk.pk_seed != engine.pk_seed() {
        return Err(BaggyError::KeyBindingMismatch);
    }
    match engine.key_identity() {
        Ok(Some(bound)) if bound == binding.identity() => Ok(()),
        _ => Err(BaggyError::KeyBindingMismatch),
    }
}

/// Check `digits` against the first-signed record of `key`. An equal record admits them; a
/// different one refuses them; with no record they are queued in `records` for the write
/// that precedes the opening round, unless `must_exist` (the message was vouched for by the
/// cache alone), which refuses.
fn admit_digits<L: FirstSignedLedger + ?Sized>(
    ledger: &L,
    key: StaticKeyId,
    digits: Vec<u8>,
    must_exist: bool,
    records: &mut Vec<FirstSignedRecord>,
) -> Result<(), BaggyError> {
    match ledger.first_signed(&key)? {
        Some(first) if first == digits => Ok(()),
        Some(_) => Err(BaggyError::StaticKeyDigitsConflict {
            layer: key.layer,
            tree: key.tree,
            key_pair: key.key_pair,
        }),
        None if must_exist => Err(BaggyError::CacheUnanchored),
        None => {
            records.push(FirstSignedRecord { key, digits });
            Ok(())
        }
    }
}

/// Verify every cached entry of a planned path, before anything is evaluated or opened:
/// each cached signature against its stored child root and subtree root, each cached leaf
/// set against its stored root, adjacent cached layers against each other, and the top
/// against `pk_root`. A cached signature above a layer that is evaluated in full is compared
/// with that layer's computed root later, before the chain-node opening round.
fn authenticate_cached_path(
    params: &BaggyParams,
    pk: &BaggyPublicKey,
    leaf_idx: u64,
    plans: &[LayerPlan],
) -> Result<(), BaggyError> {
    // Root of the layer below as the cache states it; `None` if that layer is computed.
    let mut below: Option<[u8; 32]> = None;
    for (layer, plan) in plans.iter().enumerate() {
        let (kp, tree) = params.path_at(leaf_idx, layer);
        below = match plan {
            LayerPlan::Cached(entry) => {
                let root =
                    layer_root(params, &pk.pk_seed, layer, tree, kp, &entry.child_root, &entry.sig);
                if root != Some(entry.layer_root) || below.is_some_and(|r| r != entry.child_root) {
                    return Err(BaggyError::CacheEntryUnauthenticated);
                }
                Some(entry.layer_root)
            }
            LayerPlan::LeafOnly(set, _) => {
                if set.leaves.len() != params.subtree_leaves() {
                    return Err(BaggyError::CacheEntryUnauthenticated);
                }
                let levels =
                    merkle_levels(&pk.pk_seed, layer as u32, tree, AdrsKind::Tree, 0, &set.leaves, 0);
                if levels[params.subtree_height][0] != set.root {
                    return Err(BaggyError::CacheEntryUnauthenticated);
                }
                Some(set.root)
            }
            LayerPlan::Full(_) => None,
        };
    }
    if below.is_some_and(|r| r != pk.pk_root) {
        return Err(BaggyError::CacheEntryUnauthenticated);
    }
    Ok(())
}

/// Distributed key generation: sweeps the top subtree, verifies, opens its chain endpoints.
/// The top subtree's leaves are placed in `cache` when it covers the top layer.
///
/// Returns the public key and its [`BaggyKeyBinding`], which the caller stores with the key
/// shares and hands to every later [`baggy_sign_mpc`] and [`WaistbandCache::precompute`]. A
/// cache already bound to another `pk_seed` or parameter set is refused before the sweep,
/// one bound to another `pk_root` once the root is known; nothing is stored in either case.
/// Key generation opens chain endpoints only, so it writes nothing to a first-signed ledger.
