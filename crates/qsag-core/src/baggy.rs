//! `Baggy`: stateless threshold hash-based signatures (`WOTS+C` `w = 4`, `v = 128`, `T = 192`,
//! hypertree, over `FORS+C` or `PORS+FP`), with the `Waistband` top-layer cache.
//!
//! ### Structure
//! A hypertree of `d` layers of height-`h'` subtrees over `WOTS+C` leaves ([`crate::wots_c`]);
//! the bottom leaf signs a few-time public key ([`BaggyFewTime`]):
//! * **Version 1, `FORS+C`:** `k - 1` trees of height `a`. A public counter is ground until
//!   the index of the `k`-th tree is zero, and that tree is omitted.
//! * **Version 2, `PORS+FP`** ([`crate::pors_fp`]): one tree; a public counter is ground
//!   until the distinct sorted index subset has a multiproof within the pruning bound.
//!
//! All secret values derive from the shared `sk_seed`; only values that belong in a
//! signature, or chain endpoints and leaf hashes that are public-key material, are opened.
//!
//! ### Engines
//! The ceremonies are written against [`BaggyEngine`]. [`Rss256Engine`] is the 2-of-3
//! replicated engine; [`crate::spdz_sweep::SpdzSweepEngine`] runs the same sweep for any
//! `2 <= t <= n`. Both produce the signature of [`baggy_reference_sign`], byte for byte.
//!
//! ### Three phases ([`baggy_sign_mpc`])
//! 1. **Randomiser.** `opt_rand = PRF(sk_prf, mu)` stays shared and keys
//!    `R = PRF(opt_rand, mu)`; both are evaluated under MPC, verified at their own barrier,
//!    and only `R` is opened. `R` therefore depends on the shared key and the message alone:
//!    a signer that aborts after seeing `R` gets the same `R`, and the same leaf and
//!    few-time indices, on every retry.
//! 2. **All-layer sweep.** `R` fixes every address, so the few-time leaves and the chains of
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
//! * The number of signatures per key is bounded by the few-time security of the bottom
//!   scheme at the chosen geometry; [`BaggyParams::SHA3_128F`] reuses the tree geometry of
//!   [`crate::tsw_baggy::PqHashParams::BAGGY_TSW_128F`], which that preset sizes for `2^16`
//!   signatures. For version 2 the per-tree bound is
//!   [`crate::pors_fp::PorsFpParams::forgery_bits_milli`]; how often one hypertree leaf is
//!   reused over `2^16` signatures of a height-32 hypertree is the same as for version 1.
//!   The layer signatures use the 128-chain `WOTS+C` encoding of a full
//!   256-bit digest ([`crate::wots_c::WotsCParams::V128`]).
//! * The `t`-of-`n` engine costs one authenticated 64-instance permutation per 64 lanes per
//!   level, 38,400 triple words each. A [`BaggyParams::SHA3_128F_V2`] signature without
//!   `Waistband` is 578 such permutations (512 for the hypertree, 64 for the `PORS+FP`
//!   tree, 2 for the randomiser); see [`crate::spdz_sweep`].
//! * `BaggyPoseidon2` is the existing authenticated-share Poseidon2 engine under this suite's
//!   name; it does not run on the 256-lane engine.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::fmt;

use crate::keccak_mpc::TSW_SUITE_MIDSTATE;
use crate::pors_fp::{
    PorsFpOpening, PorsFpParams, pors_fp_auth, pors_fp_root, pors_fp_select, pors_levels,
};
use crate::rss256::{Rss256Engine, Rss256Error, SharedState256, active_lane_mask};
use crate::sponge::keccak::{
    Cshake256Xof, SHAKE256_RATE_BYTES, cshake256_32, encode_multi_frame,
};
use crate::tsw_baggy::{
    AdrsKind, Cshake256Suite, HashAdrs, PqSecretKey, extract_bit_window_checked,
    fors_leaf_hash_from_secret, th_call, th_call_secret, th_chain_f, th_pre_hash, th_preimage,
    th_secret_prf, th_tweak_tl, walk_merkle_auth_path,
};
use crate::wipe::SecretVec;
use crate::wots_c::{
    DigestGrinder, LaneSpec, Sweep, WOTS_STEPS, WotsCParams, merkle_auth_path, merkle_levels,
    wots_c_digest_adrs, wots_c_leaf, wots_c_recover_pk, wots_c_reference_leaf,
    wots_c_reference_nodes,
};

/// Role tags of the `Baggy` suite.
pub const TAG_BAGGY_OPT_RAND: &[u8] = b"QSAG.BAGGY.OPTRAND/v1";
pub const TAG_BAGGY_R: &[u8] = b"QSAG.BAGGY.R/v1";
pub const TAG_BAGGY_HMSG: &[u8] = b"QSAG.BAGGY.HMSG/v1";
/// Message hash of the `PORS+FP` suite (version 2): an XOF, read as the hypertree leaf index
/// followed by the index words of [`pors_fp_select`].
pub const TAG_BAGGY_V2_HMSG: &[u8] = b"QSAG.BAGGY.HMSG/v2";
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

/// The few-time scheme a hypertree leaf signs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BaggyFewTime {
    /// `FORS+C` with [`BaggyParams::fors_trees`] trees of height
    /// [`BaggyParams::fors_height`] (version 1).
    ForsC,
    /// [`crate::pors_fp`]: one tree, a distinct sorted subset, a bounded canonical
    /// multiproof (version 2). `fors_trees` and `fors_height` are zero.
    PorsFp(PorsFpParams),
}

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
    pub few_time: BaggyFewTime,
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
        few_time: BaggyFewTime::ForsC,
    };

    /// Version 2: the hypertree of [`Self::SHA3_128F`] over
    /// [`PorsFpParams::SHA3_128F`]. At most 71,654-byte signatures; the few-time layer is
    /// 2048 leaves under MPC, as before, and at most 4,994 bytes instead of 7,168.
    pub const SHA3_128F_V2: Self = Self {
        fors_trees: 0,
        fors_height: 0,
        few_time: BaggyFewTime::PorsFp(PorsFpParams::SHA3_128F),
        ..Self::SHA3_128F
    };

    /// Small geometry for tests.
    pub const TEST_SMALL: Self = Self {
        wots: WotsCParams::V128,
        subtree_height: 2,
        num_layers: 3,
        fors_trees: 5,
        fors_height: 3,
        max_grind: 1 << 26,
        few_time: BaggyFewTime::ForsC,
    };

    /// Small version-2 geometry for tests.
    pub const TEST_SMALL_V2: Self = Self {
        fors_trees: 0,
        fors_height: 0,
        few_time: BaggyFewTime::PorsFp(PorsFpParams::TEST_SMALL),
        ..Self::TEST_SMALL
    };

    pub const fn total_height_checked(&self) -> Option<usize> {
        self.subtree_height.checked_mul(self.num_layers)
    }

    /// FORS trees that appear in a signature (none under `PORS+FP`).
    pub const fn signed_fors_trees_checked(&self) -> Option<usize> {
        match self.few_time {
            BaggyFewTime::ForsC => self.fors_trees.checked_sub(1),
            BaggyFewTime::PorsFp(_) => Some(0),
        }
    }

    pub const fn is_well_formed(&self) -> bool {
        if !self.wots.is_well_formed()
            || self.subtree_height < 1
            || self.subtree_height > 8
            || self.num_layers < 1
            || self.num_layers > 62
        {
            return false;
        }
        let Some(total_h) = self.total_height_checked() else {
            return false;
        };
        if total_h > 62 {
            return false;
        }
        match self.few_time {
            BaggyFewTime::ForsC => {
                if self.fors_trees < 2
                    || self.fors_trees > 256
                    || self.fors_height < 1
                    || self.fors_height > 16
                {
                    return false;
                }
                let Some(fors_bits) = self.fors_trees.checked_mul(self.fors_height) else {
                    return false;
                };
                let Some(total_bits) = fors_bits.checked_add(total_h) else {
                    return false;
                };
                if total_bits > 256 {
                    return false;
                }
            }
            BaggyFewTime::PorsFp(pors) => {
                if self.fors_trees != 0 || self.fors_height != 0 || !pors.is_well_formed() {
                    return false;
                }
            }
        }
        self.sig_bytes_checked().is_some()
    }

    /// Signature size; under `PORS+FP` the largest one, reached when the multiproof is at
    /// its bound.
    pub const fn sig_bytes_checked(&self) -> Option<usize> {
        let fors_bytes = match self.few_time {
            BaggyFewTime::ForsC => {
                let Some(signed_fors) = self.signed_fors_trees_checked() else {
                    return None;
                };
                let Some(fors_auth_bytes) = 32usize.checked_mul(self.fors_height) else {
                    return None;
                };
                let Some(per_fors) = 32usize.checked_add(fors_auth_bytes) else {
                    return None;
                };
                let Some(fors_bytes) = signed_fors.checked_mul(per_fors) else {
                    return None;
                };
                fors_bytes
            }
            BaggyFewTime::PorsFp(pors) => pors.opening_bytes_max(),
        };
        let Some(wots_bytes) = 32usize.checked_mul(self.wots.chains) else {
            return None;
        };
        let Some(sub_auth_bytes) = 32usize.checked_mul(self.subtree_height) else {
            return None;
        };
        let Some(layer_head) = 4usize.checked_add(wots_bytes) else {
            return None;
        };
        let Some(layer_inner) = layer_head.checked_add(sub_auth_bytes) else {
            return None;
        };
        let Some(layers_bytes) = self.num_layers.checked_mul(layer_inner) else {
            return None;
        };
        let Some(prefix_bytes) = 36usize.checked_add(fors_bytes) else {
            return None;
        };
        prefix_bytes.checked_add(layers_bytes)
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
            few_time,
        } = *self;
        let WotsCParams {
            chains,
            zero_digits,
            target_sum,
        } = wots;
        let word = |v: usize| (v as u64).to_be_bytes();
        let words = [
            word(chains),
            word(zero_digits),
            word(target_sum),
            word(subtree_height),
            word(num_layers),
            word(fors_trees),
            word(fors_height),
            u64::from(max_grind).to_be_bytes(),
        ];
        let mut fields: Vec<&[u8]> = words.iter().map(|w| w.as_slice()).collect();
        // Version 1 hashes exactly the eight words above, as it always has.
        let pors_words;
        if let BaggyFewTime::PorsFp(PorsFpParams {
            tree_height,
            reveal,
            max_auth_nodes,
        }) = few_time
        {
            pors_words = [word(tree_height), word(reveal), word(max_auth_nodes)];
            fields.push(b"PORS+FP");
            fields.extend(pors_words.iter().map(|w| w.as_slice()));
        }
        cshake256_32(TAG_BAGGY_PARAMS, &encode_multi_frame(&fields))
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
    fn begin_release(
        &mut self,
        _key: &[u8; 32],
        _ceremony: &[u8; 32],
        _codeword: &[u8; 32],
    ) -> Result<(), FirstSignedError> {
        Err(FirstSignedError::Io)
    }

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

    /// Canonical public-state commitment for an external keyed integrity wrapper.
    /// This is not itself a MAC or a durability guarantee.
    pub fn authentication_digest(&self) -> [u8; 32] {
        let mut xof = crate::sponge::keccak::Cshake256Xof::new(b"QSAG.BAGGY.MEMORY_RECORDS/v1");
        xof.absorb(&(self.records.len() as u64).to_be_bytes());
        for (key, digits) in &self.records {
            xof.absorb(&key.identity);
            xof.absorb(&key.layer.to_be_bytes());
            xof.absorb(&key.tree.to_be_bytes());
            xof.absorb(&key.key_pair.to_be_bytes());
            xof.absorb(&(digits.len() as u64).to_be_bytes());
            xof.absorb(digits);
        }
        xof.absorb(&self.syncs.to_be_bytes());
        xof.absorb(&[u8::from(self.fail_next)]);
        let mut out = [0; 32];
        xof.squeeze(&mut out);
        out
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
    fn begin_release(
        &mut self,
        _key: &[u8; 32],
        _ceremony: &[u8; 32],
        _codeword: &[u8; 32],
    ) -> Result<(), FirstSignedError> {
        Ok(())
    }
    fn first_signed(&self, key: &StaticKeyId) -> Result<Option<Vec<u8>>, FirstSignedError> {
        Ok(self.records.get(key).cloned())
    }

    fn sync_record(&mut self, records: &[FirstSignedRecord]) -> Result<(), FirstSignedError> {
        if self.fail_next {
            self.fail_next = false;
            return Err(FirstSignedError::Io);
        }
        let mut staged = self.records.clone();
        for r in records {
            if let Some(existing) = staged.get(&r.key) {
                if *existing != r.digits {
                    return Err(FirstSignedError::Conflict);
                }
            } else {
                staged.insert(r.key, r.digits.clone());
            }
        }
        self.records = staged;
        self.syncs += 1;
        Ok(())
    }
}

/// Authenticated durable first-signed records. Retain `checkpoint()` independently
/// before opening signing material; supply it on recovery to reject rollback.
#[cfg(feature = "std")]
pub struct FsFirstSignedLedger(
    crate::durable_ledger::Ledger,
    Option<crate::ceremony_journal::CeremonyReservation>,
);
#[cfg(feature = "std")]
impl FsFirstSignedLedger {
    /// Consume a committed journal permit for the next signing or precomputation attempt.
    /// Bind key_id to BaggyKeyBinding::identity(), ceremony_id to the engine session,
    /// and epoch_or_codeword to baggy_msg_digest (or precompute_release_binding).
    pub fn authorize_release(
        &mut self,
        journal: &crate::ceremony_journal::FsCeremonyJournal,
        permit: crate::ceremony_journal::CeremonyReleasePermit,
    ) -> Result<(), FirstSignedError> {
        self.1 = None;
        self.1 = Some(
            journal
                .consume_release(permit)
                .map_err(|_| FirstSignedError::Io)?,
        );
        Ok(())
    }

    pub fn provision_genesis(
        path: impl Into<std::path::PathBuf>,
        key: [u8; 32],
    ) -> Result<Self, FirstSignedError> {
        crate::durable_ledger::Ledger::create(path, key, b"QSAG.FIRST_SIGNED.V1")
            .map(|ledger| Self(ledger, None))
            .map_err(|_| FirstSignedError::Io)
    }
    pub fn open_existing(
        path: impl Into<std::path::PathBuf>,
        key: [u8; 32],
        checkpoint: crate::LedgerCheckpoint,
    ) -> Result<Self, FirstSignedError> {
        crate::durable_ledger::Ledger::open(path, key, b"QSAG.FIRST_SIGNED.V1", checkpoint)
            .map(|ledger| Self(ledger, None))
            .map_err(|_| FirstSignedError::Corrupt)
    }
    pub fn checkpoint(&self) -> crate::LedgerCheckpoint {
        self.0.checkpoint()
    }
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
    fn begin_release(
        &mut self,
        key: &[u8; 32],
        ceremony: &[u8; 32],
        codeword: &[u8; 32],
    ) -> Result<(), FirstSignedError> {
        let r = self.1.take().ok_or(FirstSignedError::Io)?;
        if r.key_id != *key || r.ceremony_id != *ceremony || r.epoch_or_codeword != *codeword {
            return Err(FirstSignedError::Conflict);
        }
        Ok(())
    }

    fn first_signed(&self, key: &StaticKeyId) -> Result<Option<Vec<u8>>, FirstSignedError> {
        Ok(self
            .0
            .read()
            .map_err(|_| FirstSignedError::Corrupt)?
            .get(&Self::key(key))
            .cloned())
    }
    fn sync_record(&mut self, records: &[FirstSignedRecord]) -> Result<(), FirstSignedError> {
        let mut stored = self.0.read().map_err(|_| FirstSignedError::Corrupt)?;
        for r in records {
            let key = Self::key(&r.key);
            if stored.get(&key).is_some_and(|d| *d != r.digits) {
                return Err(FirstSignedError::Conflict);
            }
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
    /// `FORS+C` openings (version 1); empty under `PORS+FP`.
    pub fors: Vec<BaggyForsOpening>,
    /// The `PORS+FP` opening (version 2); `None` under `FORS+C`.
    pub pors: Option<PorsFpOpening>,
    pub layers: Vec<BaggyLayerSig>,
}

impl BaggySig {
    /// `r || be32(msg_ctr) || few-time part || layers`, where a `FORS+C` opening is
    /// `secret || auth`, the `PORS+FP` part is [`PorsFpOpening::to_wire_bytes`], and a layer
    /// is `be32(ctr) || chains || auth`. Every count is fixed by the parameters except the
    /// `PORS+FP` multiproof length, which the encoding carries.
    pub fn to_wire_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(&self.r);
        out.extend_from_slice(&self.msg_ctr.to_be_bytes());
        for opening in &self.fors {
            out.extend_from_slice(&opening.secret);
            out.extend_from_slice(opening.auth.as_flattened());
        }
        if let Some(pors) = &self.pors {
            out.extend_from_slice(&pors.to_wire_bytes());
        }
        for layer in &self.layers {
            out.extend_from_slice(&layer.ctr.to_be_bytes());
            out.extend_from_slice(layer.chains.as_flattened());
            out.extend_from_slice(layer.auth.as_flattened());
        }
        out
    }

    /// Inverse of [`Self::to_wire_bytes`] under `params`. The whole of `raw` must be used;
    /// counters at or above `max_grind` and oversized multiproofs are refused. Decoding
    /// checks shape only: the result still has to pass [`baggy_verify`].
    pub fn from_wire_bytes(params: &BaggyParams, raw: &[u8]) -> Option<Self> {
        if !params.is_well_formed() || raw.len() > params.sig_bytes_checked()? {
            return None;
        }
        fn take<'a>(rest: &mut &'a [u8], n: usize) -> Option<&'a [u8]> {
            let (head, tail) = rest.split_at_checked(n)?;
            *rest = tail;
            Some(head)
        }
        let mut rest = raw;
        let nodes = |bytes: &[u8]| bytes.as_chunks::<32>().0.to_vec();
        let be32 = |bytes: &[u8]| Some(u32::from_be_bytes(bytes.try_into().ok()?));
        let r: [u8; 32] = take(&mut rest, 32)?.try_into().ok()?;
        let msg_ctr = be32(take(&mut rest, 4)?)?;
        let mut fors = Vec::new();
        let mut pors = None;
        match params.few_time {
            BaggyFewTime::ForsC => {
                for _ in 0..params.signed_fors_trees_checked()? {
                    fors.push(BaggyForsOpening {
                        secret: take(&mut rest, 32)?.try_into().ok()?,
                        auth: nodes(take(&mut rest, 32 * params.fors_height)?),
                    });
                }
            }
            BaggyFewTime::PorsFp(pors_params) => {
                let (opening, used) = PorsFpOpening::from_wire_bytes(&pors_params, rest)?;
                take(&mut rest, used)?;
                pors = Some(opening);
            }
        }
        let mut layers = Vec::with_capacity(params.num_layers);
        for _ in 0..params.num_layers {
            layers.push(BaggyLayerSig {
                ctr: be32(take(&mut rest, 4)?)?,
                chains: nodes(take(&mut rest, 32 * params.wots.chains)?),
                auth: nodes(take(&mut rest, 32 * params.subtree_height)?),
            });
        }
        (rest.is_empty()
            && msg_ctr < params.max_grind
            && layers.iter().all(|l| l.ctr < params.max_grind))
        .then_some(Self {
            r,
            msg_ctr,
            fors,
            pors,
            layers,
        })
    }
}

/// The MPC operations a `Baggy` ceremony runs. Key generation, signing and the `Waistband`
/// precomputation are written once against this trait; the threshold structure is the
/// engine's. [`Rss256Engine`] is the 2-of-3 replicated engine and
/// [`crate::spdz_sweep::SpdzSweepEngine`] the `t`-of-`n` authenticated-share engine.
///
/// Contract: nothing derived from the shared key leaves an engine except through
/// [`Self::randomiser`] and [`Self::open_round`], and [`Self::open_round`] fails unless every
/// gate evaluated so far has passed [`Self::barrier`].
pub trait BaggyEngine {
    /// Shared chain values of one [`Self::sweep`].
    type Sweep;

    fn pk_seed(&self) -> [u8; 32];
    fn session_id(&self) -> &[u8; 32];
    /// The [`BaggyKeyBinding::identity`] recorded in the key shares, if any.
    fn key_identity(&self) -> Result<Option<[u8; 32]>, BaggyError>;
    /// Record `identity` in the key shares; refused if they carry another one.
    fn bind_key_identity(&mut self, identity: &[u8; 32]) -> Result<(), BaggyError>;
    /// `R = PRF(PRF(sk_prf, mu), mu)`: both calls evaluated shared, verified, and only `R`
    /// opened.
    fn randomiser(&mut self, mu: &[u8; 32]) -> Result<[u8; 32], BaggyError>;
    /// Evaluate every lane (ordered by non-increasing `steps`) to its last position.
    fn sweep(
        &mut self,
        pk_seed: &[u8; 32],
        lanes: Vec<LaneSpec>,
    ) -> Result<Self::Sweep, BaggyError>;
    /// Verify every gate evaluated since the last barrier.
    fn barrier(&mut self) -> Result<(), BaggyError>;
    /// One opening round: the value of each `(lane, position)` pick.
    fn open_round(
        &mut self,
        sweep: &Self::Sweep,
        picks: &[(usize, u8)],
    ) -> Result<Vec<[u8; 32]>, BaggyError>;
}

impl BaggyEngine for Rss256Engine {
    type Sweep = Sweep;

    fn pk_seed(&self) -> [u8; 32] {
        Rss256Engine::pk_seed(self)
    }

    fn session_id(&self) -> &[u8; 32] {
        Rss256Engine::session_id(self)
    }

    fn key_identity(&self) -> Result<Option<[u8; 32]>, BaggyError> {
        Ok(Rss256Engine::key_identity(self)?)
    }

    fn bind_key_identity(&mut self, identity: &[u8; 32]) -> Result<(), BaggyError> {
        Ok(Rss256Engine::bind_key_identity(self, identity)?)
    }

    fn randomiser(&mut self, mu: &[u8; 32]) -> Result<[u8; 32], BaggyError> {
        let one = active_lane_mask(1);
        let (frame, off) = keyed_mu_frame(TAG_BAGGY_OPT_RAND, mu);
        let mut st = SharedState256::from_public_frames(&TSW_SUITE_MIDSTATE, &[frame])?;
        st.xor_shared_key(off, self.sk_prf_slots(), &one)?;
        self.mark_sequential_level();
        self.permute(&mut st, 1)?;
        let opt_rand = st.digest();
        let (frame, off) = keyed_mu_frame(TAG_BAGGY_R, mu);
        let mut st = SharedState256::from_public_frames(&TSW_SUITE_MIDSTATE, &[frame])?;
        st.xor_shared_digest(off, &opt_rand)?;
        self.mark_sequential_level();
        self.permute(&mut st, 1)?;
        self.check()?;
        self.mark_open_round();
        Ok(self.open_digests(&st.digest(), &one, 1)?[0])
    }

    fn sweep(
        &mut self,
        pk_seed: &[u8; 32],
        lanes: Vec<LaneSpec>,
    ) -> Result<Sweep, BaggyError> {
        Ok(Sweep::evaluate(self, pk_seed, lanes, WOTS_STEPS as u8)?)
    }

    fn barrier(&mut self) -> Result<(), BaggyError> {
        Ok(self.check()?)
    }

    fn open_round(
        &mut self,
        sweep: &Sweep,
        picks: &[(usize, u8)],
    ) -> Result<Vec<[u8; 32]>, BaggyError> {
        self.mark_open_round();
        Ok(sweep.open_positions(self, picks)?)
    }
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
            Self::CacheEntryUnauthenticated => f.write_str("Waistband entry failed authentication"),
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
pub(crate) fn keyed_mu_frame(tag: &[u8], mu: &[u8; 32]) -> ([u8; SHAKE256_RATE_BYTES], usize) {
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
    let leaf = extract_bit_window_checked(hash, k * a, params.total_height_checked()?)?;
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

/// Few-time indices and hypertree leaf index selected by message counter `ctr`, if that
/// counter is usable: under `FORS+C` the omitted tree's index is zero, under `PORS+FP` the
/// subset passes the forced-pruning bound.
fn select_at(
    params: &BaggyParams,
    pk: &BaggyPublicKey,
    r: &[u8; 32],
    mu: &[u8; 32],
    ctr: u32,
) -> Option<(Vec<u32>, u64)> {
    match params.few_time {
        BaggyFewTime::ForsC => parse_hmsg(params, &hmsg(pk, r, mu, ctr)),
        BaggyFewTime::PorsFp(pors) => {
            let mut xof = Cshake256Xof::new(TAG_BAGGY_V2_HMSG);
            xof.absorb(&encode_multi_frame(&[
                r,
                &pk.pk_seed,
                &pk.pk_root,
                mu,
                &ctr.to_be_bytes(),
            ]));
            let mut word = [0u8; 8];
            xof.squeeze(&mut word);
            let leaf = u64::from_be_bytes(word) & ((1u64 << params.total_height_checked()?) - 1);
            Some((pors_fp_select(&pors, &mut xof)?, leaf))
        }
    }
}

/// Smallest usable message counter.
fn grind_hmsg(
    params: &BaggyParams,
    pk: &BaggyPublicKey,
    r: &[u8; 32],
    mu: &[u8; 32],
) -> Option<(u32, Vec<u32>, u64)> {
    (0..params.max_grind)
        .find_map(|ctr| select_at(params, pk, r, mu, ctr).map(|(idxs, leaf)| (ctr, idxs, leaf)))
}

/// The lanes of the few-time instance of hypertree leaf `(tree, key_pair)`: every `FORS+C`
/// leaf of every signed tree, or every `PORS+FP` leaf. Position 0 of a lane is the leaf
/// secret and position 1 its leaf hash.
fn few_time_lanes(params: &BaggyParams, tree: u64, key_pair: u32) -> Vec<LaneSpec> {
    match params.few_time {
        BaggyFewTime::ForsC => (0..params.fors_trees as u32 - 1)
            .flat_map(|j| {
                (0..1u32 << params.fors_height)
                    .map(move |leaf| LaneSpec::fors(tree, key_pair, j, leaf))
            })
            .collect(),
        BaggyFewTime::PorsFp(pors) => (0..pors.leaves() as u32)
            .map(|leaf| LaneSpec::pors(tree, key_pair, leaf))
            .collect(),
    }
}

/// Offsets into [`few_time_lanes`] of the secrets a signature reveals.
fn few_time_picks(params: &BaggyParams, idxs: &[u32]) -> Vec<usize> {
    match params.few_time {
        BaggyFewTime::ForsC => idxs
            .iter()
            .enumerate()
            .map(|(j, idx)| (j << params.fors_height) + *idx as usize)
            .collect(),
        BaggyFewTime::PorsFp(_) => idxs.iter().map(|idx| *idx as usize).collect(),
    }
}

/// Authentication data of a few-time opening, before the secrets are known.
enum FewTimeAuth {
    Fors(Vec<Vec<[u8; 32]>>),
    Pors(Vec<[u8; 32]>),
}

/// From the leaf hashes of [`few_time_lanes`]: the node the bottom hypertree layer signs
/// and the authentication data of the selected leaves.
fn few_time_public(
    params: &BaggyParams,
    pk_seed: &[u8; 32],
    tree: u64,
    key_pair: u32,
    idxs: &[u32],
    leaf_hashes: &[[u8; 32]],
) -> Option<([u8; 32], FewTimeAuth)> {
    match params.few_time {
        BaggyFewTime::ForsC => {
            let per_tree = 1usize << params.fors_height;
            let mut roots = Vec::with_capacity(idxs.len());
            let mut auths = Vec::with_capacity(idxs.len());
            for (j, idx) in idxs.iter().enumerate() {
                let levels = merkle_levels(
                    pk_seed,
                    0,
                    tree,
                    AdrsKind::ForsTree,
                    key_pair,
                    leaf_hashes.get(j * per_tree..(j + 1) * per_tree)?,
                    j,
                );
                roots.push(levels[params.fors_height][0]);
                auths.push(merkle_auth_path(&levels, *idx as usize));
            }
            Some((
                fors_pk(pk_seed, tree, key_pair, &roots),
                FewTimeAuth::Fors(auths),
            ))
        }
        BaggyFewTime::PorsFp(pors) => {
            if leaf_hashes.len() != pors.leaves() {
                return None;
            }
            let levels = pors_levels(pk_seed, tree, key_pair, leaf_hashes);
            let auth = pors_fp_auth(&pors, &levels, idxs)?;
            Some((levels[pors.tree_height][0], FewTimeAuth::Pors(auth)))
        }
    }
}

/// Join the authentication data with the revealed secrets (in [`few_time_picks`] order).
fn few_time_assemble(
    auth: FewTimeAuth,
    secrets: &[[u8; 32]],
) -> (Vec<BaggyForsOpening>, Option<PorsFpOpening>) {
    match auth {
        FewTimeAuth::Fors(auths) => (
            auths
                .into_iter()
                .zip(secrets)
                .map(|(auth, secret)| BaggyForsOpening {
                    secret: *secret,
                    auth,
                })
                .collect(),
            None,
        ),
        FewTimeAuth::Pors(auth) => (
            Vec::new(),
            Some(PorsFpOpening {
                secrets: secrets.to_vec(),
                auth,
            }),
        ),
    }
}

/// The node the bottom hypertree layer signs, recomputed from a signature's few-time part.
/// `None` if that part has the wrong shape for the parameters or does not hash to a node.
fn few_time_node(
    params: &BaggyParams,
    pk_seed: &[u8; 32],
    tree: u64,
    key_pair: u32,
    idxs: &[u32],
    sig: &BaggySig,
) -> Option<[u8; 32]> {
    match (params.few_time, &sig.pors) {
        (BaggyFewTime::ForsC, None) => {
            if sig.fors.len() != idxs.len() {
                return None;
            }
            let mut roots = Vec::with_capacity(idxs.len());
            for (j, (idx, opening)) in idxs.iter().zip(&sig.fors).enumerate() {
                let leaf = fors_leaf_hash_from_secret(
                    Cshake256Suite,
                    pk_seed,
                    tree,
                    key_pair,
                    j as u32,
                    *idx,
                    &opening.secret,
                );
                roots.push(walk_merkle_auth_path(
                    Cshake256Suite,
                    pk_seed,
                    0,
                    tree,
                    AdrsKind::ForsTree,
                    key_pair,
                    params.fors_height,
                    j,
                    *idx as usize,
                    leaf,
                    &opening.auth,
                )?);
            }
            Some(fors_pk(pk_seed, tree, key_pair, &roots))
        }
        (BaggyFewTime::PorsFp(pors), Some(opening)) if sig.fors.is_empty() => {
            pors_fp_root(&pors, pk_seed, tree, key_pair, idxs, opening)
        }
        _ => None,
    }
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
        || Some(sig.fors.len()) != params.signed_fors_trees_checked()
        || sig.layers.len() != params.num_layers
        || sig.msg_ctr >= params.max_grind
    {
        return None;
    }
    let mu = baggy_msg_digest(pk, msg);
    let (idxs, leaf_idx) = select_at(params, pk, &sig.r, &mu, sig.msg_ctr)?;
    let (kp0, tree0) = params.path_at(leaf_idx, 0);
    let mut nodes = Vec::with_capacity(params.num_layers + 1);
    nodes.push(few_time_node(
        params,
        &pk.pk_seed,
        tree0,
        kp0,
        &idxs,
        sig,
    )?);
    for (layer, layer_sig) in sig.layers.iter().enumerate() {
        let (kp, tree) = params.path_at(leaf_idx, layer);
        let root = layer_root(
            params,
            &pk.pk_seed,
            layer,
            tree,
            kp,
            &nodes[layer],
            layer_sig,
        )?;
        nodes.push(root);
    }
    (nodes[params.num_layers] == pk.pk_root).then_some(nodes)
}

/// Single-party reference: public key from the top subtree, or `None` for malformed
/// parameters.
pub fn baggy_reference_keygen(params: &BaggyParams, sk: &PqSecretKey) -> Option<BaggyPublicKey> {
    if !params.is_well_formed() {
        return None;
    }
    let top = (params.num_layers - 1) as u32;
    let leaves: Vec<[u8; 32]> = (0..params.subtree_leaves() as u32)
        .map(|kp| wots_c_reference_leaf(&params.wots, sk, top, 0, kp))
        .collect();
    let levels = merkle_levels(&sk.pk_seed, top, 0, AdrsKind::Tree, 0, &leaves, 0);
    Some(BaggyPublicKey {
        pk_seed: sk.pk_seed,
        pk_root: levels[params.subtree_height][0],
    })
}

/// Single-party reference signature (tests and known-answer comparisons).
pub fn baggy_reference_sign(
    params: &BaggyParams,
    sk: &PqSecretKey,
    pk: &BaggyPublicKey,
    msg: &[u8],
) -> Option<BaggySig> {
    if !params.is_well_formed() {
        return None;
    }
    let mu = baggy_msg_digest(pk, msg);
    let opt_rand = crate::wipe::SecretBuffer(th_call_secret(
        Cshake256Suite,
        TAG_BAGGY_OPT_RAND,
        &[],
        &HashAdrs::ZERO,
        &[&sk.sk_prf, &mu],
    ));
    let r = th_call_secret(
        Cshake256Suite,
        TAG_BAGGY_R,
        &[],
        &HashAdrs::ZERO,
        &[&*opt_rand, &mu],
    );
    drop(opt_rand);
    let (msg_ctr, idxs, leaf_idx) = grind_hmsg(params, pk, &r, &mu)?;
    let (kp0, tree0) = params.path_at(leaf_idx, 0);
    // The same lanes the MPC sweep evaluates: `PRF` for the secret, one `F` for its hash.
    let few_lanes = few_time_lanes(params, tree0, kp0);
    let secrets = SecretVec::new(
        few_lanes
            .iter()
            .map(|lane| th_secret_prf(Cshake256Suite, &sk.pk_seed, &sk.sk_seed, &lane.prf))
            .collect::<Vec<[u8; 32]>>(),
    );
    let leaf_hashes: Vec<[u8; 32]> = few_lanes
        .iter()
        .zip(secrets.iter())
        .map(|(lane, secret)| th_chain_f(Cshake256Suite, &pk.pk_seed, &lane.f, secret))
        .collect();
    let (mut node, few_auth) =
        few_time_public(params, &pk.pk_seed, tree0, kp0, &idxs, &leaf_hashes)?;
    let revealed: Vec<[u8; 32]> = few_time_picks(params, &idxs)
        .into_iter()
        .map(|lane| secrets[lane])
        .collect();
    let (fors, pors) = few_time_assemble(few_auth, &revealed);
    let mut layers = Vec::with_capacity(params.num_layers);
    for layer in 0..params.num_layers {
        let (kp, tree) = params.path_at(leaf_idx, layer);
        let leaves: Vec<[u8; 32]> = (0..params.subtree_leaves() as u32)
            .map(|l| wots_c_reference_leaf(&params.wots, sk, layer as u32, tree, l))
            .collect();
        let levels = merkle_levels(
            &pk.pk_seed,
            layer as u32,
            tree,
            AdrsKind::Tree,
            0,
            &leaves,
            0,
        );
        let (ctr, digits) = layer_grinder(&pk.pk_seed, layer, tree, kp, &node)
            .grind(&params.wots, params.max_grind)?;
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
        pors,
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
    /// Canonical commitment to every field that can influence signing. Callers
    /// must authenticate this digest with a secret MAC key before trusting it.
    /// Counters are included too so the representation has no uncommitted fields.
    pub fn authentication_digest(&self) -> [u8; 32] {
        let mut xof = crate::sponge::keccak::Cshake256Xof::new(b"QSAG.BAGGY.WAISTBAND.STATE/v1");
        for n in [
            self.top_layers,
            self.max_entries,
            self.leaves.len(),
            self.sigs.len(),
        ] {
            xof.absorb(&(n as u64).to_be_bytes());
        }
        xof.absorb(&[u8::from(self.bound.is_some())]);
        if let Some(binding) = &self.bound {
            xof.absorb(&binding.identity());
        }
        for ((layer, tree), entry) in &self.leaves {
            xof.absorb(&layer.to_be_bytes());
            xof.absorb(&tree.to_be_bytes());
            xof.absorb(&entry.root);
            xof.absorb(&(entry.leaves.len() as u64).to_be_bytes());
            for node in &entry.leaves {
                xof.absorb(node);
            }
        }
        for ((layer, tree, key_pair), entry) in &self.sigs {
            xof.absorb(&layer.to_be_bytes());
            xof.absorb(&tree.to_be_bytes());
            xof.absorb(&key_pair.to_be_bytes());
            xof.absorb(&entry.child_root);
            xof.absorb(&entry.layer_root);
            xof.absorb(&entry.sig.ctr.to_be_bytes());
            xof.absorb(&(entry.sig.chains.len() as u64).to_be_bytes());
            for node in &entry.sig.chains {
                xof.absorb(node);
            }
            xof.absorb(&(entry.sig.auth.len() as u64).to_be_bytes());
            for node in &entry.sig.auth {
                xof.absorb(node);
            }
        }
        xof.absorb(&self.hits.to_be_bytes());
        xof.absorb(&self.misses.to_be_bytes());
        let mut out = [0; 32];
        xof.squeeze(&mut out);
        out
    }

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
        cshake256_32(
            b"QSAG.BAGGY.PRECOMPUTE.RELEASE/v1",
            &encode_multi_frame(&[&binding.identity(), &(self.top_layers as u64).to_le_bytes()]),
        )
    }

    /// Fill every signature of the top `top_layers` layers eagerly (distributed-key-ceremony
    /// time). Requires `top_layers < num_layers`: the bottom layer signs message-dependent
    /// FORS keys and cannot be precomputed. Sweeps `sum_{j <= L} 2^{h' j}` subtrees.
    ///
    /// Refused before any MPC work if `binding` does not match the engine, `pk` and `params`
    /// or if the cache is bound to another identity. Every digit vector is checked against
    /// `ledger` and recorded there before the chain-node opening round, and every entry is
    /// verified against the swept subtree roots before it is stored.
    pub fn precompute<E: BaggyEngine, L: FirstSignedLedger + ?Sized>(
        &mut self,
        engine: &mut E,
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
        ledger.begin_release(
            &binding.identity(),
            engine.session_id(),
            &self.precompute_release_binding(binding),
        )?;
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
        let picks: Vec<(usize, u8)> = (0..lanes.len()).map(|l| (l, WOTS_STEPS as u8)).collect();
        let sweep = engine.sweep(&pk.pk_seed, lanes)?;
        engine.barrier()?;
        let endpoints = engine.open_round(&sweep, &picks)?;
        let mut levels: BTreeMap<(usize, u64), Vec<Vec<[u8; 32]>>> = BTreeMap::new();
        for (i, &(layer, tree)) in subtrees.iter().enumerate() {
            let leaves: Vec<[u8; 32]> = endpoints[i * per_tree..(i + 1) * per_tree]
                .chunks_exact(chains)
                .enumerate()
                .map(|(kp, ends)| wots_c_leaf(&pk.pk_seed, layer as u32, tree, kp as u32, ends))
                .collect();
            levels.insert(
                (layer, tree),
                merkle_levels(
                    &pk.pk_seed,
                    layer as u32,
                    tree,
                    AdrsKind::Tree,
                    0,
                    &leaves,
                    0,
                ),
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
                let wb_ctx = WaistbandGuardContext {
                    binding,
                    cache_bound: self.binding(),
                    expected_child_root: child_root,
                    recomputed_child_root: child_root,
                };
                admit_digits(ledger, &wb_ctx, key, digits.clone(), false, &mut records)?;
                let lane0 = i * per_tree + kp as usize * chains;
                node_picks.extend(digits.iter().enumerate().map(|(c, dg)| (lane0 + c, *dg)));
                jobs.push((layer, tree, kp, ctr, child_root));
            }
        }
        if !records.is_empty() {
            ledger.sync_record(&records)?;
        }
        let nodes = engine.open_round(&sweep, &node_picks)?;
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
fn check_key_binding<E: BaggyEngine>(
    engine: &E,
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

fn waistband_pk_tag(pk_seed: &[u8; 32], pk_root: &[u8; 32]) -> [u8; 32] {
    cshake256_32(
        b"QSAG.BAGGY.WAISTBAND.PK_TAG/v1",
        &encode_multi_frame(&[pk_seed, pk_root]),
    )
}

fn waistband_codeword_tag(digits: &[u8]) -> [u8; 32] {
    cshake256_32(b"QSAG.BAGGY.WAISTBAND.CODEWORD_TAG/v1", digits)
}

struct WaistbandGuardContext<'a> {
    binding: &'a BaggyKeyBinding,
    cache_bound: Option<&'a BaggyKeyBinding>,
    expected_child_root: [u8; 32],
    recomputed_child_root: [u8; 32],
}

fn verify_waistband_derivation(
    ctx: &WaistbandGuardContext<'_>,
    key: StaticKeyId,
    locked_digits: Option<&[u8]>,
    candidate_digits: &[u8],
) -> Result<qsag_verified::WaistbandAncestorPermit, BaggyError> {
    let key_pk_tag = waistband_pk_tag(ctx.binding.pk_seed(), ctx.binding.pk_root());
    let key_params_tag = *ctx.binding.params_digest();
    let active_cache = ctx.cache_bound.unwrap_or(ctx.binding);
    let cache_pk_tag = waistband_pk_tag(active_cache.pk_seed(), active_cache.pk_root());
    let cache_params_tag = *active_cache.params_digest();
    let mut guard = qsag_verified::VerifiedWaistbandRootGuard::new_enrolled(
        key_pk_tag,
        key_params_tag,
        key.layer,
        key.tree,
        key.key_pair,
        ctx.expected_child_root,
    );
    if let Some(locked) = locked_digits {
        let lock_req = qsag_verified::WaistbandDerivationRequest {
            req_layer: key.layer,
            req_tree: key.tree,
            req_kp: key.key_pair,
            cache_pk_tag: key_pk_tag,
            cache_params_tag: key_params_tag,
            recomputed_child_root: ctx.expected_child_root,
            candidate_ancestor_codeword_tag: waistband_codeword_tag(locked),
        };
        let (locked_guard, lock_res) = guard.authorize_ancestor_derivation(lock_req);
        lock_res.map_err(|_| BaggyError::CacheEntryUnauthenticated)?;
        guard = locked_guard;
    }
    let req = qsag_verified::WaistbandDerivationRequest {
        req_layer: key.layer,
        req_tree: key.tree,
        req_kp: key.key_pair,
        cache_pk_tag,
        cache_params_tag,
        recomputed_child_root: ctx.recomputed_child_root,
        candidate_ancestor_codeword_tag: waistband_codeword_tag(candidate_digits),
    };
    let (_next, res) = guard.authorize_ancestor_derivation(req);
    res.map_err(|err| match err {
        qsag_verified::PantsGuardError::WaistbandCachePkMismatch
        | qsag_verified::PantsGuardError::WaistbandCacheParamsMismatch => {
            BaggyError::CacheIdentityMismatch
        }
        qsag_verified::PantsGuardError::WaistbandCodewordEquivocation => {
            BaggyError::StaticKeyDigitsConflict {
                layer: key.layer,
                tree: key.tree,
                key_pair: key.key_pair,
            }
        }
        _ => BaggyError::CacheEntryUnauthenticated,
    })
}

/// Check `digits` against the first-signed record of `key` and gate static ancestor derivation
/// through `qsag_verified::VerifiedWaistbandRootGuard`. An equal record admits them; a
/// different one refuses them; with no record they are queued in `records` for the write
/// that precedes the opening round, unless `must_exist` (the message was vouched for by the
/// cache alone), which refuses.
fn admit_digits<L: FirstSignedLedger + ?Sized>(
    ledger: &L,
    ctx: &WaistbandGuardContext<'_>,
    key: StaticKeyId,
    digits: Vec<u8>,
    must_exist: bool,
    records: &mut Vec<FirstSignedRecord>,
) -> Result<(), BaggyError> {
    match ledger.first_signed(&key)? {
        Some(first) => {
            let permit = verify_waistband_derivation(ctx, key, Some(&first), &digits)?;
            if first != digits || permit.verified_child_root != ctx.expected_child_root {
                return Err(BaggyError::StaticKeyDigitsConflict {
                    layer: key.layer,
                    tree: key.tree,
                    key_pair: key.key_pair,
                });
            }
            Ok(())
        }
        None if must_exist => Err(BaggyError::CacheUnanchored),
        None => {
            let permit = verify_waistband_derivation(ctx, key, None, &digits)?;
            if permit.verified_child_root != ctx.expected_child_root {
                return Err(BaggyError::CacheEntryUnauthenticated);
            }
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
                let root = layer_root(
                    params,
                    &pk.pk_seed,
                    layer,
                    tree,
                    kp,
                    &entry.child_root,
                    &entry.sig,
                );
                if root != Some(entry.layer_root) || below.is_some_and(|r| r != entry.child_root) {
                    return Err(BaggyError::CacheEntryUnauthenticated);
                }
                Some(entry.layer_root)
            }
            LayerPlan::LeafOnly(set, _) => {
                if set.leaves.len() != params.subtree_leaves() {
                    return Err(BaggyError::CacheEntryUnauthenticated);
                }
                let levels = merkle_levels(
                    &pk.pk_seed,
                    layer as u32,
                    tree,
                    AdrsKind::Tree,
                    0,
                    &set.leaves,
                    0,
                );
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
pub fn baggy_keygen_mpc<E: BaggyEngine>(
    engine: &mut E,
    params: &BaggyParams,
    cache: &mut WaistbandCache,
) -> Result<(BaggyPublicKey, BaggyKeyBinding), BaggyError> {
    if !params.is_well_formed() {
        return Err(BaggyError::InvalidParameters);
    }
    let pk_seed = engine.pk_seed();
    if let Some(bound) = cache.binding()
        && (bound.pk_seed != pk_seed || bound.params_digest != params.digest())
    {
        return Err(BaggyError::CacheIdentityMismatch);
    }
    let top = params.num_layers - 1;
    let chains = params.wots.chains;
    let mut lanes = Vec::with_capacity(params.subtree_leaves() * chains);
    for kp in 0..params.subtree_leaves() as u32 {
        for c in 0..chains as u32 {
            lanes.push(LaneSpec::wots(top as u32, 0, kp, c));
        }
    }
    let picks: Vec<(usize, u8)> = (0..lanes.len()).map(|l| (l, WOTS_STEPS as u8)).collect();
    let sweep = engine.sweep(&pk_seed, lanes)?;
    engine.barrier()?;
    let endpoints = engine.open_round(&sweep, &picks)?;
    let leaves: Vec<[u8; 32]> = endpoints
        .chunks_exact(chains)
        .enumerate()
        .map(|(kp, ends)| wots_c_leaf(&pk_seed, top as u32, 0, kp as u32, ends))
        .collect();
    let levels = merkle_levels(&pk_seed, top as u32, 0, AdrsKind::Tree, 0, &leaves, 0);
    let pk_root = levels[params.subtree_height][0];
    let pk = BaggyPublicKey { pk_seed, pk_root };
    let binding = BaggyKeyBinding::new(params, &pk);
    cache.check_identity(&binding)?;
    // From here on the shares belong to this key under these parameters and no other.
    engine
        .bind_key_identity(&binding.identity())
        .map_err(|_| BaggyError::KeyBindingMismatch)?;
    if cache.covers(params, top) {
        cache.bind(&binding);
        cache.insert_leaves(
            top,
            0,
            CachedLeaves {
                leaves,
                root: pk_root,
            },
        );
    }
    Ok((pk, binding))
}

/// What the sweep must evaluate for one layer of the path.
enum LayerPlan {
    /// Signature served by `Waistband`: nothing to evaluate.
    Cached(CachedSig),
    /// Subtree leaves are cached: only the signing leaf's chains, starting at this lane.
    LeafOnly(CachedLeaves, usize),
    /// The whole subtree, starting at this lane.
    Full(usize),
}

/// Sign `msg` under MPC (see the module documentation). `cache` may be
/// [`WaistbandCache::disabled`]. The signature is verified before it is returned.
///
/// Order of the checks:
/// 1. Before any MPC work: `binding` against the engine's `pk_seed`, `pk` and `params`
///    ([`BaggyError::KeyBindingMismatch`]) and the cache's identity
///    ([`BaggyError::CacheIdentityMismatch`]).
/// 2. After `R` is open and the path is known, before the sweep: every cached entry on the
///    path ([`BaggyError::CacheEntryUnauthenticated`]).
/// 3. After the endpoint round, before the chain-node round: cached signatures against the
///    computed roots below them, then for every layer that opens nodes its digits against
///    `ledger` ([`BaggyError::StaticKeyDigitsConflict`], [`BaggyError::CacheUnanchored`]),
///    then one [`FirstSignedLedger::sync_record`] for the keys that had no record.
///
/// New cache entries are stored only after the finished signature verified, with the roots
/// of that verified path.
pub fn baggy_sign_mpc<E: BaggyEngine, L: FirstSignedLedger + ?Sized>(
    engine: &mut E,
    params: &BaggyParams,
    pk: &BaggyPublicKey,
    binding: &BaggyKeyBinding,
    cache: &mut WaistbandCache,
    ledger: &mut L,
    msg: &[u8],
) -> Result<BaggySig, BaggyError> {
    if !params.is_well_formed() {
        return Err(BaggyError::InvalidParameters);
    }
    check_key_binding(engine, params, pk, binding)?;
    cache.check_identity(binding)?;
    let identity = binding.identity();
    let (d, hp, chains) = (params.num_layers, params.subtree_height, params.wots.chains);
    let mu = baggy_msg_digest(pk, msg);
    ledger.begin_release(&identity, engine.session_id(), &mu)?;

    // Phase 1.
    let r = engine.randomiser(&mu)?;
    let (msg_ctr, idxs, leaf_idx) =
        grind_hmsg(params, pk, &r, &mu).ok_or(BaggyError::GrindExhausted)?;
    let (kp0, tree0) = params.path_at(leaf_idx, 0);

    // Phase 2: plan every layer, then one sweep over all of them and the few-time leaves.
    let mut lanes: Vec<LaneSpec> = Vec::new();
    let mut plans: Vec<LayerPlan> = Vec::with_capacity(d);
    for layer in 0..d {
        let (kp, tree) = params.path_at(leaf_idx, layer);
        let covered = cache.covers(params, layer);
        if covered && let Some(entry) = cache.sigs.get(&(layer as u32, tree, kp)) {
            cache.hits += 1;
            plans.push(LayerPlan::Cached(entry.clone()));
            continue;
        }
        if covered {
            cache.misses += 1;
        }
        let lane0 = lanes.len();
        if covered && let Some(set) = cache.leaves.get(&(layer as u32, tree)) {
            for c in 0..chains as u32 {
                lanes.push(LaneSpec::wots(layer as u32, tree, kp, c));
            }
            plans.push(LayerPlan::LeafOnly(set.clone(), lane0));
        } else {
            for leaf in 0..params.subtree_leaves() as u32 {
                for c in 0..chains as u32 {
                    lanes.push(LaneSpec::wots(layer as u32, tree, leaf, c));
                }
            }
            plans.push(LayerPlan::Full(lane0));
        }
    }
    authenticate_cached_path(params, pk, leaf_idx, &plans)?;
    let few_lane0 = lanes.len();
    lanes.extend(few_time_lanes(params, tree0, kp0));
    let few_total = lanes.len() - few_lane0;
    let sweep = engine.sweep(&pk.pk_seed, lanes)?;

    // Phase 3: the cut. One barrier, then two opening rounds.
    engine.barrier()?;
    let mut picks: Vec<(usize, u8)> = Vec::new();
    for plan in &plans {
        if let LayerPlan::Full(lane0) = plan {
            picks.extend(
                (0..params.subtree_leaves() * chains).map(|i| (lane0 + i, WOTS_STEPS as u8)),
            );
        }
    }
    let endpoint_count = picks.len();
    picks.extend((0..few_total).map(|i| (few_lane0 + i, 1u8)));
    let opened = engine.open_round(&sweep, &picks)?;
    let (endpoints, few_hashes) = opened.split_at(endpoint_count);
    // The secrets are opened only after every cached child-root binding has passed.
    let (few_node, few_auth) =
        few_time_public(params, &pk.pk_seed, tree0, kp0, &idxs, few_hashes)
            .ok_or(BaggyError::SelfCheckFailed)?;

    // Public pass up the path: roots, digits and authentication paths of every layer.
    // `node` is the value the current layer signs; `node_from_cache` says whether the cache
    // (a cached signature's stored root, or the root of a cached leaf set) supplied it,
    // rather than endpoints or few-time leaves opened after this session's barrier.
    let mut node = few_node;
    let mut node_from_cache = false;
    let mut path_nodes: Vec<[u8; 32]> = Vec::with_capacity(d + 1);
    path_nodes.push(node);
    let mut records: Vec<FirstSignedRecord> = Vec::new();
    let mut layers: Vec<Option<BaggyLayerSig>> = Vec::with_capacity(d);
    let mut pending: Vec<(usize, u32, Vec<[u8; 32]>)> = Vec::new();
    let mut node_picks: Vec<(usize, u8)> = Vec::new();
    let mut fresh_leaves: Vec<(usize, u64, Vec<[u8; 32]>)> = Vec::new();
    let mut endpoint_cursor = 0usize;
    let cache_bound_snapshot = cache.binding().copied();
    for (layer, plan) in plans.into_iter().enumerate() {
        let (kp, tree) = params.path_at(leaf_idx, layer);
        let (leaves, lane0, leaves_cached) = match plan {
            LayerPlan::Cached(entry) => {
                // The entry verified against its stored roots before the sweep. Gate its
                // child-root binding and identity tags through `VerifiedWaistbandRootGuard`
                // before allowing the layer above to sign its stored root.
                let cached_digits = layer_grinder(&pk.pk_seed, layer, tree, kp, &entry.child_root)
                    .digits_at(&params.wots, entry.sig.ctr)
                    .ok_or(BaggyError::CacheEntryUnauthenticated)?;
                let key = StaticKeyId {
                    identity,
                    layer: layer as u32,
                    tree,
                    key_pair: kp,
                };
                let wb_ctx = WaistbandGuardContext {
                    binding,
                    cache_bound: cache_bound_snapshot.as_ref(),
                    expected_child_root: entry.child_root,
                    recomputed_child_root: node,
                };
                verify_waistband_derivation(&wb_ctx, key, None, &cached_digits)?;
                node = entry.layer_root;
                node_from_cache = true;
                path_nodes.push(node);
                layers.push(Some(entry.sig));
                continue;
            }
            LayerPlan::LeafOnly(set, lane0) => (set.leaves, lane0, true),
            LayerPlan::Full(lane0) => {
                let count = params.subtree_leaves() * chains;
                let leaves: Vec<[u8; 32]> = endpoints[endpoint_cursor..endpoint_cursor + count]
                    .chunks_exact(chains)
                    .enumerate()
                    .map(|(l, ends)| wots_c_leaf(&pk.pk_seed, layer as u32, tree, l as u32, ends))
                    .collect();
                endpoint_cursor += count;
                fresh_leaves.push((layer, tree, leaves.clone()));
                (leaves, lane0 + kp as usize * chains, false)
            }
        };
        let levels = merkle_levels(
            &pk.pk_seed,
            layer as u32,
            tree,
            AdrsKind::Tree,
            0,
            &leaves,
            0,
        );
        let (ctr, digits) = layer_grinder(&pk.pk_seed, layer, tree, kp, &node)
            .grind(&params.wots, params.max_grind)
            .ok_or(BaggyError::GrindExhausted)?;
        node_picks.extend(digits.iter().enumerate().map(|(c, dg)| (lane0 + c, *dg)));
        let key = StaticKeyId {
            identity,
            layer: layer as u32,
            tree,
            key_pair: kp,
        };
        let wb_ctx = WaistbandGuardContext {
            binding,
            cache_bound: cache_bound_snapshot.as_ref(),
            expected_child_root: node,
            recomputed_child_root: node,
        };
        admit_digits(ledger, &wb_ctx, key, digits, node_from_cache, &mut records)?;
        pending.push((layer, ctr, merkle_auth_path(&levels, kp as usize)));
        layers.push(None);
        node = levels[hp][0];
        node_from_cache = leaves_cached;
        path_nodes.push(node);
    }
    if node != pk.pk_root {
        return Err(BaggyError::SelfCheckFailed);
    }
    // Durable write first, then the round that opens the chain nodes.
    if !records.is_empty() {
        ledger.sync_record(&records)?;
    }
    let chain_node_count = node_picks.len();
    node_picks.extend(
        few_time_picks(params, &idxs)
            .into_iter()
            .map(|lane| (few_lane0 + lane, 0u8)),
    );
    let revealed = engine.open_round(&sweep, &node_picks)?;
    let (nodes, few_secrets) = revealed.split_at(chain_node_count);
    let (fors, pors) = few_time_assemble(few_auth, few_secrets);
    let mut opened_layers = Vec::with_capacity(pending.len());
    for ((layer, ctr, auth), chain_nodes) in pending.into_iter().zip(nodes.chunks_exact(chains)) {
        layers[layer] = Some(BaggyLayerSig {
            ctr,
            chains: chain_nodes.to_vec(),
            auth,
        });
        opened_layers.push(layer);
    }
    let sig = BaggySig {
        r,
        msg_ctr,
        fors,
        pors,
        layers: layers.into_iter().flatten().collect(),
    };
    // The signature must verify along exactly the nodes that were signed above.
    if verified_path(params, pk, msg, &sig).as_ref() != Some(&path_nodes) {
        return Err(BaggyError::SelfCheckFailed);
    }
    // Lazy fill from the verified path, upper layers first: they are shared by more leaves,
    // and an upper entry is what lets a lower one be used without consulting the ledger.
    cache.bind(binding);
    for layer in opened_layers.into_iter().rev() {
        if cache.covers(params, layer) {
            let (kp, tree) = params.path_at(leaf_idx, layer);
            cache.insert_sig(
                layer,
                tree,
                kp,
                CachedSig {
                    sig: sig.layers[layer].clone(),
                    child_root: path_nodes[layer],
                    layer_root: path_nodes[layer + 1],
                },
            );
        }
    }
    for (layer, tree, leaves) in fresh_leaves {
        if cache.covers(params, layer) {
            cache.insert_leaves(
                layer,
                tree,
                CachedLeaves {
                    leaves,
                    root: path_nodes[layer + 1],
                },
            );
        }
    }
    Ok(sig)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::keccak_mpc::run_dealerless_rss_dkg_2of3;
    use crate::preprocessing::PartyPrivateRng;
    use crate::rss256::{AndMode, Fault256};

    /// Engine for one signing session over a fixed key; `session` varies the parties'
    /// session randomness only.
    fn test_engine(key_tag: u8, session: u8) -> (Rss256Engine, PqSecretKey) {
        let sid = [key_tag; 32];
        let mut dkg_rngs: [PartyPrivateRng; 3] = core::array::from_fn(|p| {
            PartyPrivateRng::from_seed([key_tag ^ ((p as u8) << 4); 32], b"baggy-dkg")
        });
        let (keys, _) = run_dealerless_rss_dkg_2of3(sid, 32, &mut dkg_rngs).unwrap();
        let rngs: [PartyPrivateRng; 3] = core::array::from_fn(|p| {
            PartyPrivateRng::from_seed([session ^ ((p as u8) << 4); 32], b"baggy-session")
        });
        let engine = Rss256Engine::new(sid, keys, rngs).unwrap();
        let xor3 = |slots: [&[u8]; 3]| -> [u8; 32] {
            core::array::from_fn(|i| slots[0][i] ^ slots[1][i] ^ slots[2][i])
        };
        let sk = PqSecretKey {
            sk_seed: xor3(engine.sk_seed_slots()),
            sk_prf: xor3(engine.sk_prf_slots()),
            pk_seed: engine.pk_seed(),
        };
        (engine, sk)
    }

    /// Reference public key of `sk` and the binding a signer would have stored at keygen.
    /// The engine's shares are bound to it, as shares stored after key generation would be.
    fn keyed(
        engine: &mut Rss256Engine,
        params: &BaggyParams,
        sk: &PqSecretKey,
    ) -> (BaggyPublicKey, BaggyKeyBinding) {
        let pk = baggy_reference_keygen(params, sk).unwrap();
        let binding = BaggyKeyBinding::new(params, &pk);
        engine.bind_key_identity(&binding.identity()).unwrap();
        (pk, binding)
    }

    /// Hypertree leaf index a valid signature on `msg` selects.
    fn leaf_of(params: &BaggyParams, pk: &BaggyPublicKey, msg: &[u8], sig: &BaggySig) -> u64 {
        let mu = baggy_msg_digest(pk, msg);
        parse_hmsg(params, &hmsg(pk, &sig.r, &mu, sig.msg_ctr))
            .unwrap()
            .1
    }

    /// Key id and reference digit vector of the path's leaf at `layer`.
    fn path_key(
        params: &BaggyParams,
        pk: &BaggyPublicKey,
        binding: &BaggyKeyBinding,
        msg: &[u8],
        sig: &BaggySig,
        layer: usize,
    ) -> (StaticKeyId, Vec<u8>) {
        let nodes = verified_path(params, pk, msg, sig).unwrap();
        let (key_pair, tree) = params.path_at(leaf_of(params, pk, msg, sig), layer);
        let digits = layer_grinder(&pk.pk_seed, layer, tree, key_pair, &nodes[layer])
            .grind(&params.wots, params.max_grind)
            .unwrap()
            .1;
        let key = StaticKeyId {
            identity: binding.identity(),
            layer: layer as u32,
            tree,
            key_pair,
        };
        (key, digits)
    }

    #[test]
    fn mpc_signature_equals_reference_verifies_and_rejects_tampering() {
        let params = BaggyParams::TEST_SMALL;
        assert!(params.is_well_formed() && BaggyParams::SHA3_128F.is_well_formed());
        let big = BaggyParams::SHA3_128F;
        assert_eq!(
            big.sig_bytes_checked(),
            Some(36 + 32 * (32 + 32 * 6) + 16 * (4 + 32 * big.wots.chains + 32 * 2))
        );
        let (mut engine, sk) = test_engine(0xC1, 1);
        let mut cache = WaistbandCache::disabled();
        let mut ledger = MemoryFirstSigned::new();
        let (pk, binding) = baggy_keygen_mpc(&mut engine, &params, &mut cache).unwrap();
        assert_eq!(Some(pk), baggy_reference_keygen(&params, &sk));
        assert_eq!(binding, BaggyKeyBinding::new(&params, &pk));
        assert!(cache.binding().is_none() && ledger.is_empty());

        let msg = b"baggy threshold signature";
        let before = engine.stats();
        let sig = baggy_sign_mpc(
            &mut engine,
            &params,
            &pk,
            &binding,
            &mut cache,
            &mut ledger,
            msg,
        )
        .unwrap();
        let after = engine.stats();
        assert_eq!(
            Some(sig.clone()),
            baggy_reference_sign(&params, &sk, &pk, msg)
        );
        // Every layer's key opened its first codeword, recorded in one write before the round.
        assert_eq!((ledger.len(), ledger.sync_count()), (params.num_layers, 1));
        for layer in 0..params.num_layers {
            let (key, digits) = path_key(&params, &pk, &binding, msg, &sig, layer);
            assert_eq!(ledger.first_signed(&key), Ok(Some(digits)), "layer {layer}");
        }
        assert!(baggy_verify(&params, &pk, msg, &sig));
        // Two randomiser levels, then four levels for every layer and the FORS leaves.
        assert_eq!(after.perm_levels - before.perm_levels, 6);
        // Two cut barriers (randomiser, cut) and three opening rounds (R, endpoints, nodes).
        // The memory bound may force further barriers inside the sweep.
        assert_eq!(after.cut_checks - before.cut_checks, 2);
        assert_eq!(after.open_rounds - before.open_rounds, 3);
        assert_eq!(cache.sig_entries(), 0);

        assert!(!baggy_verify(&params, &pk, b"another message", &sig));
        let mut bad = sig.clone();
        bad.r[0] ^= 1;
        assert!(!baggy_verify(&params, &pk, msg, &bad));
        let mut bad = sig.clone();
        bad.fors[0].secret[0] ^= 1;
        assert!(!baggy_verify(&params, &pk, msg, &bad));
        let mut bad = sig.clone();
        bad.fors[3].auth[2][5] ^= 1;
        assert!(!baggy_verify(&params, &pk, msg, &bad));
        let mut bad = sig.clone();
        bad.layers[1].chains[17][9] ^= 0x80;
        assert!(!baggy_verify(&params, &pk, msg, &bad));
        let mut bad = sig.clone();
        bad.layers[2].auth[0][0] ^= 1;
        assert!(!baggy_verify(&params, &pk, msg, &bad));
        let mut bad = sig.clone();
        bad.layers[0].ctr ^= 1;
        assert!(!baggy_verify(&params, &pk, msg, &bad));
        let mut bad = sig;
        bad.layers.pop();
        assert!(!baggy_verify(&params, &pk, msg, &bad));
    }

    /// The randomiser depends on the shared key and the message only: a second session with
    /// fresh party randomness (a retry after an abort) produces the identical signature, so
    /// aborting never buys a new draw of the FORS indices.
    #[test]
    fn retries_with_fresh_session_randomness_give_the_identical_signature() {
        let params = BaggyParams::TEST_SMALL;
        let msg = b"retry me";
        let mut sigs = Vec::new();
        for session in [10u8, 11, 12] {
            let (mut engine, sk) = test_engine(0xC2, session);
            let (pk, binding) = keyed(&mut engine, &params, &sk);
            let mut cache = WaistbandCache::disabled();
            let mut ledger = MemoryFirstSigned::new();
            sigs.push(
                baggy_sign_mpc(
                    &mut engine,
                    &params,
                    &pk,
                    &binding,
                    &mut cache,
                    &mut ledger,
                    msg,
                )
                .unwrap(),
            );
        }
        assert_eq!(sigs[0], sigs[1]);
        assert_eq!(sigs[0], sigs[2]);
        // A different message moves the randomiser.
        let (mut engine, sk) = test_engine(0xC2, 13);
        let (pk, binding) = keyed(&mut engine, &params, &sk);
        let other = baggy_sign_mpc(
            &mut engine,
            &params,
            &pk,
            &binding,
            &mut WaistbandCache::disabled(),
            &mut MemoryFirstSigned::new(),
            b"x",
        )
        .unwrap();
        assert_ne!(other.r, sigs[0].r);
    }

    #[test]
    fn waistband_precompute_and_lazy_fill_skip_cached_layers_without_changing_signatures() {
        let params = BaggyParams::TEST_SMALL;
        let chains = params.wots.chains as u64;
        let (mut engine, sk) = test_engine(0xC3, 1);
        let (pk, binding) = keyed(&mut engine, &params, &sk);
        // One ledger for the key, whichever cache a signature goes through.
        let mut ledger = MemoryFirstSigned::new();

        // Eager: top two of three layers. 1 + 4 covered subtrees, 5 * 4 signatures.
        let mut eager = WaistbandCache::new(2, 4096);
        eager
            .precompute(&mut engine, &params, &pk, &binding, &mut ledger)
            .unwrap();
        assert_eq!(eager.sig_entries(), 20);
        assert_eq!(eager.leaf_entries(), 5);
        assert_eq!(eager.binding(), Some(&binding));
        // Precompute recorded the digits of every key whose nodes it opened.
        assert_eq!(ledger.len(), 20);

        let mut lazy = WaistbandCache::new(2, 4096);
        let mut none = WaistbandCache::disabled();
        for (i, msg) in [&b"m0"[..], b"m1", b"m2", b"m3"].into_iter().enumerate() {
            let want = baggy_reference_sign(&params, &sk, &pk, msg).unwrap();

            let s0 = engine.stats();
            let mut sign = |cache: &mut WaistbandCache| {
                let sig =
                    baggy_sign_mpc(&mut engine, &params, &pk, &binding, cache, &mut ledger, msg);
                (sig.unwrap(), engine.stats())
            };
            let (cold, s1) = sign(&mut none);
            let (warm, s2) = sign(&mut eager);
            let (lazily, _) = sign(&mut lazy);
            assert_eq!(cold, want, "message {i}");
            assert_eq!(warm, want, "message {i}");
            assert_eq!(lazily, want, "message {i}");

            // Uncached: three full subtrees and the FORS leaves. Eagerly cached: only the
            // bottom subtree and the FORS leaves are evaluated.
            let fors = 4 * 8 * 2;
            assert_eq!(s1.lane_perms - s0.lane_perms, 2 + 3 * 4 * chains * 4 + fors);
            assert_eq!(s2.lane_perms - s1.lane_perms, 2 + 4 * chains * 4 + fors);
        }
        assert_eq!(eager.hits(), 8);
        assert_eq!(eager.misses(), 0);
        // The lazy cache served the top layer from the second signature on at the latest.
        assert!(lazy.hits() >= 1 && lazy.sig_entries() >= 2);
        // A cache built for another key is caught by the root check.
        let (mut other_engine, other_sk) = test_engine(0xC4, 1);
        let other_pk = baggy_reference_keygen(&params, &other_sk).unwrap();
        let mut wrong = WaistbandCache::new(1, 64);
        let bogus = BaggyPublicKey {
            pk_seed: other_pk.pk_seed,
            pk_root: [0x55; 32],
        };
        let bogus_binding = BaggyKeyBinding::new(&params, &bogus);
        // Unbound shares are refused outright.
        let mut other_ledger = MemoryFirstSigned::new();
        assert_eq!(
            wrong.precompute(
                &mut other_engine,
                &params,
                &bogus,
                &bogus_binding,
                &mut other_ledger
            ),
            Err(BaggyError::KeyBindingMismatch)
        );
        // Shares bound to the wrong root get as far as the root check and no further.
        other_engine
            .bind_key_identity(&bogus_binding.identity())
            .unwrap();
        assert_eq!(
            wrong.precompute(
                &mut other_engine,
                &params,
                &bogus,
                &bogus_binding,
                &mut other_ledger
            ),
            Err(BaggyError::CacheInconsistent)
        );
        // Nothing stored, nothing recorded, and the cache did not bind to the wrong root.
        assert_eq!(wrong.sig_entries(), 0);
        assert!(wrong.binding().is_none() && other_ledger.is_empty());
    }

    /// A cached top-layer signature that no longer verifies, or one whose path and stored
    /// root were rewritten together, is rejected before the sweep: only `R` is open.
    #[test]
    fn a_poisoned_top_layer_waistband_entry_aborts_before_the_sweep() {
        let params = BaggyParams::TEST_SMALL;
        let (mut engine, sk) = test_engine(0xC5, 1);
        let (pk, binding) = keyed(&mut engine, &params, &sk);
        let mut ledger = MemoryFirstSigned::new();
        let mut clean = WaistbandCache::new(1, 64);
        clean
            .precompute(&mut engine, &params, &pk, &binding, &mut ledger)
            .unwrap();
        let top = params.num_layers - 1;

        let mut bad_chain = clean.clone();
        for entry in bad_chain.sigs.values_mut() {
            entry.sig.chains[0][0] ^= 1;
        }
        // Authentication path and stored root changed consistently: the entry verifies
        // against itself and fails only against `pk_root`.
        let mut rewritten = clean.clone();
        for (&(_, tree, kp), entry) in rewritten.sigs.iter_mut() {
            entry.sig.auth[0][0] ^= 1;
            entry.layer_root = layer_root(
                &params,
                &pk.pk_seed,
                top,
                tree,
                kp,
                &entry.child_root,
                &entry.sig,
            )
            .unwrap();
            assert_ne!(entry.layer_root, pk.pk_root);
        }
        // A damaged cached leaf set (served when the signature itself is not cached).
        let mut bad_leaves = clean.clone();
        bad_leaves.sigs.clear();
        for set in bad_leaves.leaves.values_mut() {
            set.leaves[0][0] ^= 1;
        }
        let records = ledger.len();
        for (i, cache) in [bad_chain, rewritten, bad_leaves].iter_mut().enumerate() {
            let before = engine.stats();
            assert_eq!(
                baggy_sign_mpc(
                    &mut engine,
                    &params,
                    &pk,
                    &binding,
                    cache,
                    &mut ledger,
                    b"m"
                ),
                Err(BaggyError::CacheEntryUnauthenticated),
                "case {i}"
            );
            let after = engine.stats();
            assert_eq!(after.open_rounds - before.open_rounds, 1, "case {i}");
            assert_eq!(after.open_bytes - before.open_bytes, 32, "case {i}");
            assert_eq!(after.lane_perms - before.lane_perms, 2, "case {i}");
        }
        assert_eq!(ledger.len(), records);
        let sig = baggy_sign_mpc(
            &mut engine,
            &params,
            &pk,
            &binding,
            &mut clean,
            &mut ledger,
            b"m",
        )
        .unwrap();
        assert_eq!(Some(sig), baggy_reference_sign(&params, &sk, &pk, b"m"));
    }

    /// An intermediate layer is cached and its parent is not. One authentication-path
    /// sibling of the cached signature is flipped: the signature still passes its own
    /// `WOTS+C` check and reconstructs a different intermediate root, which the parent
    /// would sign. Signing must stop before the sweep, and the parent key's first-signed
    /// record must end up being the digits of the true child root.
    #[test]
    fn a_corrupted_intermediate_entry_under_an_uncached_parent_aborts_before_any_opening() {
        let params = BaggyParams::TEST_SMALL;
        let d = params.num_layers;
        let (mid, top) = (d - 2, d - 1);
        let (mut engine, sk) = test_engine(0xC8, 1);
        let (pk, binding) = keyed(&mut engine, &params, &sk);
        let msg = b"intermediate";
        let want = baggy_reference_sign(&params, &sk, &pk, msg).unwrap();
        let nodes = verified_path(&params, &pk, msg, &want).unwrap();
        let leaf_idx = leaf_of(&params, &pk, msg, &want);
        let (mid_kp, mid_tree) = params.path_at(leaf_idx, mid);
        let mid_slot = (mid as u32, mid_tree, mid_kp);
        let (top_key, legit) = path_key(&params, &pk, &binding, msg, &want, top);

        // Lazy fill caches both covered layers; then the parent's entries are dropped.
        let mut witness = MemoryFirstSigned::new();
        let mut original = WaistbandCache::new(2, 4096);
        let mut sign = |cache: &mut WaistbandCache, ledger: &mut MemoryFirstSigned| {
            let before = engine.stats();
            let out = baggy_sign_mpc(&mut engine, &params, &pk, &binding, cache, ledger, msg);
            let after = engine.stats();
            (
                out,
                after.open_rounds - before.open_rounds,
                after.open_bytes - before.open_bytes,
                after.lane_perms - before.lane_perms,
            )
        };
        assert_eq!(sign(&mut original, &mut witness).0, Ok(want.clone()));
        assert!(
            original
                .sigs
                .remove(&(top as u32, top_key.tree, top_key.key_pair))
                .is_some()
        );
        assert!(
            original
                .leaves
                .remove(&(top as u32, top_key.tree))
                .is_some()
        );
        assert!(original.sigs.contains_key(&mid_slot));

        let mut corrupted = original.clone();
        corrupted.sigs.get_mut(&mid_slot).unwrap().sig.auth[0][0] ^= 1;
        let entry = &corrupted.sigs[&mid_slot];
        let wrong_root = layer_root(
            &params,
            &pk.pk_seed,
            mid,
            mid_tree,
            mid_kp,
            &entry.child_root,
            &entry.sig,
        )
        .expect("the corrupted signature still passes its own digest check");
        assert_ne!(wrong_root, nodes[top]);
        let wrong_digits = layer_grinder(
            &pk.pk_seed,
            top,
            top_key.tree,
            top_key.key_pair,
            &wrong_root,
        )
        .grind(&params.wots, params.max_grind)
        .unwrap()
        .1;
        assert_ne!(wrong_digits, legit);

        // Only `R` is open: no sweep, no endpoint round, no node round, nothing recorded.
        let mut fresh = MemoryFirstSigned::new();
        assert_eq!(
            sign(&mut corrupted, &mut fresh),
            (Err(BaggyError::CacheEntryUnauthenticated), 1, 32, 2)
        );
        assert!(fresh.is_empty());

        // The same corruption with the stored root rewritten to match passes the entry's
        // own check. The parent then has to be anchored in the ledger: with no record the
        // run stops after the endpoint round, with the true record the wrong digits are
        // refused. Neither run reaches the node round or writes a record.
        let mut rewritten = corrupted.clone();
        rewritten.sigs.get_mut(&mid_slot).unwrap().layer_root = wrong_root;
        let (out, rounds, _, _) = sign(&mut rewritten, &mut fresh);
        assert_eq!((out, rounds), (Err(BaggyError::CacheUnanchored), 2));
        assert!(fresh.is_empty());
        let (out, rounds, _, _) = sign(&mut rewritten, &mut witness);
        assert_eq!(
            (out, rounds),
            (
                Err(BaggyError::StaticKeyDigitsConflict {
                    layer: top as u32,
                    tree: top_key.tree,
                    key_pair: top_key.key_pair,
                }),
                2
            )
        );
        assert_eq!((witness.len(), witness.sync_count()), (d, 1));

        // Clean runs. A new cache with the ledger that has seen nothing: the parent's
        // first-signed record is the digit vector of the true child root.
        let mut clean = WaistbandCache::new(2, 4096);
        let (out, rounds, _, _) = sign(&mut clean, &mut fresh);
        assert_eq!((out, rounds), (Ok(want.clone()), 3));
        assert!(baggy_verify(&params, &pk, msg, &want));
        assert_eq!(fresh.first_signed(&top_key), Ok(Some(legit.clone())));
        assert_eq!(fresh.len(), d);
        // The uncorrupted partial cache with the ledger that witnessed its entries.
        assert_eq!(sign(&mut original, &mut witness).0, Ok(want));
        assert_eq!(witness.first_signed(&top_key), Ok(Some(legit)));
        assert!(original.hits() >= 1);
    }

    #[test]
    fn a_cache_or_binding_for_another_key_or_parameter_set_is_refused_before_any_mpc_work() {
        let params = BaggyParams::TEST_SMALL;
        // Every field moves the digest.
        let edits: [fn(&mut BaggyParams); 8] = [
            |p| p.wots.chains -= 1,
            |p| p.wots.zero_digits += 1,
            |p| p.wots.target_sum -= 1,
            |p| p.subtree_height += 1,
            |p| p.num_layers += 1,
            |p| p.fors_trees += 1,
            |p| p.fors_height += 1,
            |p| p.max_grind -= 1,
        ];
        let mut digests = alloc::vec![params.digest()];
        for edit in edits {
            let mut p = params;
            edit(&mut p);
            assert!(!digests.contains(&p.digest()));
            digests.push(p.digest());
        }

        let (mut engine, sk) = test_engine(0xC9, 1);
        let mut cache = WaistbandCache::new(1, 64);
        assert!(cache.binding().is_none());
        let (pk, binding) = baggy_keygen_mpc(&mut engine, &params, &mut cache).unwrap();
        assert_eq!((pk, binding), keyed(&mut engine, &params, &sk));
        assert_eq!((cache.binding(), cache.leaf_entries()), (Some(&binding), 1));
        let mut ledger = MemoryFirstSigned::new();
        cache
            .precompute(&mut engine, &params, &pk, &binding, &mut ledger)
            .unwrap();
        let recorded = ledger.len();

        // A WOTS+C shape outside the verified profile is refused as malformed.
        let mut off_wots = params;
        off_wots.wots.target_sum -= 1;
        assert!(!off_wots.is_well_formed());
        assert_eq!(
            baggy_sign_mpc(
                &mut engine,
                &off_wots,
                &pk,
                &binding,
                &mut cache,
                &mut ledger,
                b"m"
            ),
            Err(BaggyError::InvalidParameters)
        );
        // Same key, grind bound off by one.
        let mut off = params;
        off.max_grind -= 1;
        assert!(off.is_well_formed());
        let off_binding = BaggyKeyBinding::new(&off, &pk);
        // Same parameters, another root.
        let other_root = BaggyPublicKey {
            pk_root: [0x55; 32],
            ..pk
        };
        let other_root_binding = BaggyKeyBinding::new(&params, &other_root);
        let before = engine.stats();
        // (parameters, public key, binding presented, expected refusal). The binding stored
        // at keygen does not match the changed inputs, and a binding rebuilt for them does
        // not match the identity the key shares were bound to at keygen: both are refused
        // before the cache is consulted.
        let cases = [
            (&off, &pk, &binding, BaggyError::KeyBindingMismatch),
            (&off, &pk, &off_binding, BaggyError::KeyBindingMismatch),
            (
                &params,
                &other_root,
                &binding,
                BaggyError::KeyBindingMismatch,
            ),
            (
                &params,
                &other_root,
                &other_root_binding,
                BaggyError::KeyBindingMismatch,
            ),
        ];
        for (i, (p, k, b, want)) in cases.into_iter().enumerate() {
            assert_eq!(
                baggy_sign_mpc(&mut engine, p, k, b, &mut cache, &mut ledger, b"m"),
                Err(want.clone()),
                "sign case {i}"
            );
            assert_eq!(
                cache.precompute(&mut engine, p, k, b, &mut ledger),
                Err(want),
                "precompute case {i}"
            );
        }
        assert_eq!(
            baggy_keygen_mpc(&mut engine, &off, &mut cache),
            Err(BaggyError::CacheIdentityMismatch)
        );
        assert_eq!(engine.stats(), before);

        // Another key.
        let (mut other_engine, other_sk) = test_engine(0xCA, 1);
        let (other_pk, other_binding) = keyed(&mut other_engine, &params, &other_sk);
        assert_ne!(other_pk.pk_seed, pk.pk_seed);
        let before = other_engine.stats();
        assert_eq!(
            baggy_sign_mpc(
                &mut other_engine,
                &params,
                &other_pk,
                &other_binding,
                &mut cache,
                &mut ledger,
                b"m"
            ),
            Err(BaggyError::CacheIdentityMismatch)
        );
        assert_eq!(
            cache.precompute(
                &mut other_engine,
                &params,
                &other_pk,
                &other_binding,
                &mut ledger
            ),
            Err(BaggyError::CacheIdentityMismatch)
        );
        // This key's public key and binding on the other key's engine.
        assert_eq!(
            baggy_sign_mpc(
                &mut other_engine,
                &params,
                &pk,
                &binding,
                &mut cache,
                &mut ledger,
                b"m"
            ),
            Err(BaggyError::KeyBindingMismatch)
        );
        assert_eq!(
            baggy_keygen_mpc(&mut other_engine, &params, &mut cache),
            Err(BaggyError::CacheIdentityMismatch)
        );
        assert_eq!(other_engine.stats(), before);

        // The cache is unchanged and still serves its own key.
        assert_eq!((cache.binding(), ledger.len()), (Some(&binding), recorded));
        let sig = baggy_sign_mpc(
            &mut engine,
            &params,
            &pk,
            &binding,
            &mut cache,
            &mut ledger,
            b"m",
        )
        .unwrap();
        assert_eq!(Some(sig), baggy_reference_sign(&params, &sk, &pk, b"m"));
        assert!(cache.hits() >= 1);
    }

    #[test]
    fn a_second_digit_vector_for_a_recorded_static_key_is_refused_before_the_node_round() {
        let params = BaggyParams::TEST_SMALL;
        let d = params.num_layers;
        let (mut engine, sk) = test_engine(0xCB, 1);
        let (pk, binding) = keyed(&mut engine, &params, &sk);
        let msg = b"first-signed";
        let want = baggy_reference_sign(&params, &sk, &pk, msg).unwrap();
        let (key, legit) = path_key(&params, &pk, &binding, msg, &want, d - 1);
        let conflict = BaggyError::StaticKeyDigitsConflict {
            layer: key.layer,
            tree: key.tree,
            key_pair: key.key_pair,
        };
        // Another codeword of the same key: the same digits in another order.
        let mut other = legit.clone();
        let j = (1..other.len()).find(|&j| other[j] != other[0]).unwrap();
        other.swap(0, j);
        let record = |digits: &Vec<u8>| FirstSignedRecord {
            key,
            digits: digits.clone(),
        };

        let mut ledger = MemoryFirstSigned::new();
        ledger.sync_record(&[record(&other)]).unwrap();
        // The store keeps the first vector: an equal record is a no-op, another is refused.
        assert_eq!(ledger.sync_record(&[record(&other)]), Ok(()));
        assert_eq!(
            ledger.sync_record(&[record(&legit)]),
            Err(FirstSignedError::Conflict)
        );
        assert_eq!(ledger.first_signed(&key), Ok(Some(other.clone())));

        // Signing would open `legit` on a key recorded with `other`: refused after the
        // endpoint round, before the node round, and nothing is written.
        let mut none = WaistbandCache::disabled();
        let before = engine.stats();
        assert_eq!(
            baggy_sign_mpc(
                &mut engine,
                &params,
                &pk,
                &binding,
                &mut none,
                &mut ledger,
                msg
            ),
            Err(conflict.clone())
        );
        assert_eq!(engine.stats().open_rounds - before.open_rounds, 2);
        assert_eq!(ledger.len(), 1);
        // Precompute opens the same key's nodes and is refused the same way.
        let mut cache = WaistbandCache::new(1, 64);
        let before = engine.stats();
        assert_eq!(
            cache.precompute(&mut engine, &params, &pk, &binding, &mut ledger),
            Err(conflict)
        );
        assert_eq!(engine.stats().open_rounds - before.open_rounds, 1);
        assert_eq!((cache.sig_entries(), ledger.len()), (0, 1));
        assert!(cache.binding().is_none());

        // A ledger whose write fails: no node round.
        let mut ledger = MemoryFirstSigned::new();
        ledger.fail_next_sync();
        let before = engine.stats();
        assert_eq!(
            baggy_sign_mpc(
                &mut engine,
                &params,
                &pk,
                &binding,
                &mut none,
                &mut ledger,
                msg
            ),
            Err(BaggyError::FirstSigned(FirstSignedError::Io))
        );
        assert_eq!(engine.stats().open_rounds - before.open_rounds, 2);
        assert!(ledger.is_empty());
        // The retry records all layers once; a repeat finds them and writes nothing.
        for _ in 0..2 {
            assert_eq!(
                baggy_sign_mpc(
                    &mut engine,
                    &params,
                    &pk,
                    &binding,
                    &mut none,
                    &mut ledger,
                    msg
                ),
                Ok(want.clone())
            );
            assert_eq!((ledger.len(), ledger.sync_count()), (d, 1));
            assert_eq!(ledger.first_signed(&key), Ok(Some(legit.clone())));
        }
    }

    #[test]
    fn beaver_bank_mode_signs_identically_and_never_reuses_a_triple() {
        let params = BaggyParams::TEST_SMALL;
        let (mut engine, sk) = test_engine(0xC6, 1);
        let (pk, binding) = keyed(&mut engine, &params, &sk);
        let msg = b"mode 1A";
        // 2 randomiser waves; the chain lanes of three subtrees and 32 FORS lanes over PRF
        // and the first F level, then the chain lanes alone over the two remaining levels.
        let chain_lanes = 3 * 4 * params.wots.chains;
        let waves = 2 + 2 * (chain_lanes + 32).div_ceil(256) + 2 * chain_lanes.div_ceil(256);
        engine.stage_beaver_bank(waves).unwrap();
        engine.set_mode(AndMode::BeaverBank).unwrap();
        let before = engine.stats();
        let mut ledger = MemoryFirstSigned::new();
        let mut none = WaistbandCache::disabled();
        let sig = baggy_sign_mpc(
            &mut engine,
            &params,
            &pk,
            &binding,
            &mut none,
            &mut ledger,
            msg,
        )
        .unwrap();
        let after = engine.stats();
        assert_eq!(Some(sig), baggy_reference_sign(&params, &sk, &pk, msg));
        assert_eq!(engine.bank().remaining_planes(), 0);
        // Twice the inline gate traffic for the same lane-permutations.
        let lane_perms = after.lane_perms - before.lane_perms;
        assert_eq!(after.and_bytes - before.and_bytes, 2 * 4800 * lane_perms);
        // The bank is spent: another signature must not fall back to reused triples.
        assert_eq!(
            baggy_sign_mpc(
                &mut engine,
                &params,
                &pk,
                &binding,
                &mut none,
                &mut ledger,
                msg
            ),
            Err(BaggyError::Engine(Rss256Error::BeaverBankExhausted))
        );
    }

    /// Faults in either phase abort at that phase's barrier; nothing of the signature is
    /// opened (a randomiser fault opens nothing at all, a sweep fault only `R`).
    #[test]
    fn active_faults_in_either_phase_abort_before_any_wots_or_fors_share_is_opened() {
        let params = BaggyParams::TEST_SMALL;
        let cases: [(u64, usize, usize, usize, [u64; 4], u64); 6] = [
            // (wave, round, plane, sender, mask, opened bytes allowed). Once phase 1 has
            // passed, `R` is open: exactly its 32-byte compact digest payload.
            (0, 0, 0, 0, [1, 0, 0, 0], 0),
            (1, 23, 1599, 2, [1, 0, 0, 0], 0),
            (2, 5, 700, 1, [1 << 40, 0, 0, 0], 32),
            (3, 11, 64, 0, [0, 0, 0, 1 << 63], 32),
            (7, 2, 1000, 2, [u64::MAX; 4], 32),
            (12, 23, 3, 1, [0b1010, 0, 0, 0], 32),
        ];
        for (i, (wave, round, plane, sender, mask, allowed)) in cases.into_iter().enumerate() {
            let (mut engine, sk) = test_engine(0xC7, i as u8);
            let (pk, binding) = keyed(&mut engine, &params, &sk);
            let mut ledger = MemoryFirstSigned::new();
            engine.inject_fault_next_wave(Fault256::GateMessage {
                wave,
                round,
                plane,
                sender,
                mask,
            });
            let before = engine.stats();
            assert_eq!(
                baggy_sign_mpc(
                    &mut engine,
                    &params,
                    &pk,
                    &binding,
                    &mut WaistbandCache::disabled(),
                    &mut ledger,
                    b"m"
                ),
                Err(BaggyError::Engine(Rss256Error::MultiplicationCheckFailed)),
                "case {i}"
            );
            assert!(ledger.is_empty(), "case {i}");
            assert_eq!(
                engine.stats().open_bytes - before.open_bytes,
                allowed,
                "case {i}"
            );
            assert!(engine.has_unverified_gates(), "case {i}");
        }
        // A bad coin opening at the cut barrier is caught the same way.
        let (mut engine, sk) = test_engine(0xC7, 99);
        let (pk, binding) = keyed(&mut engine, &params, &sk);
        engine.inject_fault(Fault256::CoinReveal { party: 2 });
        assert_eq!(
            baggy_sign_mpc(
                &mut engine,
                &params,
                &pk,
                &binding,
                &mut WaistbandCache::disabled(),
                &mut MemoryFirstSigned::new(),
                b"m"
            ),
            Err(BaggyError::Engine(Rss256Error::CoinOpeningRejected {
                party: 2
            }))
        );
    }

    #[test]
    fn baggy_params_overflow_and_intra_batch_conflict_rejected() {
        let mut bad = BaggyParams::TEST_SMALL;
        bad.subtree_height = 2;
        bad.num_layers = (1usize << (usize::BITS - 1)) + 1;
        assert!(!bad.is_well_formed());
        assert_eq!(bad.total_height_checked(), None);

        let mut bad_fors = BaggyParams::TEST_SMALL;
        bad_fors.fors_trees = usize::MAX;
        bad_fors.fors_height = 2;
        assert!(!bad_fors.is_well_formed());
        assert_eq!(bad_fors.sig_bytes_checked(), None);

        let mut no_fors = BaggyParams::TEST_SMALL;
        no_fors.fors_trees = 0;
        assert!(!no_fors.is_well_formed());
        assert_eq!(no_fors.signed_fors_trees_checked(), None);
        let sk = PqSecretKey {
            sk_seed: [1; 32],
            sk_prf: [2; 32],
            pk_seed: [3; 32],
        };
        let pk = BaggyPublicKey {
            pk_seed: [3; 32],
            pk_root: [0; 32],
        };
        for malformed in [bad, bad_fors, no_fors] {
            assert_eq!(baggy_reference_keygen(&malformed, &sk), None);
            assert_eq!(baggy_reference_sign(&malformed, &sk, &pk, b"m"), None);
            assert!(!baggy_verify(
                &malformed,
                &pk,
                b"m",
                &BaggySig {
                    r: [0; 32],
                    msg_ctr: 0,
                    fors: Vec::new(),
                    pors: None,
                    layers: Vec::new(),
                }
            ));
        }

        let mut ledger = MemoryFirstSigned::new();
        let key = StaticKeyId {
            identity: [7; 32],
            layer: 1,
            tree: 0,
            key_pair: 2,
        };
        let r1 = FirstSignedRecord {
            key,
            digits: alloc::vec![1u8, 2, 3],
        };
        let r2 = FirstSignedRecord {
            key,
            digits: alloc::vec![1u8, 2, 4],
        };
        assert_eq!(
            ledger.sync_record(&[r1.clone(), r2]),
            Err(FirstSignedError::Conflict)
        );
        assert!(ledger.is_empty());
        assert_eq!(ledger.sync_record(&[r1.clone(), r1]), Ok(()));
    }

    #[test]
    fn v2_reference_signature_verifies_round_trips_and_rejects_tampering() {
        let params = BaggyParams::TEST_SMALL_V2;
        let BaggyFewTime::PorsFp(pors_params) = params.few_time else {
            unreachable!()
        };
        let sk = PqSecretKey {
            sk_seed: [0x17; 32],
            sk_prf: [0x29; 32],
            pk_seed: [0x3b; 32],
        };
        let pk = baggy_reference_keygen(&params, &sk).unwrap();
        // Same hypertree, so the same public key as version 1 over these seeds.
        assert_eq!(
            Some(pk),
            baggy_reference_keygen(&BaggyParams::TEST_SMALL, &sk)
        );
        assert_ne!(params.digest(), BaggyParams::TEST_SMALL.digest());
        let msg = b"version two";
        let sig = baggy_reference_sign(&params, &sk, &pk, msg).unwrap();
        assert!(baggy_verify(&params, &pk, msg, &sig));
        assert!(!baggy_verify(&params, &pk, b"version 2", &sig));
        let opening = sig.pors.as_ref().unwrap();
        assert!(sig.fors.is_empty());
        assert_eq!(opening.secrets.len(), pors_params.reveal);
        assert!(opening.auth.len() <= pors_params.max_auth_nodes);

        // The two versions do not accept each other's signatures.
        assert!(!baggy_verify(&BaggyParams::TEST_SMALL, &pk, msg, &sig));
        let v1 = baggy_reference_sign(&BaggyParams::TEST_SMALL, &sk, &pk, msg).unwrap();
        assert!(!baggy_verify(&params, &pk, msg, &v1));

        // Every part of the opening is bound.
        let mut bad = sig.clone();
        bad.pors.as_mut().unwrap().secrets[0][0] ^= 1;
        assert!(!baggy_verify(&params, &pk, msg, &bad));
        let mut bad = sig.clone();
        bad.pors.as_mut().unwrap().auth[0][0] ^= 1;
        assert!(!baggy_verify(&params, &pk, msg, &bad));
        let mut bad = sig.clone();
        bad.pors.as_mut().unwrap().auth.push([0; 32]);
        assert!(!baggy_verify(&params, &pk, msg, &bad));
        let mut bad = sig.clone();
        bad.pors.as_mut().unwrap().secrets.swap(0, 1);
        assert!(!baggy_verify(&params, &pk, msg, &bad));
        // Another counter selects another subset (or fails the pruning bound).
        let mut bad = sig.clone();
        bad.msg_ctr += 1;
        assert!(!baggy_verify(&params, &pk, msg, &bad));
        // A FORS opening smuggled next to the PORS one is refused.
        let mut bad = sig.clone();
        bad.fors = v1.fors.clone();
        assert!(!baggy_verify(&params, &pk, msg, &bad));

        // A multiproof above the bound is refused even though it hashes to the same root:
        // tighten the bound to one node below this signature's.
        let tight = BaggyParams {
            few_time: BaggyFewTime::PorsFp(PorsFpParams {
                max_auth_nodes: opening.auth.len() - 1,
                ..pors_params
            }),
            ..params
        };
        assert!(tight.is_well_formed());
        assert!(!baggy_verify(&tight, &pk, msg, &sig));

        for (p, s) in [(&params, &sig), (&BaggyParams::TEST_SMALL, &v1)] {
            let raw = s.to_wire_bytes();
            assert!(raw.len() <= p.sig_bytes_checked().unwrap());
            assert_eq!(BaggySig::from_wire_bytes(p, &raw).as_ref(), Some(s));
            assert_eq!(BaggySig::from_wire_bytes(p, &raw[..raw.len() - 1]), None);
            let mut long = raw.clone();
            long.push(0);
            assert_eq!(BaggySig::from_wire_bytes(p, &long), None);
        }
        assert_eq!(
            v1.to_wire_bytes().len(),
            BaggyParams::TEST_SMALL.sig_bytes_checked().unwrap()
        );
        assert_eq!(BaggyParams::SHA3_128F.sig_bytes_checked(), Some(73_828));
        assert_eq!(BaggyParams::SHA3_128F_V2.sig_bytes_checked(), Some(71_654));
        assert!(BaggyParams::SHA3_128F_V2.is_well_formed());
        // FORS fields have no meaning under PORS+FP and must be zero.
        assert!(
            !BaggyParams {
                fors_trees: 5,
                ..params
            }
            .is_well_formed()
        );
    }

    #[test]
    fn v2_mpc_signature_on_the_replicated_engine_equals_the_reference() {
        let params = BaggyParams::TEST_SMALL_V2;
        let (mut engine, sk) = test_engine(0x61, 0x62);
        let (pk, binding) =
            baggy_keygen_mpc(&mut engine, &params, &mut WaistbandCache::disabled()).unwrap();
        assert_eq!(Some(pk), baggy_reference_keygen(&params, &sk));
        let msg = b"replicated version two";
        let sig = baggy_sign_mpc(
            &mut engine,
            &params,
            &pk,
            &binding,
            &mut WaistbandCache::disabled(),
            &mut MemoryFirstSigned::new(),
            msg,
        )
        .unwrap();
        assert!(baggy_verify(&params, &pk, msg, &sig));
        assert_eq!(Some(sig), baggy_reference_sign(&params, &sk, &pk, msg));
    }
}
