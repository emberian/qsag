//! `Jorts`: stateful single-tree 2-of-3 threshold hash-based signatures.
//!
//! One Merkle tree of height `h` over `2^h` one-time `WOTS+C` leaves (`w = 4`, `v = 128`, `T = 192`); a
//! signature spends one leaf (an *epoch*). `JortsSha3` runs on the 256-lane replicated
//! engine ([`crate::rss256`]); the algebraic `JortsPoseidon2` variant is the existing
//! authenticated-share Poseidon2 engine re-exported under this suite's name (see the end of
//! the file).
//!
//! ### Every opening is gated by `BeltLatch`
//! Before any chain share is opened, each signer durably binds
//! `(epoch, msg_digest, retry_salt, digits)`, echoes the binding to both peers and checks
//! their echoes ([`crate::belt_latch`]). The opening routines take the three resulting
//! [`OpenPermit`]s and verify them against the record being opened.
//!
//! * **Echoes are authenticated per pair.** Each signer derives one MAC key per peer from
//!   the two replicated share slots (`sk_seed`, `sk_prf`) it holds in common with that peer
//!   and with nobody else, through a hash used for nothing else. The third signer holds
//!   neither slot, so it cannot forge an echo between the other two.
//! * **Epochs advance by at most [`crate::belt_latch::MAX_EPOCH_JUMP`] per request.** A proposal further above
//!   any signer's high-water mark is refused before a salt is drawn or anything is bound.
//!   Signers whose marks have drifted further apart than that cannot sign together.
//! * The **retry salt** is a joint coin drawn after the message is fixed, so the digest a
//!   leaf signs is not known while the message is chosen. A retry replays the persisted salt
//!   and therefore the same digits; a signer set that disagrees on whether a salt exists
//!   must burn the epoch ([`BeltLatchError::RetrySaltUnavailable`]).
//!
//! ### Modes
//! * **Mode 3A, zero-preparation leaf sweep** ([`JortsSigner::sign_mode3a`]): the 128 chains of
//!   the epoch's leaf are evaluated online (one `PRF` level and up to three `F` levels, 24
//!   gate rounds each), verified at the barrier, and the selected nodes opened.
//! * **Mode 3B, rolling window** ([`JortsSigner::stage_window`],
//!   [`JortsSigner::sign_mode3b`]): the chains of the next leaves are evaluated and verified
//!   ahead of time and kept shared. Online signing is the salt coin, the latch echo and one
//!   opening round. The window lives in memory only: after a crash the epoch is re-signed
//!   with Mode 3A under the same latched salt, which opens the same nodes.
//!
//! ### Key generation
//! Every leaf of the tree is evaluated under MPC, so key generation costs `2^h * 128 * 4`
//! lane-permutations. That is a long offline ceremony at `h = 20`; the tests and the
//! benchmark use small heights and the measured cost per lane-permutation scales linearly.

use alloc::vec::Vec;
use core::fmt;

use crate::belt_latch::{
    BeltEcho, BeltLatch, BeltLatchError, BeltLatchRecord, DurableWal, EchoMacKeys,
    OpenPermit, derive_echo_mac_key, permits_authorise,
};
use crate::keccak_mpc::RssKeyShare256;
use crate::rss256::{Rss256Engine, Rss256Error};
use crate::sponge::keccak::{cshake256_32, encode_multi_frame};
use crate::tsw_baggy::{
    AdrsKind, Cshake256Suite, HashAdrs, PqSecretKey, th_pre_hash, walk_merkle_auth_path,
};
use crate::wots_c::{
    DigestGrinder, LaneSpec, Sweep, WOTS_STEPS, WotsCParams, merkle_auth_path, merkle_levels,
    wots_c_leaf, wots_c_recover_pk, wots_c_reference_leaf, wots_c_reference_nodes,
};

/// Role tag of the `WOTS+C` digest of a `Jorts` message.
pub const TAG_JORTS_DIGEST: &[u8] = b"QSAG.JORTS.DIGEST/v1";
const TAG_JORTS_BIND: &[u8] = b"QSAG.JORTS.BIND/v1";
const SALT_COIN_LABEL: &[u8] = b"QSAG-JORTS-RETRY-SALT-v1";

/// Bytes one signer sends in the echo exchange: one echo to each of its two peers, each
/// carrying epoch, message digest, salt, binding and the pairwise tag. Sender and receiver
/// are implied by the channel.
const ECHO_WIRE_BYTES: u64 = 2 * (8 + 32 + 32 + 32 + 32);

/// Marker for the `SHAKE`-based suite.
#[derive(Clone, Copy, Debug)]
pub struct JortsSha3;

/// `Jorts` parameters.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct JortsParams {
    pub wots: WotsCParams,
    /// Tree height `h`: the key signs `2^h` messages.
    pub height: usize,
    /// Bound on the public digest grind.
    pub max_grind: u32,
}

impl JortsParams {
    /// `d = 1`, `h = 20`: about one million signatures per key, 4,780-byte signatures.
    pub const SHA3_H20: Self = Self {
        wots: WotsCParams::V128,
        height: 20,
        max_grind: 1 << 26,
    };

    /// Small tree for tests and benchmarks.
    pub const fn with_height(height: usize) -> Self {
        Self {
            height,
            ..Self::SHA3_H20
        }
    }

    pub const fn is_well_formed(&self) -> bool {
        self.wots.is_well_formed() && self.height >= 1 && self.height <= 30
    }

    pub const fn capacity(&self) -> u64 {
        1u64 << self.height
    }

    /// Signature bytes: epoch, salt, grind counter, chain nodes, authentication path.
    pub const fn sig_bytes(&self) -> usize {
        8 + 32 + 4 + 32 * self.wots.chains + 32 * self.height
    }
}

/// Public key.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct JortsPublicKey {
    pub pk_seed: [u8; 32],
    pub pk_root: [u8; 32],
}

/// Public key with the public Merkle tree (every level), from which authentication paths are
/// read.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JortsKeyMaterial {
    pub pk: JortsPublicKey,
    /// `levels[0]` are the leaves, `levels[h]` is the root.
    pub levels: Vec<Vec<[u8; 32]>>,
}

/// Signature.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JortsSig {
    pub epoch: u64,
    pub retry_salt: [u8; 32],
    pub ctr: u32,
    pub chains: Vec<[u8; 32]>,
    /// Root-first authentication path.
    pub auth: Vec<[u8; 32]>,
}

/// Errors of `Jorts` signing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum JortsError {
    InvalidParameters,
    EpochOutOfRange,
    /// No valid `WOTS+C` digest below `max_grind`.
    GrindExhausted,
    /// The epoch is not staged in the window (or was already spent from it).
    NotStaged,
    Engine(Rss256Error),
    Latch(BeltLatchError),
    /// The assembled signature did not verify; it is not released.
    SelfCheckFailed,
}

impl From<Rss256Error> for JortsError {
    fn from(e: Rss256Error) -> Self {
        Self::Engine(e)
    }
}

impl From<BeltLatchError> for JortsError {
    fn from(e: BeltLatchError) -> Self {
        Self::Latch(e)
    }
}

impl fmt::Display for JortsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidParameters => f.write_str("invalid Jorts parameters"),
            Self::EpochOutOfRange => f.write_str("epoch beyond the key's capacity"),
            Self::GrindExhausted => f.write_str("no valid digest within the grind bound"),
            Self::NotStaged => f.write_str("epoch is not staged in the window"),
            Self::Engine(e) => write!(f, "engine: {e}"),
            Self::Latch(e) => write!(f, "latch: {e}"),
            Self::SelfCheckFailed => f.write_str("assembled signature failed verification"),
        }
    }
}

impl core::error::Error for JortsError {}

/// Message digest bound to the public key.
pub fn jorts_msg_digest(pk: &JortsPublicKey, msg: &[u8]) -> [u8; 32] {
    th_pre_hash(Cshake256Suite, &pk.pk_seed, &pk.pk_root, msg)
}

fn jorts_grinder(
    pk: &JortsPublicKey,
    epoch: u64,
    retry_salt: &[u8; 32],
    msg_digest: &[u8; 32],
) -> DigestGrinder {
    let value = cshake256_32(
        TAG_JORTS_BIND,
        &encode_multi_frame(&[&pk.pk_root, retry_salt, msg_digest]),
    );
    let adrs = HashAdrs {
        layer: 0,
        tree: 0,
        kind: AdrsKind::WotsHash,
        key_pair: epoch as u32,
        chain_idx: u32::MAX,
        hash_step: 0,
    };
    DigestGrinder::new(TAG_JORTS_DIGEST, &pk.pk_seed, &adrs, &value)
}

/// Public digit derivation: the smallest valid grind counter and its digits.
pub fn jorts_digits(
    params: &JortsParams,
    pk: &JortsPublicKey,
    epoch: u64,
    retry_salt: &[u8; 32],
    msg_digest: &[u8; 32],
) -> Option<(u32, Vec<u8>)> {
    jorts_grinder(pk, epoch, retry_salt, msg_digest).grind(&params.wots, params.max_grind)
}

/// Verify a `Jorts` signature.
pub fn jorts_verify(params: &JortsParams, pk: &JortsPublicKey, msg: &[u8], sig: &JortsSig) -> bool {
    if !params.is_well_formed()
        || sig.epoch >= params.capacity()
        || sig.chains.len() != params.wots.chains
        || sig.auth.len() != params.height
        || sig.ctr >= params.max_grind
    {
        return false;
    }
    let md = jorts_msg_digest(pk, msg);
    let Some(digits) =
        jorts_grinder(pk, sig.epoch, &sig.retry_salt, &md).digits_at(&params.wots, sig.ctr)
    else {
        return false;
    };
    let Some(leaf) = wots_c_recover_pk(
        &params.wots,
        &pk.pk_seed,
        0,
        0,
        sig.epoch as u32,
        &digits,
        &sig.chains,
    ) else {
        return false;
    };
    walk_merkle_auth_path(
        Cshake256Suite,
        &pk.pk_seed,
        0,
        0,
        AdrsKind::Tree,
        0,
        params.height,
        0,
        sig.epoch as usize,
        leaf,
        &sig.auth,
    ) == Some(pk.pk_root)
}

fn key_material_from_leaves(pk_seed: [u8; 32], leaves: &[[u8; 32]]) -> JortsKeyMaterial {
    let levels = merkle_levels(&pk_seed, 0, 0, AdrsKind::Tree, 0, leaves, 0);
    let pk_root = levels[levels.len() - 1][0];
    JortsKeyMaterial {
        pk: JortsPublicKey { pk_seed, pk_root },
        levels,
    }
}

/// Single-party reference key generation (tests and known-answer comparisons).
pub fn jorts_reference_keygen(params: &JortsParams, sk: &PqSecretKey) -> JortsKeyMaterial {
    let leaves: Vec<[u8; 32]> = (0..params.capacity())
        .map(|leaf| wots_c_reference_leaf(&params.wots, sk, 0, 0, leaf as u32))
        .collect();
    key_material_from_leaves(sk.pk_seed, &leaves)
}

/// Single-party reference signature for a given salt.
pub fn jorts_reference_sign(
    params: &JortsParams,
    sk: &PqSecretKey,
    key: &JortsKeyMaterial,
    epoch: u64,
    retry_salt: &[u8; 32],
    msg: &[u8],
) -> Option<JortsSig> {
    let md = jorts_msg_digest(&key.pk, msg);
    let (ctr, digits) = jorts_digits(params, &key.pk, epoch, retry_salt, &md)?;
    Some(JortsSig {
        epoch,
        retry_salt: *retry_salt,
        ctr,
        chains: wots_c_reference_nodes(&params.wots, sk, 0, 0, epoch as u32, &digits),
        auth: merkle_auth_path(&key.levels, epoch as usize),
    })
}

/// Distributed key generation: evaluates every leaf under MPC, verifies, and opens only the
/// chain endpoints.
pub fn jorts_keygen_mpc(
    engine: &mut Rss256Engine,
    params: &JortsParams,
) -> Result<JortsKeyMaterial, JortsError> {
    if !params.is_well_formed() {
        return Err(JortsError::InvalidParameters);
    }
    let pk_seed = engine.pk_seed();
    let chains = params.wots.chains;
    let mut lanes = Vec::with_capacity(chains << params.height);
    for leaf in 0..params.capacity() as u32 {
        for chain in 0..chains as u32 {
            lanes.push(LaneSpec::wots(0, 0, leaf, chain));
        }
    }
    let sweep = Sweep::evaluate(engine, &pk_seed, lanes, WOTS_STEPS as u8)?;
    engine.check()?;
    engine.mark_open_round();
    let picks: Vec<(usize, u8)> =
        (0..sweep.lane_count()).map(|l| (l, WOTS_STEPS as u8)).collect();
    let endpoints = sweep.open_positions(engine, &picks)?;
    let leaves: Vec<[u8; 32]> = endpoints
        .chunks_exact(chains)
        .enumerate()
        .map(|(leaf, ends)| wots_c_leaf(&pk_seed, 0, 0, leaf as u32, ends))
        .collect();
    Ok(key_material_from_leaves(pk_seed, &leaves))
}

/// Pre-staged, verified chain shares of a run of epochs (Mode 3B).
struct StagedWindow {
    first_epoch: u64,
    spent: Vec<bool>,
    sweep: Sweep,
}

/// The three signers' latches plus the public key material, driving both signing modes.
