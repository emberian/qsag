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
    BeltEcho, BeltLatch, BeltLatchError, BeltLatchRecord, DurableWal, EchoMacKeys, OpenPermit,
    WalError, derive_echo_mac_key, permits_authorise,
};
use crate::keccak_mpc::RssKeyShare256;
use crate::rss256::{Rss256Engine, Rss256Error};
use crate::sponge::keccak::cshake256_32_multi_frame;
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
    let value = cshake256_32_multi_frame(TAG_JORTS_BIND, &[&pk.pk_root, retry_salt, msg_digest]);
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
pub struct JortsSigner<W: DurableWal> {
    params: JortsParams,
    key: JortsKeyMaterial,
    latches: [BeltLatch<W>; 3],
    windows: Vec<StagedWindow>,
}

/// Prepared immutable `Jorts` epoch binding returned by [`JortsSigner::prepare_sign_mode3a`]
/// and [`JortsSigner::prepare_sign_mode3b`] after joint salt selection, digit grinding, and
/// durable [`BeltLatch::bind`] persistence, before echo verification or any secret opening.
///
/// Not `Clone`; callers backing `JortsSigner` with [`crate::belt_latch::FsBeltWal`] commit
/// per-party ceremony reservations against [`Self::records`] and install permits via
/// [`JortsSigner::install_ceremony_permits`] (or [`JortsSigner::authorize_wals_with`]) before
/// calling [`JortsSigner::complete_sign_mode3a`] / [`JortsSigner::complete_sign_mode3b`].
#[derive(Debug, PartialEq, Eq)]
pub struct PreparedJortsSign {
    epoch: u64,
    ctr: u32,
    records: [BeltLatchRecord; 3],
}

impl PreparedJortsSign {
    pub const fn epoch(&self) -> u64 {
        self.epoch
    }

    pub const fn ctr(&self) -> u32 {
        self.ctr
    }

    pub fn retry_salt(&self) -> &[u8; 32] {
        &self.records[0].retry_salt
    }

    pub fn records(&self) -> &[BeltLatchRecord; 3] {
        &self.records
    }

    pub fn record(&self, party: usize) -> Option<&BeltLatchRecord> {
        self.records.get(party)
    }

    pub fn bindings(&self) -> [[u8; 32]; 3] {
        [
            self.records[0].binding(),
            self.records[1].binding(),
            self.records[2].binding(),
        ]
    }
}

/// What the latch phase hands to the opening phase.
struct Latched {
    record: BeltLatchRecord,
    ctr: u32,
    permits: [OpenPermit; 3],
}

/// Party `share.party_id`'s two echo-MAC keys, computed from that party's share alone.
/// Its primary slot is slot `p`, held in common with party `p + 2`; its secondary slot is
/// slot `p + 1`, held in common with party `p + 1`.
fn echo_mac_keys(pk: &JortsPublicKey, share: &RssKeyShare256) -> Result<EchoMacKeys, JortsError> {
    let p = share.party_id;
    if p >= 3 {
        return Err(JortsError::InvalidParameters);
    }
    let (next, prev) = ((p + 1) % 3, (p + 2) % 3);
    let mut context = [0u8; 64];
    context[..32].copy_from_slice(&pk.pk_seed);
    context[32..].copy_from_slice(&pk.pk_root);
    let (seed_primary, seed_secondary) = share.sk_seed_shares();
    let (prf_primary, prf_secondary) = share.sk_prf_shares();
    let with_next = derive_echo_mac_key(&context, p, next, &[seed_secondary, prf_secondary]);
    let with_prev = derive_echo_mac_key(&context, p, prev, &[seed_primary, prf_primary]);
    Ok(EchoMacKeys::new(p, with_next, with_prev)?)
}

impl<W: DurableWal> JortsSigner<W> {
    /// `wals[p]` is party `p`'s write-ahead log; existing state is recovered from it.
    /// `shares[p]` is party `p`'s key share of the key `key` belongs to
    /// ([`Rss256Engine::keys`]); it is read once, to derive that party's echo-MAC keys.
    pub fn new(
        params: JortsParams,
        key: JortsKeyMaterial,
        wals: [W; 3],
        shares: &[RssKeyShare256; 3],
    ) -> Result<Self, JortsError> {
        if !params.is_well_formed() || key.levels.len() != params.height + 1 {
            return Err(JortsError::InvalidParameters);
        }
        for (p, share) in shares.iter().enumerate() {
            if share.party_id != p || share.pk_seed != key.pk.pk_seed {
                return Err(JortsError::InvalidParameters);
            }
        }
        let [w0, w1, w2] = wals;
        let recover = |wal: W, share: &RssKeyShare256| -> Result<BeltLatch<W>, JortsError> {
            let keys = echo_mac_keys(&key.pk, share)?;
            Ok(BeltLatch::recover_with_echo_keys(wal, params.height, keys)?)
        };
        let latches = [
            recover(w0, &shares[0])?,
            recover(w1, &shares[1])?,
            recover(w2, &shares[2])?,
        ];
        Ok(Self {
            params,
            key,
            latches,
            windows: Vec::new(),
        })
    }

    pub fn public_key(&self) -> &JortsPublicKey {
        &self.key.pk
    }

    pub fn latches(&self) -> &[BeltLatch<W>; 3] {
        &self.latches
    }

    /// Smallest epoch no signer has bound yet.
    pub fn next_free_epoch(&self) -> u64 {
        self.latches.iter().map(|l| l.next_epoch()).max().unwrap_or(0)
    }

    /// Dismantle into the three logs (a simulated restart in tests).
    pub fn into_wals(self) -> [W; 3] {
        self.latches.map(BeltLatch::into_wal)
    }

    /// Epochs currently staged and unspent in the rolling window.
    pub fn staged_epochs(&self) -> usize {
        self.windows
            .iter()
            .map(|w| w.spent.iter().filter(|s| !**s).count())
            .sum()
    }

    /// Salt, digits, and durable bind across all three signers, stopping before echo
    /// verification and WAL release consumption. `views[p]` is the message digest party `p`
    /// was asked to sign; honest callers pass the same digest three times.
    fn prepare_views(
        &mut self,
        engine: &mut Rss256Engine,
        epoch: u64,
        views: &[[u8; 32]; 3],
    ) -> Result<PreparedJortsSign, JortsError> {
        if epoch >= self.params.capacity() {
            return Err(JortsError::EpochOutOfRange);
        }
        // 1. Salt: replay the persisted one, or draw a fresh joint coin if nobody has one.
        //    `latched_salt` also refuses an epoch outside a signer's window
        //    (`MAX_EPOCH_JUMP`), a consumed epoch and a poisoned latch. All three signers
        //    are asked before the coin is drawn and before any of them binds, so a refused
        //    proposal consumes no leaf at any signer.
        let mut persisted = [None; 3];
        for (slot, (latch, md)) in persisted.iter_mut().zip(self.latches.iter().zip(views)) {
            *slot = latch.latched_salt(epoch, md)?;
        }
        let salt = match persisted {
            [Some(a), Some(b), Some(c)] if a == b && b == c => a,
            [None, None, None] => {
                let mut binding = [0u8; 32];
                binding[..8].copy_from_slice(&epoch.to_be_bytes());
                binding[8..].copy_from_slice(&views[0][..24]);
                engine.joint_coin(SALT_COIN_LABEL, &binding)?
            }
            _ => return Err(BeltLatchError::RetrySaltUnavailable.into()),
        };
        // 2. Each party derives the digits of its own view and binds them durably.
        let mut ctr0 = 0u32;
        for (p, (latch, md)) in self.latches.iter_mut().zip(views).enumerate() {
            let (ctr, digits) = jorts_digits(&self.params, &self.key.pk, epoch, &salt, md)
                .ok_or(JortsError::GrindExhausted)?;
            latch.bind(epoch, md, &salt, &digits)?;
            if p == 0 {
                ctr0 = ctr;
            }
        }
        let r0 = self.latches[0]
            .in_flight()
            .cloned()
            .ok_or(BeltLatchError::NothingBound)?;
        let r1 = self.latches[1]
            .in_flight()
            .cloned()
            .ok_or(BeltLatchError::NothingBound)?;
        let r2 = self.latches[2]
            .in_flight()
            .cloned()
            .ok_or(BeltLatchError::NothingBound)?;
        Ok(PreparedJortsSign {
            epoch,
            ctr: ctr0,
            records: [r0, r1, r2],
        })
    }

    /// Install release authorization on each party's underlying [`DurableWal`] for the exact
    /// persisted [`BeltLatchRecord`] in `prepared` before completing the echo/opening phase.
    pub fn authorize_wals_with<E>(
        &mut self,
        prepared: &PreparedJortsSign,
        mut authorize: impl FnMut(usize, &mut W, &BeltLatchRecord) -> Result<(), E>,
    ) -> Result<(), E> {
        for (party, (latch, rec)) in self
            .latches
            .iter_mut()
            .zip(prepared.records.iter())
            .enumerate()
        {
            authorize(party, latch.wal_mut(), rec)?;
        }
        Ok(())
    }

    /// Verify pairwise echoes and consume each WAL's release authorization for `prepared`.
    fn verify_prepared_echoes(
        &self,
        engine: &mut Rss256Engine,
        prepared: PreparedJortsSign,
    ) -> Result<Latched, JortsError> {
        for (latch, expected) in self.latches.iter().zip(prepared.records.iter()) {
            if expected.epoch != prepared.epoch || latch.in_flight() != Some(expected) {
                return Err(BeltLatchError::PermitMismatch.into());
            }
        }
        // 3. Echo exchange: every party sends each peer an echo tagged under their pairwise
        //    key, and checks both echoes addressed to it before anything can be opened.
        let mut echoes: Vec<BeltEcho> = Vec::with_capacity(6);
        for (p, latch) in self.latches.iter().enumerate() {
            for receiver in (0..3).filter(|r| *r != p) {
                echoes.push(latch.echo_for(receiver)?);
            }
        }
        engine.charge_broadcast(ECHO_WIRE_BYTES, 1);
        let p0 = self.latches[0].verify_peer_echoes(&echoes)?;
        let p1 = self.latches[1].verify_peer_echoes(&echoes)?;
        let p2 = self.latches[2].verify_peer_echoes(&echoes)?;
        let [r0, _, _] = prepared.records;
        Ok(Latched {
            record: r0,
            ctr: prepared.ctr,
            permits: [p0, p1, p2],
        })
    }

    /// Open the signature nodes of `latched.record` from `sweep`, whose lane `first_lane + c`
    /// is chain `c` of the epoch's leaf. Refuses without three matching permits.
    fn open_and_assemble(
        &self,
        engine: &mut Rss256Engine,
        sweep: &Sweep,
        first_lane: usize,
        latched: &Latched,
        msg: &[u8],
    ) -> Result<JortsSig, JortsError> {
        permits_authorise(&latched.permits, &latched.record)?;
        let picks: Vec<(usize, u8)> = latched
            .record
            .target_sum_digits
            .iter()
            .enumerate()
            .map(|(c, d)| (first_lane + c, *d))
            .collect();
        engine.mark_open_round();
        let chains = sweep.open_positions(engine, &picks)?;
        let sig = JortsSig {
            epoch: latched.record.epoch,
            retry_salt: latched.record.retry_salt,
            ctr: latched.ctr,
            chains,
            auth: merkle_auth_path(&self.key.levels, latched.record.epoch as usize),
        };
        if !jorts_verify(&self.params, &self.key.pk, msg, &sig) {
            return Err(JortsError::SelfCheckFailed);
        }
        Ok(sig)
    }

    fn sign_mode3a_views(
        &mut self,
        engine: &mut Rss256Engine,
        epoch: u64,
        msg: &[u8],
        views: &[[u8; 32]; 3],
    ) -> Result<JortsSig, JortsError> {
        let prepared = self.prepare_views(engine, epoch, views)?;
        self.complete_sign_mode3a(engine, prepared, msg)
    }

    /// Phase 1 of Mode 3A: draw or replay the joint retry salt, grind digits, and durably
    /// persist `(epoch, msg_digest, retry_salt, digits)` on all three signers' WALs without
    /// consuming WAL release authorization or opening any shares.
    pub fn prepare_sign_mode3a(
        &mut self,
        engine: &mut Rss256Engine,
        epoch: u64,
        msg: &[u8],
    ) -> Result<PreparedJortsSign, JortsError> {
        let md = jorts_msg_digest(&self.key.pk, msg);
        self.prepare_views(engine, epoch, &[md; 3])
    }

    /// Phase 2 of Mode 3A: verify pairwise echoes (consuming each WAL's release permit),
    /// evaluate the epoch's leaf online, check multiplication proofs, and open selected nodes.
    pub fn complete_sign_mode3a(
        &mut self,
        engine: &mut Rss256Engine,
        prepared: PreparedJortsSign,
        msg: &[u8],
    ) -> Result<JortsSig, JortsError> {
        let epoch = prepared.epoch;
        let latched = self.verify_prepared_echoes(engine, prepared)?;
        let chains = self.params.wots.chains;
        let lanes: Vec<LaneSpec> = (0..chains as u32)
            .map(|c| LaneSpec::wots(0, 0, epoch as u32, c))
            .collect();
        let deepest = latched
            .record
            .target_sum_digits
            .iter()
            .copied()
            .max()
            .unwrap_or(0);
        let pk_seed = self.key.pk.pk_seed;
        let sweep = Sweep::evaluate(engine, &pk_seed, lanes, deepest)?;
        engine.check()?;
        self.open_and_assemble(engine, &sweep, 0, &latched, msg)
    }

    /// Mode 3A with an inline WAL release-authorization callback invoked after durable
    /// binding persistence and before echo verification / node opening.
    pub fn sign_mode3a_authorized(
        &mut self,
        engine: &mut Rss256Engine,
        epoch: u64,
        msg: &[u8],
        authorize: impl FnMut(usize, &mut W, &BeltLatchRecord) -> Result<(), WalError>,
    ) -> Result<JortsSig, JortsError> {
        let prepared = self.prepare_sign_mode3a(engine, epoch, msg)?;
        self.authorize_wals_with(&prepared, authorize)
            .map_err(BeltLatchError::Wal)?;
        self.complete_sign_mode3a(engine, prepared, msg)
    }

    /// Mode 3A: evaluate the epoch's leaf online and sign `msg` with it.
    pub fn sign_mode3a(
        &mut self,
        engine: &mut Rss256Engine,
        epoch: u64,
        msg: &[u8],
    ) -> Result<JortsSig, JortsError> {
        self.sign_mode3a_authorized(engine, epoch, msg, |_, _, _| Ok(()))
    }

    /// Mode 3B, background: evaluate and verify all chains of epochs
    /// `first_epoch .. first_epoch + count` and keep them shared.
    pub fn stage_window(
        &mut self,
        engine: &mut Rss256Engine,
        first_epoch: u64,
        count: usize,
    ) -> Result<(), JortsError> {
        let end = first_epoch
            .checked_add(count as u64)
            .ok_or(JortsError::EpochOutOfRange)?;
        if count == 0 || end > self.params.capacity() {
            return Err(JortsError::EpochOutOfRange);
        }
        let chains = self.params.wots.chains;
        let mut lanes = Vec::with_capacity(count * chains);
        for epoch in first_epoch..end {
            for c in 0..chains as u32 {
                lanes.push(LaneSpec::wots(0, 0, epoch as u32, c));
            }
        }
        let pk_seed = self.key.pk.pk_seed;
        let sweep = Sweep::evaluate(engine, &pk_seed, lanes, WOTS_STEPS as u8)?;
        engine.check()?;
        self.windows.push(StagedWindow {
            first_epoch,
            spent: alloc::vec![false; count],
            sweep,
        });
        Ok(())
    }

    fn find_staged_epoch(&self, epoch: u64) -> Option<(usize, usize)> {
        self.windows.iter().enumerate().find_map(|(w, win)| {
            let idx = epoch.checked_sub(win.first_epoch)? as usize;
            (idx < win.spent.len() && !win.spent[idx]).then_some((w, idx))
        })
    }

    /// Phase 1 of Mode 3B: verify `epoch` is staged, draw or replay the joint retry salt,
    /// grind digits, and durably persist the binding across all three WALs.
    pub fn prepare_sign_mode3b(
        &mut self,
        engine: &mut Rss256Engine,
        epoch: u64,
        msg: &[u8],
    ) -> Result<PreparedJortsSign, JortsError> {
        if self.find_staged_epoch(epoch).is_none() {
            return Err(JortsError::NotStaged);
        }
        let md = jorts_msg_digest(&self.key.pk, msg);
        self.prepare_views(engine, epoch, &[md; 3])
    }

    /// Phase 2 of Mode 3B: verify pairwise echoes (consuming each WAL's release permit) and
    /// open the pre-staged nodes of `prepared.epoch()` with zero online gate evaluation.
    pub fn complete_sign_mode3b(
        &mut self,
        engine: &mut Rss256Engine,
        prepared: PreparedJortsSign,
        msg: &[u8],
    ) -> Result<JortsSig, JortsError> {
        let chains = self.params.wots.chains;
        let (window, index) = self
            .find_staged_epoch(prepared.epoch)
            .ok_or(JortsError::NotStaged)?;
        let latched = self.verify_prepared_echoes(engine, prepared)?;
        let sig = self.open_and_assemble(
            engine,
            &self.windows[window].sweep,
            index * chains,
            &latched,
            msg,
        )?;
        let win = &mut self.windows[window];
        win.spent[index] = true;
        win.sweep.wipe_lanes(index * chains..(index + 1) * chains);
        Ok(sig)
    }

    /// Mode 3B with an inline WAL release-authorization callback invoked after durable
    /// binding persistence and before echo verification / node opening.
    pub fn sign_mode3b_authorized(
        &mut self,
        engine: &mut Rss256Engine,
        epoch: u64,
        msg: &[u8],
        authorize: impl FnMut(usize, &mut W, &BeltLatchRecord) -> Result<(), WalError>,
    ) -> Result<JortsSig, JortsError> {
        let prepared = self.prepare_sign_mode3b(engine, epoch, msg)?;
        self.authorize_wals_with(&prepared, authorize)
            .map_err(BeltLatchError::Wal)?;
        self.complete_sign_mode3b(engine, prepared, msg)
    }

    /// Mode 3B, online: sign `msg` at a staged epoch with no online gate evaluation. The
    /// staged shares of the epoch are erased once its nodes have been opened.
    pub fn sign_mode3b(
        &mut self,
        engine: &mut Rss256Engine,
        epoch: u64,
        msg: &[u8],
    ) -> Result<JortsSig, JortsError> {
        self.sign_mode3b_authorized(engine, epoch, msg, |_, _, _| Ok(()))
    }
}

#[cfg(feature = "std")]
impl JortsSigner<crate::belt_latch::FsBeltWal> {
    /// Install per-party [`crate::ceremony_journal::CeremonyReleasePermit`]s onto the three
    /// filesystem belt WALs for `prepared` prior to [`Self::complete_sign_mode3a`] or
    /// [`Self::complete_sign_mode3b`].
    pub fn install_ceremony_permits(
        &mut self,
        prepared: &PreparedJortsSign,
        journals: [&crate::ceremony_journal::FsCeremonyJournal; 3],
        permits: [crate::ceremony_journal::CeremonyReleasePermit; 3],
    ) -> std::io::Result<()> {
        for ((latch, rec), (journal, permit)) in self
            .latches
            .iter_mut()
            .zip(prepared.records.iter())
            .zip(journals.into_iter().zip(permits))
        {
            if latch.in_flight() != Some(rec) {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::InvalidData,
                    "prepared Jorts record does not match in-flight belt latch",
                ));
            }
            latch.wal_mut().authorize_release(journal, permit)?;
        }
        Ok(())
    }
}

// The algebraic stateful suite: the authenticated-share Poseidon2 engine, gated by the
// monotonic epoch latch of `tsw_baggy`. It does not run on the 256-lane engine above.
pub use crate::poseidon2_mpc::{
    retry_jorts_poseidon2_mpc, retry_jorts_poseidon2_mpc_cached, sign_jorts_poseidon2_mpc,
    sign_jorts_poseidon2_mpc_cached,
};

/// Marker for the algebraic suite; its parameters are
/// [`crate::tsw_baggy::PqHashParams::JORTS_POSEIDON2`].
#[derive(Clone, Copy, Debug)]
pub struct JortsPoseidon2;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::belt_latch::{MAX_EPOCH_JUMP, MemoryWal};
    use crate::keccak_mpc::run_dealerless_rss_dkg_2of3;
    use crate::preprocessing::PartyPrivateRng;

    fn test_engine(tag: u8) -> (Rss256Engine, PqSecretKey) {
        let sid = [tag; 32];
        let mut rngs: [PartyPrivateRng; 3] = core::array::from_fn(|p| {
            PartyPrivateRng::from_seed([tag ^ ((p as u8) << 4); 32], b"jorts")
        });
        let (keys, _) = run_dealerless_rss_dkg_2of3(sid, 32, &mut rngs).unwrap();
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

    fn fresh_wals() -> [MemoryWal; 3] {
        [MemoryWal::new(), MemoryWal::new(), MemoryWal::new()]
    }

    #[test]
    fn keygen_and_both_modes_match_the_reference_and_verify() {
        let params = JortsParams::with_height(3);
        let (mut engine, sk) = test_engine(0xB1);
        let key = jorts_keygen_mpc(&mut engine, &params).unwrap();
        assert_eq!(key, jorts_reference_keygen(&params, &sk));
        let pk = key.pk;
        let mut signer = JortsSigner::new(params, key.clone(), fresh_wals(), engine.keys()).unwrap();

        // Mode 3A.
        let sig = signer.sign_mode3a(&mut engine, 0, b"first").unwrap();
        assert!(jorts_verify(&params, &pk, b"first", &sig));
        assert_eq!(
            Some(sig.clone()),
            jorts_reference_sign(&params, &sk, &key, 0, &sig.retry_salt, b"first")
        );
        assert_eq!(sig.chains.len(), params.wots.chains);
        assert_eq!(8 + 32 + 4 + 32 * (sig.chains.len() + sig.auth.len()), params.sig_bytes());

        // Mode 3B over a staged window of three epochs.
        signer.stage_window(&mut engine, 1, 3).unwrap();
        assert_eq!(signer.staged_epochs(), 3);
        let before = engine.stats();
        let sig2 = signer.sign_mode3b(&mut engine, 2, b"second").unwrap();
        let after = engine.stats();
        assert!(jorts_verify(&params, &pk, b"second", &sig2));
        assert_eq!(
            Some(sig2.clone()),
            jorts_reference_sign(&params, &sk, &key, 2, &sig2.retry_salt, b"second")
        );
        // No gate was evaluated and no product proof ran online.
        assert_eq!(after.lane_perms, before.lane_perms);
        assert_eq!(after.and_bytes, before.and_bytes);
        assert_eq!(after.checks, before.checks);
        // The spent epoch is gone from the window; the others remain.
        assert_eq!(signer.staged_epochs(), 2);
        assert_eq!(
            signer.sign_mode3b(&mut engine, 2, b"second"),
            Err(JortsError::NotStaged)
        );
        assert_eq!(signer.sign_mode3b(&mut engine, 7, b"x"), Err(JortsError::NotStaged));

        // Tampered signatures and wrong messages are rejected.
        assert!(!jorts_verify(&params, &pk, b"other", &sig));
        let mut bad = sig.clone();
        bad.chains[57][31] ^= 1;
        assert!(!jorts_verify(&params, &pk, b"first", &bad));
        let mut bad = sig.clone();
        bad.auth[0][0] ^= 1;
        assert!(!jorts_verify(&params, &pk, b"first", &bad));
        let mut bad = sig.clone();
        bad.retry_salt[0] ^= 1;
        assert!(!jorts_verify(&params, &pk, b"first", &bad));
        let mut bad = sig;
        bad.epoch = 1;
        assert!(!jorts_verify(&params, &pk, b"first", &bad));
    }

    #[test]
    fn crash_replay_reopens_the_same_nodes_and_refuses_a_second_message() {
        let params = JortsParams::with_height(2);
        let (mut engine, _sk) = test_engine(0xB2);
        let key = jorts_keygen_mpc(&mut engine, &params).unwrap();
        let mut signer = JortsSigner::new(params, key.clone(), fresh_wals(), engine.keys()).unwrap();
        let sig = signer.sign_mode3a(&mut engine, 1, b"pay 5").unwrap();

        // Crash: memory is lost, the three logs survive.
        let wals = signer.into_wals();
        let mut signer = JortsSigner::new(params, key.clone(), wals, engine.keys()).unwrap();
        assert_eq!(signer.next_free_epoch(), 2);

        // Retrying the same message replays the persisted salt: identical signature.
        let again = signer.sign_mode3a(&mut engine, 1, b"pay 5").unwrap();
        assert_eq!(again, sig);

        // A different message on the latched epoch is refused before any gate runs.
        let before = engine.stats();
        assert_eq!(
            signer.sign_mode3a(&mut engine, 1, b"pay 500"),
            Err(JortsError::Latch(BeltLatchError::EpochAlreadyBound))
        );
        assert_eq!(engine.stats().lane_perms, before.lane_perms);
        // A burned or earlier epoch cannot be used either.
        assert_eq!(
            signer.sign_mode3a(&mut engine, 0, b"pay 5"),
            Err(JortsError::Latch(BeltLatchError::EpochConsumed))
        );
        assert_eq!(
            signer.sign_mode3a(&mut engine, 4, b"pay 5"),
            Err(JortsError::EpochOutOfRange)
        );

        // One signer lost its log entirely: the others hold a salt it cannot confirm, so
        // the epoch must be burned instead of adopting a claimed salt.
        let [w0, w1, _lost] = signer.into_wals();
        let mut signer = JortsSigner::new(params, key, [w0, w1, MemoryWal::new()], engine.keys()).unwrap();
        assert_eq!(
            signer.sign_mode3a(&mut engine, 1, b"pay 5"),
            Err(JortsError::Latch(BeltLatchError::RetrySaltUnavailable))
        );
        let next = signer.next_free_epoch();
        let sig3 = signer.sign_mode3a(&mut engine, next, b"pay 5").unwrap();
        assert!(jorts_verify(&params, signer.public_key(), b"pay 5", &sig3));
    }

    /// A corrupted signer shows the two honest signers different messages for one epoch.
    /// Both honest latches bind their own view, the echo exchange exposes the split, and no
    /// gate is evaluated and no share opened for either message.
    #[test]
    fn split_view_equivocation_opens_nothing() {
        let params = JortsParams::with_height(2);
        let (mut engine, _sk) = test_engine(0xB3);
        let key = jorts_keygen_mpc(&mut engine, &params).unwrap();
        let pk = key.pk;
        let mut signer = JortsSigner::new(params, key, fresh_wals(), engine.keys()).unwrap();
        let md_a = jorts_msg_digest(&pk, b"pay alice");
        let md_b = jorts_msg_digest(&pk, b"pay mallory");
        let before = engine.stats();
        // Party 0 is told message A, party 1 message B; party 2 plays along with A.
        let err = signer
            .sign_mode3a_views(&mut engine, 0, b"pay alice", &[md_a, md_b, md_a])
            .unwrap_err();
        assert_eq!(err, JortsError::Latch(BeltLatchError::SplitView { party: 1 }));
        let after = engine.stats();
        assert_eq!(after.lane_perms, before.lane_perms);
        assert_eq!(after.open_bytes - before.open_bytes, ECHO_WIRE_BYTES);
        // The honest parties stay bound to what they saw; neither message can be completed
        // on this epoch, by either view.
        assert_eq!(
            signer.sign_mode3a(&mut engine, 0, b"pay alice"),
            Err(JortsError::Latch(BeltLatchError::EpochAlreadyBound))
        );
        assert_eq!(
            signer.sign_mode3a(&mut engine, 0, b"pay mallory"),
            Err(JortsError::Latch(BeltLatchError::EpochAlreadyBound))
        );
        // The next epoch still works.
        let sig = signer.sign_mode3a(&mut engine, 1, b"pay alice").unwrap();
        assert!(jorts_verify(&params, &pk, b"pay alice", &sig));
    }

    /// One request far above the high-water mark must not burn the key. The tree comes from
    /// the reference key generation (same key as the engine's shares) to keep a height with
    /// more leaves than the window cheap.
    #[test]
    fn an_epoch_beyond_the_window_is_refused_and_consumes_no_leaf() {
        let params = JortsParams::with_height(7);
        assert!(params.capacity() - 1 > MAX_EPOCH_JUMP + 1);
        let (mut engine, sk) = test_engine(0xB5);
        let key = jorts_reference_keygen(&params, &sk);
        let pk = key.pk;
        let mut signer = JortsSigner::new(params, key, fresh_wals(), engine.keys()).unwrap();
        let before = engine.stats();
        for epoch in [params.capacity() - 1, MAX_EPOCH_JUMP + 1] {
            assert_eq!(
                signer.sign_mode3a(&mut engine, epoch, b"burn"),
                Err(JortsError::Latch(BeltLatchError::EpochJumpTooLarge))
            );
        }
        // No coin, no echo, no gate, and no signer bound or advanced.
        let after = engine.stats();
        assert_eq!(after.lane_perms, before.lane_perms);
        assert_eq!(after.open_bytes, before.open_bytes);
        assert_eq!(after.check_hops, before.check_hops);
        assert_eq!(signer.next_free_epoch(), 0);
        for latch in signer.latches() {
            assert_eq!(latch.next_epoch(), 0);
            assert_eq!(latch.in_flight(), None);
        }
        // The largest jump inside the window signs.
        let sig = signer.sign_mode3a(&mut engine, MAX_EPOCH_JUMP, b"ok").unwrap();
        assert!(jorts_verify(&params, &pk, b"ok", &sig));
        assert_eq!(signer.next_free_epoch(), MAX_EPOCH_JUMP + 1);
    }

    /// Each pair's key is computed identically from either member's share, and the third
    /// party's two keys are both different from it.
    #[test]
    fn echo_keys_agree_within_a_pair_and_are_not_derivable_by_the_third_party() {
        let params = JortsParams::with_height(1);
        let (engine, sk) = test_engine(0xB6);
        let key = jorts_reference_keygen(&params, &sk);
        let shares = engine.keys();
        let context = [key.pk.pk_seed, key.pk.pk_root].concat();
        // The keys each party derives, from its own share only, as (with_next, with_prev).
        let derived: [([u8; 32], [u8; 32]); 3] = core::array::from_fn(|p| {
            let (seed_primary, seed_secondary) = shares[p].sk_seed_shares();
            let (prf_primary, prf_secondary) = shares[p].sk_prf_shares();
            (
                derive_echo_mac_key(&context, p, (p + 1) % 3, &[seed_secondary, prf_secondary]),
                derive_echo_mac_key(&context, p, (p + 2) % 3, &[seed_primary, prf_primary]),
            )
        });
        for p in 0..3 {
            let (next, third) = ((p + 1) % 3, (p + 2) % 3);
            // Pair {p, next}: p's key with its next peer is next's key with its previous one.
            assert_eq!(derived[p].0, derived[next].1);
            assert_ne!(derived[third].0, derived[p].0);
            assert_ne!(derived[third].1, derived[p].0);
        }
        // The signer built from the same shares completes the echo exchange with them.
        let mut engine = engine;
        let pk = key.pk;
        let mut signer = JortsSigner::new(params, key, fresh_wals(), engine.keys()).unwrap();
        let sig = signer.sign_mode3a(&mut engine, 0, b"m").unwrap();
        assert!(jorts_verify(&params, &pk, b"m", &sig));
        // Shares of another key are refused.
        let (other, _) = test_engine(0xB7);
        let key = jorts_reference_keygen(&params, &sk);
        assert!(matches!(
            JortsSigner::new(params, key, fresh_wals(), other.keys()),
            Err(JortsError::InvalidParameters)
        ));
    }

    #[test]
    fn an_engine_fault_during_the_leaf_sweep_aborts_before_any_node_is_opened() {
        use crate::rss256::Fault256;
        let params = JortsParams::with_height(1);
        let (mut engine, _sk) = test_engine(0xB4);
        let key = jorts_keygen_mpc(&mut engine, &params).unwrap();
        let mut signer = JortsSigner::new(params, key, fresh_wals(), engine.keys()).unwrap();
        // Corrupt one gate message of the next wave the engine evaluates.
        engine.inject_fault_next_wave(Fault256::GateMessage {
            wave: 0,
            round: 10,
            plane: 500,
            sender: 1,
            mask: [1 << 7, 0, 0, 0],
        });
        let opened_before = engine.stats().open_bytes;
        assert_eq!(
            signer.sign_mode3a(&mut engine, 0, b"msg"),
            Err(JortsError::Engine(Rss256Error::MultiplicationCheckFailed))
        );
        // Only the latch echo was broadcast; no chain share left any party.
        assert_eq!(engine.stats().open_bytes - opened_before, ECHO_WIRE_BYTES);
    }

    #[cfg(feature = "std")]
    #[test]
    fn fs_belt_wal_fresh_prepare_permit_install_and_crash_retry_flow() {
        use crate::belt_latch::FsBeltWal;
        use crate::ceremony_journal::{CeremonyReservation, FsCeremonyJournal};

        let dir = std::env::temp_dir().join(std::format!(
            "qsag-jorts-fs-wal-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir_all(&dir).unwrap();

        let params = JortsParams::with_height(2);
        let (mut engine, _sk) = test_engine(0xB8);
        let key = jorts_keygen_mpc(&mut engine, &params).unwrap();
        let pk = key.pk;
        let key_id = pk.pk_root;

        let wals: [FsBeltWal; 3] = core::array::from_fn(|p| {
            FsBeltWal::provision_genesis(dir.join(std::format!("belt-{p}")), [0x20 + p as u8; 32])
                .unwrap()
        });
        let mut journals: [FsCeremonyJournal; 3] = core::array::from_fn(|p| {
            FsCeremonyJournal::create_new(
                dir.join(std::format!("journal-{p}")),
                key_id,
                [0x40 + p as u8; 32],
            )
            .unwrap()
        });

        let mut signer = JortsSigner::new(params, key.clone(), wals, engine.keys()).unwrap();

        // 1. Fresh Mode 3A signing via prepare -> install_ceremony_permits -> complete.
        let prepared0 = signer.prepare_sign_mode3a(&mut engine, 0, b"tx-epoch-0").unwrap();
        let permits0: [_; 3] = core::array::from_fn(|p| {
            journals[p]
                .persist_epoch_before_release(
                    prepared0.epoch(),
                    CeremonyReservation {
                        ceremony_id: [0x01; 32],
                        key_id,
                        epoch_or_codeword: prepared0.records()[p].binding(),
                        seed_burn_cursor: 1,
                        hedge_generation: 1,
                    },
                )
                .unwrap()
        });
        signer
            .install_ceremony_permits(&prepared0, [&journals[0], &journals[1], &journals[2]], permits0)
            .unwrap();
        let sig0 = signer
            .complete_sign_mode3a(&mut engine, prepared0, b"tx-epoch-0")
            .unwrap();
        assert!(jorts_verify(&params, &pk, b"tx-epoch-0", &sig0));

        // 2. Crash after prepare + journal reservation on epoch 1 BEFORE completing opening:
        //    recovery clears in-memory WAL release permits, and commit_epoch_retry_attempt
        //    mints a fresh attempt permit for the identical persisted binding!
        let prepared1 = signer.prepare_sign_mode3a(&mut engine, 1, b"tx-epoch-1").unwrap();
        let _lost_permits: [_; 3] = core::array::from_fn(|p| {
            journals[p]
                .persist_epoch_before_release(
                    prepared1.epoch(),
                    CeremonyReservation {
                        ceremony_id: [0x02; 32],
                        key_id,
                        epoch_or_codeword: prepared1.records()[p].binding(),
                        seed_burn_cursor: 2,
                        hedge_generation: 2,
                    },
                )
                .unwrap()
        });
        let wal_ckpts: [_; 3] = core::array::from_fn(|p| signer.latches()[p].wal().checkpoint());
        let journal_ckpts: [_; 3] = core::array::from_fn(|p| journals[p].checkpoint());
        drop((prepared1, signer, journals));

        let reopened_wals: [FsBeltWal; 3] = core::array::from_fn(|p| {
            FsBeltWal::open_existing_at_least(
                dir.join(std::format!("belt-{p}")),
                [0x20 + p as u8; 32],
                wal_ckpts[p],
            )
            .unwrap()
        });
        let mut reopened_journals: [FsCeremonyJournal; 3] = core::array::from_fn(|p| {
            FsCeremonyJournal::open_existing_at_least(
                dir.join(std::format!("journal-{p}")),
                key_id,
                [0x40 + p as u8; 32],
                journal_ckpts[p],
            )
            .unwrap()
        });
        let mut recovered_signer =
            JortsSigner::new(params, key, reopened_wals, engine.keys()).unwrap();

        let sig1 = recovered_signer
            .sign_mode3a_authorized(&mut engine, 1, b"tx-epoch-1", |p, wal, rec| {
                let permit = reopened_journals[p]
                    .commit_epoch_retry_attempt(
                        rec.epoch,
                        CeremonyReservation {
                            ceremony_id: [0x03; 32],
                            key_id,
                            epoch_or_codeword: rec.binding(),
                            seed_burn_cursor: 3,
                            hedge_generation: 3,
                        },
                    )
                    .map_err(|_| WalError::Corrupt)?;
                wal.authorize_release(&reopened_journals[p], permit)
                    .map_err(|_| WalError::Io)
            })
            .unwrap();
        assert!(jorts_verify(&params, &pk, b"tx-epoch-1", &sig1));

        drop((recovered_signer, reopened_journals));
        std::fs::remove_dir_all(&dir).unwrap();
    }
}
