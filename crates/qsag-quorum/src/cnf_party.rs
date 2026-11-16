//! Isolated-party honest-majority CNF replicated sharing: one custodian per value.
//!
//! [`IsolatedCnfParty`] is one party of a `(t, n)` CNF protocol with `f = t - 1` corruptions
//! and `2f < n`. It holds only the slots of its own custody share (slot `S`, an `f`-subset
//! of the parties, is held by exactly the parties outside `S`), its pairwise link keys, its
//! private coins, its poison flag and its journal. It talks to its peers through
//! authenticated encrypted pairwise links ([`MacSealedWireChannel::new_encrypted`]). No value
//! of this module holds two parties' state, and nothing here reconstructs a wire, a slot seed
//! or the MAC key.
//!
//! ### Sharing
//! A bit `x` is the xor of one bit per slot. Every `f`-coalition misses the slot equal to
//! itself. Each slot also carries a 32-byte seed known to its holders only; it keys that
//! slot's pseudorandom shares (PRSS).
//!
//! ### Multiplication (Maurer)
//! `x * y` is the xor over all ordered slot pairs `(S, S')` of `x_S & y_S'`. The term is
//! computed by the smallest party outside `S ∪ S'`, which exists because `2f < n`. Party `i`
//! xors its terms into `v_i` and reshares it: on each of its slots but one designated slot
//! the contribution is a PRSS value every holder derives locally, and the correction
//! `v_i ^ (those values)` is sent only to the other holders of the designated slot.
//!
//! ### Active security with abort
//! Following Chida, Genkin, Hamada, Ikarashi, Kikuchi, Lindell and Nof, "Fast Large-Scale
//! Honest-Majority MPC for Malicious Adversaries" (CRYPTO 2018), every wire bit `w` has a
//! second sharing of `r * w` in `GF(2^128)` under a PRSS-random key `[r]` that is never
//! opened. Each AND also multiplies `[r * x]` by `[y]`; secret inputs are randomized by one
//! multiplication with `[r]`. A barrier ([`IsolatedCnfParty::barrier`]) runs before anything
//! is opened:
//!
//! 1. every pair of parties compares a digest of each slot they both hold: the custody
//!    replica and every correction either of them received or sent for that slot. A corrupted
//!    party that dealt different corrections to two holders is caught here, which leaves it
//!    only additive errors;
//! 2. a commit-then-open joint coin fixes one coefficient `alpha_k` per multiplication
//!    output and randomized input;
//! 3. the parties compute `[u] = sum alpha_k [r z_k]`, `[w] = sum alpha_k [z_k]`,
//!    `[T] = [u] + [r] * [w]`, and `[rho * T]` for a fresh PRSS-random `[rho]`;
//! 4. the pairs compare digests again (covering step 3 and the coin transcript);
//! 5. `rho * T` is opened and must be zero.
//!
//! Openings are checked: each missing slot arrives from all of its holders, at least one of
//! which is honest, and the copies must agree.
//!
//! Any failure poisons the party: the flag is set, the journal records the session, an abort
//! frame goes to every peer, and every later call is refused.
//!
//! ### Limits
//! * The pairwise link keys must already be authenticated. With a custody share from
//!   `qsag_core::cnf_rss` they are derived from its pairwise PRF keys; the wire DKG takes
//!   them as input.
//! * Security is with abort, not fairness: a corrupted party can stop a session, and can
//!   learn an opened output while an honest party aborts in the same opening.
//! * The barrier's statistical error is about `2^-126` per barrier.
//! * Honest-majority topologies (`2 * (t - 1) < n`, such as `2-of-3`, `3-of-5` and `4-of-7`)
//!   are supported. Dishonest-majority thresholds (`2 * (t - 1) >= n`) use `SpdzSweepEngine`
//!   or `SpdzSlhMpcCluster` instead.

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use qsag_asm::{KECCAK_ROTATION_OFFSETS, KECCAK_ROUND_CONSTANTS, KeccakState8x, keccak_f1600_x8};
use qsag_core::baggy::{BaggyEngine, BaggyError, TAG_BAGGY_OPT_RAND, TAG_BAGGY_R};
use qsag_core::cnf_rss::{
    BAGGY_F_SECRET_OFFSET, BAGGY_PRF_SECRET_OFFSET, BAGGY_SUITE_MIDSTATE, CnfRssConfig,
    CnfRssKeyShare256, IsolatedCnfSlhOracles, IsolatedSlhBackend, baggy_mu_frame,
    baggy_secret32_frame, compute_slh_profile_digest,
};
use qsag_core::fips205::{
    CommittedHedgedRandomizer, Fips205Adrs, Fips205Error, Fips205Params, HedgedRandomizerCommit,
    HedgedRandomizerOpen, SlhBlock, SlhPublicKey, compute_hedged_r_commit_v1, slh_keygen_mpc,
    slh_sign_mpc,
};
use qsag_core::rss256::Rss256Error;
use qsag_core::sponge::keccak::Cshake256Xof;
use qsag_core::tsw_baggy::{HashAdrs, TAG_PRF, TAG_TH_F};
use qsag_core::wipe::{
    ct_eq_bytes, ct_eq_bytes32, wipe_bytes, wipe_bytes32, wipe_u64s, wipe_u128s,
};
use qsag_core::wots_c::{LaneSpec, WOTS_STEPS};

use crate::hash::{SeedRng, expand, h32};
use crate::party_node::{PoisonJournal, ROUND_ABORT};
use crate::wire_channel::{MacSealedWireChannel, TransportError, WireTransport};

/// Reshare corrections of one multiplication batch.
pub const ROUND_CNF_MUL: u32 = 0x0400_0000;
/// Pairwise slot-view digests.
pub const ROUND_CNF_CONSISTENCY: u32 = 0x0401_0000;
pub const ROUND_CNF_COIN_COMMIT: u32 = 0x0402_0000;
pub const ROUND_CNF_COIN_OPEN: u32 = 0x0403_0000;
/// Shares of the blinded check value `rho * T`.
pub const ROUND_CNF_CHECK_OPEN: u32 = 0x0404_0000;
/// Shares of an opened output.
pub const ROUND_CNF_OPEN: u32 = 0x0405_0000;
/// Round-1 commitment for hedged `SLH-DSA` `opt_rand` coin-tossing (`QSAG.R_COMMIT/v1`).
pub const ROUND_CNF_HEDGED_COMMIT: u32 = 0x0406_0000;
/// Round-2 commitment-echo + opening for hedged `SLH-DSA` `opt_rand` coin-tossing.
pub const ROUND_CNF_HEDGED_OPEN: u32 = 0x0407_0000;
pub const ROUND_CNF_DKG_COMMIT: u32 = 0x0410_0000;
pub const ROUND_CNF_DKG_OPEN: u32 = 0x0411_0000;
pub const ROUND_CNF_DKG_CONFIRM: u32 = 0x0412_0000;

const STATE_BITS: usize = 1600;
const RATE_BYTES: usize = 136;
/// Multiplication outputs that may wait for a barrier before one is run automatically.
const MAX_PENDING_OUTPUTS: usize = 16 * 24 * STATE_BITS;
/// Parallel sponges evaluated per batched bit-plane `Keccak-f[1600]` wave (`1.57 MiB` reshare frame `< 4 MiB` cap).
const BATCH_SPONGES: usize = 64;
/// Bit-plane `u64` words per plane (`64` sponges = `38,400` words) before an automatic barrier flush.
const MAX_PENDING_PLANE_WORDS: usize = 24 * BATCH_SPONGES * 25;

const PURPOSE_RESHARE: u8 = 1;
const PURPOSE_MAC_KEY: u8 = 2;
const PURPOSE_CHECK_BLIND: u8 = 3;

/// Errors of the isolated CNF party.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CnfPartyError {
    /// The topology does not satisfy `2 * (t - 1) < n`.
    UnsupportedConfig,
    InvalidParameters,
    Transport(TransportError),
    /// The poison journal refused the session or could not be written.
    Journal,
    /// The party's poison flag is set for this session.
    Poisoned,
    /// A peer sent an abort frame.
    PeerAborted {
        party: usize,
    },
    /// A peer's message has the wrong length for its round.
    MalformedMessage {
        from: usize,
        round: u32,
    },
    /// `peer` reports a different view of a slot both parties hold, or of the coin.
    ConsistencyMismatch {
        peer: usize,
    },
    /// A coin or DKG opening does not match its commitment.
    OpeningRejected {
        party: usize,
    },
    /// The blinded multiplication check did not open to zero.
    MultiplicationCheckFailed,
    /// Two holders of slot `slot` sent different copies of an opened share.
    OpenShareMismatch {
        slot: usize,
    },
    CounterOverflow,
}

impl From<TransportError> for CnfPartyError {
    fn from(e: TransportError) -> Self {
        Self::Transport(e)
    }
}

impl fmt::Display for CnfPartyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnsupportedConfig => f.write_str("CNF topology is not an honest majority"),
            Self::InvalidParameters => f.write_str("invalid CNF party parameters"),
            Self::Transport(e) => write!(f, "transport: {e}"),
            Self::Journal => f.write_str("poison journal refused the session"),
            Self::Poisoned => f.write_str("session is poisoned"),
            Self::PeerAborted { party } => write!(f, "party {party} aborted"),
            Self::MalformedMessage { from, round } => {
                write!(f, "malformed message from party {from} in round {round:#x}")
            }
            Self::ConsistencyMismatch { peer } => {
                write!(f, "party {peer} holds a different view of a shared slot")
            }
            Self::OpeningRejected { party } => write!(f, "opening of party {party} rejected"),
            Self::MultiplicationCheckFailed => f.write_str("multiplication check failed"),
            Self::OpenShareMismatch { slot } => write!(f, "copies of slot {slot} differ"),
            Self::CounterOverflow => f.write_str("protocol counter overflow"),
        }
    }
}

impl core::error::Error for CnfPartyError {}

// ---------------------------------------------------------------------------------------------
// Topology
// ---------------------------------------------------------------------------------------------

/// The slot structure as one party sees it.
#[derive(Clone, Debug)]
struct Topology {
    n: usize,
    me: usize,
    /// Excluded subset of every slot, in the canonical order of [`CnfRssConfig`].
    subsets: Vec<Vec<usize>>,
    /// Global indices of the slots this party holds, ascending.
    held: Vec<usize>,
    /// Global slot index to position in `held`.
    local: Vec<Option<usize>>,
    /// For every party, the slot that receives its reshare correction.
    designated: Vec<usize>,
    /// For each held slot `S'` (by position): the held slots `S` whose term `(S, S')` is
    /// computed by this party.
    plan: Vec<Vec<usize>>,
}

impl Topology {
    fn new(cfg: &CnfRssConfig, me: usize) -> Result<Self, CnfPartyError> {
        let n = cfg.parties();
        let f = cfg.threshold() - 1;
        if f == 0 || 2 * f >= n {
            return Err(CnfPartyError::UnsupportedConfig);
        }
        if me >= n {
            return Err(CnfPartyError::InvalidParameters);
        }
        let subsets: Vec<Vec<usize>> = (0..cfg.total_slots())
            .map(|s| cfg.excluded_subset(s).map(<[usize]>::to_vec))
            .collect::<Option<_>>()
            .ok_or(CnfPartyError::InvalidParameters)?;
        let held: Vec<usize> = (0..subsets.len())
            .filter(|&s| !subsets[s].contains(&me))
            .collect();
        let mut local = vec![None; subsets.len()];
        for (pos, &s) in held.iter().enumerate() {
            local[s] = Some(pos);
        }
        let designated = (0..n)
            .map(|p| {
                subsets
                    .iter()
                    .position(|s| !s.contains(&p))
                    .ok_or(CnfPartyError::InvalidParameters)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let owner = |a: usize, b: usize| {
            (0..n).find(|p| !subsets[a].contains(p) && !subsets[b].contains(p))
        };
        let plan = held
            .iter()
            .map(|&sy| {
                (0..held.len())
                    .filter(|&lx| owner(held[lx], sy) == Some(me))
                    .collect()
            })
            .collect();
        Ok(Self {
            n,
            me,
            subsets,
            held,
            local,
            designated,
            plan,
        })
    }

    fn holds(&self, party: usize, slot: usize) -> bool {
        !self.subsets[slot].contains(&party)
    }

    fn peers(&self) -> impl Iterator<Item = usize> + use<> {
        let me = self.me;
        (0..self.n).filter(move |&p| p != me)
    }

    /// Positions (in `held`) of the slots this party and `peer` both hold, ascending.
    fn common(&self, peer: usize) -> Vec<usize> {
        (0..self.held.len())
            .filter(|&l| self.holds(peer, self.held[l]))
            .collect()
    }
}

// ---------------------------------------------------------------------------------------------
// Party key material
// ---------------------------------------------------------------------------------------------

/// One custodian's CNF key material: its replica of every slot it holds (`sk_seed`,
/// `sk_prf` and PRSS seed) and its pairwise link keys. Wiped on drop, not `Clone`, opaque
/// `Debug`.
pub struct CnfPartyKeys {
    cfg: CnfRssConfig,
    party: usize,
    key_len: usize,
    pk_seed: [u8; 32],
    /// Global indices of the held slots, ascending.
    slots: Vec<usize>,
    key_shares: Vec<[u8; 32]>,
    prf_shares: Vec<[u8; 32]>,
    prss_seeds: Vec<[u8; 32]>,
    /// `link_keys[peer]`; the own entry is zero and unused.
    link_keys: Vec<[u8; 32]>,
    scheme_identity: Option<[u8; 32]>,
    slh_profile_digest: Option<[u64; 4]>,
}

impl Drop for CnfPartyKeys {
    fn drop(&mut self) {
        for k in self
            .key_shares
            .iter_mut()
            .chain(&mut self.prf_shares)
            .chain(&mut self.prss_seeds)
            .chain(&mut self.link_keys)
        {
            wipe_bytes32(k);
        }
    }
}

impl fmt::Debug for CnfPartyKeys {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CnfPartyKeys")
            .field("party", &self.party)
            .field("slots", &self.slots)
            .finish_non_exhaustive()
    }
}

impl CnfPartyKeys {
    /// Load exactly the slots `share` holds (`sk_seed`, `sk_prf` and slot PRSS seeds). The
    /// link keys are derived from the custody share's pairwise PRF keys, which the custody
    /// DKG established between each pair.
    pub fn from_custody(share: &CnfRssKeyShare256) -> Result<Self, CnfPartyError> {
        let cfg = share.config().clone();
        let party = share.party_id;
        Topology::new(&cfg, party)?;
        if !matches!(share.key_len, 16 | 24 | 32) {
            return Err(CnfPartyError::InvalidParameters);
        }
        let slots = share.slot_indices().to_vec();
        let mut key_shares = Vec::with_capacity(slots.len());
        let mut prf_shares = Vec::with_capacity(slots.len());
        let mut prss_seeds = Vec::with_capacity(slots.len());
        for &slot in &slots {
            let (sk_seed, sk_prf, prg) = share
                .held_slot(slot)
                .ok_or(CnfPartyError::InvalidParameters)?;
            key_shares.push(*sk_seed);
            prf_shares.push(*sk_prf);
            prss_seeds.push(*prg);
        }
        let mut link_keys = vec![[0u8; 32]; cfg.parties()];
        for (peer, key) in link_keys.iter_mut().enumerate() {
            if peer != party {
                let pair = share
                    .pair_prf_key(peer)
                    .ok_or(CnfPartyError::InvalidParameters)?;
                *key = h32(b"cnf-party/link", &[pair]);
            }
        }
        Ok(Self {
            cfg,
            party,
            key_len: share.key_len,
            pk_seed: share.pk_seed,
            slots,
            key_shares,
            prf_shares,
            prss_seeds,
            link_keys,
            scheme_identity: share.scheme_identity(),
            slh_profile_digest: share.slh_profile_digest(),
        })
    }

    pub fn party(&self) -> usize {
        self.party
    }

    pub fn config(&self) -> &CnfRssConfig {
        &self.cfg
    }

    pub fn key_len(&self) -> usize {
        self.key_len
    }

    pub fn pk_seed(&self) -> &[u8; 32] {
        &self.pk_seed
    }

    /// Global indices of the slots this party holds.
    pub fn held_slots(&self) -> &[usize] {
        &self.slots
    }

    /// Bound `Baggy` key identity, if locked.
    pub fn scheme_identity(&self) -> Option<[u8; 32]> {
        self.scheme_identity
    }

    /// Bound `SLH-DSA` parameter-profile digest, if locked.
    pub fn slh_profile_digest(&self) -> Option<[u64; 4]> {
        self.slh_profile_digest
    }

    /// Lock these custodian keys to a `BaggyKeyBinding::identity()` digest (idempotent on same digest).
    pub fn bind_scheme_identity(&mut self, identity: &[u8; 32]) -> Result<(), CnfPartyError> {
        if self.slh_profile_digest.is_some() {
            return Err(CnfPartyError::InvalidParameters);
        }
        match &self.scheme_identity {
            None => {
                self.scheme_identity = Some(*identity);
                Ok(())
            }
            Some(bound) if ct_eq_bytes32(bound, identity) => Ok(()),
            Some(_) => Err(CnfPartyError::InvalidParameters),
        }
    }

    /// Lock these custodian keys to an `SLH-DSA` parameter set and `pk_seed`.
    pub fn bind_slh_params(
        &mut self,
        params: &Fips205Params,
        pk_seed: &[u8],
    ) -> Result<(), Fips205Error> {
        if !params.is_valid()
            || params.n != self.key_len
            || pk_seed.len() != self.key_len
            || !ct_eq_bytes(pk_seed, &self.pk_seed[..self.key_len])
            || self.scheme_identity.is_some()
        {
            return Err(Fips205Error::InvalidParameterSet);
        }
        let digest = compute_slh_profile_digest(params);
        match &self.slh_profile_digest {
            None => {
                self.slh_profile_digest = Some(digest);
                Ok(())
            }
            Some(bound) if *bound == digest => Ok(()),
            Some(_) => Err(Fips205Error::InvalidParameterSet),
        }
    }
}

fn recv_checked<T: WireTransport>(
    transport: &mut T,
    from: usize,
    round: u32,
    len: usize,
) -> Result<Vec<u8>, CnfPartyError> {
    match transport.recv_frame(from, round) {
        Ok(mut payload) => {
            if payload.len() == len {
                Ok(payload)
            } else {
                wipe_bytes(&mut payload);
                Err(CnfPartyError::MalformedMessage { from, round })
            }
        }
        Err(TransportError::RoundTagMismatch {
            got: ROUND_ABORT, ..
        }) => Err(CnfPartyError::PeerAborted { party: from }),
        Err(e) => Err(CnfPartyError::Transport(e)),
    }
}

fn send_abort<T: WireTransport>(transport: &mut T, topo: &Topology) {
    for peer in topo.peers() {
        // Best effort: the peer may already be gone.
        let _ = transport.send_frame(peer, ROUND_ABORT, &[]);
    }
}

// ---------------------------------------------------------------------------------------------
// Wire DKG
// ---------------------------------------------------------------------------------------------

/// One party's side of the dealerless slot-seed ceremony.
///
/// For every slot the holders, and only the holders, commit to a contribution, open it to
/// each other and derive the slot's key share and PRSS seed from all contributions. `pk_seed`
/// is a public coin of all parties. A final confirmation round compares what each pair
/// derived. `link_keys[peer]` must be pre-authenticated pairwise keys; every frame travels
/// encrypted under them, so a party outside a slot's holder set sees nothing of that slot.
///
/// A contribution opened last can depend on the others only through an abort, so each slot
/// seed is uniform as long as one holder is honest; every slot has one.
pub fn run_isolated_cnf_dkg<T: WireTransport>(
    cfg: &CnfRssConfig,
    key_len: usize,
    transport: T,
    session_id: [u8; 32],
    link_keys: Vec<[u8; 32]>,
    rng: &mut SeedRng,
) -> Result<CnfPartyKeys, CnfPartyError> {
    let me = transport.party();
    let topo = Topology::new(cfg, me)?;
    if !matches!(key_len, 16 | 24 | 32)
        || transport.parties() != topo.n
        || link_keys.len() != topo.n
    {
        return Err(CnfPartyError::InvalidParameters);
    }
    let mut keys = CnfPartyKeys {
        cfg: cfg.clone(),
        party: me,
        key_len,
        pk_seed: [0; 32],
        slots: topo.held.clone(),
        key_shares: vec![[0; 32]; topo.held.len()],
        prf_shares: vec![[0; 32]; topo.held.len()],
        prss_seeds: vec![[0; 32]; topo.held.len()],
        link_keys: link_keys.clone(),
        scheme_identity: None,
        slh_profile_digest: None,
    };
    let dkg_session = h32(b"cnf-party/dkg-session", &[&session_id]);
    let mut channel = MacSealedWireChannel::new_encrypted(transport, dkg_session, link_keys)?;
    let outcome = dkg_inner(&topo, key_len, &mut channel, &session_id, rng, &mut keys);
    match outcome {
        Ok(()) => Ok(keys),
        Err(e) => {
            send_abort(&mut channel, &topo);
            Err(e)
        }
    }
}

fn dkg_commitment(
    session: &[u8; 32],
    item: u64,
    party: usize,
    salt: &[u8; 32],
    contribution: &[u8; 32],
) -> [u8; 32] {
    h32(
        b"cnf-party/dkg-commit",
        &[
            session,
            &item.to_be_bytes(),
            &(party as u64).to_be_bytes(),
            salt,
            contribution,
        ],
    )
}

fn dkg_inner<T: WireTransport>(
    topo: &Topology,
    key_len: usize,
    channel: &mut MacSealedWireChannel<T>,
    session: &[u8; 32],
    rng: &mut SeedRng,
    keys: &mut CnfPartyKeys,
) -> Result<(), CnfPartyError> {
    const PK_ITEM: u64 = u64::MAX;
    let me = topo.me;
    let held = topo.held.len();
    // Item `held` is the public `pk_seed` coin; items `0..held` are this party's slots.
    let mut salts = vec![[0u8; 32]; held + 1];
    let mut contribs = vec![[0u8; 32]; held + 1];
    for i in 0..=held {
        salts[i] = rng.bytes32();
        contribs[i] = rng.bytes32();
    }
    let item_id = |i: usize| {
        if i == held {
            PK_ITEM
        } else {
            topo.held[i] as u64
        }
    };
    let items_with = |peer: usize| {
        let mut items = topo.common(peer);
        items.push(held);
        items
    };
    let my_coms: Vec<[u8; 32]> = (0..=held)
        .map(|i| dkg_commitment(session, item_id(i), me, &salts[i], &contribs[i]))
        .collect();

    for peer in topo.peers() {
        let mut payload = Vec::new();
        for i in items_with(peer) {
            payload.extend_from_slice(&my_coms[i]);
        }
        channel.send_frame(peer, ROUND_CNF_DKG_COMMIT, &payload)?;
    }
    // `coms[item][party]` and `opened[item][party]`.
    let mut coms = vec![vec![[0u8; 32]; topo.n]; held + 1];
    let mut opened = vec![vec![[0u8; 32]; topo.n]; held + 1];
    for i in 0..=held {
        coms[i][me] = my_coms[i];
        opened[i][me] = contribs[i];
    }
    for peer in topo.peers() {
        let items = items_with(peer);
        let raw = recv_checked(channel, peer, ROUND_CNF_DKG_COMMIT, 32 * items.len())?;
        for (chunk, &i) in raw.as_chunks::<32>().0.iter().zip(&items) {
            coms[i][peer] = *chunk;
        }
    }
    for peer in topo.peers() {
        let mut payload = Vec::new();
        for i in items_with(peer) {
            payload.extend_from_slice(&salts[i]);
            payload.extend_from_slice(&contribs[i]);
        }
        let sent = channel.send_frame(peer, ROUND_CNF_DKG_OPEN, &payload);
        wipe_bytes(&mut payload);
        sent?;
    }
    for peer in topo.peers() {
        let items = items_with(peer);
        let mut raw = recv_checked(channel, peer, ROUND_CNF_DKG_OPEN, 64 * items.len())?;
        let mut ok = true;
        for (chunk, &i) in raw.as_chunks::<64>().0.iter().zip(&items) {
            let (salt, contribution) = chunk.split_at(32);
            let (salt, contribution): (&[u8; 32], &[u8; 32]) = (
                salt.try_into()
                    .map_err(|_| CnfPartyError::InvalidParameters)?,
                contribution
                    .try_into()
                    .map_err(|_| CnfPartyError::InvalidParameters)?,
            );
            let expect = dkg_commitment(session, item_id(i), peer, salt, contribution);
            ok &= ct_eq_bytes32(&expect, &coms[i][peer]);
            opened[i][peer] = *contribution;
        }
        wipe_bytes(&mut raw);
        if !ok {
            return Err(CnfPartyError::OpeningRejected { party: peer });
        }
    }
    let derive = |i: usize, out: &mut [u8]| {
        let mut xof = Cshake256Xof::new_shake256();
        absorb_framed(&mut xof, b"cnf-party/dkg-derive");
        absorb_framed(&mut xof, session);
        absorb_framed(&mut xof, &item_id(i).to_be_bytes());
        absorb_framed(&mut xof, &(key_len as u64).to_be_bytes());
        for p in 0..topo.n {
            if i == held || topo.holds(p, topo.held[i]) {
                absorb_framed(&mut xof, &coms[i][p]);
                absorb_framed(&mut xof, &opened[i][p]);
            }
        }
        xof.squeeze(out);
    };
    for i in 0..held {
        let mut raw = [0u8; 96];
        derive(i, &mut raw);
        keys.key_shares[i][..key_len].copy_from_slice(&raw[..key_len]);
        keys.prf_shares[i][..key_len].copy_from_slice(&raw[32..32 + key_len]);
        keys.prss_seeds[i].copy_from_slice(&raw[64..96]);
        wipe_bytes(&mut raw);
    }
    let mut pk = [0u8; 32];
    derive(held, &mut pk);
    keys.pk_seed[..key_len].copy_from_slice(&pk[..key_len]);
    for row in &mut opened {
        for c in row {
            wipe_bytes32(c);
        }
    }
    for c in contribs.iter_mut().chain(&mut salts) {
        wipe_bytes32(c);
    }

    let confirmation = |peer: usize| {
        let (lo, hi) = (me.min(peer) as u64, me.max(peer) as u64);
        let mut xof = Cshake256Xof::new_shake256();
        absorb_framed(&mut xof, b"cnf-party/dkg-confirm");
        absorb_framed(&mut xof, session);
        absorb_framed(&mut xof, &lo.to_be_bytes());
        absorb_framed(&mut xof, &hi.to_be_bytes());
        absorb_framed(&mut xof, &keys.pk_seed);
        for l in topo.common(peer) {
            absorb_framed(&mut xof, &(topo.held[l] as u64).to_be_bytes());
            absorb_framed(&mut xof, &keys.key_shares[l]);
            absorb_framed(&mut xof, &keys.prf_shares[l]);
            absorb_framed(&mut xof, &keys.prss_seeds[l]);
        }
        let mut out = [0u8; 32];
        xof.squeeze(&mut out);
        out
    };
    for peer in topo.peers() {
        channel.send_frame(peer, ROUND_CNF_DKG_CONFIRM, &confirmation(peer))?;
    }
    for peer in topo.peers() {
        let raw = recv_checked(channel, peer, ROUND_CNF_DKG_CONFIRM, 32)?;
        if !ct_eq_bytes(&raw, &confirmation(peer)) {
            return Err(CnfPartyError::ConsistencyMismatch { peer });
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------------------------
// Local arithmetic
// ---------------------------------------------------------------------------------------------

fn absorb_framed(xof: &mut Cshake256Xof, part: &[u8]) {
    xof.absorb(&(part.len() as u64).to_be_bytes());
    xof.absorb(part);
}

#[inline]
fn gf_words(x: u128) -> [u64; 2] {
    [x as u64, (x >> 64) as u64]
}

#[inline]
fn gf_from_words(w: [u64; 2]) -> u128 {
    u128::from(w[0]) | (u128::from(w[1]) << 64)
}

/// Product in `GF(2)[x] / (x^128 + x^7 + x^2 + x + 1)`, the field of [`crate::dzk::Gf128`].
fn gf_mul(a: u128, b: u128) -> u128 {
    let mut acc = [0u64; 2];
    qsag_asm::gf2_128_mul_acc_batch(&mut acc, &[gf_words(a)], &[gf_words(b)]);
    gf_from_words(acc)
}

/// Theta, rho and pi on one slot's bit share.
fn linear_bits(a: &[u64; 25]) -> [u64; 25] {
    let mut c = [0u64; 5];
    for x in 0..5 {
        c[x] = a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20];
    }
    let mut b = [0u64; 25];
    for (source, &rot) in KECCAK_ROTATION_OFFSETS.iter().enumerate() {
        let (x, y) = (source % 5, source / 5);
        let d = c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
        b[y + 5 * ((2 * x + 3 * y) % 5)] = (a[source] ^ d).rotate_left(rot);
    }
    b
}

/// Theta, rho and pi on one slot's share of the 1,600 randomized wires (`lane * 64 + bit`).
fn linear_rand(a: &[u128]) -> Vec<u128> {
    let mut c = [0u128; 320];
    for x in 0..5 {
        for y in 0..5 {
            for z in 0..64 {
                c[x * 64 + z] ^= a[(x + 5 * y) * 64 + z];
            }
        }
    }
    let mut d = [0u128; 320];
    for x in 0..5 {
        for z in 0..64 {
            d[x * 64 + z] = c[((x + 4) % 5) * 64 + z] ^ c[((x + 1) % 5) * 64 + ((z + 63) & 63)];
        }
    }
    let mut b = vec![0u128; STATE_BITS];
    for (source, &rot) in KECCAK_ROTATION_OFFSETS.iter().enumerate() {
        let (x, y) = (source % 5, source / 5);
        let target = y + 5 * ((2 * x + 3 * y) % 5);
        for z in 0..64 {
            let src_z = (z + 64 - rot as usize) & 63;
            b[target * 64 + z] = a[source * 64 + src_z] ^ d[x * 64 + src_z];
        }
    }
    wipe_u128s(&mut c);
    wipe_u128s(&mut d);
    b
}

fn words_to_bytes(words: &[u64], out: &mut Vec<u8>) {
    for w in words {
        out.extend_from_slice(&w.to_le_bytes());
    }
}

fn elems_to_bytes(elems: &[u128], out: &mut Vec<u8>) {
    for e in elems {
        out.extend_from_slice(&e.to_le_bytes());
    }
}

fn xor_words_from_bytes(dst: &mut [u64], raw: &[u8]) {
    for (d, chunk) in dst.iter_mut().zip(raw.as_chunks::<8>().0) {
        *d ^= u64::from_le_bytes(*chunk);
    }
}

fn xor_elems_from_bytes(dst: &mut [u128], raw: &[u8]) {
    for (d, chunk) in dst.iter_mut().zip(raw.as_chunks::<16>().0) {
        *d ^= u128::from_le_bytes(*chunk);
    }
}

// ---------------------------------------------------------------------------------------------
// Shared values
// ---------------------------------------------------------------------------------------------

/// One party's share of a secret byte string and of its randomized wires. Opaque, wiped on
/// drop, usable only with the party and session that produced it.
pub struct SharedBytes {
    len: usize,
    party: usize,
    session: [u8; 32],
    /// Per held slot: the bit share, little-endian bit order, `ceil(8 * len / 64)` words.
    bits: Vec<Vec<u64>>,
    /// Per held slot: the share of `r * bit` for each of the `8 * len` bits.
    rand: Vec<Vec<u128>>,
}

impl SharedBytes {
    /// Length of the shared string in bytes.
    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

impl Drop for SharedBytes {
    fn drop(&mut self) {
        for b in &mut self.bits {
            wipe_u64s(b);
        }
        for r in &mut self.rand {
            wipe_u128s(r);
        }
    }
}

impl fmt::Debug for SharedBytes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SharedBytes")
            .field("len", &self.len)
            .finish_non_exhaustive()
    }
}

/// One piece of a hashed frame.
#[derive(Clone, Copy, Debug)]
pub enum FramePart<'a> {
    Public(&'a [u8]),
    Secret(&'a SharedBytes),
}

/// Per held slot: a bit-vector share and the matching randomized shares.
type SlotShares = (Vec<Vec<u64>>, Vec<Vec<u128>>);

struct SharedState {
    bits: Vec<[u64; 25]>,
    rand: Vec<Vec<u128>>,
}

impl Drop for SharedState {
    fn drop(&mut self) {
        for b in &mut self.bits {
            wipe_u64s(b);
        }
        for r in &mut self.rand {
            wipe_u128s(r);
        }
    }
}

/// Deviations a test party can be told to make.
#[cfg(test)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Fault {
    /// Add an error to the bit part of the correction of multiplication `ctr`, the same for
    /// every holder and for the party itself: a pure additive attack on `z`.
    AdditiveBitCorrection { ctr: u64 },
    /// The same on the randomized part (`r * z`).
    AdditiveRandCorrection { ctr: u64 },
    /// Send holder `peer` a different correction of multiplication `ctr` than the others.
    InconsistentCorrection { ctr: u64, peer: usize },
    /// Send `peer` a wrong share when an output is opened.
    WrongOpeningShare { peer: usize },
    /// Send `peer` a wrong slot-view digest.
    WrongConsistencyHash { peer: usize },
}

/// Per held slot: packed `u64` bit-shares and flattened `128 * words` `u64` `GF(2^128)` bit-planes.
type PlaneSlotShares = (Vec<Vec<u64>>, Vec<Vec<u64>>);

struct CachedKeyPlanes {
    words: usize,
    /// Per held slot: `words` little-endian `u64` words.
    bits: Vec<Vec<u64>>,
    /// Per held slot: `128 * words` `u64` words (`plane k` at `k * words..(k + 1) * words`).
    rand: Vec<Vec<u64>>,
}

impl Drop for CachedKeyPlanes {
    fn drop(&mut self) {
        for b in &mut self.bits {
            wipe_u64s(b);
        }
        for r in &mut self.rand {
            wipe_u64s(r);
        }
    }
}

/// Shared chain-node digests produced by [`IsolatedCnfParty::sweep`] for one custodian.
pub struct IsolatedCnfSweep {
    party: usize,
    session: [u8; 32],
    steps_per_lane: Vec<u8>,
    lane_offsets: Vec<usize>,
    /// `[held_slot][flat_node_idx]` 32-byte digest shares, wiped on `Drop`.
    slot_digests: Vec<Vec<[u8; 32]>>,
}

impl Drop for IsolatedCnfSweep {
    fn drop(&mut self) {
        for slot_nodes in &mut self.slot_digests {
            qsag_asm::volatile_fill(slot_nodes, [0u8; 32]);
        }
    }
}

impl fmt::Debug for IsolatedCnfSweep {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("IsolatedCnfSweep")
            .field("party", &self.party)
            .field("lanes", &self.steps_per_lane.len())
            .finish_non_exhaustive()
    }
}

// ---------------------------------------------------------------------------------------------
// The party
// ---------------------------------------------------------------------------------------------

/// One party of the isolated CNF engine. See the module documentation.
pub struct IsolatedCnfParty<T: WireTransport, J: PoisonJournal> {
    topo: Topology,
    transport: MacSealedWireChannel<T>,
    journal: J,
    session: [u8; 32],
    key_len: usize,
    pk_seed: [u8; 32],
    key_shares: Vec<[u8; 32]>,
    prf_shares: Vec<[u8; 32]>,
    prss_seeds: Vec<[u8; 32]>,
    scheme_identity: Option<[u8; 32]>,
    slh_profile_digest: Option<[u64; 4]>,
    rng: SeedRng,
    /// This party's share of the MAC key `r`, per held slot.
    r: Vec<u128>,
    /// Per held slot: running hash of the custody replica and every reshare correction.
    transcripts: Vec<Cshake256Xof>,
    /// Chained hash of every joint-coin transcript of this session.
    coin_binding: [u8; 32],
    mult_ctr: u64,
    barrier_ctr: u64,
    hedged_ctr: u64,
    cached_sk_seed: Option<CachedKeyPlanes>,
    cached_sk_prf: Option<CachedKeyPlanes>,
    /// Per held slot: bit shares of every unverified scalar multiplication output and input.
    pending_bits: Vec<Vec<u64>>,
    /// Per held slot: the matching shares of `r * bit`.
    pending_rand: Vec<Vec<[u64; 2]>>,
    /// Per held slot: packed `u64` bit-shares from batched multi-sponge permutations.
    pending_plane_bits: Vec<Vec<u64>>,
    /// Per held slot and `GF(2^128)` bit-plane `0..128`: packed `u64` shares of `r * bit`.
    pending_plane_rand: Vec<Vec<Vec<u64>>>,
    poisoned: bool,
    #[cfg(test)]
    fault: Option<Fault>,
    /// Plaintext of every frame received, for view tests.
    #[cfg(test)]
    received: Vec<(usize, u32, Vec<u8>)>,
}

impl<T: WireTransport, J: PoisonJournal> Drop for IsolatedCnfParty<T, J> {
    fn drop(&mut self) {
        self.wipe_secrets();
    }
}

impl<T: WireTransport, J: PoisonJournal> IsolatedCnfParty<T, J> {
    /// Build the party of `share`'s custodian for one session.
    pub fn from_custody(
        share: &CnfRssKeyShare256,
        transport: T,
        session_id: [u8; 32],
        rng_seed: &[u8; 32],
        journal: J,
    ) -> Result<Self, CnfPartyError> {
        let keys = CnfPartyKeys::from_custody(share)?;
        Self::new(&keys, transport, session_id, rng_seed, journal)
    }

    /// Build a party from its own key material. `session_id` must be fresh: the journal
    /// reserves it, and a session that was ever reserved or poisoned is refused.
    /// `rng_seed` is this party's private entropy for its coin shares.
    pub fn new(
        keys: &CnfPartyKeys,
        transport: T,
        session_id: [u8; 32],
        rng_seed: &[u8; 32],
        mut journal: J,
    ) -> Result<Self, CnfPartyError> {
        let topo = Topology::new(&keys.cfg, keys.party)?;
        if transport.party() != keys.party
            || transport.parties() != topo.n
            || keys.slots != topo.held
            || keys.prf_shares.len() != topo.held.len()
            || keys.link_keys.len() != topo.n
        {
            return Err(CnfPartyError::InvalidParameters);
        }
        if journal.is_poisoned(&session_id) {
            return Err(CnfPartyError::Poisoned);
        }
        journal
            .reserve_session(&session_id)
            .map_err(|_| CnfPartyError::Journal)?;
        let transport =
            MacSealedWireChannel::new_encrypted(transport, session_id, keys.link_keys.clone())?;
        let mut r = Vec::with_capacity(topo.held.len());
        let mut transcripts = Vec::with_capacity(topo.held.len());
        for (l, &slot) in topo.held.iter().enumerate() {
            let mut raw = [0u8; 16];
            expand(
                b"cnf-party/prss-key",
                &[
                    &keys.prss_seeds[l],
                    &session_id,
                    &(slot as u64).to_be_bytes(),
                    &[PURPOSE_MAC_KEY],
                ],
                &mut raw,
            );
            r.push(u128::from_le_bytes(raw));
            wipe_bytes(&mut raw);
            // Keyed by the slot seed: only a holder can produce or check this digest.
            let mut xof = Cshake256Xof::new_shake256();
            absorb_framed(&mut xof, b"cnf-party/slot-view");
            absorb_framed(&mut xof, &keys.prss_seeds[l]);
            absorb_framed(&mut xof, &session_id);
            absorb_framed(&mut xof, &(slot as u64).to_be_bytes());
            absorb_framed(&mut xof, &(keys.key_len as u64).to_be_bytes());
            absorb_framed(&mut xof, &keys.pk_seed);
            absorb_framed(&mut xof, &keys.key_shares[l]);
            absorb_framed(&mut xof, &keys.prf_shares[l]);
            if let Some(id) = &keys.scheme_identity {
                absorb_framed(&mut xof, b"scheme-id");
                absorb_framed(&mut xof, id);
            }
            if let Some(profile) = &keys.slh_profile_digest {
                absorb_framed(&mut xof, b"slh-profile");
                for word in profile {
                    absorb_framed(&mut xof, &word.to_le_bytes());
                }
            }
            transcripts.push(xof);
        }
        let held = topo.held.len();
        Ok(Self {
            topo,
            transport,
            journal,
            session: session_id,
            key_len: keys.key_len,
            pk_seed: keys.pk_seed,
            key_shares: keys.key_shares.clone(),
            prf_shares: keys.prf_shares.clone(),
            prss_seeds: keys.prss_seeds.clone(),
            scheme_identity: keys.scheme_identity,
            slh_profile_digest: keys.slh_profile_digest,
            rng: SeedRng::new(rng_seed, b"cnf-party"),
            r,
            transcripts,
            coin_binding: [0; 32],
            mult_ctr: 0,
            barrier_ctr: 0,
            hedged_ctr: 0,
            cached_sk_seed: None,
            cached_sk_prf: None,
            pending_bits: vec![Vec::new(); held],
            pending_rand: vec![Vec::new(); held],
            pending_plane_bits: vec![Vec::new(); held],
            pending_plane_rand: vec![vec![Vec::new(); 128]; held],
            poisoned: false,
            #[cfg(test)]
            fault: None,
            #[cfg(test)]
            received: Vec::new(),
        })
    }

    pub fn party(&self) -> usize {
        self.topo.me
    }

    pub fn is_poisoned(&self) -> bool {
        self.poisoned || self.journal.is_poisoned(&self.session)
    }

    /// Global indices of the slots whose shares this party holds.
    pub fn held_slots(&self) -> &[usize] {
        &self.topo.held
    }

    /// Bound `Baggy` key identity recorded in this party, if any.
    pub fn scheme_identity(&self) -> Option<[u8; 32]> {
        self.scheme_identity
    }

    /// Bound `SLH-DSA` parameter-profile digest recorded in this party, if any.
    pub fn slh_profile_digest(&self) -> Option<[u64; 4]> {
        self.slh_profile_digest
    }

    /// Whether multiplications are waiting for a barrier.
    pub fn has_unverified_gates(&self) -> bool {
        self.pending_rand.first().is_some_and(|p| !p.is_empty())
            || self
                .pending_plane_bits
                .first()
                .is_some_and(|p| !p.is_empty())
    }

    /// Multiplication batches run so far (one per chi round and one per loaded input).
    pub fn multiplications(&self) -> u64 {
        self.mult_ctr
    }

    pub fn barriers(&self) -> u64 {
        self.barrier_ctr
    }

    fn wipe_secrets(&mut self) {
        for k in self
            .key_shares
            .iter_mut()
            .chain(&mut self.prf_shares)
            .chain(&mut self.prss_seeds)
        {
            wipe_bytes32(k);
        }
        self.cached_sk_seed = None;
        self.cached_sk_prf = None;
        wipe_u128s(&mut self.r);
        for p in &mut self.pending_bits {
            wipe_u64s(p);
            p.clear();
        }
        for p in &mut self.pending_rand {
            qsag_asm::volatile_fill(p, [0; 2]);
            p.clear();
        }
        for p in &mut self.pending_plane_bits {
            wipe_u64s(p);
            p.clear();
        }
        for planes in &mut self.pending_plane_rand {
            for plane in planes {
                wipe_u64s(plane);
                plane.clear();
            }
        }
    }

    fn poison(&mut self) {
        if !self.poisoned {
            self.poisoned = true;
            // The in-memory flag already refuses every later call; the journal makes the
            // refusal survive a restart.
            let _ = self.journal.mark_poisoned(&self.session);
            send_abort(&mut self.transport, &self.topo);
            self.wipe_secrets();
        }
    }

    fn guarded<R>(
        &mut self,
        op: impl FnOnce(&mut Self) -> Result<R, CnfPartyError>,
    ) -> Result<R, CnfPartyError> {
        if self.is_poisoned() {
            return Err(CnfPartyError::Poisoned);
        }
        let out = op(self);
        if out.is_err() {
            self.poison();
        }
        out
    }

    fn recv(&mut self, from: usize, round: u32, len: usize) -> Result<Vec<u8>, CnfPartyError> {
        let payload = recv_checked(&mut self.transport, from, round, len)?;
        #[cfg(test)]
        self.received.push((from, round, payload.clone()));
        Ok(payload)
    }

    /// Pseudorandom contribution of `contributor` to held slot `l` in multiplication `ctr`.
    fn prss(&self, l: usize, contributor: usize, ctr: u64, words: usize, elems: usize) -> Vec<u8> {
        let mut raw = vec![0u8; 8 * words + 16 * elems];
        expand(
            b"cnf-party/prss",
            &[
                &self.prss_seeds[l],
                &self.session,
                &(self.topo.held[l] as u64).to_be_bytes(),
                &(contributor as u64).to_be_bytes(),
                &ctr.to_be_bytes(),
                &[PURPOSE_RESHARE],
            ],
            &mut raw,
        );
        raw
    }

    /// Reshare this party's product term sum `(v_bits, v_rand)` and collect every party's
    /// contribution: returns, per held slot, the share of the product.
    fn reshare(&mut self, v_bits: &[u64], v_rand: &[u128]) -> Result<SlotShares, CnfPartyError> {
        let ctr = self.mult_ctr;
        self.mult_ctr = ctr.checked_add(1).ok_or(CnfPartyError::CounterOverflow)?;
        let (words, elems) = (v_bits.len(), v_rand.len());
        let me = self.topo.me;
        let held = self.topo.held.len();
        let mut z_bits = vec![vec![0u64; words]; held];
        let mut z_rand = vec![vec![0u128; elems]; held];
        let mut corr_bits = v_bits.to_vec();
        let mut corr_rand = v_rand.to_vec();
        for l in 0..held {
            let slot = self.topo.held[l];
            for j in 0..self.topo.n {
                if !self.topo.holds(j, slot) || self.topo.designated[j] == slot {
                    continue;
                }
                let mut raw = self.prss(l, j, ctr, words, elems);
                xor_words_from_bytes(&mut z_bits[l], &raw[..8 * words]);
                xor_elems_from_bytes(&mut z_rand[l], &raw[8 * words..]);
                if j == me {
                    xor_words_from_bytes(&mut corr_bits, &raw[..8 * words]);
                    xor_elems_from_bytes(&mut corr_rand, &raw[8 * words..]);
                }
                wipe_bytes(&mut raw);
            }
        }
        #[cfg(test)]
        match self.fault {
            Some(Fault::AdditiveBitCorrection { ctr: c }) if c == ctr && words > 0 => {
                corr_bits[0] ^= 1;
            }
            Some(Fault::AdditiveRandCorrection { ctr: c }) if c == ctr && elems > 0 => {
                corr_rand[0] ^= 1;
            }
            _ => {}
        }
        let mut payload = Vec::with_capacity(8 * words + 16 * elems);
        words_to_bytes(&corr_bits, &mut payload);
        elems_to_bytes(&corr_rand, &mut payload);
        wipe_u64s(&mut corr_bits);
        wipe_u128s(&mut corr_rand);

        // The correction goes to the other holders of this party's designated slot only.
        let my_slot = self.topo.designated[me];
        for peer in self.topo.peers() {
            if !self.topo.holds(peer, my_slot) {
                continue;
            }
            #[cfg(test)]
            if self.fault == Some(Fault::InconsistentCorrection { ctr, peer }) {
                let mut bad = payload.clone();
                bad[0] ^= 1;
                self.transport.send_frame(peer, ROUND_CNF_MUL, &bad)?;
                continue;
            }
            self.transport.send_frame(peer, ROUND_CNF_MUL, &payload)?;
        }
        // Collect the corrections of every party whose designated slot this party holds, in
        // party order, so that all holders of a slot absorb the same sequence.
        for j in 0..self.topo.n {
            let slot = self.topo.designated[j];
            let Some(l) = self.topo.local[slot] else {
                continue;
            };
            let mut incoming = if j == me {
                payload.clone()
            } else {
                self.recv(j, ROUND_CNF_MUL, payload.len())?
            };
            xor_words_from_bytes(&mut z_bits[l], &incoming[..8 * words]);
            xor_elems_from_bytes(&mut z_rand[l], &incoming[8 * words..]);
            let xof = &mut self.transcripts[l];
            xof.absorb(&(j as u64).to_be_bytes());
            xof.absorb(&ctr.to_be_bytes());
            xof.absorb(&(incoming.len() as u64).to_be_bytes());
            xof.absorb(&incoming);
            wipe_bytes(&mut incoming);
        }
        wipe_bytes(&mut payload);
        Ok((z_bits, z_rand))
    }

    /// Multiply shared bit vectors: `[x] * [y]` (when `x_bits` is given) and `[r x] * [y]`.
    /// All vectors are per held slot and `nbits` long; `nbits` is a multiple of 64.
    fn mul(
        &mut self,
        x_bits: Option<&[Vec<u64>]>,
        x_rand: &[Vec<u128>],
        y_bits: &[Vec<u64>],
        nbits: usize,
    ) -> Result<SlotShares, CnfPartyError> {
        let words = nbits / 64;
        let mut v_bits = vec![0u64; if x_bits.is_some() { words } else { 0 }];
        let mut v_rand = vec![0u128; nbits];
        let mut part_rand = vec![0u128; nbits];
        let mut part_bits = vec![0u64; words];
        for (xs, y) in self.topo.plan.iter().zip(y_bits) {
            if xs.is_empty() {
                continue;
            }
            part_rand.fill(0);
            part_bits.fill(0);
            for &lx in xs {
                for (p, &x) in part_rand.iter_mut().zip(&x_rand[lx]) {
                    *p ^= x;
                }
                if let Some(x_bits) = x_bits {
                    for (p, &x) in part_bits.iter_mut().zip(&x_bits[lx]) {
                        *p ^= x;
                    }
                }
            }
            for (p, (v, &x)) in v_rand.iter_mut().zip(&part_rand).enumerate() {
                let bit = (y[p / 64] >> (p % 64)) & 1;
                *v ^= x & 0u128.wrapping_sub(u128::from(bit));
            }
            for (v, (&x, &yw)) in v_bits.iter_mut().zip(part_bits.iter().zip(y)) {
                *v ^= x & yw;
            }
        }
        wipe_u128s(&mut part_rand);
        wipe_u64s(&mut part_bits);
        let out = self.reshare(&v_bits, &v_rand);
        wipe_u64s(&mut v_bits);
        wipe_u128s(&mut v_rand);
        out
    }

    /// Multiply two shared field elements.
    fn mul_field(&mut self, a: &[u128], b: &[u128]) -> Result<Vec<u128>, CnfPartyError> {
        let mut v = 0u128;
        for (xs, &y) in self.topo.plan.iter().zip(b) {
            let part = xs.iter().fold(0u128, |acc, &lx| acc ^ a[lx]);
            v ^= gf_mul(part, y);
        }
        let (_, z) = self.reshare(&[], &[v])?;
        Ok(z.into_iter().map(|share| share[0]).collect())
    }

    /// Record one batch of wires for the next barrier.
    fn defer_check(&mut self, bits: &[Vec<u64>], rand: &[Vec<u128>]) {
        for l in 0..self.topo.held.len() {
            self.pending_bits[l].extend_from_slice(&bits[l]);
            self.pending_rand[l].extend(rand[l].iter().map(|&e| gf_words(e)));
        }
    }

    fn slot_digest(&self, l: usize) -> [u8; 32] {
        let mut out = [0u8; 32];
        self.transcripts[l].clone().squeeze(&mut out);
        out
    }

    /// Compare, with every peer, the views of all slots both parties hold and of the coins.
    fn exchange_consistency(&mut self, stage: u8) -> Result<(), CnfPartyError> {
        let me = self.topo.me;
        let digests: Vec<[u8; 32]> = (0..self.topo.held.len())
            .map(|l| self.slot_digest(l))
            .collect();
        let pair_digest = |peer: usize| {
            let mut xof = Cshake256Xof::new_shake256();
            absorb_framed(&mut xof, b"cnf-party/consistency");
            absorb_framed(&mut xof, &self.session);
            absorb_framed(&mut xof, &(me.min(peer) as u64).to_be_bytes());
            absorb_framed(&mut xof, &(me.max(peer) as u64).to_be_bytes());
            absorb_framed(&mut xof, &[stage]);
            absorb_framed(&mut xof, &self.barrier_ctr.to_be_bytes());
            absorb_framed(&mut xof, &self.coin_binding);
            for l in self.topo.common(peer) {
                absorb_framed(&mut xof, &(self.topo.held[l] as u64).to_be_bytes());
                absorb_framed(&mut xof, &digests[l]);
            }
            let mut out = [0u8; 32];
            xof.squeeze(&mut out);
            out
        };
        let expected: Vec<[u8; 32]> = (0..self.topo.n).map(pair_digest).collect();
        for peer in self.topo.peers() {
            #[allow(unused_mut)]
            let mut digest = expected[peer];
            #[cfg(test)]
            if self.fault == Some(Fault::WrongConsistencyHash { peer }) {
                digest[0] ^= 1;
            }
            self.transport
                .send_frame(peer, ROUND_CNF_CONSISTENCY, &digest)?;
        }
        for peer in self.topo.peers() {
            let raw = self.recv(peer, ROUND_CNF_CONSISTENCY, 32)?;
            if !ct_eq_bytes(&raw, &expected[peer]) {
                return Err(CnfPartyError::ConsistencyMismatch { peer });
            }
        }
        Ok(())
    }

    /// Commit-then-open coin of all parties. Its transcript is chained into `coin_binding`,
    /// which the next consistency exchange compares between every pair.
    fn joint_coin(&mut self) -> Result<[u8; 32], CnfPartyError> {
        let me = self.topo.me;
        let n = self.topo.n;
        let ctr = self.barrier_ctr.to_be_bytes();
        let commitment = |session: &[u8; 32], party: usize, salt: &[u8], seed: &[u8]| {
            h32(
                b"cnf-party/coin-commit",
                &[session, &ctr, &(party as u64).to_be_bytes(), salt, seed],
            )
        };
        let salt = self.rng.bytes32();
        let seed = self.rng.bytes32();
        let mut coms = vec![[0u8; 32]; n];
        let mut seeds = vec![[0u8; 32]; n];
        coms[me] = commitment(&self.session, me, &salt, &seed);
        seeds[me] = seed;
        for peer in self.topo.peers() {
            self.transport
                .send_frame(peer, ROUND_CNF_COIN_COMMIT, &coms[me])?;
        }
        for peer in self.topo.peers() {
            let raw = self.recv(peer, ROUND_CNF_COIN_COMMIT, 32)?;
            coms[peer].copy_from_slice(&raw);
        }
        let mut opening = [0u8; 64];
        opening[..32].copy_from_slice(&salt);
        opening[32..].copy_from_slice(&seed);
        for peer in self.topo.peers() {
            self.transport
                .send_frame(peer, ROUND_CNF_COIN_OPEN, &opening)?;
        }
        for peer in self.topo.peers() {
            let raw = self.recv(peer, ROUND_CNF_COIN_OPEN, 64)?;
            let expect = commitment(&self.session, peer, &raw[..32], &raw[32..]);
            if !ct_eq_bytes32(&expect, &coms[peer]) {
                return Err(CnfPartyError::OpeningRejected { party: peer });
            }
            seeds[peer].copy_from_slice(&raw[32..]);
        }
        let mut xof = Cshake256Xof::new_shake256();
        absorb_framed(&mut xof, b"cnf-party/coin");
        absorb_framed(&mut xof, &self.session);
        absorb_framed(&mut xof, &ctr);
        for p in 0..n {
            absorb_framed(&mut xof, &coms[p]);
            absorb_framed(&mut xof, &seeds[p]);
        }
        let mut coin = [0u8; 32];
        xof.squeeze(&mut coin);
        self.coin_binding = h32(b"cnf-party/coin-binding", &[&self.coin_binding, &coin]);
        Ok(coin)
    }

    /// Open a value shared as `shares[l]` (equal lengths) to every party. Each party sends
    /// each peer the slots that peer misses; a missing slot arrives from all of its holders
    /// and the copies must agree.
    fn open_shares(&mut self, round: u32, shares: &[Vec<u8>]) -> Result<Vec<u8>, CnfPartyError> {
        let me = self.topo.me;
        let len = shares[0].len();
        for peer in self.topo.peers() {
            let mut payload = Vec::new();
            for (l, &slot) in self.topo.held.iter().enumerate() {
                if !self.topo.holds(peer, slot) {
                    payload.extend_from_slice(&shares[l]);
                }
            }
            #[cfg(test)]
            if round == ROUND_CNF_OPEN && self.fault == Some(Fault::WrongOpeningShare { peer }) {
                payload[0] ^= 1;
            }
            self.transport.send_frame(peer, round, &payload)?;
        }
        let mut missing: Vec<Option<Vec<u8>>> = vec![None; self.topo.subsets.len()];
        for peer in self.topo.peers() {
            let slots: Vec<usize> = (0..self.topo.subsets.len())
                .filter(|&s| self.topo.holds(peer, s) && !self.topo.holds(me, s))
                .collect();
            let raw = self.recv(peer, round, len * slots.len())?;
            for (k, &slot) in slots.iter().enumerate() {
                let copy = &raw[k * len..(k + 1) * len];
                match &missing[slot] {
                    Some(first) if !ct_eq_bytes(first, copy) => {
                        return Err(CnfPartyError::OpenShareMismatch { slot });
                    }
                    Some(_) => {}
                    None => missing[slot] = Some(copy.to_vec()),
                }
            }
        }
        let mut value = vec![0u8; len];
        for share in shares.iter().chain(missing.iter().flatten()) {
            for (v, &s) in value.iter_mut().zip(share) {
                *v ^= s;
            }
        }
        Ok(value)
    }

    fn barrier_inner(&mut self) -> Result<(), CnfPartyError> {
        if !self.has_unverified_gates() {
            return Ok(());
        }
        let held = self.topo.held.len();
        self.exchange_consistency(0)?;
        let coin = self.joint_coin()?;
        let mut u = vec![0u128; held];
        let mut w = vec![0u128; held];
        let count = self.pending_rand[0].len();
        if count > 0 {
            let mut raw = vec![0u8; 16 * count];
            expand(b"cnf-party/alpha", &[&coin], &mut raw);
            let alpha: Vec<[u64; 2]> = raw
                .as_chunks::<16>()
                .0
                .iter()
                .map(|c| gf_words(u128::from_le_bytes(*c)))
                .collect();
            for l in 0..held {
                let mut acc = [0u64; 2];
                qsag_asm::gf2_128_mul_acc_batch(&mut acc, &alpha, &self.pending_rand[l]);
                u[l] ^= gf_from_words(acc);
                let bits = &self.pending_bits[l];
                let mut sum = [0u64; 2];
                for (k, a) in alpha.iter().enumerate() {
                    let mask = 0u64.wrapping_sub((bits[k / 64] >> (k % 64)) & 1);
                    sum[0] ^= a[0] & mask;
                    sum[1] ^= a[1] & mask;
                }
                w[l] ^= gf_from_words(sum);
            }
        }
        let plane_words = self.pending_plane_bits[0].len();
        if plane_words > 0 {
            let mut raw_plane = vec![0u8; 16 * (64 + plane_words)];
            expand(b"cnf-party/plane-alpha", &[&coin], &mut raw_plane);
            let chunks = raw_plane.as_chunks::<16>().0;
            let mut gamma = [[0u64; 2]; 64];
            for (dst, chunk) in gamma.iter_mut().zip(&chunks[..64]) {
                *dst = gf_words(u128::from_le_bytes(*chunk));
            }
            let beta: Vec<[u64; 2]> = chunks[64..]
                .iter()
                .map(|chunk| gf_words(u128::from_le_bytes(*chunk)))
                .collect();
            let mut gamma_lut = vec![[[0u64; 2]; 256]; 8];
            for (byte_pos, table) in gamma_lut.iter_mut().enumerate() {
                for (val, entry) in table.iter_mut().enumerate() {
                    let mut sum = [0u64; 2];
                    for bit in 0..8 {
                        if ((val >> bit) & 1) == 1 {
                            let g = gamma[8 * byte_pos + bit];
                            sum[0] ^= g[0];
                            sum[1] ^= g[1];
                        }
                    }
                    *entry = sum;
                }
            }
            let mut row_g = vec![[0u64; 2]; plane_words];
            let fold_plane = |plane: &[u64], row_g: &mut [[u64; 2]]| -> u128 {
                for (dst, &word) in row_g.iter_mut().zip(plane) {
                    let b = word.to_le_bytes();
                    let s0 = gamma_lut[0][b[0] as usize][0]
                        ^ gamma_lut[1][b[1] as usize][0]
                        ^ gamma_lut[2][b[2] as usize][0]
                        ^ gamma_lut[3][b[3] as usize][0]
                        ^ gamma_lut[4][b[4] as usize][0]
                        ^ gamma_lut[5][b[5] as usize][0]
                        ^ gamma_lut[6][b[6] as usize][0]
                        ^ gamma_lut[7][b[7] as usize][0];
                    let s1 = gamma_lut[0][b[0] as usize][1]
                        ^ gamma_lut[1][b[1] as usize][1]
                        ^ gamma_lut[2][b[2] as usize][1]
                        ^ gamma_lut[3][b[3] as usize][1]
                        ^ gamma_lut[4][b[4] as usize][1]
                        ^ gamma_lut[5][b[5] as usize][1]
                        ^ gamma_lut[6][b[6] as usize][1]
                        ^ gamma_lut[7][b[7] as usize][1];
                    *dst = [s0, s1];
                }
                let mut acc = [0u64; 2];
                qsag_asm::gf2_128_mul_acc_batch(&mut acc, &beta, row_g);
                gf_from_words(acc)
            };
            for l in 0..held {
                w[l] ^= fold_plane(&self.pending_plane_bits[l], &mut row_g);
                for m in 0..128 {
                    let pm = fold_plane(&self.pending_plane_rand[l][m], &mut row_g);
                    u[l] ^= gf_mul(pm, 1u128 << m);
                }
            }
            qsag_asm::volatile_fill(&mut row_g, [0; 2]);
        }
        let r = self.r.clone();
        let rw = self.mul_field(&r, &w)?;
        let t: Vec<u128> = u.iter().zip(&rw).map(|(a, b)| a ^ b).collect();
        let rho: Vec<u128> = (0..held)
            .map(|l| {
                let mut raw = [0u8; 16];
                expand(
                    b"cnf-party/prss-key",
                    &[
                        &self.prss_seeds[l],
                        &self.session,
                        &(self.topo.held[l] as u64).to_be_bytes(),
                        &[PURPOSE_CHECK_BLIND],
                        &self.barrier_ctr.to_be_bytes(),
                    ],
                    &mut raw,
                );
                u128::from_le_bytes(raw)
            })
            .collect();
        let blinded = self.mul_field(&rho, &t)?;
        self.exchange_consistency(1)?;
        let shares: Vec<Vec<u8>> = blinded.iter().map(|s| s.to_le_bytes().to_vec()).collect();
        let opened = self.open_shares(ROUND_CNF_CHECK_OPEN, &shares)?;
        if !ct_eq_bytes(&opened, &[0u8; 16]) {
            return Err(CnfPartyError::MultiplicationCheckFailed);
        }
        for l in 0..held {
            wipe_u64s(&mut self.pending_bits[l]);
            self.pending_bits[l].clear();
            qsag_asm::volatile_fill(&mut self.pending_rand[l], [0; 2]);
            self.pending_rand[l].clear();
            wipe_u64s(&mut self.pending_plane_bits[l]);
            self.pending_plane_bits[l].clear();
            for plane in &mut self.pending_plane_rand[l] {
                wipe_u64s(plane);
                plane.clear();
            }
        }
        self.barrier_ctr = self
            .barrier_ctr
            .checked_add(1)
            .ok_or(CnfPartyError::CounterOverflow)?;
        Ok(())
    }

    /// Verify every multiplication since the last barrier. Nothing is opened before this
    /// accepts; [`Self::open`] runs it when gates are pending.
    pub fn barrier(&mut self) -> Result<(), CnfPartyError> {
        self.guarded(Self::barrier_inner)
    }

    fn check_owned(&self, value: &SharedBytes) -> Result<(), CnfPartyError> {
        if value.party != self.topo.me
            || !ct_eq_bytes32(&value.session, &self.session)
            || value.bits.len() != self.topo.held.len()
        {
            return Err(CnfPartyError::InvalidParameters);
        }
        Ok(())
    }

    fn load_key_inner(&mut self) -> Result<SharedBytes, CnfPartyError> {
        let held = self.topo.held.len();
        let nbits = 8 * self.key_len;
        let bits: Vec<Vec<u64>> = (0..held)
            .map(|l| {
                self.key_shares[l][..self.key_len]
                    .as_chunks::<8>()
                    .0
                    .iter()
                    .map(|c| u64::from_le_bytes(*c))
                    .collect()
            })
            .collect();
        let r_rows: Vec<Vec<u128>> = self.r.iter().map(|&r| vec![r; nbits]).collect();
        let (_, rand) = self.mul(None, &r_rows, &bits, nbits)?;
        self.defer_check(&bits, &rand);
        Ok(SharedBytes {
            len: self.key_len,
            party: self.topo.me,
            session: self.session,
            bits,
            rand,
        })
    }

    /// Load this party's share of the custody secret `sk_seed` (`key_len` bytes) and
    /// randomize it under the MAC key.
    pub fn load_key_seed(&mut self) -> Result<SharedBytes, CnfPartyError> {
        self.guarded(Self::load_key_inner)
    }

    fn keccak_f(&mut self, state: &mut SharedState) -> Result<(), CnfPartyError> {
        if self.pending_rand[0].len() >= MAX_PENDING_OUTPUTS {
            self.barrier_inner()?;
        }
        let held = self.topo.held.len();
        // The public constant one lives in global slot 0's bit share.
        let one = self.topo.local[0];
        for &rc in &KECCAK_ROUND_CONSTANTS {
            let mut x_bits = vec![vec![0u64; 25]; held];
            let mut y_bits = vec![vec![0u64; 25]; held];
            let mut x_rand = vec![vec![0u128; STATE_BITS]; held];
            let mut lin_bits = Vec::with_capacity(held);
            let mut lin_rand = Vec::with_capacity(held);
            for l in 0..held {
                let b = linear_bits(&state.bits[l]);
                let br = linear_rand(&state.rand[l]);
                for lane in 0..25 {
                    let row = 5 * (lane / 5);
                    let u_lane = row + (lane + 1) % 5;
                    let v_lane = row + (lane + 2) % 5;
                    x_bits[l][lane] = if one == Some(l) {
                        !b[u_lane]
                    } else {
                        b[u_lane]
                    };
                    y_bits[l][lane] = b[v_lane];
                    for z in 0..64 {
                        x_rand[l][lane * 64 + z] = br[u_lane * 64 + z] ^ self.r[l];
                    }
                }
                lin_bits.push(b);
                lin_rand.push(br);
            }
            let product = self.mul(Some(&x_bits), &x_rand, &y_bits, STATE_BITS);
            for l in 0..held {
                wipe_u64s(&mut x_bits[l]);
                wipe_u64s(&mut y_bits[l]);
                wipe_u128s(&mut x_rand[l]);
            }
            let (z_bits, mut z_rand) = match product {
                Ok(z) => z,
                Err(e) => {
                    for l in 0..held {
                        wipe_u64s(&mut lin_bits[l]);
                        wipe_u128s(&mut lin_rand[l]);
                    }
                    return Err(e);
                }
            };
            self.defer_check(&z_bits, &z_rand);
            for l in 0..held {
                for lane in 0..25 {
                    state.bits[l][lane] = lin_bits[l][lane] ^ z_bits[l][lane];
                }
                for p in 0..STATE_BITS {
                    state.rand[l][p] = lin_rand[l][p] ^ z_rand[l][p];
                }
                if one == Some(l) {
                    state.bits[l][0] ^= rc;
                }
                for z in 0..64 {
                    if (rc >> z) & 1 == 1 {
                        state.rand[l][z] ^= self.r[l];
                    }
                }
                wipe_u64s(&mut lin_bits[l]);
                wipe_u128s(&mut lin_rand[l]);
                wipe_u128s(&mut z_rand[l]);
            }
        }
        Ok(())
    }

    fn shake_inner(
        &mut self,
        parts: &[FramePart<'_>],
        out_len: usize,
    ) -> Result<SharedBytes, CnfPartyError> {
        let total: usize = parts
            .iter()
            .map(|p| match p {
                FramePart::Public(b) => b.len(),
                FramePart::Secret(s) => s.len,
            })
            .sum();
        if total >= RATE_BYTES || out_len == 0 || out_len > RATE_BYTES {
            return Err(CnfPartyError::InvalidParameters);
        }
        let held = self.topo.held.len();
        let mut public = [0u8; 200];
        let mut state = SharedState {
            bits: vec![[0u64; 25]; held],
            rand: vec![vec![0u128; STATE_BITS]; held],
        };
        let mut offset = 0usize;
        for part in parts {
            match part {
                FramePart::Public(bytes) => {
                    public[offset..offset + bytes.len()].copy_from_slice(bytes);
                    offset += bytes.len();
                }
                FramePart::Secret(secret) => {
                    self.check_owned(secret)?;
                    for l in 0..held {
                        for b in 0..8 * secret.len {
                            let pos = 8 * offset + b;
                            let bit = (secret.bits[l][b / 64] >> (b % 64)) & 1;
                            state.bits[l][pos / 64] ^= bit << (pos % 64);
                            state.rand[l][pos] ^= secret.rand[l][b];
                        }
                    }
                    offset += secret.len;
                }
            }
        }
        public[total] ^= 0x1f;
        public[RATE_BYTES - 1] ^= 0x80;
        for (lane, chunk) in public.as_chunks::<8>().0.iter().enumerate() {
            let word = u64::from_le_bytes(*chunk);
            if let Some(l) = self.topo.local[0] {
                state.bits[l][lane] ^= word;
            }
            for z in 0..64 {
                if (word >> z) & 1 == 1 {
                    for l in 0..held {
                        state.rand[l][lane * 64 + z] ^= self.r[l];
                    }
                }
            }
        }
        self.keccak_f(&mut state)?;
        let words = (8 * out_len).div_ceil(64);
        let tail_bits = (8 * out_len) % 64;
        let bits = (0..held)
            .map(|l| {
                let mut share = state.bits[l][..words].to_vec();
                if tail_bits != 0 {
                    share[words - 1] &= (1u64 << tail_bits) - 1;
                }
                share
            })
            .collect();
        let rand = (0..held)
            .map(|l| state.rand[l][..8 * out_len].to_vec())
            .collect();
        Ok(SharedBytes {
            len: out_len,
            party: self.topo.me,
            session: self.session,
            bits,
            rand,
        })
    }

    /// Single-block `SHAKE256` of the concatenated `parts` (fewer than 136 bytes in total),
    /// whose first `out_len` output bytes stay shared.
    pub fn shake256_block(
        &mut self,
        parts: &[FramePart<'_>],
        out_len: usize,
    ) -> Result<SharedBytes, CnfPartyError> {
        self.guarded(|party| party.shake_inner(parts, out_len))
    }

    /// `SHAKE256(prefix || sk_seed || suffix)` truncated to `out_len` bytes, kept shared.
    pub fn keyed_shake256(
        &mut self,
        prefix: &[u8],
        suffix: &[u8],
        out_len: usize,
    ) -> Result<SharedBytes, CnfPartyError> {
        self.guarded(|party| {
            let key = party.load_key_inner()?;
            party.shake_inner(
                &[
                    FramePart::Public(prefix),
                    FramePart::Secret(&key),
                    FramePart::Public(suffix),
                ],
                out_len,
            )
        })
    }

    fn open_inner(&mut self, value: &SharedBytes) -> Result<Vec<u8>, CnfPartyError> {
        self.check_owned(value)?;
        self.barrier_inner()?;
        let shares: Vec<Vec<u8>> = value
            .bits
            .iter()
            .map(|words| {
                let mut raw = Vec::with_capacity(8 * words.len());
                words_to_bytes(words, &mut raw);
                raw
            })
            .collect();
        let mut opened = self.open_shares(ROUND_CNF_OPEN, &shares)?;
        opened.truncate(value.len);
        Ok(opened)
    }

    /// Open a shared value to all parties, after a barrier has accepted every pending gate.
    pub fn open(&mut self, value: &SharedBytes) -> Result<Vec<u8>, CnfPartyError> {
        self.guarded(|party| party.open_inner(value))
    }

    /// One threshold FIPS 205 WOTS chain element on the CNF-shared `sk_seed`:
    /// `chain(PRF(pk_seed, sk_seed, prf_adrs), 0, steps, pk_seed, chain_adrs)`. The secret
    /// chain start and every intermediate value stay shared; only the element after `steps`
    /// applications of `F` is opened. `n` is the custody key length.
    pub fn wots_chain_element(
        &mut self,
        prf_adrs: &Fips205Adrs,
        chain_adrs: &Fips205Adrs,
        steps: u32,
    ) -> Result<Vec<u8>, CnfPartyError> {
        self.guarded(|party| {
            let n = party.key_len;
            let pk_seed = party.pk_seed;
            let key = party.load_key_inner()?;
            let mut x = party.shake_inner(
                &[
                    FramePart::Public(&pk_seed[..n]),
                    FramePart::Public(&prf_adrs.to_bytes()),
                    FramePart::Secret(&key),
                ],
                n,
            )?;
            for j in 0..steps {
                let mut adrs = *chain_adrs;
                adrs.f6 = j;
                x = party.shake_inner(
                    &[
                        FramePart::Public(&pk_seed[..n]),
                        FramePart::Public(&adrs.to_bytes()),
                        FramePart::Secret(&x),
                    ],
                    n,
                )?;
            }
            party.open_inner(&x)
        })
    }

    // -----------------------------------------------------------------------------------------
    // Bit-plane multi-sponge Keccak engine, `Baggy` sweep & `SLH-DSA` ceremonies
    // -----------------------------------------------------------------------------------------

    fn reshare_planes(
        &mut self,
        v_bits: &[u64],
        v_rand: &[u64],
        words: usize,
    ) -> Result<PlaneSlotShares, CnfPartyError> {
        let ctr = self.mult_ctr;
        self.mult_ctr = ctr.checked_add(1).ok_or(CnfPartyError::CounterOverflow)?;
        let bit_words = v_bits.len();
        let rand_words = 128 * words;
        let me = self.topo.me;
        let held = self.topo.held.len();
        let mut z_bits = vec![vec![0u64; bit_words]; held];
        let mut z_rand = vec![vec![0u64; rand_words]; held];
        let mut corr_bits = v_bits.to_vec();
        let mut corr_rand = v_rand.to_vec();

        for l in 0..held {
            let slot = self.topo.held[l];
            for j in 0..self.topo.n {
                if !self.topo.holds(j, slot) || self.topo.designated[j] == slot {
                    continue;
                }
                let mut seed_key = h32(
                    b"cnf-party/prss-planes",
                    &[
                        &self.prss_seeds[l],
                        &self.session,
                        &(slot as u64).to_be_bytes(),
                        &(j as u64).to_be_bytes(),
                        &ctr.to_be_bytes(),
                        &[PURPOSE_RESHARE],
                    ],
                );
                if j == me {
                    prss_planes_xor(
                        &seed_key,
                        &mut z_bits[l],
                        &mut z_rand[l],
                        Some(&mut corr_bits),
                        Some(&mut corr_rand),
                    );
                } else {
                    prss_planes_xor(&seed_key, &mut z_bits[l], &mut z_rand[l], None, None);
                }
                wipe_bytes32(&mut seed_key);
            }
        }
        #[cfg(test)]
        match self.fault {
            Some(Fault::AdditiveBitCorrection { ctr: c }) if c == ctr && bit_words > 0 => {
                corr_bits[0] ^= 1;
            }
            Some(Fault::AdditiveRandCorrection { ctr: c }) if c == ctr && rand_words > 0 => {
                corr_rand[0] ^= 1;
            }
            _ => {}
        }
        let mut payload = Vec::with_capacity(8 * (bit_words + rand_words));
        words_to_bytes(&corr_bits, &mut payload);
        words_to_bytes(&corr_rand, &mut payload);
        wipe_u64s(&mut corr_bits);
        wipe_u64s(&mut corr_rand);

        let my_slot = self.topo.designated[me];
        for peer in self.topo.peers() {
            if !self.topo.holds(peer, my_slot) {
                continue;
            }
            #[cfg(test)]
            if self.fault == Some(Fault::InconsistentCorrection { ctr, peer }) {
                let mut bad = payload.clone();
                bad[0] ^= 1;
                self.transport.send_frame(peer, ROUND_CNF_MUL, &bad)?;
                continue;
            }
            self.transport.send_frame(peer, ROUND_CNF_MUL, &payload)?;
        }
        for j in 0..self.topo.n {
            let slot = self.topo.designated[j];
            let Some(l) = self.topo.local[slot] else {
                continue;
            };
            let mut incoming = if j == me {
                payload.clone()
            } else {
                self.recv(j, ROUND_CNF_MUL, payload.len())?
            };
            xor_words_from_bytes(&mut z_bits[l], &incoming[..8 * bit_words]);
            xor_words_from_bytes(&mut z_rand[l], &incoming[8 * bit_words..]);
            let xof = &mut self.transcripts[l];
            xof.absorb(&(j as u64).to_be_bytes());
            xof.absorb(&ctr.to_be_bytes());
            xof.absorb(&(incoming.len() as u64).to_be_bytes());
            xof.absorb(&incoming);
            wipe_bytes(&mut incoming);
        }
        wipe_bytes(&mut payload);
        Ok((z_bits, z_rand))
    }

    fn mul_planes(
        &mut self,
        x_bits: Option<&[Vec<u64>]>,
        x_rand: &[Vec<u64>],
        y_bits: &[Vec<u64>],
        words: usize,
    ) -> Result<PlaneSlotShares, CnfPartyError> {
        let bit_words = if x_bits.is_some() { words } else { 0 };
        let rand_words = 128 * words;
        let mut v_bits = vec![0u64; bit_words];
        let mut v_rand = vec![0u64; rand_words];
        let mut part_bits = vec![0u64; words];
        let mut part_rand = vec![0u64; rand_words];

        for (xs, y) in self.topo.plan.iter().zip(y_bits) {
            if xs.is_empty() {
                continue;
            }
            part_bits.fill(0);
            part_rand.fill(0);
            for &lx in xs {
                for (p, &x) in part_rand.iter_mut().zip(&x_rand[lx]) {
                    *p ^= x;
                }
                if let Some(xb) = x_bits {
                    for (p, &x) in part_bits.iter_mut().zip(&xb[lx]) {
                        *p ^= x;
                    }
                }
            }
            for (v, (&px, &yw)) in v_bits.iter_mut().zip(part_bits.iter().zip(y)) {
                *v ^= px & yw;
            }
            for plane in 0..128 {
                let base = plane * words;
                let vr = &mut v_rand[base..base + words];
                let pr = &part_rand[base..base + words];
                for (v, (&px, &yw)) in vr.iter_mut().zip(pr.iter().zip(y)) {
                    *v ^= px & yw;
                }
            }
        }
        wipe_u64s(&mut part_bits);
        wipe_u64s(&mut part_rand);
        let out = self.reshare_planes(&v_bits, &v_rand, words);
        wipe_u64s(&mut v_bits);
        wipe_u64s(&mut v_rand);
        out
    }

    fn defer_planes(&mut self, bits: &[Vec<u64>], rand: &[Vec<u64>], words: usize) {
        for l in 0..self.topo.held.len() {
            self.pending_plane_bits[l].extend_from_slice(&bits[l]);
            for plane in 0..128 {
                self.pending_plane_rand[l][plane]
                    .extend_from_slice(&rand[l][plane * words..(plane + 1) * words]);
            }
        }
    }

    fn load_cached_key_planes(&mut self, use_prf: bool) -> Result<(), CnfPartyError> {
        let held = self.topo.held.len();
        let words = self.key_len / 8;
        let src_shares = if use_prf {
            &self.prf_shares
        } else {
            &self.key_shares
        };
        let bits: Vec<Vec<u64>> = (0..held)
            .map(|l| {
                src_shares[l][..self.key_len]
                    .as_chunks::<8>()
                    .0
                    .iter()
                    .map(|c| u64::from_le_bytes(*c))
                    .collect()
            })
            .collect();
        let mut r_planes = vec![vec![0u64; 128 * words]; held];
        for (rp, &rl) in r_planes.iter_mut().zip(&self.r) {
            for k in 0..128 {
                if ((rl >> k) & 1) == 1 {
                    rp[k * words..(k + 1) * words].fill(u64::MAX);
                }
            }
        }
        let res = self.mul_planes(None, &r_planes, &bits, words);
        for rp in &mut r_planes {
            wipe_u64s(rp);
        }
        let (_, rand) = res?;
        self.defer_planes(&bits, &rand, words);
        let cached = CachedKeyPlanes { words, bits, rand };
        if use_prf {
            self.cached_sk_prf = Some(cached);
        } else {
            self.cached_sk_seed = Some(cached);
        }
        Ok(())
    }

    fn ensure_key_seed_planes(&mut self) -> Result<(), CnfPartyError> {
        if self.cached_sk_seed.is_none() {
            self.load_cached_key_planes(false)?;
        }
        Ok(())
    }

    fn ensure_key_prf_planes(&mut self) -> Result<(), CnfPartyError> {
        if self.cached_sk_prf.is_none() {
            self.load_cached_key_planes(true)?;
        }
        Ok(())
    }

    fn init_batch_states(
        &self,
        midstate: &[u64; 25],
        frames: &[[u8; RATE_BYTES]],
    ) -> BatchPlaneStates {
        let held = self.topo.held.len();
        let count = frames.len();
        let mut state = BatchPlaneStates::zero(held, count);
        let one = self.topo.local[0];
        for (sp, frame) in frames.iter().enumerate() {
            let mut pub_st = *midstate;
            for (lane, chunk) in frame.as_chunks::<8>().0.iter().enumerate() {
                pub_st[lane] ^= u64::from_le_bytes(*chunk);
            }
            if let Some(l) = one {
                state.bits[l][sp] = pub_st;
            }
            for l in 0..held {
                let rl = self.r[l];
                for k in 0..128 {
                    if ((rl >> k) & 1) == 1 {
                        state.rand[l][k * count + sp] = pub_st;
                    }
                }
            }
        }
        state
    }

    fn xor_public_block_into_sponge(
        &self,
        state: &mut BatchPlaneStates,
        sp: usize,
        block: &[u8; RATE_BYTES],
    ) {
        let held = self.topo.held.len();
        let one = self.topo.local[0];
        let count = state.count;
        for (lane, chunk) in block.as_chunks::<8>().0.iter().enumerate() {
            let word = u64::from_le_bytes(*chunk);
            if word == 0 {
                continue;
            }
            if let Some(l) = one {
                state.bits[l][sp][lane] ^= word;
            }
            for l in 0..held {
                let rl = self.r[l];
                for k in 0..128 {
                    if ((rl >> k) & 1) == 1 {
                        state.rand[l][k * count + sp][lane] ^= word;
                    }
                }
            }
        }
    }

    fn keccak_f_batch(&mut self, state: &mut BatchPlaneStates) -> Result<(), CnfPartyError> {
        if self.pending_plane_bits[0].len() >= MAX_PENDING_PLANE_WORDS {
            self.barrier_inner()?;
        }
        let count = state.count;
        let words = 25 * count;
        let held = self.topo.held.len();
        let one = self.topo.local[0];

        let mut lin_bits = vec![vec![[0u64; 25]; count]; held];
        let mut lin_rand = vec![vec![[0u64; 25]; 128 * count]; held];
        let mut x_bits = vec![vec![0u64; words]; held];
        let mut y_bits = vec![vec![0u64; words]; held];
        let mut x_rand = vec![vec![0u64; 128 * words]; held];

        let wipe_scratch = |lb: &mut [Vec<[u64; 25]>],
                            lr: &mut [Vec<[u64; 25]>],
                            xb: &mut [Vec<u64>],
                            yb: &mut [Vec<u64>],
                            xr: &mut [Vec<u64>]| {
            for slot in lb {
                wipe_u64s(slot.as_flattened_mut());
            }
            for slot in lr {
                wipe_u64s(slot.as_flattened_mut());
            }
            for slot in xb {
                wipe_u64s(slot);
            }
            for slot in yb {
                wipe_u64s(slot);
            }
            for slot in xr {
                wipe_u64s(slot);
            }
        };

        for &rc in &KECCAK_ROUND_CONSTANTS {
            for l in 0..held {
                for sp in 0..count {
                    let b = linear_bits(&state.bits[l][sp]);
                    lin_bits[l][sp] = b;
                    let xb = &mut x_bits[l][25 * sp..25 * (sp + 1)];
                    let yb = &mut y_bits[l][25 * sp..25 * (sp + 1)];
                    for lane in 0..25 {
                        let row = 5 * (lane / 5);
                        let u_lane = row + (lane + 1) % 5;
                        let v_lane = row + (lane + 2) % 5;
                        xb[lane] = if one == Some(l) {
                            !b[u_lane]
                        } else {
                            b[u_lane]
                        };
                        yb[lane] = b[v_lane];
                    }
                }
                let rl = self.r[l];
                for k in 0..128 {
                    let r_mask = if ((rl >> k) & 1) == 1 { u64::MAX } else { 0 };
                    for sp in 0..count {
                        let idx = k * count + sp;
                        let br = linear_bits(&state.rand[l][idx]);
                        lin_rand[l][idx] = br;
                        let xr = &mut x_rand[l][25 * idx..25 * (idx + 1)];
                        for (lane, dst_x) in xr.iter_mut().enumerate() {
                            let row = 5 * (lane / 5);
                            let u_lane = row + (lane + 1) % 5;
                            *dst_x = br[u_lane] ^ r_mask;
                        }
                    }
                }
            }

            let (mut z_bits, mut z_rand) =
                match self.mul_planes(Some(&x_bits), &x_rand, &y_bits, words) {
                    Ok(z) => z,
                    Err(e) => {
                        wipe_scratch(
                            &mut lin_bits,
                            &mut lin_rand,
                            &mut x_bits,
                            &mut y_bits,
                            &mut x_rand,
                        );
                        return Err(e);
                    }
                };
            self.defer_planes(&z_bits, &z_rand, words);

            for l in 0..held {
                for (dst, (&lb, &zb)) in state.bits[l]
                    .as_flattened_mut()
                    .iter_mut()
                    .zip(lin_bits[l].as_flattened().iter().zip(&z_bits[l]))
                {
                    *dst = lb ^ zb;
                }
                for (dst, (&lr, &zr)) in state.rand[l]
                    .as_flattened_mut()
                    .iter_mut()
                    .zip(lin_rand[l].as_flattened().iter().zip(&z_rand[l]))
                {
                    *dst = lr ^ zr;
                }
                if one == Some(l) {
                    for sp in 0..count {
                        state.bits[l][sp][0] ^= rc;
                    }
                }
                let rl = self.r[l];
                for k in 0..128 {
                    if ((rl >> k) & 1) == 1 {
                        for sp in 0..count {
                            state.rand[l][k * count + sp][0] ^= rc;
                        }
                    }
                }
                wipe_u64s(&mut z_bits[l]);
                wipe_u64s(&mut z_rand[l]);
            }
        }
        wipe_scratch(
            &mut lin_bits,
            &mut lin_rand,
            &mut x_bits,
            &mut y_bits,
            &mut x_rand,
        );
        Ok(())
    }

    /// Run a 2-round `QSAG.R_COMMIT/v1` hedged coin-tossing ceremony over the encrypted wire
    /// channels (with commitment-vector echo verification) to derive an unbiased
    /// [`CommittedHedgedRandomizer`] prior to `SLH-DSA` signing.
    pub fn hedged_slh_randomizer(
        &mut self,
        n_bytes: usize,
    ) -> Result<CommittedHedgedRandomizer, CnfPartyError> {
        if n_bytes != self.key_len || !matches!(n_bytes, 16 | 24 | 32) {
            return Err(CnfPartyError::InvalidParameters);
        }
        self.guarded(|party| {
            let ctr = party.hedged_ctr;
            party.hedged_ctr = ctr.checked_add(1).ok_or(CnfPartyError::CounterOverflow)?;
            let hedged_sid = h32(
                b"cnf-party/hedged-sid",
                &[&party.session, &ctr.to_be_bytes()],
            );
            let me = party.topo.me;
            let n = party.topo.n;

            let r_raw = party.rng.bytes32();
            let r_share = r_raw[..n_bytes].to_vec();
            let open_salt = party.rng.bytes32();
            let (my_com, my_open) =
                HedgedRandomizerOpen::commit_and_open(&hedged_sid, me as u64, r_share, open_salt);

            for peer in party.topo.peers() {
                party
                    .transport
                    .send_frame(peer, ROUND_CNF_HEDGED_COMMIT, &my_com.commit)?;
            }
            let mut commits = Vec::with_capacity(n);
            for p in 0..n {
                if p == me {
                    commits.push(my_com);
                } else {
                    let raw = party.recv(p, ROUND_CNF_HEDGED_COMMIT, 32)?;
                    let mut com = [0u8; 32];
                    com.copy_from_slice(&raw);
                    commits.push(HedgedRandomizerCommit {
                        party_id: p as u64,
                        commit: com,
                    });
                }
            }

            let mut echo_xof = Cshake256Xof::new_shake256();
            absorb_framed(&mut echo_xof, b"cnf-party/hedged-echo");
            absorb_framed(&mut echo_xof, &hedged_sid);
            for c in &commits {
                absorb_framed(&mut echo_xof, &c.commit);
            }
            let mut commits_digest = [0u8; 32];
            echo_xof.squeeze(&mut commits_digest);
            party.coin_binding = h32(
                b"cnf-party/coin-binding",
                &[&party.coin_binding, &commits_digest],
            );

            let mut open_payload = Vec::with_capacity(64 + n_bytes);
            open_payload.extend_from_slice(&commits_digest);
            open_payload.extend_from_slice(&my_open.open_salt);
            open_payload.extend_from_slice(&my_open.r_share);
            for peer in party.topo.peers() {
                let sent = party
                    .transport
                    .send_frame(peer, ROUND_CNF_HEDGED_OPEN, &open_payload);
                if let Err(e) = sent {
                    wipe_bytes(&mut open_payload);
                    return Err(e.into());
                }
            }
            wipe_bytes(&mut open_payload);

            let mut opens = Vec::with_capacity(n);
            for (p, com_entry) in commits.iter().enumerate() {
                if p == me {
                    opens.push(my_open.clone());
                } else {
                    let mut raw = party.recv(p, ROUND_CNF_HEDGED_OPEN, 64 + n_bytes)?;
                    let mut peer_echo = [0u8; 32];
                    peer_echo.copy_from_slice(&raw[..32]);
                    if !ct_eq_bytes32(&peer_echo, &commits_digest) {
                        wipe_bytes(&mut raw);
                        return Err(CnfPartyError::ConsistencyMismatch { peer: p });
                    }
                    let mut salt = [0u8; 32];
                    salt.copy_from_slice(&raw[32..64]);
                    let share = raw[64..].to_vec();
                    wipe_bytes(&mut raw);
                    let exp = compute_hedged_r_commit_v1(&hedged_sid, p as u64, &share, &salt);
                    if !ct_eq_bytes32(&exp, &com_entry.commit) {
                        return Err(CnfPartyError::OpeningRejected { party: p });
                    }
                    opens.push(HedgedRandomizerOpen {
                        party_id: p as u64,
                        r_share: share,
                        open_salt: salt,
                    });
                }
            }
            let roster: Vec<u64> = (0..n as u64).collect();
            CommittedHedgedRandomizer::from_coin_toss(
                &hedged_sid,
                &roster,
                n_bytes,
                &commits,
                &opens,
            )
            .map_err(|_| CnfPartyError::InvalidParameters)
        })
    }

    /// Sealed [`SlhMpcOracles`] view over this isolated custodian party.
    pub fn slh_oracles(&mut self) -> IsolatedCnfSlhOracles<'_, Self> {
        IsolatedCnfSlhOracles(self)
    }

    /// Distributed `SLH-DSA` public-key derivation over isolated custodian parties (`0` coordinator).
    pub fn slh_keygen(&mut self, params: &Fips205Params) -> Result<SlhPublicKey, Fips205Error> {
        if !params.is_valid() || params.n != self.key_len {
            return Err(Fips205Error::InvalidParameterSet);
        }
        let pk_seed = self.pk_seed[..params.n].to_vec();
        let mut oracles = IsolatedCnfSlhOracles(self);
        slh_keygen_mpc(params, &mut oracles, &pk_seed)
    }

    /// Distributed NIST FIPS 205 `SLH-DSA` signing over isolated custodian parties (`0` coordinator).
    pub fn slh_sign(
        &mut self,
        params: &Fips205Params,
        msg: &[u8],
        ctx: &[u8],
        pk: &SlhPublicKey,
        addrnd: Option<&CommittedHedgedRandomizer>,
    ) -> Result<Vec<u8>, Fips205Error> {
        let mut oracles = IsolatedCnfSlhOracles(self);
        slh_sign_mpc(params, &mut oracles, msg, ctx, pk, addrnd)
    }
}

struct BatchPlaneStates {
    count: usize,
    bits: Vec<Vec<[u64; 25]>>,
    rand: Vec<Vec<[u64; 25]>>,
}

impl BatchPlaneStates {
    fn zero(held: usize, count: usize) -> Self {
        Self {
            count,
            bits: vec![vec![[0u64; 25]; count]; held],
            rand: vec![vec![[0u64; 25]; 128 * count]; held],
        }
    }

    fn absorb_secret_words(
        &mut self,
        sp: usize,
        byte_off: usize,
        word_len: usize,
        sec_bits: &[Vec<u64>],
        sec_rand: &[Vec<u64>],
    ) {
        let count = self.count;
        for l in 0..self.bits.len() {
            xor_words_at_byte_offset(&mut self.bits[l][sp], byte_off, &sec_bits[l][..word_len]);
            for k in 0..128 {
                let src = &sec_rand[l][k * word_len..(k + 1) * word_len];
                xor_words_at_byte_offset(&mut self.rand[l][k * count + sp], byte_off, src);
            }
        }
    }

    fn extract_secret_words(&self, sp: usize, word_len: usize) -> (Vec<Vec<u64>>, Vec<Vec<u64>>) {
        let held = self.bits.len();
        let count = self.count;
        let mut bits = Vec::with_capacity(held);
        let mut rand = Vec::with_capacity(held);
        for l in 0..held {
            bits.push(self.bits[l][sp][..word_len].to_vec());
            let mut r_flat = Vec::with_capacity(128 * word_len);
            for k in 0..128 {
                r_flat.extend_from_slice(&self.rand[l][k * count + sp][..word_len]);
            }
            rand.push(r_flat);
        }
        (bits, rand)
    }
}

impl Drop for BatchPlaneStates {
    fn drop(&mut self) {
        for slot in &mut self.bits {
            wipe_u64s(slot.as_flattened_mut());
        }
        for slot in &mut self.rand {
            wipe_u64s(slot.as_flattened_mut());
        }
    }
}

#[inline]
fn xor_words_at_byte_offset(dst: &mut [u64; 25], byte_off: usize, src: &[u64]) {
    let lane = byte_off / 8;
    let shift = 8 * (byte_off % 8);
    if shift == 0 {
        for (w, &val) in src.iter().enumerate() {
            dst[lane + w] ^= val;
        }
    } else {
        let rshift = 64 - shift;
        for (w, &val) in src.iter().enumerate() {
            dst[lane + w] ^= val << shift;
            dst[lane + w + 1] ^= val >> rshift;
        }
    }
}

#[inline]
fn unpack_digest32(state: &[u64; 25]) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (dst, &w) in out.as_chunks_mut::<8>().0.iter_mut().zip(&state[..4]) {
        *dst = w.to_le_bytes();
    }
    out
}

fn prss_planes_xor(
    seed_key: &[u8; 32],
    dst_bits: &mut [u64],
    dst_rand: &mut [u64],
    mut corr_bits: Option<&mut [u64]>,
    mut corr_rand: Option<&mut [u64]>,
) {
    let mut k_words = [0u64; 4];
    for (dst, chunk) in k_words.iter_mut().zip(seed_key.as_chunks::<8>().0) {
        *dst = u64::from_le_bytes(*chunk);
    }
    let bit_len = dst_bits.len();
    let total = bit_len + dst_rand.len();
    let mut cursor = 0usize;
    let mut blk_base = 0u64;
    let mut st = KeccakState8x::default();
    while cursor < total {
        st.0 = [[0u64; 8]; 25];
        st.0[0] = [k_words[0]; 8];
        st.0[1] = [k_words[1]; 8];
        st.0[2] = [k_words[2]; 8];
        st.0[3] = [k_words[3]; 8];
        st.0[4] = core::array::from_fn(|lane| blk_base + lane as u64);
        st.0[5] = [0x1f; 8];
        st.0[16] = [1u64 << 63; 8];
        keccak_f1600_x8(&mut st);
        if cursor >= bit_len && cursor + 136 <= total {
            let base = cursor - bit_len;
            if let Some(cr) = &mut corr_rand {
                for lane in 0..8 {
                    for rate_w in 0..17 {
                        let idx = base + 17 * lane + rate_w;
                        let w = st.0[rate_w][lane];
                        dst_rand[idx] ^= w;
                        cr[idx] ^= w;
                    }
                }
            } else {
                for lane in 0..8 {
                    for rate_w in 0..17 {
                        let idx = base + 17 * lane + rate_w;
                        dst_rand[idx] ^= st.0[rate_w][lane];
                    }
                }
            }
            cursor += 136;
        } else {
            'block: for lane in 0..8 {
                for rate_w in 0..17 {
                    if cursor == total {
                        break 'block;
                    }
                    let w = st.0[rate_w][lane];
                    if cursor < bit_len {
                        dst_bits[cursor] ^= w;
                        if let Some(cb) = &mut corr_bits {
                            cb[cursor] ^= w;
                        }
                    } else {
                        let r_idx = cursor - bit_len;
                        dst_rand[r_idx] ^= w;
                        if let Some(cr) = &mut corr_rand {
                            cr[r_idx] ^= w;
                        }
                    }
                    cursor += 1;
                }
            }
        }
        blk_base += 8;
    }
    wipe_u64s(&mut k_words);
    qsag_asm::volatile_fill(&mut st.0, [0; 8]);
}

fn cnf_party_to_baggy_error(err: CnfPartyError) -> BaggyError {
    match err {
        CnfPartyError::UnsupportedConfig | CnfPartyError::InvalidParameters => {
            BaggyError::Engine(Rss256Error::InvalidParameters)
        }
        CnfPartyError::Poisoned | CnfPartyError::Journal => {
            BaggyError::Engine(Rss256Error::Poisoned)
        }
        CnfPartyError::OpeningRejected { party } => {
            BaggyError::Engine(Rss256Error::CoinOpeningRejected { party })
        }
        CnfPartyError::ConsistencyMismatch { peer } => {
            BaggyError::Engine(Rss256Error::TranscriptMismatch { slot: peer })
        }
        CnfPartyError::OpenShareMismatch { slot } => {
            BaggyError::Engine(Rss256Error::OpenShareMismatch { slot })
        }
        CnfPartyError::CounterOverflow => BaggyError::Engine(Rss256Error::WaveCounterOverflow),
        CnfPartyError::MultiplicationCheckFailed
        | CnfPartyError::Transport(_)
        | CnfPartyError::PeerAborted { .. }
        | CnfPartyError::MalformedMessage { .. } => {
            BaggyError::Engine(Rss256Error::MultiplicationCheckFailed)
        }
    }
}

fn cnf_party_to_fips205_error(err: CnfPartyError) -> Fips205Error {
    match err {
        CnfPartyError::UnsupportedConfig | CnfPartyError::InvalidParameters => {
            Fips205Error::InvalidParameterSet
        }
        CnfPartyError::Transport(_)
        | CnfPartyError::Journal
        | CnfPartyError::Poisoned
        | CnfPartyError::PeerAborted { .. }
        | CnfPartyError::MalformedMessage { .. }
        | CnfPartyError::ConsistencyMismatch { .. }
        | CnfPartyError::OpeningRejected { .. }
        | CnfPartyError::MultiplicationCheckFailed
        | CnfPartyError::OpenShareMismatch { .. }
        | CnfPartyError::CounterOverflow => Fips205Error::MpcActiveTamperDetected,
    }
}

fn wipe_sponge_chain_state(bits: &mut [Vec<Vec<u64>>], rand: &mut [Vec<Vec<u64>>]) {
    for sp in bits {
        for slot in sp {
            wipe_u64s(slot);
        }
    }
    for sp in rand {
        for slot in sp {
            wipe_u64s(slot);
        }
    }
}

impl<T: WireTransport, J: PoisonJournal> BaggyEngine for IsolatedCnfParty<T, J> {
    type Sweep = IsolatedCnfSweep;

    fn pk_seed(&self) -> [u8; 32] {
        self.pk_seed
    }

    fn session_id(&self) -> &[u8; 32] {
        &self.session
    }

    fn key_identity(&self) -> Result<Option<[u8; 32]>, BaggyError> {
        if self.is_poisoned() {
            return Err(BaggyError::Engine(Rss256Error::Poisoned));
        }
        Ok(self.scheme_identity)
    }

    fn bind_key_identity(&mut self, identity: &[u8; 32]) -> Result<(), BaggyError> {
        if self.is_poisoned() {
            return Err(BaggyError::Engine(Rss256Error::Poisoned));
        }
        if self.slh_profile_digest.is_some() {
            return Err(BaggyError::KeyBindingMismatch);
        }
        match &self.scheme_identity {
            None => {
                self.scheme_identity = Some(*identity);
                for xof in &mut self.transcripts {
                    absorb_framed(xof, b"scheme-id");
                    absorb_framed(xof, identity);
                }
                Ok(())
            }
            Some(bound) if ct_eq_bytes32(bound, identity) => Ok(()),
            Some(_) => Err(BaggyError::KeyBindingMismatch),
        }
    }

    fn randomiser(&mut self, mu: &[u8; 32]) -> Result<[u8; 32], BaggyError> {
        if self.is_poisoned() {
            return Err(BaggyError::Engine(Rss256Error::Poisoned));
        }
        if self.key_len != 32 {
            return Err(BaggyError::InvalidParameters);
        }
        self.guarded(|party| {
            party.ensure_key_prf_planes()?;
            let (frame0, off0) = baggy_mu_frame(TAG_BAGGY_OPT_RAND, mu);
            let mut st0 = party.init_batch_states(&BAGGY_SUITE_MIDSTATE, &[frame0]);
            if let Some(prf) = &party.cached_sk_prf {
                st0.absorb_secret_words(0, off0, prf.words, &prf.bits, &prf.rand);
            }
            party.keccak_f_batch(&mut st0)?;
            let (mut opt_bits, mut opt_rand) = st0.extract_secret_words(0, 4);

            let (frame1, off1) = baggy_mu_frame(TAG_BAGGY_R, mu);
            let mut st1 = party.init_batch_states(&BAGGY_SUITE_MIDSTATE, &[frame1]);
            st1.absorb_secret_words(0, off1, 4, &opt_bits, &opt_rand);
            for b in &mut opt_bits {
                wipe_u64s(b);
            }
            for r in &mut opt_rand {
                wipe_u64s(r);
            }
            let r_res = party.keccak_f_batch(&mut st1);
            r_res?;
            party.barrier_inner()?;

            let held = party.topo.held.len();
            let mut shares = Vec::with_capacity(held);
            for l in 0..held {
                shares.push(unpack_digest32(&st1.bits[l][0]).to_vec());
            }
            let opened_res = party.open_shares(ROUND_CNF_OPEN, &shares);
            for s in &mut shares {
                wipe_bytes(s);
            }
            let opened = opened_res?;
            let mut out = [0u8; 32];
            out.copy_from_slice(&opened[..32]);
            Ok(out)
        })
        .map_err(cnf_party_to_baggy_error)
    }

    fn sweep(
        &mut self,
        pk_seed: &[u8; 32],
        lanes: Vec<LaneSpec>,
    ) -> Result<IsolatedCnfSweep, BaggyError> {
        if self.is_poisoned() {
            return Err(BaggyError::Engine(Rss256Error::Poisoned));
        }
        if self.key_len != 32 || !ct_eq_bytes32(pk_seed, &self.pk_seed) {
            return Err(BaggyError::InvalidParameters);
        }
        if lanes.is_empty() || lanes.windows(2).any(|w| w[0].steps < w[1].steps) {
            return Err(BaggyError::Engine(Rss256Error::InvalidParameters));
        }
        let max_steps = WOTS_STEPS as u8;
        let mut steps_per_lane = Vec::with_capacity(lanes.len());
        let mut lane_offsets = Vec::with_capacity(lanes.len());
        let mut total_nodes = 0usize;
        for lane in &lanes {
            let s = lane.steps.min(max_steps);
            steps_per_lane.push(s);
            lane_offsets.push(total_nodes);
            total_nodes += usize::from(s) + 1;
        }

        self.guarded(|party| {
            party.ensure_key_seed_planes()?;
            let held = party.topo.held.len();
            let mut slot_digests = vec![vec![[0u8; 32]; total_nodes]; held];

            for (chunk_idx, chunk) in lanes.chunks(BATCH_SPONGES).enumerate() {
                let base_lane = chunk_idx * BATCH_SPONGES;
                let c_len = chunk.len();
                let prf_frames: Vec<[u8; RATE_BYTES]> = chunk
                    .iter()
                    .map(|l| baggy_secret32_frame(TAG_PRF, pk_seed, &l.prf))
                    .collect();
                let mut st = party.init_batch_states(&BAGGY_SUITE_MIDSTATE, &prf_frames);
                if let Some(seed) = &party.cached_sk_seed {
                    for sp in 0..c_len {
                        st.absorb_secret_words(
                            sp,
                            BAGGY_PRF_SECRET_OFFSET,
                            seed.words,
                            &seed.bits,
                            &seed.rand,
                        );
                    }
                }
                party.keccak_f_batch(&mut st)?;

                let deepest = chunk[0].steps.min(max_steps);
                let mut cur_bits = Vec::with_capacity(c_len);
                let mut cur_rand = Vec::with_capacity(c_len);
                for sp in 0..c_len {
                    let node_off = lane_offsets[base_lane + sp];
                    for (l, slot) in slot_digests.iter_mut().enumerate() {
                        slot[node_off] = unpack_digest32(&st.bits[l][sp]);
                    }
                    if deepest > 0 {
                        let (b, r) = st.extract_secret_words(sp, 4);
                        cur_bits.push(b);
                        cur_rand.push(r);
                    }
                }

                for step in 0..deepest {
                    let running = chunk
                        .iter()
                        .take_while(|l| l.steps.min(max_steps) > step)
                        .count();
                    if running == 0 {
                        break;
                    }
                    let f_frames: Vec<[u8; RATE_BYTES]> = chunk[..running]
                        .iter()
                        .map(|l| {
                            let adrs = if l.step_indexed {
                                HashAdrs {
                                    hash_step: u32::from(step),
                                    ..l.f
                                }
                            } else {
                                l.f
                            };
                            baggy_secret32_frame(TAG_TH_F, pk_seed, &adrs)
                        })
                        .collect();
                    let mut f_st = party.init_batch_states(&BAGGY_SUITE_MIDSTATE, &f_frames);
                    for sp in 0..running {
                        f_st.absorb_secret_words(
                            sp,
                            BAGGY_F_SECRET_OFFSET,
                            4,
                            &cur_bits[sp],
                            &cur_rand[sp],
                        );
                    }
                    if let Err(e) = party.keccak_f_batch(&mut f_st) {
                        wipe_sponge_chain_state(&mut cur_bits, &mut cur_rand);
                        return Err(e);
                    }
                    for sp in 0..running {
                        let node_off = lane_offsets[base_lane + sp] + usize::from(step) + 1;
                        for (l, slot) in slot_digests.iter_mut().enumerate() {
                            slot[node_off] = unpack_digest32(&f_st.bits[l][sp]);
                        }
                        if step + 1 < deepest {
                            let (b, r) = f_st.extract_secret_words(sp, 4);
                            for slot in &mut cur_bits[sp] {
                                wipe_u64s(slot);
                            }
                            for slot in &mut cur_rand[sp] {
                                wipe_u64s(slot);
                            }
                            cur_bits[sp] = b;
                            cur_rand[sp] = r;
                        }
                    }
                }
                wipe_sponge_chain_state(&mut cur_bits, &mut cur_rand);
            }

            Ok(IsolatedCnfSweep {
                party: party.topo.me,
                session: party.session,
                steps_per_lane,
                lane_offsets,
                slot_digests,
            })
        })
        .map_err(cnf_party_to_baggy_error)
    }

    fn barrier(&mut self) -> Result<(), BaggyError> {
        self.barrier().map_err(cnf_party_to_baggy_error)
    }

    fn open_round(
        &mut self,
        sweep: &IsolatedCnfSweep,
        picks: &[(usize, u8)],
    ) -> Result<Vec<[u8; 32]>, BaggyError> {
        if self.is_poisoned() {
            return Err(BaggyError::Engine(Rss256Error::Poisoned));
        }
        if self.has_unverified_gates() {
            return Err(BaggyError::Engine(Rss256Error::OpenBeforeCheck));
        }
        if sweep.party != self.topo.me
            || !ct_eq_bytes32(&sweep.session, &self.session)
            || sweep.slot_digests.len() != self.topo.held.len()
        {
            return Err(BaggyError::Engine(Rss256Error::InvalidParameters));
        }
        for &(lane, pos) in picks {
            if lane >= sweep.steps_per_lane.len() || pos > sweep.steps_per_lane[lane] {
                return Err(BaggyError::Engine(Rss256Error::InvalidParameters));
            }
        }
        if picks.is_empty() {
            return Ok(Vec::new());
        }

        self.guarded(|party| {
            let held = party.topo.held.len();
            let mut shares = vec![Vec::with_capacity(32 * picks.len()); held];
            for &(lane, pos) in picks {
                let idx = sweep.lane_offsets[lane] + usize::from(pos);
                for (l, dst) in shares.iter_mut().enumerate() {
                    dst.extend_from_slice(&sweep.slot_digests[l][idx]);
                }
            }
            let opened_res = party.open_shares(ROUND_CNF_OPEN, &shares);
            for s in &mut shares {
                wipe_bytes(s);
            }
            let opened = opened_res?;
            Ok(opened.as_chunks::<32>().0.to_vec())
        })
        .map_err(cnf_party_to_baggy_error)
    }
}

impl<T: WireTransport, J: PoisonJournal> IsolatedSlhBackend for IsolatedCnfParty<T, J> {
    fn bind_slh_profile(
        &mut self,
        params: &Fips205Params,
        pk_seed: &[u8],
    ) -> Result<(), Fips205Error> {
        if self.is_poisoned() {
            return Err(Fips205Error::MpcActiveTamperDetected);
        }
        if !params.is_valid()
            || params.n != self.key_len
            || pk_seed.len() != self.key_len
            || !ct_eq_bytes(pk_seed, &self.pk_seed[..self.key_len])
            || self.scheme_identity.is_some()
        {
            return Err(Fips205Error::InvalidParameterSet);
        }
        let digest = compute_slh_profile_digest(params);
        match &self.slh_profile_digest {
            None => {
                self.slh_profile_digest = Some(digest);
                for xof in &mut self.transcripts {
                    absorb_framed(xof, b"slh-profile");
                    for word in &digest {
                        absorb_framed(xof, &word.to_le_bytes());
                    }
                }
                Ok(())
            }
            Some(bound) if *bound == digest => Ok(()),
            Some(_) => Err(Fips205Error::InvalidParameterSet),
        }
    }

    fn eval_prf_msg_verified(
        &mut self,
        n: usize,
        opt_rand: &[u8],
        m_prime: &[u8],
    ) -> Result<SlhBlock, Fips205Error> {
        if self.is_poisoned() {
            return Err(Fips205Error::MpcActiveTamperDetected);
        }
        if n != self.key_len || opt_rand.len() != n || self.slh_profile_digest.is_none() {
            return Err(Fips205Error::InvalidParameterSet);
        }
        self.guarded(|party| {
            party.ensure_key_prf_planes()?;
            let total_len = 2 * n + m_prime.len();
            let num_blocks = (total_len / RATE_BYTES) + 1;
            let mut padded = vec![0u8; num_blocks * RATE_BYTES];
            padded[n..2 * n].copy_from_slice(opt_rand);
            padded[2 * n..total_len].copy_from_slice(m_prime);
            padded[total_len] ^= 0x1f;
            padded[num_blocks * RATE_BYTES - 1] ^= 0x80;

            let held = party.topo.held.len();
            let mut state = BatchPlaneStates::zero(held, 1);
            for blk_idx in 0..num_blocks {
                let block: &[u8; RATE_BYTES] = padded
                    [blk_idx * RATE_BYTES..(blk_idx + 1) * RATE_BYTES]
                    .try_into()
                    .map_err(|_| CnfPartyError::InvalidParameters)?;
                party.xor_public_block_into_sponge(&mut state, 0, block);
                if blk_idx == 0
                    && let Some(prf) = &party.cached_sk_prf
                {
                    state.absorb_secret_words(0, 0, prf.words, &prf.bits, &prf.rand);
                }
                party.keccak_f_batch(&mut state)?;
            }
            party.barrier_inner()?;

            let words = n / 8;
            let mut shares = Vec::with_capacity(held);
            for l in 0..held {
                let mut raw = Vec::with_capacity(n);
                words_to_bytes(&state.bits[l][0][..words], &mut raw);
                shares.push(raw);
            }
            let opened_res = party.open_shares(ROUND_CNF_OPEN, &shares);
            for s in &mut shares {
                wipe_bytes(s);
            }
            let opened = opened_res?;
            SlhBlock::from_slice_checked(n, &opened[..n])
                .map_err(|_| CnfPartyError::InvalidParameters)
        })
        .map_err(cnf_party_to_fips205_error)
    }

    fn eval_chains_verified(
        &mut self,
        n: usize,
        pk_seed: &[u8],
        chains: &[(Fips205Adrs, Vec<Fips205Adrs>)],
    ) -> Result<Vec<SlhBlock>, Fips205Error> {
        if self.is_poisoned() {
            return Err(Fips205Error::MpcActiveTamperDetected);
        }
        if n != self.key_len
            || pk_seed.len() != n
            || !ct_eq_bytes(pk_seed, &self.pk_seed[..n])
            || self.slh_profile_digest.is_none()
        {
            return Err(Fips205Error::InvalidParameterSet);
        }
        if chains.is_empty() {
            return Ok(Vec::new());
        }

        self.guarded(|party| {
            party.ensure_key_seed_planes()?;
            let held = party.topo.held.len();
            let key_words = n / 8;
            let sec_off = n + 32;
            let mut final_shares = vec![Vec::with_capacity(chains.len() * n); held];

            for chunk in chains.chunks(BATCH_SPONGES) {
                let c_len = chunk.len();
                let prf_frames: Vec<[u8; RATE_BYTES]> = chunk
                    .iter()
                    .map(|(prf_adrs, _)| {
                        let mut frame = [0u8; RATE_BYTES];
                        frame[0..n].copy_from_slice(pk_seed);
                        frame[n..n + 32].copy_from_slice(&prf_adrs.to_bytes());
                        frame[2 * n + 32] = 0x1f;
                        frame[RATE_BYTES - 1] ^= 0x80;
                        frame
                    })
                    .collect();
                let mut st = party.init_batch_states(&[0u64; 25], &prf_frames);
                if let Some(seed) = &party.cached_sk_seed {
                    for sp in 0..c_len {
                        st.absorb_secret_words(sp, sec_off, key_words, &seed.bits, &seed.rand);
                    }
                }
                party.keccak_f_batch(&mut st)?;

                let max_steps = chunk.iter().map(|(_, s)| s.len()).max().unwrap_or(0);
                let mut cur_bits = Vec::with_capacity(c_len);
                let mut cur_rand = Vec::with_capacity(c_len);
                for sp in 0..c_len {
                    let (b, r) = st.extract_secret_words(sp, key_words);
                    cur_bits.push(b);
                    cur_rand.push(r);
                }

                for step in 0..max_steps {
                    let active: Vec<usize> =
                        (0..c_len).filter(|&sp| chunk[sp].1.len() > step).collect();
                    if active.is_empty() {
                        break;
                    }
                    let step_frames: Vec<[u8; RATE_BYTES]> = active
                        .iter()
                        .map(|&sp| {
                            let mut frame = [0u8; RATE_BYTES];
                            frame[0..n].copy_from_slice(pk_seed);
                            frame[n..n + 32].copy_from_slice(&chunk[sp].1[step].to_bytes());
                            frame[2 * n + 32] = 0x1f;
                            frame[RATE_BYTES - 1] ^= 0x80;
                            frame
                        })
                        .collect();
                    let mut step_st = party.init_batch_states(&[0u64; 25], &step_frames);
                    for (batch_pos, &sp) in active.iter().enumerate() {
                        step_st.absorb_secret_words(
                            batch_pos,
                            sec_off,
                            key_words,
                            &cur_bits[sp],
                            &cur_rand[sp],
                        );
                    }
                    if let Err(e) = party.keccak_f_batch(&mut step_st) {
                        wipe_sponge_chain_state(&mut cur_bits, &mut cur_rand);
                        return Err(e);
                    }
                    for (batch_pos, &sp) in active.iter().enumerate() {
                        let (b, r) = step_st.extract_secret_words(batch_pos, key_words);
                        for slot in &mut cur_bits[sp] {
                            wipe_u64s(slot);
                        }
                        for slot in &mut cur_rand[sp] {
                            wipe_u64s(slot);
                        }
                        cur_bits[sp] = b;
                        cur_rand[sp] = r;
                    }
                }

                for sp_bits in &cur_bits {
                    for (l, dst) in final_shares.iter_mut().enumerate() {
                        words_to_bytes(&sp_bits[l][..key_words], dst);
                    }
                }
                wipe_sponge_chain_state(&mut cur_bits, &mut cur_rand);
            }

            let bar_res = party.barrier_inner();
            if let Err(e) = bar_res {
                for s in &mut final_shares {
                    wipe_bytes(s);
                }
                return Err(e);
            }
            let opened_res = party.open_shares(ROUND_CNF_OPEN, &final_shares);
            for s in &mut final_shares {
                wipe_bytes(s);
            }
            let opened = opened_res?;
            opened
                .chunks_exact(n)
                .map(|raw| {
                    SlhBlock::from_slice_checked(n, raw)
                        .map_err(|_| CnfPartyError::InvalidParameters)
                })
                .collect()
        })
        .map_err(cnf_party_to_fips205_error)
    }
}

/// Run one closure per party, each on its own thread with exclusive ownership of its party
/// value, and return what the closures return (their public outputs), in party order. The
/// caller of this helper never touches a share, a seed or the MAC key: it only moves each
/// party value into its thread. Party values are dropped after every thread has finished, so
/// a party that returns early does not close links its peers still use.
#[cfg(any(test, feature = "std"))]
pub fn run_isolated_cnf_ceremony<P: Send, R: Send>(
    parties: Vec<P>,
    job: impl Fn(usize, &mut P) -> R + Sync,
) -> Vec<R> {
    let job = &job;
    let finished: Vec<Option<(R, P)>> = std::thread::scope(|scope| {
        let handles: Vec<_> = parties
            .into_iter()
            .enumerate()
            .map(|(index, mut party)| {
                scope.spawn(move || {
                    let out = job(index, &mut party);
                    (out, party)
                })
            })
            .collect();
        handles.into_iter().map(|h| h.join().ok()).collect()
    });
    finished
        .into_iter()
        .flatten()
        .map(|(out, _party)| out)
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::party_node::MemoryPoisonJournal;
    use crate::wire_channel::{InMemoryEndpoint, InMemoryWireMesh, MeshStats};
    use qsag_core::cnf_rss::run_dealerless_cnf_rss_dkg;
    use qsag_core::fips205::{Fips205AdrsType, SlhBlock, fips205_chain, fips205_prf};
    use qsag_core::preprocessing::PartyPrivateRng;
    use qsag_core::sponge::keccak::shake256_xof;
    use std::sync::Arc;
    use std::time::{Duration, Instant};

    type Party = IsolatedCnfParty<InMemoryEndpoint, MemoryPoisonJournal>;

    /// Custody shares from the core dealerless DKG, loaded one custodian at a time.
    fn custody_keys(t: usize, n: usize, key_len: usize, tape: u8) -> Vec<CnfPartyKeys> {
        let cfg = CnfRssConfig::new(t, n).unwrap();
        let mut rngs: Vec<PartyPrivateRng> = (0..n)
            .map(|p| PartyPrivateRng::from_seed([tape ^ (p as u8); 32], b"cnf-party-test"))
            .collect();
        let (shares, _) = run_dealerless_cnf_rss_dkg([tape; 32], &cfg, key_len, &mut rngs).unwrap();
        shares
            .iter()
            .map(|s| CnfPartyKeys::from_custody(s).unwrap())
            .collect()
    }

    /// Test-only pooling of every party's key material: the clear `sk_seed`.
    fn pooled_secret(keys: &[CnfPartyKeys]) -> Vec<u8> {
        let total = keys[0].cfg.total_slots();
        let mut secret = [0u8; 32];
        for slot in 0..total {
            let (holder, pos) = keys
                .iter()
                .find_map(|k| k.slots.iter().position(|&s| s == slot).map(|pos| (k, pos)))
                .unwrap();
            for (s, b) in secret.iter_mut().zip(&holder.key_shares[pos]) {
                *s ^= b;
            }
        }
        secret[..keys[0].key_len].to_vec()
    }

    fn parties(
        keys: &[CnfPartyKeys],
        session: [u8; 32],
        faults: &[(usize, Fault)],
    ) -> (Vec<Party>, Arc<MeshStats>) {
        let (endpoints, stats) = InMemoryWireMesh::connect(keys.len(), session);
        let parties = endpoints
            .into_iter()
            .zip(keys)
            .enumerate()
            .map(|(p, (mut endpoint, key))| {
                endpoint.set_timeout(Duration::from_secs(20));
                let mut party = IsolatedCnfParty::new(
                    key,
                    endpoint,
                    session,
                    &[0x30 + p as u8; 32],
                    MemoryPoisonJournal::new(),
                )
                .unwrap();
                party.fault = faults.iter().find(|(who, _)| *who == p).map(|(_, f)| *f);
                party
            })
            .collect();
        (parties, stats)
    }

    const PREFIX: &[u8] = b"isolated cnf prefix";
    const SUFFIX: &[u8] = b"suffix";

    fn keyed_hash_run(
        keys: &[CnfPartyKeys],
        session: [u8; 32],
        faults: &[(usize, Fault)],
    ) -> (Vec<Result<Vec<u8>, CnfPartyError>>, Vec<bool>) {
        let (parties, _) = parties(keys, session, faults);
        let out = run_isolated_cnf_ceremony(parties, |_, party: &mut Party| {
            let result = party
                .keyed_shake256(PREFIX, SUFFIX, 32)
                .and_then(|digest| party.open(&digest));
            (result, party.is_poisoned())
        });
        out.into_iter().unzip()
    }

    fn keyed_hash_reference(keys: &[CnfPartyKeys]) -> Vec<u8> {
        let input = [PREFIX, &pooled_secret(keys), SUFFIX].concat();
        shake256_xof(32, &input)
    }

    #[test]
    fn keyed_shake256_matches_the_clear_reference_for_2_of_3_and_3_of_5() {
        for (t, n, key_len) in [(2, 3, 16), (3, 5, 32)] {
            let keys = custody_keys(t, n, key_len, 0x51);
            let want = keyed_hash_reference(&keys);
            let (results, poisoned) = keyed_hash_run(&keys, [0xA0 + n as u8; 32], &[]);
            assert_eq!(results.len(), n);
            for result in results {
                assert_eq!(result.unwrap(), want);
            }
            assert!(poisoned.iter().all(|p| !p));
        }
    }

    fn wots_reference(
        keys: &[CnfPartyKeys],
        prf: &Fips205Adrs,
        chain: &Fips205Adrs,
        steps: u32,
    ) -> Vec<u8> {
        let n = keys[0].key_len;
        let pk_seed = &keys[0].pk_seed[..n];
        let start: SlhBlock = fips205_prf(n, pk_seed, &pooled_secret(keys), prf);
        fips205_chain(start, 0, steps, pk_seed, *chain)
            .as_slice()
            .to_vec()
    }

    #[test]
    fn threshold_wots_chain_element_matches_fips205_reference() {
        let mut prf = Fips205Adrs::ZERO;
        prf.layer = 1;
        prf.set_tree_address(0x1234_5678_9abc);
        prf.adrs_type = Fips205AdrsType::WotsPrf;
        prf.key_pair = 7;
        prf.f5 = 11;
        let mut chain = prf;
        chain.adrs_type = Fips205AdrsType::WotsHash;
        for (t, n, key_len, steps) in [(2, 3, 16, 3u32), (3, 5, 24, 2), (3, 5, 16, 0)] {
            let keys = custody_keys(t, n, key_len, 0x62);
            let want = wots_reference(&keys, &prf, &chain, steps);
            let (parties, _) = parties(&keys, [0xB0 + steps as u8; 32], &[]);
            let out = run_isolated_cnf_ceremony(parties, |_, party: &mut Party| {
                let element = party.wots_chain_element(&prf, &chain, steps);
                // Input randomization plus 24 chi rounds per permutation.
                assert_eq!(party.multiplications(), 1 + 24 * (1 + u64::from(steps)) + 2);
                assert!(!party.has_unverified_gates());
                element
            });
            assert_eq!(out.len(), n);
            for element in out {
                assert_eq!(element.unwrap(), want);
            }
        }
    }

    #[test]
    fn wire_dkg_gives_each_slot_to_its_holders_only_and_keys_evaluate() {
        for (t, n) in [(2usize, 3usize), (3, 5)] {
            let cfg = CnfRssConfig::new(t, n).unwrap();
            let session = [0xC0 + n as u8; 32];
            // Pre-authenticated pairwise link keys, here from a fixed table.
            let link = |a: usize, b: usize| [(1 + a.min(b) * 16 + a.max(b)) as u8; 32];
            let (endpoints, stats) = InMemoryWireMesh::connect(n, session);
            let endpoints: Vec<_> = endpoints.into_iter().map(Some).collect();
            let keys: Vec<CnfPartyKeys> = run_isolated_cnf_ceremony(endpoints, |p, endpoint| {
                // The DKG consumes its transport.
                let endpoint = endpoint.take().unwrap();
                let links = (0..n).map(|q| link(p, q)).collect();
                let mut rng = SeedRng::new(&[0x70 + p as u8; 32], b"dkg");
                run_isolated_cnf_dkg(&cfg, 16, endpoint, session, links, &mut rng)
            })
            .into_iter()
            .map(Result::unwrap)
            .collect();
            // Every frame of the DKG is a DKG frame, and each party talks to each peer.
            assert!(stats.frames().iter().all(|f| matches!(
                f.round_tag,
                ROUND_CNF_DKG_COMMIT | ROUND_CNF_DKG_OPEN | ROUND_CNF_DKG_CONFIRM
            )));
            for slot in 0..cfg.total_slots() {
                let excluded = cfg.excluded_subset(slot).unwrap();
                let replicas: Vec<_> = keys
                    .iter()
                    .filter_map(|k| {
                        let pos = k.slots.iter().position(|&s| s == slot)?;
                        Some((k.party, k.key_shares[pos], k.prss_seeds[pos]))
                    })
                    .collect();
                // Held by exactly the parties outside the excluded subset, identically.
                assert_eq!(replicas.len(), n - (t - 1));
                assert!(replicas.iter().all(|(p, _, _)| !excluded.contains(p)));
                assert!(
                    replicas
                        .iter()
                        .all(|r| (r.1, r.2) == (replicas[0].1, replicas[0].2))
                );
                assert_ne!(replicas[0].2, [0u8; 32]);
            }
            assert!(keys.iter().all(|k| k.pk_seed == keys[0].pk_seed));
            let want = keyed_hash_reference(&keys);
            let (results, _) = keyed_hash_run(&keys, [0xD0 + n as u8; 32], &[]);
            for result in results {
                assert_eq!(result.unwrap(), want);
            }
        }
    }

    #[test]
    fn wire_dkg_rejects_another_session_and_a_wrong_link_key() {
        let cfg = CnfRssConfig::new(2, 3).unwrap();
        for wrong_link in [false, true] {
            let session = [0xC8 + u8::from(wrong_link); 32];
            let (endpoints, _) = InMemoryWireMesh::connect(3, session);
            let endpoints: Vec<_> = endpoints.into_iter().map(Some).collect();
            let out = run_isolated_cnf_ceremony(endpoints, |p, endpoint| {
                let mut endpoint = endpoint.take().unwrap();
                endpoint.set_timeout(Duration::from_secs(5));
                let mut links: Vec<[u8; 32]> = (0..3)
                    .map(|q| [(1 + p.min(q) * 16 + p.max(q)) as u8; 32])
                    .collect();
                if wrong_link && p == 0 {
                    links[1] = [0xEE; 32];
                }
                // Without the wrong link key, party 0 runs under another session instead:
                // its commitments and openings then never verify at its peers.
                let sid = if !wrong_link && p == 0 {
                    [0x01; 32]
                } else {
                    session
                };
                let mut rng = SeedRng::new(&[0x70 + p as u8; 32], b"dkg");
                run_isolated_cnf_dkg(&cfg, 16, endpoint, sid, links, &mut rng).map(|_| ())
            });
            assert!(out.iter().all(Result::is_err), "{out:?}");
        }
    }

    #[test]
    fn a_party_holds_exactly_its_slots_and_every_coalition_misses_one() {
        for (t, n) in [(2usize, 3usize), (3, 5), (4, 7)] {
            let cfg = CnfRssConfig::new(t, n).unwrap();
            let f = t - 1;
            let keys = custody_keys(t, n, 16, 0x33);
            let (parties, _) = parties(&keys, [0x90 + n as u8; 32], &[]);
            for (p, party) in parties.iter().enumerate() {
                assert_eq!(party.held_slots(), cfg.party_slot_indices(p).unwrap());
                assert_eq!(party.key_shares.len(), party.held_slots().len());
                assert_eq!(party.prss_seeds.len(), party.held_slots().len());
                assert_eq!(party.r.len(), party.held_slots().len());
            }
            // Each slot is missed by exactly its excluded subset: every f-coalition (and no
            // smaller set of slots) is blind in one slot, so it never sees a full sharing.
            for slot in 0..cfg.total_slots() {
                let coalition = cfg.excluded_subset(slot).unwrap();
                assert_eq!(coalition.len(), f);
                assert!(
                    coalition
                        .iter()
                        .all(|&p| !parties[p].held_slots().contains(&slot))
                );
                let seen: Vec<usize> = coalition
                    .iter()
                    .flat_map(|&p| parties[p].held_slots().to_vec())
                    .collect();
                assert_eq!(
                    (0..cfg.total_slots()).filter(|s| !seen.contains(s)).count(),
                    1
                );
            }
        }
        // Topologies without an honest majority are refused.
        for (t, n) in [(2usize, 2usize), (3, 4), (4, 6)] {
            let cfg = CnfRssConfig::new(t, n).unwrap();
            assert_eq!(
                Topology::new(&cfg, 0).unwrap_err(),
                CnfPartyError::UnsupportedConfig
            );
        }
    }

    type ReceivedLog = Vec<(usize, u32, Vec<u8>)>;

    /// Run the keyed hash and return the frame log and every party's received plaintexts.
    fn recorded_run(
        keys: &[CnfPartyKeys],
        session: [u8; 32],
    ) -> (Arc<MeshStats>, Vec<ReceivedLog>, Vec<Vec<u8>>) {
        let (parties, stats) = parties(keys, session, &[]);
        let out = run_isolated_cnf_ceremony(parties, |_, party: &mut Party| {
            let digest = party.keyed_shake256(PREFIX, SUFFIX, 32).unwrap();
            let opened = party.open(&digest).unwrap();
            (core::mem::take(&mut party.received), opened)
        });
        let (received, opened) = out.into_iter().unzip();
        (stats, received, opened)
    }

    #[test]
    fn corrections_reach_only_holders_and_are_masked_by_the_missed_slot() {
        let (t, n) = (3usize, 5usize);
        let cfg = CnfRssConfig::new(t, n).unwrap();
        let session = [0x77; 32];
        let keys = custody_keys(t, n, 16, 0x44);
        let (stats, base, opened_base) = recorded_run(&keys, session);

        // Routing: party j's corrections go to the other holders of its designated slot
        // (the first slot not containing j) and to nobody else.
        let frames = stats.frames();
        for j in 0..n {
            let slot = (0..cfg.total_slots())
                .find(|&s| !cfg.excluded_subset(s).unwrap().contains(&j))
                .unwrap();
            let excluded = cfg.excluded_subset(slot).unwrap();
            let sent: Vec<_> = frames
                .iter()
                .filter(|f| f.from == j && f.round_tag == ROUND_CNF_MUL)
                .collect();
            assert!(!sent.is_empty());
            assert!(sent.iter().all(|f| !excluded.contains(&f.to)));
            for holder in (0..n).filter(|p| *p != j && !excluded.contains(p)) {
                // One correction per multiplication batch: the input randomization, 24
                // chi rounds and the two field products of the barrier.
                assert_eq!(sent.iter().filter(|f| f.to == holder).count(), 27);
            }
        }

        // The coalition {3, 4} misses the last slot and receives corrections from every
        // honest party. Control: an identical rerun gives it identical frames.
        let coalition = [3usize, 4];
        let missed = cfg.total_slots() - 1;
        assert_eq!(cfg.excluded_subset(missed).unwrap(), coalition);
        let (_, same, _) = recorded_run(&keys, session);
        for &c in &coalition {
            assert_eq!(base[c], same[c]);
        }

        // Replace only the PRSS seed of the missed slot at its (honest) holders. Nothing the
        // coalition holds changes, yet every correction it receives from an honest party
        // changes: each one is masked by a stream keyed with a seed the coalition lacks.
        let mut reseeded = custody_keys(t, n, 16, 0x44);
        for k in &mut reseeded {
            if let Some(pos) = k.slots.iter().position(|&s| s == missed) {
                k.prss_seeds[pos] = [0x5A; 32];
            }
        }
        let (_, other, opened_other) = recorded_run(&reseeded, session);
        assert_eq!(opened_base, opened_other);
        for &c in &coalition {
            assert_eq!(base[c].len(), other[c].len());
            let mut honest_corrections = 0;
            for (a, b) in base[c].iter().zip(&other[c]) {
                assert_eq!((a.0, a.1, a.2.len()), (b.0, b.1, b.2.len()));
                if a.1 == ROUND_CNF_MUL && !coalition.contains(&a.0) {
                    honest_corrections += 1;
                    assert_ne!(a.2, b.2);
                }
            }
            assert_eq!(honest_corrections, 3 * 27);
        }

        // Changing the secret in the missed slot leaves the shape of the coalition's view
        // (senders, rounds, lengths) unchanged, and changes the opened output.
        let mut resecret = custody_keys(t, n, 16, 0x44);
        for k in &mut resecret {
            if let Some(pos) = k.slots.iter().position(|&s| s == missed) {
                k.key_shares[pos][0] ^= 0x80;
            }
        }
        let (_, third, opened_third) = recorded_run(&resecret, session);
        assert_ne!(opened_base, opened_third);
        assert_eq!(opened_third[0], keyed_hash_reference(&resecret));
        for &c in &coalition {
            let shape = |log: &[(usize, u32, Vec<u8>)]| -> Vec<(usize, u32, usize)> {
                log.iter().map(|m| (m.0, m.1, m.2.len())).collect()
            };
            assert_eq!(shape(&base[c]), shape(&third[c]));
        }
    }

    /// Every tamper test first shows that the same run succeeds untampered, then that with
    /// the fault no party obtains an output, every party is poisoned, and some honest party
    /// reports `expect`.
    fn assert_fault_aborts(
        t: usize,
        n: usize,
        cheater: usize,
        fault: Fault,
        expect: impl Fn(&CnfPartyError) -> bool,
    ) {
        let keys = custody_keys(t, n, 16, 0x29);
        let want = keyed_hash_reference(&keys);
        let (clean, _) = keyed_hash_run(&keys, [0xE1; 32], &[]);
        assert!(clean.iter().all(|r| r.as_ref() == Ok(&want)));

        let (results, poisoned) = keyed_hash_run(&keys, [0xE2; 32], &[(cheater, fault)]);
        assert!(results.iter().all(Result::is_err), "{fault:?}: {results:?}");
        assert!(poisoned.iter().all(|p| *p), "{fault:?}: {poisoned:?}");
        assert!(
            results
                .iter()
                .enumerate()
                .any(|(p, r)| p != cheater && r.as_ref().is_err_and(&expect)),
            "{fault:?}: {results:?}"
        );
    }

    #[test]
    fn additive_error_on_a_bit_correction_fails_the_multiplication_check() {
        for (t, n, cheater) in [(2, 3, 1), (3, 5, 0), (3, 5, 4)] {
            assert_fault_aborts(
                t,
                n,
                cheater,
                Fault::AdditiveBitCorrection { ctr: 9 },
                |e| *e == CnfPartyError::MultiplicationCheckFailed,
            );
        }
    }

    #[test]
    fn wrong_randomized_share_fails_the_multiplication_check() {
        // Counter 0 is the input randomization, 13 a chi round, 25 the first product of the
        // barrier itself.
        for ctr in [0, 13, 25] {
            assert_fault_aborts(3, 5, 2, Fault::AdditiveRandCorrection { ctr }, |e| {
                *e == CnfPartyError::MultiplicationCheckFailed
            });
        }
        assert_fault_aborts(2, 3, 0, Fault::AdditiveRandCorrection { ctr: 4 }, |e| {
            *e == CnfPartyError::MultiplicationCheckFailed
        });
    }

    #[test]
    fn inconsistent_corrections_are_caught_by_the_slot_view_comparison() {
        // Party 4's designated slot {0, 1} is held by 2, 3 and 4; holder 2 gets another
        // correction than holder 3. In the first case during the circuit, in the second
        // during the barrier's own products (caught by the second comparison).
        for ctr in [6, 26] {
            assert_fault_aborts(
                3,
                5,
                4,
                Fault::InconsistentCorrection { ctr, peer: 2 },
                |e| matches!(e, CnfPartyError::ConsistencyMismatch { .. }),
            );
        }
        assert_fault_aborts(
            2,
            3,
            2,
            Fault::InconsistentCorrection { ctr: 3, peer: 1 },
            |e| matches!(e, CnfPartyError::ConsistencyMismatch { .. }),
        );
    }

    #[test]
    fn wrong_consistency_digest_aborts() {
        assert_fault_aborts(3, 5, 1, Fault::WrongConsistencyHash { peer: 3 }, |e| {
            *e == CnfPartyError::ConsistencyMismatch { peer: 1 }
        });
    }

    #[test]
    fn wrong_opening_share_is_caught_by_the_other_holders_copy() {
        // The receiver gets the missing slot from another holder too and compares.
        let keys = custody_keys(3, 5, 16, 0x29);
        let want = keyed_hash_reference(&keys);
        let (clean, _) = keyed_hash_run(&keys, [0xE3; 32], &[]);
        assert!(clean.iter().all(|r| r.as_ref() == Ok(&want)));
        let (results, poisoned) = keyed_hash_run(
            &keys,
            [0xE4; 32],
            &[(2, Fault::WrongOpeningShare { peer: 0 })],
        );
        // The targeted party aborts without an output and is poisoned. Abort is not fair:
        // parties that were sent correct shares may already hold the (correct) output.
        assert!(matches!(
            results[0],
            Err(CnfPartyError::OpenShareMismatch { .. })
        ));
        assert!(poisoned[0]);
        for result in results.iter().flatten() {
            assert_eq!(result, &want);
        }
    }

    #[test]
    fn frames_of_another_session_are_rejected_and_poison_is_permanent() {
        let keys = custody_keys(2, 3, 16, 0x29);
        let want = keyed_hash_reference(&keys);
        let (clean, _) = keyed_hash_run(&keys, [0xE5; 32], &[]);
        assert!(clean.iter().all(|r| r.as_ref() == Ok(&want)));

        // Party 0 seals its frames for session A while its peers run session B: what it
        // sends is exactly a stream of frames replayed from another session.
        let session_b = [0xE6; 32];
        let (endpoints, _) = InMemoryWireMesh::connect(3, session_b);
        let parties: Vec<Party> = endpoints
            .into_iter()
            .zip(&keys)
            .enumerate()
            .map(|(p, (mut endpoint, key))| {
                endpoint.set_timeout(Duration::from_secs(5));
                let sid = if p == 0 { [0xE7; 32] } else { session_b };
                IsolatedCnfParty::new(
                    key,
                    endpoint,
                    sid,
                    &[p as u8; 32],
                    MemoryPoisonJournal::new(),
                )
                .unwrap()
            })
            .collect();
        let out = run_isolated_cnf_ceremony(parties, |_, party: &mut Party| {
            let first = party
                .keyed_shake256(PREFIX, SUFFIX, 32)
                .and_then(|digest| party.open(&digest));
            // A poisoned party refuses everything afterwards.
            let later = party.load_key_seed().map(|_| ());
            let barrier = party.barrier();
            (first, later, barrier, party.is_poisoned())
        });
        for (first, later, barrier, poisoned) in out {
            assert!(first.is_err());
            assert_eq!(later, Err(CnfPartyError::Poisoned));
            assert_eq!(barrier, Err(CnfPartyError::Poisoned));
            assert!(poisoned);
        }

        // A journal that recorded the session refuses to run it again.
        let (mut endpoints, _) = InMemoryWireMesh::connect(3, session_b);
        let mut journal = MemoryPoisonJournal::new();
        journal.reserve_session(&session_b).unwrap();
        assert!(matches!(
            IsolatedCnfParty::new(&keys[0], endpoints.remove(0), session_b, &[0; 32], journal),
            Err(CnfPartyError::Journal)
        ));
        let (mut endpoints, _) = InMemoryWireMesh::connect(3, session_b);
        let mut journal = MemoryPoisonJournal::new();
        journal.mark_poisoned(&session_b).unwrap();
        assert!(matches!(
            IsolatedCnfParty::new(&keys[0], endpoints.remove(0), session_b, &[0; 32], journal),
            Err(CnfPartyError::Poisoned)
        ));
    }

    #[test]
    fn shared_values_are_bound_to_their_party_and_frames_are_bounded() {
        let keys = custody_keys(2, 3, 16, 0x29);
        let (parties, _) = parties(&keys, [0xE8; 32], &[]);
        let out = run_isolated_cnf_ceremony(parties, |_, party: &mut Party| {
            let key = party.load_key_seed().unwrap();
            // 136 bytes or more do not fit one block; an empty output is meaningless.
            let too_long = party.guarded(|p| {
                Ok(p.shake_inner(
                    &[FramePart::Public(&[0u8; 120]), FramePart::Secret(&key)],
                    16,
                )
                .err())
            });
            let foreign = SharedBytes {
                len: 16,
                party: (party.party() + 1) % 3,
                session: party.session,
                bits: key.bits.clone(),
                rand: key.rand.clone(),
            };
            let refused = party.open(&foreign);
            (too_long, refused)
        });
        for (too_long, refused) in out {
            assert_eq!(too_long, Ok(Some(CnfPartyError::InvalidParameters)));
            assert_eq!(refused, Err(CnfPartyError::InvalidParameters));
        }
    }

    #[test]
    #[ignore = "isolated CNF Keccak-f[1600] latency and traffic"]
    fn bench_isolated_cnf_keccak_permutation() {
        let mut prf = Fips205Adrs::ZERO;
        prf.adrs_type = Fips205AdrsType::WotsPrf;
        let mut chain = prf;
        chain.adrs_type = Fips205AdrsType::WotsHash;
        for (t, n) in [(2usize, 3usize), (3, 5)] {
            let keys = custody_keys(t, n, 16, 0x19);
            let steps = 7u32;
            let (parties, stats) = parties(&keys, [0xF0 + n as u8; 32], &[]);
            let start = Instant::now();
            let out = run_isolated_cnf_ceremony(parties, |_, party: &mut Party| {
                party.wots_chain_element(&prf, &chain, steps).unwrap()
            });
            let elapsed = start.elapsed();
            assert_eq!(out[0], wots_reference(&keys, &prf, &chain, steps));
            let perms = f64::from(steps + 1);
            let frames = stats.frames();
            let mul = frames
                .iter()
                .filter(|f| f.round_tag == ROUND_CNF_MUL)
                .count();
            eprintln!(
                "isolated CNF {t}-of-{n}: {} permutations in {:.1} ms = {:.2} ms/permutation \
                 (wall, all parties, barrier and opening included); {} frames ({} reshare), \
                 {:.1} KiB total, {:.1} KiB/permutation",
                steps + 1,
                elapsed.as_secs_f64() * 1e3,
                elapsed.as_secs_f64() * 1e3 / perms,
                frames.len(),
                mul,
                stats.total_bytes() as f64 / 1024.0,
                stats.total_bytes() as f64 / 1024.0 / perms,
            );
        }
    }

    /// Test-only pooling of `(sk_seed, sk_prf)` across all custodians for single-prover KAT comparison.
    fn pooled_keypair(keys: &[CnfPartyKeys]) -> ([u8; 32], [u8; 32]) {
        let total = keys[0].cfg.total_slots();
        let mut sk_seed = [0u8; 32];
        let mut sk_prf = [0u8; 32];
        for slot in 0..total {
            let (holder, pos) = keys
                .iter()
                .find_map(|k| k.slots.iter().position(|&s| s == slot).map(|pos| (k, pos)))
                .unwrap();
            for b in 0..32 {
                sk_seed[b] ^= holder.key_shares[pos][b];
                sk_prf[b] ^= holder.prf_shares[pos][b];
            }
        }
        (sk_seed, sk_prf)
    }

    fn parties_with_timeout(
        keys: &[CnfPartyKeys],
        session: [u8; 32],
        faults: &[(usize, Fault)],
        timeout: Duration,
    ) -> (Vec<Party>, Arc<MeshStats>) {
        let (endpoints, stats) = InMemoryWireMesh::connect(keys.len(), session);
        let parties = endpoints
            .into_iter()
            .zip(keys)
            .enumerate()
            .map(|(p, (mut endpoint, key))| {
                endpoint.set_timeout(timeout);
                let mut party = IsolatedCnfParty::new(
                    key,
                    endpoint,
                    session,
                    &[0x40 + p as u8; 32],
                    MemoryPoisonJournal::new(),
                )
                .unwrap();
                party.fault = faults.iter().find(|(who, _)| *who == p).map(|(_, f)| *f);
                party
            })
            .collect();
        (parties, stats)
    }

    fn compact_slh_params() -> Fips205Params {
        let p = Fips205Params {
            name: "SLH-DSA-SHAKE-128-compact-test",
            n: 16,
            h: 4,
            d: 2,
            hp: 2,
            a: 3,
            k: 4,
            lg_w: 4,
            m: 4,
        };
        assert!(p.is_valid());
        p
    }

    #[test]
    fn wire_dkg_corrupted_opening_aborts_with_opening_rejected() {
        for (t, n) in [(2usize, 3usize), (3, 5)] {
            let cfg = CnfRssConfig::new(t, n).unwrap();
            let session = [0x9A + n as u8; 32];
            let link = |a: usize, b: usize| [(7 + a.min(b) * 16 + a.max(b)) as u8; 32];
            let (endpoints, _) = InMemoryWireMesh::connect(n, session);
            let endpoints: Vec<_> = endpoints.into_iter().map(Some).collect();

            let out = run_isolated_cnf_ceremony(endpoints, |p, endpoint| {
                let mut endpoint = endpoint.take().unwrap();
                endpoint.set_timeout(Duration::from_secs(10));
                let links: Vec<[u8; 32]> = (0..n).map(|q| link(p, q)).collect();
                if p == 0 {
                    // Corrupted party 0 possesses valid link keys, commits honestly in Round 1,
                    // then flips a contribution byte in Round 2 (`ROUND_CNF_DKG_OPEN`).
                    let topo = Topology::new(&cfg, 0).unwrap();
                    let dkg_session = h32(b"cnf-party/dkg-session", &[&session]);
                    let mut chan =
                        MacSealedWireChannel::new_encrypted(endpoint, dkg_session, links).unwrap();
                    let held = topo.held.len();
                    let salt = [0x11u8; 32];
                    let contrib = [0x22u8; 32];
                    let item_id = |i: usize| {
                        if i == held {
                            u64::MAX
                        } else {
                            topo.held[i] as u64
                        }
                    };
                    let my_coms: Vec<[u8; 32]> = (0..=held)
                        .map(|i| dkg_commitment(&session, item_id(i), 0, &salt, &contrib))
                        .collect();
                    for peer in topo.peers() {
                        let mut items = topo.common(peer);
                        items.push(held);
                        let mut payload = Vec::new();
                        for i in items {
                            payload.extend_from_slice(&my_coms[i]);
                        }
                        chan.send_frame(peer, ROUND_CNF_DKG_COMMIT, &payload)
                            .unwrap();
                    }
                    for peer in topo.peers() {
                        let mut items = topo.common(peer);
                        items.push(held);
                        let _ = recv_checked(&mut chan, peer, ROUND_CNF_DKG_COMMIT, 32 * items.len());
                    }
                    let mut bad_contrib = contrib;
                    bad_contrib[0] ^= 0x01;
                    for peer in topo.peers() {
                        let mut items = topo.common(peer);
                        items.push(held);
                        let mut payload = Vec::new();
                        for _ in items {
                            payload.extend_from_slice(&salt);
                            payload.extend_from_slice(&bad_contrib);
                        }
                        let _ = chan.send_frame(peer, ROUND_CNF_DKG_OPEN, &payload);
                    }
                    Err(CnfPartyError::OpeningRejected { party: 0 })
                } else {
                    let mut rng = SeedRng::new(&[0x80 + p as u8; 32], b"dkg-bad-open");
                    run_isolated_cnf_dkg(&cfg, 32, endpoint, session, links, &mut rng).map(|_| ())
                }
            });

            for (p, res) in out.iter().enumerate().skip(1) {
                assert_eq!(
                    *res,
                    Err(CnfPartyError::OpeningRejected { party: 0 }),
                    "honest party {p} must reject corrupted DKG opening from party 0"
                );
            }
        }
    }

    #[test]
    fn isolated_baggy_2of3_and_3of5_match_reference_byte_for_byte_and_waistband() {
        use qsag_core::baggy::{
            BaggyParams, MemoryFirstSigned, WaistbandCache, baggy_keygen_mpc,
            baggy_reference_keygen, baggy_reference_sign, baggy_sign_mpc, baggy_verify,
        };
        use qsag_core::tsw_baggy::PqSecretKey;

        let params = BaggyParams::TEST_SMALL;
        let msg = b"isolated zero-coordinator Baggy PORS+FP threshold ceremony";

        for (t, n, use_wire_dkg) in [(2usize, 3usize, false), (3, 5, true)] {
            let mut keys = if use_wire_dkg {
                let cfg = CnfRssConfig::new(t, n).unwrap();
                let dkg_sid = [0x31 + n as u8; 32];
                let link = |a: usize, b: usize| [(9 + a.min(b) * 17 + a.max(b)) as u8; 32];
                let (endpoints, _) = InMemoryWireMesh::connect(n, dkg_sid);
                let endpoints: Vec<_> = endpoints.into_iter().map(Some).collect();
                run_isolated_cnf_ceremony(endpoints, |p, ep| {
                    let ep = ep.take().unwrap();
                    let links = (0..n).map(|q| link(p, q)).collect();
                    let mut rng = SeedRng::new(&[0x60 + p as u8; 32], b"baggy-wire-dkg");
                    run_isolated_cnf_dkg(&cfg, 32, ep, dkg_sid, links, &mut rng).unwrap()
                })
            } else {
                custody_keys(t, n, 32, 0x47)
            };

            let (sk_seed, sk_prf) = pooled_keypair(&keys);
            let ref_sk = PqSecretKey {
                sk_seed,
                sk_prf,
                pk_seed: keys[0].pk_seed,
            };
            let ref_pk = baggy_reference_keygen(&params, &ref_sk).unwrap();
            let ref_sig = baggy_reference_sign(&params, &ref_sk, &ref_pk, msg).unwrap();

            // 1. Keygen + uncached `baggy_sign_mpc` in isolated custodian threads.
            let (p_kg, _) =
                parties_with_timeout(&keys, [0x41 + n as u8; 32], &[], Duration::from_secs(60));
            let kg_and_sig = run_isolated_cnf_ceremony(p_kg, |_, party: &mut Party| {
                // Verify `open_round` refuses unverified gates before barrier without poisoning.
                let lane = LaneSpec::pors(0, 0, 0);
                let pk_seed = BaggyEngine::pk_seed(party);
                let dummy_sweep = party.sweep(&pk_seed, vec![lane]).unwrap();
                assert_eq!(
                    party.open_round(&dummy_sweep, &[(0, 1)]),
                    Err(BaggyError::Engine(Rss256Error::OpenBeforeCheck))
                );
                assert!(!party.is_poisoned());
                BaggyEngine::barrier(party).unwrap();

                let mut cache = WaistbandCache::disabled();
                let mut ledger = MemoryFirstSigned::new();
                let (pk, binding) = baggy_keygen_mpc(party, &params, &mut cache).unwrap();
                let sig = baggy_sign_mpc(
                    party, &params, &pk, &binding, &mut cache, &mut ledger, msg,
                )
                .unwrap();
                (pk, binding, sig)
            });

            let (pk0, binding0, sig0) = &kg_and_sig[0];
            assert_eq!(pk0, &ref_pk);
            assert_eq!(sig0.to_wire_bytes(), ref_sig.to_wire_bytes());
            assert!(baggy_verify(&params, pk0, msg, sig0));
            for (pk, binding, sig) in &kg_and_sig {
                assert_eq!(pk, pk0);
                assert_eq!(binding, binding0);
                assert_eq!(sig.to_wire_bytes(), sig0.to_wire_bytes());
            }

            // Persist bound scheme identity into each custodian's key state and run a
            // separate `WaistbandCache::precompute` + cached `baggy_sign_mpc` session.
            for k in &mut keys {
                k.bind_scheme_identity(&binding0.identity()).unwrap();
            }
            let (p_wb, _) =
                parties_with_timeout(&keys, [0x51 + n as u8; 32], &[], Duration::from_secs(60));
            let cached_sigs = run_isolated_cnf_ceremony(p_wb, |_, party: &mut Party| {
                let mut cache = WaistbandCache::new(1, 32);
                let mut ledger = MemoryFirstSigned::new();
                cache
                    .precompute(party, &params, pk0, binding0, &mut ledger)
                    .unwrap();
                let sig =
                    baggy_sign_mpc(party, &params, pk0, binding0, &mut cache, &mut ledger, msg)
                        .unwrap();
                assert!(cache.hits() > 0);
                sig
            });
            for sig in &cached_sigs {
                assert_eq!(sig.to_wire_bytes(), ref_sig.to_wire_bytes());
                assert!(baggy_verify(&params, pk0, msg, sig));
            }
        }
    }

    #[test]
    fn isolated_slh_dsa_2of3_and_3of5_deterministic_and_hedged_verify() {
        use qsag_core::fips205::{slh_keygen_internal, slh_sign, slh_verify};

        let params = compact_slh_params();
        // 400-byte message forces 4 full SHAKE256 sponge blocks inside `eval_prf_msg_verified`.
        let msg = vec![0x5Au8; 400];
        let ctx = b"qsag-subcarbon-q1-isolated-slh";

        for (t, n) in [(2usize, 3usize), (3, 5)] {
            let mut keys = custody_keys(t, n, 16, 0x68 + n as u8);
            let (sk_seed, sk_prf) = pooled_keypair(&keys);
            let (ref_sk, ref_pk) =
                slh_keygen_internal(&params, &sk_seed[..16], &sk_prf[..16], &keys[0].pk_seed[..16])
                    .unwrap();
            let ref_det_sig = slh_sign(&params, &msg, ctx, &ref_sk, None).unwrap();

            // Keygen + deterministic signing + hedged coin-toss signing.
            let (p_run, _) =
                parties_with_timeout(&keys, [0x71 + n as u8; 32], &[], Duration::from_secs(60));
            let outcomes = run_isolated_cnf_ceremony(p_run, |_, party: &mut Party| {
                let pk = party.slh_keygen(&params).unwrap();
                let det_sig = party.slh_sign(&params, &msg, ctx, &pk, None).unwrap();
                let hedged = party.hedged_slh_randomizer(params.n).unwrap();
                let hedged_sig = party
                    .slh_sign(&params, &msg, ctx, &pk, Some(&hedged))
                    .unwrap();
                (pk, det_sig, hedged.as_slice().to_vec(), hedged_sig)
            });

            let (pk0, det0, rnd0, hsig0) = &outcomes[0];
            assert_eq!(pk0, &ref_pk);
            assert_eq!(det0, &ref_det_sig);
            assert!(slh_verify(&params, &msg, det0, ctx, pk0));

            let ref_hedged_sig = slh_sign(&params, &msg, ctx, &ref_sk, Some(rnd0)).unwrap();
            assert_eq!(hsig0, &ref_hedged_sig);
            assert_ne!(hsig0, det0);
            assert!(slh_verify(&params, &msg, hsig0, ctx, pk0));

            for (pk, det, rnd, hsig) in &outcomes {
                assert_eq!(pk, pk0);
                assert_eq!(det, det0);
                assert_eq!(rnd, rnd0);
                assert_eq!(hsig, hsig0);
            }

            // Parameter-lock refusal: once bound to `params`, signing under a different profile fails cleanly.
            for k in &mut keys {
                k.bind_slh_params(&params, pk0.pk_seed_slice()).unwrap();
            }
            assert!(
                keys[0]
                    .bind_slh_params(&Fips205Params::SLH_DSA_SHAKE_128F, pk0.pk_seed_slice())
                    .is_err()
            );
        }
    }

    #[test]
    fn isolated_full_signature_view_isolation_and_active_cheater_abort() {
        use qsag_core::baggy::{
            BaggyParams, MemoryFirstSigned, WaistbandCache, baggy_keygen_mpc, baggy_sign_mpc,
        };
        use qsag_core::fips205::{slh_keygen_internal, slh_verify};

        // Part A: Full-signature 3-of-5 coalition `{3, 4}` view isolation on `SLH-DSA`.
        let (t, n) = (3usize, 5usize);
        let cfg = CnfRssConfig::new(t, n).unwrap();
        let params = compact_slh_params();
        let msg = b"full-signature view isolation check";
        let ctx = b"view";
        let session = [0x88; 32];

        let mut base_keys = custody_keys(t, n, 16, 0x73);
        let (sk_seed, sk_prf) = pooled_keypair(&base_keys);
        let (_, pk) =
            slh_keygen_internal(&params, &sk_seed[..16], &sk_prf[..16], &base_keys[0].pk_seed[..16])
                .unwrap();
        for k in &mut base_keys {
            k.bind_slh_params(&params, pk.pk_seed_slice()).unwrap();
        }

        let run_slh_recorded = |ks: &[CnfPartyKeys], pk_ref: &SlhPublicKey| {
            let (ps, _) = parties_with_timeout(ks, session, &[], Duration::from_secs(60));
            let out = run_isolated_cnf_ceremony(ps, |_, party: &mut Party| {
                let sig = party.slh_sign(&params, msg, ctx, pk_ref, None).unwrap();
                (core::mem::take(&mut party.received), sig)
            });
            let (logs, sigs): (Vec<ReceivedLog>, Vec<Vec<u8>>) = out.into_iter().unzip();
            (logs, sigs)
        };

        let (base_logs, base_sigs) = run_slh_recorded(&base_keys, &pk);
        assert!(slh_verify(&params, msg, &base_sigs[0], ctx, &pk));

        let coalition = [3usize, 4];
        let missed = cfg.total_slots() - 1;
        assert_eq!(cfg.excluded_subset(missed).unwrap(), coalition);

        // Reseeding ONLY missed slot 9 changes every `ROUND_CNF_MUL` frame received by `{3, 4}`
        // from honest parties `{0, 1, 2}` while producing the exact same signature.
        let mut reseeded = custody_keys(t, n, 16, 0x73);
        for k in &mut reseeded {
            k.bind_slh_params(&params, pk.pk_seed_slice()).unwrap();
            if let Some(pos) = k.slots.iter().position(|&s| s == missed) {
                k.prss_seeds[pos] = [0xA5; 32];
            }
        }
        let (reseed_logs, reseed_sigs) = run_slh_recorded(&reseeded, &pk);
        assert_eq!(base_sigs, reseed_sigs);
        for &c in &coalition {
            assert_eq!(base_logs[c].len(), reseed_logs[c].len());
            let mut honest_mul_frames = 0usize;
            for (a, b) in base_logs[c].iter().zip(&reseed_logs[c]) {
                assert_eq!((a.0, a.1, a.2.len()), (b.0, b.1, b.2.len()));
                if a.1 == ROUND_CNF_MUL && !coalition.contains(&a.0) {
                    honest_mul_frames += 1;
                    assert_ne!(a.2, b.2);
                }
            }
            assert!(honest_mul_frames > 100);
        }

        // Changing `(sk_seed, sk_prf)` in the missed slot leaves `{3, 4}`'s message shape
        // identical and produces a distinct valid signature for the new key.
        let mut resecret = custody_keys(t, n, 16, 0x73);
        for k in &mut resecret {
            if let Some(pos) = k.slots.iter().position(|&s| s == missed) {
                k.key_shares[pos][0] ^= 0x40;
                k.prf_shares[pos][0] ^= 0x20;
            }
        }
        let (alt_seed, alt_prf) = pooled_keypair(&resecret);
        let (_, alt_pk) = slh_keygen_internal(
            &params,
            &alt_seed[..16],
            &alt_prf[..16],
            &resecret[0].pk_seed[..16],
        )
        .unwrap();
        for k in &mut resecret {
            k.bind_slh_params(&params, alt_pk.pk_seed_slice()).unwrap();
        }
        let (alt_logs, alt_sigs) = run_slh_recorded(&resecret, &alt_pk);
        assert_ne!(base_sigs[0], alt_sigs[0]);
        assert!(slh_verify(&params, msg, &alt_sigs[0], ctx, &alt_pk));
        for &c in &coalition {
            let shape = |log: &ReceivedLog| -> Vec<(usize, u32, usize)> {
                log.iter().map(|m| (m.0, m.1, m.2.len())).collect()
            };
            assert_eq!(shape(&base_logs[c]), shape(&alt_logs[c]));
        }

        // Part B: Active-cheater faults during full `SLH-DSA` and `Baggy` signing abort and poison!
        for (idx, (cheater, fault)) in [
            (4usize, Fault::AdditiveBitCorrection { ctr: 3 }),
            (2, Fault::AdditiveRandCorrection { ctr: 5 }),
            (4, Fault::InconsistentCorrection { ctr: 4, peer: 2 }),
        ]
        .into_iter()
        .enumerate()
        {
            let (ps, _) = parties_with_timeout(
                &base_keys,
                [0x91 + idx as u8; 32],
                &[(cheater, fault)],
                Duration::from_secs(60),
            );
            let out = run_isolated_cnf_ceremony(ps, |_, party: &mut Party| {
                let res = party.slh_sign(&params, msg, ctx, &pk, None);
                let follow_up = party.barrier();
                (res, follow_up, party.is_poisoned())
            });
            for (res, follow_up, poisoned) in out {
                assert!(res.is_err(), "{fault:?} must abort SLH-DSA signing");
                assert_eq!(follow_up, Err(CnfPartyError::Poisoned));
                assert!(poisoned);
            }
        }

        // Wrong opening share targeted at custodian 0 in full `SLH-DSA` signing poisons custodian 0.
        let (ps_open, _) = parties_with_timeout(
            &base_keys,
            [0x99; 32],
            &[(2, Fault::WrongOpeningShare { peer: 0 })],
            Duration::from_secs(60),
        );
        let open_out = run_isolated_cnf_ceremony(ps_open, |_, party: &mut Party| {
            let res = party.slh_sign(&params, msg, ctx, &pk, None);
            (res, party.is_poisoned())
        });
        assert!(open_out[0].0.is_err());
        assert!(open_out[0].1);

        // Active fault during full `Baggy` `3-of-5` signing aborts and poisons all custodians.
        let baggy_params = BaggyParams::TEST_SMALL;
        let mut bkeys = custody_keys(3, 5, 32, 0x79);
        let (p_bkg, _) = parties_with_timeout(&bkeys, [0xA8; 32], &[], Duration::from_secs(60));
        let (bpk, bbind) = run_isolated_cnf_ceremony(p_bkg, |_, party: &mut Party| {
            let mut cache = WaistbandCache::disabled();
            baggy_keygen_mpc(party, &baggy_params, &mut cache).unwrap()
        })
        .remove(0);
        for k in &mut bkeys {
            k.bind_scheme_identity(&bbind.identity()).unwrap();
        }
        let (p_bsign, _) = parties_with_timeout(
            &bkeys,
            [0xA9; 32],
            &[(1, Fault::AdditiveBitCorrection { ctr: 6 })],
            Duration::from_secs(60),
        );
        let bout = run_isolated_cnf_ceremony(p_bsign, |_, party: &mut Party| {
            let mut cache = WaistbandCache::disabled();
            let mut ledger = MemoryFirstSigned::new();
            let res = baggy_sign_mpc(
                party,
                &baggy_params,
                &bpk,
                &bbind,
                &mut cache,
                &mut ledger,
                b"tampered baggy",
            );
            (res, party.is_poisoned())
        });
        for (res, poisoned) in bout {
            assert!(res.is_err());
            assert!(poisoned);
        }
    }

    #[test]
    #[ignore = "isolated CNF 2-of-3 and 3-of-5 Baggy + FIPS 205 SLH-DSA-SHAKE-128f latency"]
    fn bench_isolated_cnf_baggy_and_slh_dsa() {
        use qsag_core::baggy::{
            BaggyParams, MemoryFirstSigned, WaistbandCache, baggy_keygen_mpc,
            baggy_reference_keygen, baggy_reference_sign, baggy_sign_mpc, baggy_verify,
        };
        use qsag_core::fips205::{slh_keygen_internal, slh_sign, slh_verify};
        use qsag_core::tsw_baggy::PqSecretKey;

        for (t, n) in [(2usize, 3usize), (3, 5)] {
            // 1. Baggy SHA3_128F (full production 32-height hypertree + 2048-leaf PORS+FP)
            let bparams = BaggyParams::SHA3_128F;
            let mut bkeys = custody_keys(t, n, 32, 0xB1 + n as u8);
            let (sk_seed, sk_prf) = pooled_keypair(&bkeys);
            let ref_sk = PqSecretKey {
                sk_seed,
                sk_prf,
                pk_seed: bkeys[0].pk_seed,
            };
            let ref_bpk = baggy_reference_keygen(&bparams, &ref_sk).unwrap();
            let bmsg = b"isolated CNF Baggy SHA3_128F benchmark";
            let ref_bsig = baggy_reference_sign(&bparams, &ref_sk, &ref_bpk, bmsg).unwrap();

            let (p_kg, _) =
                parties_with_timeout(&bkeys, [0xB3 + n as u8; 32], &[], Duration::from_secs(300));
            let (bpk, bbind) = run_isolated_cnf_ceremony(p_kg, |_, party: &mut Party| {
                let mut cache = WaistbandCache::disabled();
                baggy_keygen_mpc(party, &bparams, &mut cache).unwrap()
            })
            .remove(0);
            assert_eq!(bpk, ref_bpk);
            for k in &mut bkeys {
                k.bind_scheme_identity(&bbind.identity()).unwrap();
            }

            let (p_bsign, bstats) =
                parties_with_timeout(&bkeys, [0xB5 + n as u8; 32], &[], Duration::from_secs(300));
            let t0 = Instant::now();
            let bsigs = run_isolated_cnf_ceremony(p_bsign, |_, party: &mut Party| {
                let mut cache = WaistbandCache::disabled();
                let mut ledger = MemoryFirstSigned::new();
                baggy_sign_mpc(party, &bparams, &bpk, &bbind, &mut cache, &mut ledger, bmsg)
                    .unwrap()
            });
            let b_elapsed = t0.elapsed();
            assert_eq!(bsigs[0].to_wire_bytes(), ref_bsig.to_wire_bytes());
            assert!(baggy_verify(&bparams, &bpk, bmsg, &bsigs[0]));
            eprintln!(
                "isolated CNF {t}-of-{n} Baggy SHA3_128F (uncached): {:.1} ms, {} frames, {:.2} MiB wire",
                b_elapsed.as_secs_f64() * 1e3,
                bstats.frames().len(),
                bstats.total_bytes() as f64 / (1024.0 * 1024.0),
            );

            // 2. Full NIST FIPS 205 SLH-DSA-SHAKE-128f (17,088-byte standard signature, 22 layers)
            let sparams = Fips205Params::SLH_DSA_SHAKE_128F;
            let mut skeys = custody_keys(t, n, 16, 0xC1 + n as u8);
            let (s_seed, s_prf) = pooled_keypair(&skeys);
            let (ref_ssk, ref_spk) = slh_keygen_internal(
                &sparams,
                &s_seed[..16],
                &s_prf[..16],
                &skeys[0].pk_seed[..16],
            )
            .unwrap();
            for k in &mut skeys {
                k.bind_slh_params(&sparams, ref_spk.pk_seed_slice()).unwrap();
            }
            let smsg = b"isolated CNF FIPS 205 SLH-DSA-SHAKE-128f benchmark";
            let sctx = b"bench";
            let ref_ssig = slh_sign(&sparams, smsg, sctx, &ref_ssk, None).unwrap();

            let (p_ssign, sstats) =
                parties_with_timeout(&skeys, [0xC5 + n as u8; 32], &[], Duration::from_secs(300));
            let t1 = Instant::now();
            let ssigs = run_isolated_cnf_ceremony(p_ssign, |_, party: &mut Party| {
                let hedged = party.hedged_slh_randomizer(16).unwrap();
                let det = party.slh_sign(&sparams, smsg, sctx, &ref_spk, None).unwrap();
                (det, hedged)
            });
            let s_elapsed = t1.elapsed();
            assert_eq!(ssigs[0].0.len(), 17_088);
            assert_eq!(ssigs[0].0, ref_ssig);
            assert!(slh_verify(&sparams, smsg, &ssigs[0].0, sctx, &ref_spk));
            eprintln!(
                "isolated CNF {t}-of-{n} SLH-DSA-SHAKE-128f (17,088 B): {:.1} ms, {} frames, {:.2} MiB wire",
                s_elapsed.as_secs_f64() * 1e3,
                sstats.frames().len(),
                sstats.total_bytes() as f64 / (1024.0 * 1024.0),
            );
        }
    }
}
