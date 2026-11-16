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
//! * The barrier's statistical error is about `2^-126` per barrier (two field checks).
//! * This engine evaluates one `Keccak-f[1600]` state at a time. It provides a keyed
//!   single-block `SHAKE256` and one FIPS 205 WOTS chain element; it does not implement
//!   `BaggyEngine` or the full `SlhMpcOracles` signing flow.

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use qsag_asm::{KECCAK_ROTATION_OFFSETS, KECCAK_ROUND_CONSTANTS};
use qsag_core::cnf_rss::{CnfRssConfig, CnfRssKeyShare256};
use qsag_core::fips205::Fips205Adrs;
use qsag_core::sponge::keccak::Cshake256Xof;
use qsag_core::wipe::{
    ct_eq_bytes, ct_eq_bytes32, wipe_bytes, wipe_bytes32, wipe_u64s, wipe_u128s,
};

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
pub const ROUND_CNF_DKG_COMMIT: u32 = 0x0410_0000;
pub const ROUND_CNF_DKG_OPEN: u32 = 0x0411_0000;
pub const ROUND_CNF_DKG_CONFIRM: u32 = 0x0412_0000;

const STATE_BITS: usize = 1600;
const RATE_BYTES: usize = 136;
/// Multiplication outputs that may wait for a barrier before one is run automatically.
const MAX_PENDING_OUTPUTS: usize = 16 * 24 * STATE_BITS;

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

/// One custodian's CNF key material: its replica of every slot it holds and its pairwise
/// link keys. Wiped on drop, not `Clone`, opaque `Debug`.
pub struct CnfPartyKeys {
    cfg: CnfRssConfig,
    party: usize,
    key_len: usize,
    pk_seed: [u8; 32],
    /// Global indices of the held slots, ascending.
    slots: Vec<usize>,
    key_shares: Vec<[u8; 32]>,
    prss_seeds: Vec<[u8; 32]>,
    /// `link_keys[peer]`; the own entry is zero and unused.
    link_keys: Vec<[u8; 32]>,
}

impl Drop for CnfPartyKeys {
    fn drop(&mut self) {
        for k in self
            .key_shares
            .iter_mut()
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
    /// Load exactly the slots `share` holds. The link keys are derived from the custody
    /// share's pairwise PRF keys, which the custody DKG established between each pair.
    pub fn from_custody(share: &CnfRssKeyShare256) -> Result<Self, CnfPartyError> {
        let cfg = share.config().clone();
        let party = share.party_id;
        Topology::new(&cfg, party)?;
        if !matches!(share.key_len, 16 | 24 | 32) {
            return Err(CnfPartyError::InvalidParameters);
        }
        let slots = share.slot_indices().to_vec();
        let mut key_shares = Vec::with_capacity(slots.len());
        let mut prss_seeds = Vec::with_capacity(slots.len());
        for &slot in &slots {
            let (sk_seed, _sk_prf, prg) = share
                .held_slot(slot)
                .ok_or(CnfPartyError::InvalidParameters)?;
            key_shares.push(*sk_seed);
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
            prss_seeds,
            link_keys,
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
        prss_seeds: vec![[0; 32]; topo.held.len()],
        link_keys: link_keys.clone(),
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
        let mut raw = [0u8; 64];
        derive(i, &mut raw);
        keys.key_shares[i][..key_len].copy_from_slice(&raw[..key_len]);
        keys.prss_seeds[i].copy_from_slice(&raw[32..]);
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
    prss_seeds: Vec<[u8; 32]>,
    rng: SeedRng,
    /// This party's share of the MAC key `r`, per held slot.
    r: Vec<u128>,
    /// Per held slot: running hash of the custody replica and every reshare correction.
    transcripts: Vec<Cshake256Xof>,
    /// Chained hash of every joint-coin transcript of this session.
    coin_binding: [u8; 32],
    mult_ctr: u64,
    barrier_ctr: u64,
    /// Per held slot: bit shares of every unverified multiplication output and input.
    pending_bits: Vec<Vec<u64>>,
    /// Per held slot: the matching shares of `r * bit`.
    pending_rand: Vec<Vec<[u64; 2]>>,
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
            prss_seeds: keys.prss_seeds.clone(),
            rng: SeedRng::new(rng_seed, b"cnf-party"),
            r,
            transcripts,
            coin_binding: [0; 32],
            mult_ctr: 0,
            barrier_ctr: 0,
            pending_bits: vec![Vec::new(); held],
            pending_rand: vec![Vec::new(); held],
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

    /// Whether multiplications are waiting for a barrier.
    pub fn has_unverified_gates(&self) -> bool {
        self.pending_rand.first().is_some_and(|p| !p.is_empty())
    }

    /// Multiplication batches run so far (one per chi round and one per loaded input).
    pub fn multiplications(&self) -> u64 {
        self.mult_ctr
    }

    pub fn barriers(&self) -> u64 {
        self.barrier_ctr
    }

    fn wipe_secrets(&mut self) {
        for k in self.key_shares.iter_mut().chain(&mut self.prss_seeds) {
            wipe_bytes32(k);
        }
        wipe_u128s(&mut self.r);
        for p in &mut self.pending_bits {
            wipe_u64s(p);
            p.clear();
        }
        for p in &mut self.pending_rand {
            qsag_asm::volatile_fill(p, [0; 2]);
            p.clear();
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
        let count = self.pending_rand[0].len();
        let mut raw = vec![0u8; 16 * count];
        expand(b"cnf-party/alpha", &[&coin], &mut raw);
        let alpha: Vec<[u64; 2]> = raw
            .as_chunks::<16>()
            .0
            .iter()
            .map(|c| gf_words(u128::from_le_bytes(*c)))
            .collect();
        let mut u = vec![0u128; held];
        let mut w = vec![0u128; held];
        for l in 0..held {
            let mut acc = [0u64; 2];
            qsag_asm::gf2_128_mul_acc_batch(&mut acc, &alpha, &self.pending_rand[l]);
            u[l] = gf_from_words(acc);
            let bits = &self.pending_bits[l];
            let mut sum = [0u64; 2];
            for (k, a) in alpha.iter().enumerate() {
                let mask = 0u64.wrapping_sub((bits[k / 64] >> (k % 64)) & 1);
                sum[0] ^= a[0] & mask;
                sum[1] ^= a[1] & mask;
            }
            w[l] = gf_from_words(sum);
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
}
