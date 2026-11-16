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
