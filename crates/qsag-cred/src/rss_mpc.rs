//! Honest-majority replicated secret sharing over the ML-DSA field
//! (`q = 8_380_417`) with batch multiplication verification.
//!
//! # Model
//!
//! A session has `m` parties, of which at most `t - 1` are statically and
//! maliciously corrupt, with `m >= 2t - 1`. A value is the sum modulo `q` of
//! one component per subset of `m - t + 1` parties; every member of a subset
//! knows its component. No coalition of `t - 1` parties covers every subset,
//! every subset has an honest member, and every pair of subsets shares a
//! party. Parties are connected by authenticated confidential pairwise
//! channels and an authenticated consistent broadcast channel, both supplied
//! through [`MpcTransport`]. Security is with abort: a deviating party can stop
//! a session, but honest parties never release a value that depends on an
//! unverified multiplication.
//!
//! # Protocol pieces
//!
//! * Session subset keys come from fresh contributions of every member, sent
//!   over the private channels and confirmed by broadcast. All shared
//!   randomness (random elements, random bits, resharing masks, public coins)
//!   is expanded from these keys, so nothing is dealt.
//! * Multiplication sends one field element per gate from each party to the
//!   other members of one subset. It is private, and correct up to an additive
//!   error chosen by the adversary without knowledge of honest values.
//! * Before any opening, every multiplication since the previous opening is
//!   checked in the degree-6 extension field. The tuples are folded with powers
//!   of a public coin into one inner-product claim, and that claim is reduced
//!   eight-fold per level by interpolation at a fresh coin. A random tuple
//!   placed at index 0 masks the last claim, which is then opened and checked.
//!   Holders of every subset also compare keyed digests of every value they
//!   received for it. For `N` gates the cheating probability is at most
//!   `(N + 14 * levels + 1) / q^6`, below `2^-115` for `N <= 2^22`.
//! * Opening a value: one holder of each component sends it to the parties
//!   outside the subset and every holder broadcasts its hash. Any disagreement
//!   aborts; since each subset has an honest holder, an accepted opening is
//!   the shared value.
//!
//! The engine is straight-line code for ONE party. Control flow depends only
//! on opened values, so all honest parties execute the same rounds.

use crate::fips204_ntt::{MLDSA_Q, fq_add, fq_inv_or_zero, fq_mul, fq_sub};
use alloc::vec;
use alloc::vec::Vec;
use qsag_accel::ct::{ct_eq_bytes, ct_zeroize_bytes, ct_zeroize_u32s};
use qsag_accel::keccak::{Shake256, cshake256_framed_32, finalize_cshake256, init_cshake256};

const Q64: u64 = MLDSA_Q as u64;

/// Largest supported session size.
pub const MAX_MPC_PARTIES: usize = 5;
/// Degree of the verification extension field `F_q[X] / (X^6 - 7)`.
pub const EXT_DEGREE: usize = 6;
/// `7` is neither a square nor a cube modulo `q`, and `6 | q - 1`, so
/// `X^6 - 7` is irreducible.
const EXT_NONRESIDUE: u64 = 7;
/// Fold factor of the inner-product reduction.
const FOLD: usize = 8;
const FOLD_POINTS: usize = 2 * FOLD - 1;

/// What a round carries. Transports may use it for framing; tests use it to
/// aim faults.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RoundKind {
    KeySetup,
    KeyConfirm,
    Multiply,
    VerifyReshare,
    ViewDigest,
    Open,
    Confirm,
}

/// Public position of a round inside a session.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RoundInfo {
    pub index: u64,
    pub phase: u8,
    pub kind: RoundKind,
}

/// Messages received in one round, indexed by sender position.
#[derive(Clone, Debug, Default)]
pub struct RoundInbox {
    pub private: Vec<Vec<u8>>,
    pub broadcast: Vec<Vec<u8>>,
}

/// The transport failed or a peer stopped.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MpcTransportError;

/// One party's endpoint of a synchronous round network.
///
/// `private[j]` must reach only party `j` over an authenticated confidential
/// channel (the caller's own slot is ignored). `broadcast` must reach every
/// party identically (authenticated consistent broadcast). The call returns
/// once every party's messages for this round have arrived.
pub trait MpcTransport {
    fn exchange(
        &mut self,
        info: RoundInfo,
        private: Vec<Vec<u8>>,
        broadcast: Vec<u8>,
    ) -> Result<RoundInbox, MpcTransportError>;
}

/// Failures of the sharing engine. All of them end the session.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MpcError {
    Poisoned,
    InvalidRange,
    UnsupportedStructure { parties: usize, threshold: usize },
    Transport,
    MalformedMessage { from: usize },
    KeyConfirmationMismatch { subset: usize },
    ViewDigestMismatch { subset: usize },
    OpeningInconsistent { subset: usize },
    MultiplicationCheckFailed,
    DegenerateChallenge,
    ConfirmationMismatch { party: usize },
}

/// Counters for one party.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct MpcStats {
    pub rounds: u64,
    /// Private bytes sent plus broadcast bytes times the number of receivers.
    pub bytes_sent: u64,
    pub multiplications: u64,
    pub verifications: u64,
}

/// Access structure of a session.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Structure {
    pub parties: usize,
    pub threshold: usize,
    /// Holder bitmasks, ascending; each has `parties - threshold + 1` bits.
    pub subsets: Vec<u32>,
}

impl Structure {
    pub fn new(parties: usize, threshold: usize) -> Result<Self, MpcError> {
        if threshold < 2 || parties > MAX_MPC_PARTIES || parties < 2 * threshold - 1 {
            return Err(MpcError::UnsupportedStructure { parties, threshold });
        }
        let size = (parties - threshold + 1) as u32;
        let subsets = (1u32..(1u32 << parties))
            .filter(|mask| mask.count_ones() == size)
            .collect();
        Ok(Self {
            parties,
            threshold,
            subsets,
        })
    }

    pub fn holds(&self, subset: usize, party: usize) -> bool {
        (self.subsets[subset] >> party) & 1 == 1
    }

    fn lowest_holder(&self, subset: usize) -> usize {
        self.subsets[subset].trailing_zeros() as usize
    }

    /// Subsets containing `party`, ascending.
    pub fn subsets_of(&self, party: usize) -> Vec<usize> {
        (0..self.subsets.len())
            .filter(|&s| self.holds(s, party))
            .collect()
    }
}

/// One party's components of a vector of shared field elements. `c[i]` is the
/// component of the party's `i`-th subset.
#[derive(Clone, Debug)]
pub struct Sh {
    pub c: Vec<Vec<u32>>,
}

impl Drop for Sh {
    fn drop(&mut self) {
        for comp in &mut self.c {
            ct_zeroize_u32s(comp);
        }
    }
}

impl Sh {
    pub fn zeros(comps: usize, len: usize) -> Self {
        Self {
            c: vec![vec![0u32; len]; comps],
        }
    }

    pub fn len(&self) -> usize {
        self.c.first().map_or(0, Vec::len)
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn zip_with(&self, rhs: &Self, f: impl Fn(u32, u32) -> u32) -> Self {
        assert_eq!(self.len(), rhs.len());
        Self {
            c: self
                .c
                .iter()
                .zip(&rhs.c)
                .map(|(a, b)| a.iter().zip(b).map(|(&x, &y)| f(x, y)).collect())
                .collect(),
        }
    }

    pub fn add(&self, rhs: &Self) -> Self {
        self.zip_with(rhs, fq_add)
    }

    pub fn sub(&self, rhs: &Self) -> Self {
        self.zip_with(rhs, fq_sub)
    }

    pub fn scale(&self, k: u32) -> Self {
        Self {
            c: self
                .c
                .iter()
                .map(|a| a.iter().map(|&x| fq_mul(x, k)).collect())
                .collect(),
        }
    }

    pub fn neg(&self) -> Self {
        Self {
            c: self
                .c
                .iter()
                .map(|a| a.iter().map(|&x| fq_sub(0, x)).collect())
                .collect(),
        }
    }

    /// Element-wise product with a public vector.
    pub fn mul_pub(&self, k: &[u32]) -> Self {
        assert_eq!(self.len(), k.len());
        Self {
            c: self
                .c
                .iter()
                .map(|a| a.iter().zip(k).map(|(&x, &y)| fq_mul(x, y)).collect())
                .collect(),
        }
    }

    pub fn concat(parts: &[&Self]) -> Self {
        let comps = parts[0].c.len();
        Self {
            c: (0..comps)
                .map(|i| {
                    let mut out = Vec::new();
                    for part in parts {
                        out.extend_from_slice(&part.c[i]);
                    }
                    out
                })
                .collect(),
        }
    }

    pub fn slice(&self, start: usize, len: usize) -> Self {
        Self {
            c: self
                .c
                .iter()
                .map(|a| a[start..start + len].to_vec())
                .collect(),
        }
    }

    pub fn gather(&self, idx: &[usize]) -> Self {
        Self {
            c: self
                .c
                .iter()
                .map(|a| idx.iter().map(|&i| a[i]).collect())
                .collect(),
        }
    }

    /// The length-1 sharing of the sum of all elements.
    pub fn sum(&self) -> Self {
        Self {
            c: self
                .c
                .iter()
                .map(|a| vec![a.iter().fold(0u32, |acc, &x| fq_add(acc, x))])
                .collect(),
        }
    }

    pub fn repeat(&self, times: usize) -> Self {
        Self {
            c: self
                .c
                .iter()
                .map(|a| {
                    let mut out = Vec::with_capacity(a.len() * times);
                    for _ in 0..times {
                        out.extend_from_slice(a);
                    }
                    out
                })
                .collect(),
        }
    }
}

// ---------------------------------------------------------------------------
// Extension field F_q[X] / (X^6 - 7)
// ---------------------------------------------------------------------------

pub(crate) type Kx = [u32; EXT_DEGREE];
pub(crate) const K_ZERO: Kx = [0; EXT_DEGREE];
pub(crate) const K_ONE: Kx = [1, 0, 0, 0, 0, 0];

fn k_add(a: &Kx, b: &Kx) -> Kx {
    core::array::from_fn(|i| fq_add(a[i], b[i]))
}

fn k_sub(a: &Kx, b: &Kx) -> Kx {
    core::array::from_fn(|i| fq_sub(a[i], b[i]))
}

fn k_scale(a: &Kx, s: u32) -> Kx {
    core::array::from_fn(|i| fq_mul(a[i], s))
}

fn k_base(s: u32) -> Kx {
    [s, 0, 0, 0, 0, 0]
}

/// Unreduced product accumulator. Each `add_prod` adds less than `2^49` to a
/// limb, so it is normalized every 8192 additions.
struct KAcc {
    limbs: [u64; 2 * EXT_DEGREE - 1],
    pending: u32,
}

impl KAcc {
    fn new() -> Self {
        Self {
            limbs: [0; 2 * EXT_DEGREE - 1],
            pending: 0,
        }
    }

    #[inline]
    fn add_prod(&mut self, a: &Kx, b: &Kx) {
        for (i, &ai) in a.iter().enumerate() {
            for (j, &bj) in b.iter().enumerate() {
                self.limbs[i + j] += (ai as u64) * (bj as u64);
            }
        }
        self.pending += 1;
        if self.pending == 8192 {
            for limb in &mut self.limbs {
                *limb %= Q64;
            }
            self.pending = 0;
        }
    }

    fn reduce(&self) -> Kx {
        core::array::from_fn(|i| {
            let low = self.limbs[i] % Q64;
            let high = if i + EXT_DEGREE < self.limbs.len() {
                self.limbs[i + EXT_DEGREE] % Q64
            } else {
                0
            };
            ((low + EXT_NONRESIDUE * high) % Q64) as u32
        })
    }
}

pub(crate) fn k_mul(a: &Kx, b: &Kx) -> Kx {
    let mut acc = KAcc::new();
    acc.add_prod(a, b);
    acc.reduce()
}

fn k_is_zero(a: &Kx) -> bool {
    a.iter().all(|&x| x == 0)
}

// ---------------------------------------------------------------------------
// Encoding and hashing
// ---------------------------------------------------------------------------

fn pack(values: &[u32], out: &mut Vec<u8>) {
    out.reserve(values.len() * 3);
    for &v in values {
        out.extend_from_slice(&v.to_le_bytes()[..3]);
    }
}

fn unpack(bytes: &[u8], count: usize) -> Option<Vec<u32>> {
    if bytes.len() != count * 3 {
        return None;
    }
    let mut out = Vec::with_capacity(count);
    for chunk in bytes.as_chunks::<3>().0 {
        let v = u32::from_le_bytes([chunk[0], chunk[1], chunk[2], 0]);
        if v >= MLDSA_Q {
            return None;
        }
        out.push(v);
    }
    Some(out)
}

/// Keyed pseudorandom stream shared by the holders of one subset.
struct Prss {
    xof: Shake256,
}

impl Prss {
    fn new(key: &[u8; 32]) -> Self {
        let mut xof = init_cshake256(b"", b"QSAG.RSS.PRSS.V1");
        xof.absorb(key);
        finalize_cshake256(&mut xof, true);
        Self { xof }
    }

    fn elements(&mut self, count: usize) -> Vec<u32> {
        let mut out = Vec::with_capacity(count);
        let mut buf = [0u8; 408];
        while out.len() < count {
            self.xof.squeeze(&mut buf);
            for chunk in buf.as_chunks::<3>().0 {
                let v = u32::from_le_bytes([chunk[0], chunk[1], chunk[2], 0]) & 0x7F_FFFF;
                if v < MLDSA_Q && out.len() < count {
                    out.push(v);
                }
            }
        }
        ct_zeroize_bytes(&mut buf);
        out
    }

    fn bits(&mut self, count: usize) -> Vec<u32> {
        let mut bytes = vec![0u8; count.div_ceil(8)];
        self.xof.squeeze(&mut bytes);
        let out = (0..count)
            .map(|i| ((bytes[i / 8] >> (i % 8)) & 1) as u32)
            .collect();
        ct_zeroize_bytes(&mut bytes);
        out
    }
}

// ---------------------------------------------------------------------------
// Engine
// ---------------------------------------------------------------------------

struct Tuple {
    x: Sh,
    y: Sh,
    z: Sh,
}

/// One party's state in a session.
pub struct Engine<'a, T: MpcTransport> {
    net: &'a mut T,
    st: Structure,
    me: usize,
    /// Subset ids containing this party, ascending.
    comps: Vec<usize>,
    keys: Vec<[u8; 32]>,
    streams: Vec<Prss>,
    views: Vec<[u8; 32]>,
    /// For each party, the subset that receives its resharing correction.
    correction_subset: Vec<usize>,
    /// For each of my components, the components whose cross terms I add.
    plan: Vec<Vec<usize>>,
    log: Vec<Tuple>,
    phase: u8,
    stats: MpcStats,
    poisoned: bool,
}

impl<T: MpcTransport> Drop for Engine<'_, T> {
    fn drop(&mut self) {
        for key in &mut self.keys {
            ct_zeroize_bytes(key);
        }
        for view in &mut self.views {
            ct_zeroize_bytes(view);
        }
    }
}

impl<'a, T: MpcTransport> Engine<'a, T> {
    /// Establishes fresh subset keys for this session. `context` must bind
    /// everything the parties are supposed to agree on; `entropy` must be
    /// fresh secret randomness.
    pub fn setup(
        net: &'a mut T,
        st: Structure,
        me: usize,
        context: &[u8; 32],
        entropy: &[u8; 32],
    ) -> Result<Self, MpcError> {
        assert!(me < st.parties);
        let comps = st.subsets_of(me);
        let mut correction_subset = Vec::with_capacity(st.parties);
        let mut load = vec![0usize; st.subsets.len()];
        for party in 0..st.parties {
            let choice = st
                .subsets_of(party)
                .into_iter()
                .min_by_key(|&s| (load[s], s))
                .expect("every party is in a subset");
            load[choice] += 1;
            correction_subset.push(choice);
        }
        let plan = comps
            .iter()
            .map(|&sa| {
                (0..comps.len())
                    .filter(|&j| {
                        let both = st.subsets[sa] & st.subsets[comps[j]];
                        both.trailing_zeros() as usize == me
                    })
                    .collect()
            })
            .collect();
        let mut engine = Self {
            net,
            st,
            me,
            comps,
            keys: Vec::new(),
            streams: Vec::new(),
            views: Vec::new(),
            correction_subset,
            plan,
            log: Vec::new(),
            phase: 0,
            stats: MpcStats::default(),
            poisoned: false,
        };
        engine.establish_keys(context, entropy)?;
        Ok(engine)
    }

    fn establish_keys(&mut self, context: &[u8; 32], entropy: &[u8; 32]) -> Result<(), MpcError> {
        if self.poisoned {
            return Err(MpcError::Poisoned);
        }
        let result = (|| {
            let parties = self.st.parties;
            let mine: Vec<[u8; 32]> = self
                .comps
                .iter()
                .map(|&s| {
                    cshake256_framed_32(
                        b"QSAG.RSS.KEYSHARE.V1",
                        &[
                            entropy,
                            context,
                            &(s as u32).to_le_bytes(),
                            &(self.me as u32).to_le_bytes(),
                        ],
                    )
                })
                .collect();
            let mut private = vec![Vec::new(); parties];
            for (i, &s) in self.comps.iter().enumerate() {
                for (j, out) in private.iter_mut().enumerate() {
                    if j != self.me && self.st.holds(s, j) {
                        out.extend_from_slice(&mine[i]);
                    }
                }
            }
            let inbox = self.round(RoundKind::KeySetup, private, Vec::new())?;
            let mut cursor = vec![0usize; parties];
            for (i, &s) in self.comps.iter().enumerate() {
                let mut xof = init_cshake256(b"", b"QSAG.RSS.KEY.V1");
                xof.absorb(context);
                xof.absorb(&(s as u32).to_le_bytes());
                for j in 0..parties {
                    if !self.st.holds(s, j) {
                        continue;
                    }
                    if j == self.me {
                        xof.absorb(&mine[i]);
                    } else {
                        let at = cursor[j];
                        let bytes = inbox.private[j]
                            .get(at..at + 32)
                            .ok_or(MpcError::MalformedMessage { from: j })?;
                        xof.absorb(bytes);
                        cursor[j] = at + 32;
                    }
                }
                finalize_cshake256(&mut xof, true);
                let mut key = [0u8; 32];
                xof.squeeze(&mut key);
                self.keys.push(key);
            }
            let mut broadcast = Vec::with_capacity(32 * self.comps.len());
            for key in &self.keys {
                broadcast
                    .extend_from_slice(&cshake256_framed_32(b"QSAG.RSS.KEYCONFIRM.V1", &[key]));
            }
            let mine_confirm = broadcast.clone();
            let inbox = self.round(RoundKind::KeyConfirm, vec![Vec::new(); parties], broadcast)?;
            self.check_holder_digests(&mine_confirm, &inbox.broadcast)
                .map_err(|subset| MpcError::KeyConfirmationMismatch { subset })?;
            for key in &self.keys {
                self.streams.push(Prss::new(key));
                self.views
                    .push(cshake256_framed_32(b"QSAG.RSS.VIEW.INIT.V1", &[key]));
            }
            Ok(())
        })();
        if result.is_err() {
            self.poisoned = true;
        }
        result
    }

    /// Compares one 32-byte digest per subset across all of its holders.
    /// `mine` and each broadcast list the sender's subsets in ascending order.
    fn check_holder_digests(&self, mine: &[u8], broadcast: &[Vec<u8>]) -> Result<(), usize> {
        for s in 0..self.st.subsets.len() {
            let mut reference: Option<&[u8]> = None;
            for (party, received) in broadcast.iter().enumerate() {
                if !self.st.holds(s, party) {
                    continue;
                }
                let rank = (0..s).filter(|&e| self.st.holds(e, party)).count();
                let source = if party == self.me {
                    mine
                } else {
                    received.as_slice()
                };
                let digest = source.get(rank * 32..rank * 32 + 32).ok_or(s)?;
                match reference {
                    None => reference = Some(digest),
                    Some(first) => {
                        if !ct_eq_bytes(first, digest) {
                            return Err(s);
                        }
                    }
                }
            }
        }
        Ok(())
    }

    fn round(
        &mut self,
        kind: RoundKind,
        private: Vec<Vec<u8>>,
        broadcast: Vec<u8>,
    ) -> Result<RoundInbox, MpcError> {
        if self.poisoned {
            return Err(MpcError::Poisoned);
        }
        let result = (|| {
            let parties = self.st.parties;
            let sent: usize = private
                .iter()
                .enumerate()
                .filter(|(j, _)| *j != self.me)
                .map(|(_, m)| m.len())
                .sum();
            self.stats.bytes_sent += (sent + broadcast.len() * (parties - 1)) as u64;
            let info = RoundInfo {
                index: self.stats.rounds,
                phase: self.phase,
                kind,
            };
            self.stats.rounds += 1;
            let inbox = self
                .net
                .exchange(info, private, broadcast)
                .map_err(|_| MpcError::Transport)?;
            if inbox.private.len() != parties || inbox.broadcast.len() != parties {
                return Err(MpcError::Transport);
            }
            Ok(inbox)
        })();
        if result.is_err() {
            self.poisoned = true;
        }
        result
    }

    pub fn structure(&self) -> &Structure {
        &self.st
    }

    pub fn me(&self) -> usize {
        self.me
    }

    pub fn comps(&self) -> &[usize] {
        &self.comps
    }

    pub fn stats(&self) -> MpcStats {
        self.stats
    }

    pub fn set_phase(&mut self, phase: u8) {
        self.phase = phase;
    }

    pub fn zeros(&self, len: usize) -> Result<Sh, MpcError> {
        if self.poisoned {
            return Err(MpcError::Poisoned);
        }
        Ok(Sh::zeros(self.comps.len(), len))
    }

    /// The canonical sharing of a public vector: subset 0 carries it.
    pub fn public(&self, values: &[u32]) -> Result<Sh, MpcError> {
        if self.poisoned {
            return Err(MpcError::Poisoned);
        }
        let mut out = self.zeros(values.len())?;
        if self.comps[0] == 0 {
            out.c[0].copy_from_slice(values);
        }
        Ok(out)
    }

    pub fn public_const(&self, value: u32, len: usize) -> Result<Sh, MpcError> {
        if self.poisoned {
            return Err(MpcError::Poisoned);
        }
        self.public(&vec![value; len])
    }

    /// A sharing of uniformly random field elements nobody knows.
    pub fn rand(&mut self, len: usize) -> Result<Sh, MpcError> {
        if self.poisoned {
            return Err(MpcError::Poisoned);
        }
        Ok(Sh {
            c: self
                .streams
                .iter_mut()
                .map(|stream| stream.elements(len))
                .collect(),
        })
    }

    /// For every subset of the structure, the sharing of random bits known to
    /// exactly that subset's holders.
    fn local_bits(&mut self, len: usize) -> Result<Vec<Sh>, MpcError> {
        if self.poisoned {
            return Err(MpcError::Poisoned);
        }
        let comps = self.comps.len();
        Ok((0..self.st.subsets.len())
            .map(|s| {
                let mut share = Sh::zeros(comps, len);
                if let Some(i) = self.comps.iter().position(|&c| c == s) {
                    share.c[i] = self.streams[i].bits(len);
                }
                share
            })
            .collect())
    }

    /// Sharings of uniformly random bits nobody knows: the exclusive-or of
    /// one bit per subset, computed with `subsets - 1` multiplications.
    pub fn rand_bits(&mut self, len: usize) -> Result<Sh, MpcError> {
        if self.poisoned {
            return Err(MpcError::Poisoned);
        }
        let result = (|| {
            let locals = self.local_bits(len)?;
            let mut acc = locals[0].clone();
            for local in &locals[1..] {
                let product = self.mul(&acc, local)?;
                acc = acc.add(local).sub(&product.scale(2));
            }
            Ok(acc)
        })();
        if result.is_err() {
            self.poisoned = true;
        }
        result
    }

    /// Reshares the vector `value`, which only this party knows, and returns
    /// the sharing of the sum of all parties' vectors.
    fn reshare(&mut self, mut value: Vec<u32>, kind: RoundKind) -> Result<Sh, MpcError> {
        if self.poisoned {
            return Err(MpcError::Poisoned);
        }
        let result = (|| {
            let len = value.len();
            let parties = self.st.parties;
            let mut out = self.zeros(len)?;
            for (i, &s) in self.comps.iter().enumerate() {
                for party in 0..parties {
                    if !self.st.holds(s, party) || self.correction_subset[party] == s {
                        continue;
                    }
                    let mask = self.streams[i].elements(len);
                    for k in 0..len {
                        out.c[i][k] = fq_add(out.c[i][k], mask[k]);
                        if party == self.me {
                            value[k] = fq_sub(value[k], mask[k]);
                        }
                    }
                }
            }
            let target = self.correction_subset[self.me];
            let mut message = Vec::new();
            pack(&value, &mut message);
            let mut private = vec![Vec::new(); parties];
            for (j, slot) in private.iter_mut().enumerate() {
                if j != self.me && self.st.holds(target, j) {
                    slot.clone_from(&message);
                }
            }
            let inbox = self.round(kind, private, Vec::new())?;
            for (i, &s) in self.comps.iter().enumerate() {
                for party in 0..parties {
                    if self.correction_subset[party] != s {
                        continue;
                    }
                    let (bytes, values) = if party == self.me {
                        (message.as_slice(), value.clone())
                    } else {
                        let bytes = inbox.private[party].as_slice();
                        (
                            bytes,
                            unpack(bytes, len).ok_or(MpcError::MalformedMessage { from: party })?,
                        )
                    };
                    self.views[i] = cshake256_framed_32(
                        b"QSAG.RSS.VIEW.V1",
                        &[&self.views[i], &(party as u32).to_le_bytes(), bytes],
                    );
                    for k in 0..len {
                        out.c[i][k] = fq_add(out.c[i][k], values[k]);
                    }
                }
            }
            ct_zeroize_u32s(&mut value);
            ct_zeroize_bytes(&mut message);
            Ok(out)
        })();
        if result.is_err() {
            self.poisoned = true;
        }
        result
    }

    /// Element-wise product. The result is unverified until the next opening.
    pub fn mul(&mut self, a: &Sh, b: &Sh) -> Result<Sh, MpcError> {
        if self.poisoned {
            return Err(MpcError::Poisoned);
        }
        let result = (|| {
            assert_eq!(a.len(), b.len());
            let len = a.len();
            let mut acc = vec![0u64; len];
            for (i, others) in self.plan.iter().enumerate() {
                if others.is_empty() {
                    continue;
                }
                let left = &a.c[i];
                for k in 0..len {
                    let mut sum = 0u64;
                    for &j in others {
                        sum += b.c[j][k] as u64;
                    }
                    acc[k] += (left[k] as u64) * (sum % Q64);
                }
            }
            let value: Vec<u32> = acc.iter().map(|&v| (v % Q64) as u32).collect();
            #[cfg(test)]
            let value = test_support::apply_armed_fault(self.phase, value);
            let z = self.reshare(value, RoundKind::Multiply)?;
            self.stats.multiplications += len as u64;
            self.log.push(Tuple {
                x: a.clone(),
                y: b.clone(),
                z: z.clone(),
            });
            Ok(z)
        })();
        if result.is_err() {
            self.poisoned = true;
        }
        result
    }

    /// Opens values after verifying every multiplication they may depend on.
    pub fn open(&mut self, values: &[&Sh]) -> Result<Vec<Vec<u32>>, MpcError> {
        if self.poisoned {
            return Err(MpcError::Poisoned);
        }
        let result = (|| {
            self.verify()?;
            self.open_raw(values)
        })();
        if result.is_err() {
            self.poisoned = true;
        }
        result
    }

    fn open_raw(&mut self, values: &[&Sh]) -> Result<Vec<Vec<u32>>, MpcError> {
        if self.poisoned {
            return Err(MpcError::Poisoned);
        }
        let result = (|| {
            let parties = self.st.parties;
            let total: usize = values.iter().map(|v| v.len()).sum();
            let mut mine: Vec<Vec<u8>> = Vec::with_capacity(self.comps.len());
            for i in 0..self.comps.len() {
                let mut bytes = Vec::with_capacity(total * 3);
                for value in values {
                    pack(&value.c[i], &mut bytes);
                }
                mine.push(bytes);
            }
            let mut private = vec![Vec::new(); parties];
            let mut broadcast = Vec::with_capacity(32 * self.comps.len());
            for (i, &s) in self.comps.iter().enumerate() {
                broadcast.extend_from_slice(&cshake256_framed_32(b"QSAG.RSS.OPEN.V1", &[&mine[i]]));
                if self.st.lowest_holder(s) == self.me {
                    for (j, slot) in private.iter_mut().enumerate() {
                        if !self.st.holds(s, j) {
                            slot.extend_from_slice(&mine[i]);
                        }
                    }
                }
            }
            let my_digests = broadcast.clone();
            let inbox = self.round(RoundKind::Open, private, broadcast)?;
            let mut cursor = vec![0usize; parties];
            let mut sum = vec![0u32; total];
            for s in 0..self.st.subsets.len() {
                let component = match self.comps.iter().position(|&c| c == s) {
                    Some(i) => unpack(&mine[i], total).expect("own encoding is canonical"),
                    None => {
                        let sender = self.st.lowest_holder(s);
                        let at = cursor[sender];
                        let bytes = inbox.private[sender]
                            .get(at..at + total * 3)
                            .ok_or(MpcError::OpeningInconsistent { subset: s })?;
                        cursor[sender] = at + total * 3;
                        let digest = cshake256_framed_32(b"QSAG.RSS.OPEN.V1", &[bytes]);
                        for (party, received) in inbox.broadcast.iter().enumerate() {
                            if !self.st.holds(s, party) {
                                continue;
                            }
                            let rank = (0..s).filter(|&e| self.st.holds(e, party)).count();
                            let claimed = received.get(rank * 32..rank * 32 + 32);
                            if claimed.is_none_or(|c| !ct_eq_bytes(c, &digest)) {
                                return Err(MpcError::OpeningInconsistent { subset: s });
                            }
                        }
                        unpack(bytes, total).ok_or(MpcError::OpeningInconsistent { subset: s })?
                    }
                };
                for (acc, &v) in sum.iter_mut().zip(&component) {
                    *acc = fq_add(*acc, v);
                }
            }
            self.check_holder_digests(&my_digests, &inbox.broadcast)
                .map_err(|subset| MpcError::OpeningInconsistent { subset })?;
            let mut out = Vec::with_capacity(values.len());
            let mut at = 0;
            for value in values {
                out.push(sum[at..at + value.len()].to_vec());
                at += value.len();
            }
            Ok(out)
        })();
        if result.is_err() {
            self.poisoned = true;
        }
        result
    }

    /// Broadcasts a digest of a public result and requires every party to
    /// have broadcast the same one.
    pub fn confirm(&mut self, digest: &[u8; 32]) -> Result<(), MpcError> {
        if self.poisoned {
            return Err(MpcError::Poisoned);
        }
        let result = (|| {
            let parties = self.st.parties;
            let inbox = self.round(
                RoundKind::Confirm,
                vec![Vec::new(); parties],
                digest.to_vec(),
            )?;
            for (party, received) in inbox.broadcast.iter().enumerate() {
                if party != self.me && !ct_eq_bytes(received, digest) {
                    return Err(MpcError::ConfirmationMismatch { party });
                }
            }
            Ok(())
        })();
        if result.is_err() {
            self.poisoned = true;
        }
        result
    }

    fn coin(&mut self) -> Result<Kx, MpcError> {
        let share = self.rand(EXT_DEGREE)?;
        let opened = self.open_raw(&[&share])?;
        Ok(core::array::from_fn(|i| opened[0][i]))
    }

    fn rand_k(&mut self, count: usize) -> Result<Vec<Vec<Kx>>, MpcError> {
        if self.poisoned {
            return Err(MpcError::Poisoned);
        }
        let flat = self.rand(count * EXT_DEGREE)?;
        Ok(flat.c.iter().map(|comp| unflatten(comp)).collect())
    }

    /// My additive part of the inner product of two shared extension-field
    /// vectors, over entries `offset, offset + stride, ...`.
    fn ip_local(&self, x: &[Vec<Kx>], y: &[Vec<Kx>], offset: usize, stride: usize) -> Kx {
        let mut acc = KAcc::new();
        for (i, others) in self.plan.iter().enumerate() {
            match others.as_slice() {
                [] => {}
                [only] => {
                    let right = &y[*only];
                    for k in (offset..x[i].len()).step_by(stride) {
                        acc.add_prod(&x[i][k], &right[k]);
                    }
                }
                many => {
                    for k in (offset..x[i].len()).step_by(stride) {
                        let mut sum = y[many[0]][k];
                        for &j in &many[1..] {
                            sum = k_add(&sum, &y[j][k]);
                        }
                        acc.add_prod(&x[i][k], &sum);
                    }
                }
            }
        }
        acc.reduce()
    }

    fn reshare_k(&mut self, values: &[Kx]) -> Result<Vec<Vec<Kx>>, MpcError> {
        let flat: Vec<u32> = values.iter().flat_map(|v| v.iter().copied()).collect();
        let share = self.reshare(flat, RoundKind::VerifyReshare)?;
        Ok(share.c.iter().map(|comp| unflatten(comp)).collect())
    }

    /// Checks every multiplication since the last check and compares holder
    /// views. Returns without communication when nothing is pending.
    pub fn verify(&mut self) -> Result<(), MpcError> {
        if self.poisoned {
            return Err(MpcError::Poisoned);
        }
        let result = (|| {
            if self.log.is_empty() {
                return Ok(());
            }
            let log = core::mem::take(&mut self.log);
            let comps = self.comps.len();
            let gates: usize = log.iter().map(|t| t.x.len()).sum();
            self.stats.verifications += 1;

            // Masking tuple at index 0.
            let mask_a = self.rand_k(1)?;
            let mask_b = self.rand_k(1)?;
            let mask_c_local = self.ip_local(&mask_a, &mask_b, 0, 1);
            let mask_c = self.reshare_k(&[mask_c_local])?;
            let lambda = self.coin()?;

            let mut dim = (gates + 1).div_ceil(FOLD) * FOLD;
            let mut x: Vec<Vec<Kx>> = (0..comps).map(|_| Vec::with_capacity(dim)).collect();
            let mut y: Vec<Vec<Kx>> = (0..comps).map(|_| Vec::with_capacity(dim)).collect();
            let mut z: Vec<Kx> = (0..comps).map(|i| mask_c[i][0]).collect();
            for i in 0..comps {
                x[i].push(mask_a[i][0]);
                y[i].push(mask_b[i][0]);
            }
            let mut power = lambda;
            for tuple in &log {
                for k in 0..tuple.x.len() {
                    for i in 0..comps {
                        x[i].push(k_scale(&power, tuple.x.c[i][k]));
                        y[i].push(k_base(tuple.y.c[i][k]));
                        z[i] = k_add(&z[i], &k_scale(&power, tuple.z.c[i][k]));
                    }
                    power = k_mul(&power, &lambda);
                }
            }
            drop(log);
            for i in 0..comps {
                x[i].resize(dim, K_ZERO);
                y[i].resize(dim, K_ZERO);
            }

            let tables = FoldTables::new();
            let mut mask_coefficient = K_ONE;
            while dim > 1 {
                let groups = dim / FOLD;
                // Evaluations of the group polynomials at the extra points.
                let mut locals = Vec::with_capacity(FOLD_POINTS - 1);
                for p in 0..FOLD - 1 {
                    locals.push(self.ip_local(&x, &y, p, FOLD));
                }
                for row in &tables.extra {
                    let xe: Vec<Vec<Kx>> = x
                        .iter()
                        .map(|comp| eval_groups(comp, row, groups))
                        .collect();
                    let ye: Vec<Vec<Kx>> = y
                        .iter()
                        .map(|comp| eval_groups(comp, row, groups))
                        .collect();
                    locals.push(self.ip_local(&xe, &ye, 0, 1));
                }
                let shared = self.reshare_k(&locals)?;
                let xi = self.coin()?;
                let basis = tables.basis_at(&xi);
                let full = tables.full_basis_at(&xi);
                for i in 0..comps {
                    // h(0..FOLD-2) and h(FOLD..) are shared; h(FOLD-1) follows from z.
                    let mut missing = z[i];
                    for value in &shared[i][..FOLD - 1] {
                        missing = k_sub(&missing, value);
                    }
                    let mut next = k_mul(&full[FOLD - 1], &missing);
                    for p in 0..FOLD - 1 {
                        next = k_add(&next, &k_mul(&full[p], &shared[i][p]));
                    }
                    for p in FOLD..FOLD_POINTS {
                        next = k_add(&next, &k_mul(&full[p], &shared[i][p - 1]));
                    }
                    z[i] = next;
                    x[i] = fold_groups(&x[i], &basis, groups);
                    y[i] = fold_groups(&y[i], &basis, groups);
                }
                mask_coefficient = k_mul(&mask_coefficient, &basis[0]);
                dim = groups;
                if dim > 1 {
                    let padded = dim.div_ceil(FOLD) * FOLD;
                    for i in 0..comps {
                        x[i].resize(padded, K_ZERO);
                        y[i].resize(padded, K_ZERO);
                    }
                    dim = padded;
                }
            }
            if k_is_zero(&mask_coefficient) {
                return Err(MpcError::DegenerateChallenge);
            }

            // Holder views must agree before anything value-dependent is opened.
            let mut broadcast = Vec::with_capacity(32 * comps);
            for i in 0..comps {
                broadcast.extend_from_slice(&cshake256_framed_32(
                    b"QSAG.RSS.VIEW.DIGEST.V1",
                    &[&self.keys[i], &self.views[i]],
                ));
            }
            let mine = broadcast.clone();
            let inbox = self.round(
                RoundKind::ViewDigest,
                vec![Vec::new(); self.st.parties],
                broadcast,
            )?;
            self.check_holder_digests(&mine, &inbox.broadcast)
                .map_err(|subset| MpcError::ViewDigestMismatch { subset })?;

            let mut last = self.zeros(3 * EXT_DEGREE)?;
            for i in 0..comps {
                last.c[i][..EXT_DEGREE].copy_from_slice(&x[i][0]);
                last.c[i][EXT_DEGREE..2 * EXT_DEGREE].copy_from_slice(&y[i][0]);
                last.c[i][2 * EXT_DEGREE..].copy_from_slice(&z[i]);
            }
            let opened = self.open_raw(&[&last])?;
            let fx: Kx = core::array::from_fn(|k| opened[0][k]);
            let fy: Kx = core::array::from_fn(|k| opened[0][EXT_DEGREE + k]);
            let fz: Kx = core::array::from_fn(|k| opened[0][2 * EXT_DEGREE + k]);
            if k_mul(&fx, &fy) != fz {
                return Err(MpcError::MultiplicationCheckFailed);
            }
            Ok(())
        })();
        if result.is_err() {
            self.poisoned = true;
        }
        result
    }
}

fn unflatten(flat: &[u32]) -> Vec<Kx> {
    flat.as_chunks::<EXT_DEGREE>().0.to_vec()
}

/// `out[g] = sum_d row[d] * values[FOLD * g + d]` for base-field weights.
fn eval_groups(values: &[Kx], row: &[u32; FOLD], groups: usize) -> Vec<Kx> {
    (0..groups)
        .map(|g| {
            let mut limbs = [0u64; EXT_DEGREE];
            for (d, &weight) in row.iter().enumerate() {
                let value = &values[FOLD * g + d];
                for (limb, &v) in limbs.iter_mut().zip(value) {
                    *limb += (weight as u64) * (v as u64);
                }
            }
            core::array::from_fn(|i| (limbs[i] % Q64) as u32)
        })
        .collect()
}

/// `out[g] = sum_d basis[d] * values[FOLD * g + d]` for extension weights.
fn fold_groups(values: &[Kx], basis: &[Kx; FOLD], groups: usize) -> Vec<Kx> {
    (0..groups)
        .map(|g| {
            let mut acc = KAcc::new();
            for (d, weight) in basis.iter().enumerate() {
                acc.add_prod(weight, &values[FOLD * g + d]);
            }
            acc.reduce()
        })
        .collect()
}

/// Lagrange data for nodes `0..FOLD` (group polynomials) and `0..FOLD_POINTS`
/// (their product sum).
struct FoldTables {
    /// `extra[p - FOLD][d]`: weight of node `d` at point `p`, for the points
    /// `FOLD..FOLD_POINTS`.
    extra: Vec<[u32; FOLD]>,
    inv_denominators: [u32; FOLD],
    full_inv_denominators: [u32; FOLD_POINTS],
}

fn inv_denominator(node: usize, nodes: usize) -> u32 {
    let mut denominator = 1u32;
    for m in 0..nodes {
        if m != node {
            denominator = fq_mul(denominator, fq_sub(node as u32, m as u32));
        }
    }
    fq_inv_or_zero(denominator)
}

impl FoldTables {
    fn new() -> Self {
        let inv_denominators: [u32; FOLD] = core::array::from_fn(|d| inv_denominator(d, FOLD));
        let full_inv_denominators: [u32; FOLD_POINTS] =
            core::array::from_fn(|p| inv_denominator(p, FOLD_POINTS));
        let extra = (FOLD..FOLD_POINTS)
            .map(|p| {
                core::array::from_fn(|d| {
                    let mut numerator = 1u32;
                    for m in 0..FOLD {
                        if m != d {
                            numerator = fq_mul(numerator, fq_sub(p as u32, m as u32));
                        }
                    }
                    fq_mul(numerator, inv_denominators[d])
                })
            })
            .collect();
        Self {
            extra,
            inv_denominators,
            full_inv_denominators,
        }
    }

    fn basis_at(&self, xi: &Kx) -> [Kx; FOLD] {
        core::array::from_fn(|d| lagrange_at(xi, d, FOLD, self.inv_denominators[d]))
    }

    fn full_basis_at(&self, xi: &Kx) -> [Kx; FOLD_POINTS] {
        core::array::from_fn(|p| lagrange_at(xi, p, FOLD_POINTS, self.full_inv_denominators[p]))
    }
}

fn lagrange_at(xi: &Kx, node: usize, nodes: usize, inv_denominator: u32) -> Kx {
    let mut numerator = K_ONE;
    for m in 0..nodes {
        if m != node {
            numerator = k_mul(&numerator, &k_sub(xi, &k_base(m as u32)));
        }
    }
    k_scale(&numerator, inv_denominator)
}

// ---------------------------------------------------------------------------
// Circuits over shared bits
// ---------------------------------------------------------------------------

/// `[r < bound]` per element, for bits `r` (least significant first) and
/// public bounds below `2^bits.len()`. Uses `bits.len() - 1` multiplications.
pub fn less_than_public<T: MpcTransport>(
    engine: &mut Engine<'_, T>,
    bits: &[Sh],
    bounds: &[u32],
) -> Result<Sh, MpcError> {
    let len = bounds.len();
    let ones = vec![1u32; len];
    let mut prefix: Option<Sh> = None;
    let mut result = engine.zeros(len)?;
    for i in (0..bits.len()).rev() {
        let bound_bit: Vec<u32> = bounds.iter().map(|&b| (b >> i) & 1).collect();
        // equal[k] = bit if bound_bit else 1 - bit
        let slope: Vec<u32> = bound_bit
            .iter()
            .map(|&b| if b == 1 { 1 } else { MLDSA_Q - 1 })
            .collect();
        let offset: Vec<u32> = bound_bit.iter().map(|&b| 1 - b).collect();
        let equal = bits[i].mul_pub(&slope).add(&engine.public(&offset)?);
        let previous = match &prefix {
            None => engine.public(&ones)?,
            Some(p) => p.clone(),
        };
        let next = match &prefix {
            None => equal,
            Some(p) => engine.mul(p, &equal)?,
        };
        result = result.add(&previous.sub(&next).mul_pub(&bound_bit));
        prefix = Some(next);
    }
    Ok(result)
}

/// Membership of the hidden value `e = opened - r mod q` in `[0, width)`,
/// for a uniform mask `r < q` given by its 23 bits. One comparison pass.
pub fn masked_range_test<T: MpcTransport>(
    engine: &mut Engine<'_, T>,
    opened: &[u32],
    widths: &[u32],
    mask_bits: &[Sh],
) -> Result<Sh, MpcError> {
    if engine.poisoned {
        return Err(MpcError::Poisoned);
    }
    if widths.len() != opened.len() || widths.iter().any(|&w| w == 0 || w > MLDSA_Q) {
        return Err(MpcError::InvalidRange);
    }
    let len = opened.len();
    let mut bounds = Vec::with_capacity(2 * len);
    let mut wrap = Vec::with_capacity(len);
    bounds.extend(opened.iter().map(|&c| c + 1));
    for (&c, &width) in opened.iter().zip(widths) {
        // r must lie in [c - width + 1, c] modulo q.
        bounds.push(fq_sub(c, width - 1));
        wrap.push((c < width - 1) as u32);
    }
    let doubled: Vec<Sh> = mask_bits.iter().map(|plane| plane.repeat(2)).collect();
    let both = less_than_public(engine, &doubled, &bounds)?;
    let below_upper = both.slice(0, len);
    let below_lower = both.slice(len, len);
    Ok(below_upper.sub(&below_lower).add(&engine.public(&wrap)?))
}

#[cfg(test)]
pub(crate) mod test_support {
    use super::*;
    use core::cell::Cell;

    std::thread_local! {
        static ARMED: Cell<Option<(u8, usize)>> = const { Cell::new(None) };
    }

    /// Makes the calling thread's party add 1 to the first element of its
    /// `nth` multiplication contribution in `phase`. Unlike rewriting a
    /// message in transit, the party's own view stays consistent with what it
    /// sent: this is exactly the additive attack on multiplication.
    pub(crate) fn arm_additive_fault(phase: u8, nth: usize) {
        ARMED.with(|armed| armed.set(Some((phase, nth))));
    }

    pub(crate) fn apply_armed_fault(phase: u8, mut value: Vec<u32>) -> Vec<u32> {
        ARMED.with(|armed| {
            if let Some((target, remaining)) = armed.get()
                && target == phase
            {
                if remaining == 0 {
                    value[0] = fq_add(value[0], 1);
                    armed.set(None);
                } else {
                    armed.set(Some((target, remaining - 1)));
                }
            }
        });
        value
    }

    /// Test-only dealer: splits public test values into one party's view of a
    /// replicated sharing, using a deterministic stream.
    pub(crate) fn deal(st: &Structure, me: usize, values: &[u32], seed: u8) -> Sh {
        let comps = st.subsets_of(me);
        let mut out = Sh::zeros(comps.len(), values.len());
        let mut last = values.to_vec();
        for s in 0..st.subsets.len() - 1 {
            let mut stream = Prss::new(&[seed.wrapping_add(s as u8); 32]);
            let part = stream.elements(values.len());
            for k in 0..values.len() {
                last[k] = fq_sub(last[k], part[k]);
            }
            if let Some(i) = comps.iter().position(|&c| c == s) {
                out.c[i] = part;
            }
        }
        if let Some(i) = comps.iter().position(|&c| c == st.subsets.len() - 1) {
            out.c[i] = last;
        }
        out
    }

    #[test]
    fn extension_field_is_a_field_extension() {
        fn pow(mut base: u32, mut exp: u32) -> u32 {
            let mut acc = 1;
            while exp > 0 {
                if exp & 1 == 1 {
                    acc = fq_mul(acc, base);
                }
                base = fq_mul(base, base);
                exp >>= 1;
            }
            acc
        }
        assert_ne!(pow(7, (MLDSA_Q - 1) / 2), 1, "7 must be a non-square");
        assert_ne!(pow(7, (MLDSA_Q - 1) / 3), 1, "7 must be a non-cube");
        let a: Kx = [5, 8_380_416, 77, 123_456, 9, 4_000_000];
        let b: Kx = [1_000, 2, 8_000_000, 0, 31, 17];
        let c: Kx = [3, 1, 4, 1, 5, 9];
        assert_eq!(k_mul(&k_mul(&a, &b), &c), k_mul(&a, &k_mul(&b, &c)));
        assert_eq!(
            k_mul(&a, &k_add(&b, &c)),
            k_add(&k_mul(&a, &b), &k_mul(&a, &c))
        );
        let x: Kx = [0, 1, 0, 0, 0, 0];
        let mut x6 = K_ONE;
        for _ in 0..6 {
            x6 = k_mul(&x6, &x);
        }
        assert_eq!(x6, k_base(7));
    }

    #[test]
    fn fold_tables_interpolate_exactly() {
        // A degree-7 polynomial over the base field, given at nodes 0..8, is
        // reproduced at the extra points and at an extension point.
        let poly = |t: u32| (0..8u32).fold(0u32, |acc, i| fq_add(fq_mul(acc, t), 1_000 + 37 * i));
        let tables = FoldTables::new();
        let values: Vec<Kx> = (0..8).map(|d| k_base(poly(d))).collect();
        for (offset, row) in tables.extra.iter().enumerate() {
            let got = eval_groups(&values, row, 1);
            assert_eq!(got[0], k_base(poly((FOLD + offset) as u32)));
        }
        let xi: Kx = [3, 5, 0, 1, 0, 2];
        let basis = tables.basis_at(&xi);
        let folded = fold_groups(&values, &basis, 1)[0];
        let mut expected = K_ZERO;
        for i in 0..8u32 {
            expected = k_add(&k_mul(&expected, &xi), &k_base(1_000 + 37 * i));
        }
        assert_eq!(folded, expected);
    }
}
