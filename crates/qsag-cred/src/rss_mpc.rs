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
