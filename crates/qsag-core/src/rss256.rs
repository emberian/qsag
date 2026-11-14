//! 256-lane bitsliced 2-of-3 replicated (`CNF`) `Keccak-f[1600]` engine with deferred,
//! transcript-bound active verification.
//!
//! Three parties hold a replicated sharing: share slot `j` is held by party `j` and party
//! `j - 1`. One *wave* evaluates up to 256 independent `Keccak-f[1600]` permutations at once;
//! bit `i` of every lane's state lives in one 256-bit plane, so each of the 1,600 chi ANDs per
//! round is one plane operation.
//!
//! ### AND gates
//! * **Mode 1B, inline (default).** Party `p` sends one masked product share per gate:
//!   `u_p = a_p (b_p + b_q) + a_q b_p + rho_p + rho_q` with `q = p + 1`, where `rho_j` is the
//!   pad stream of slot key `j`. Party `p` holds keys `p` and `p + 1`; the receiver `p - 1`
//!   holds `p - 1` and `p`, the remaining party holds `p + 1` and `p + 2`. Each observer is
//!   therefore missing one of the two pads, and no party ever holds both pads of a message it
//!   did not compute ([`sender_pad_slots`], [`slots_held_by`]).
//! * **Mode 1A, pre-staged bank.** A [`BeaverBank256`] of triples is produced and verified
//!   ahead of time with Mode 1B. Online, each gate opens two mask differences (two bits per
//!   gate and party instead of one) and no product proof runs online; the opened shares are
//!   checked for replica consistency at the barrier.
//!
//! ### Verification barrier ([`Rss256Engine::check`])
//! Nothing may be opened until the barrier has accepted every gate evaluated so far, and
//! [`Rss256Engine::open_planes`] refuses otherwise. The barrier:
//! 1. finalises, per sender, a hash of every gate message transmitted since the last barrier
//!    and requires both holders of each message stream to announce the same digest;
//! 2. runs a commit-then-open coin flip whose commitments are bound to that transcript digest,
//!    and derives `seed = SHAKE256("QSAG-WAVE-CHECK-v1" || transcript_digest || r_0 + r_1 + r_2)`;
//! 3. Mode 1B: runs the product proof described below under two independent challenges
//!    expanded from `seed`;
//!    Mode 1A: draws two independent `GF(2^128)` points from `seed` and compares, for every
//!    slot, the two holders' Horner evaluations of the opened mask-difference shares at both
//!    points (a mismatch survives with probability at most `(N / 2^128)^2` for `N` opened
//!    128-bit words).
//!
//! The challenges cannot be known while gate messages are being chosen: the coin shares are
//! committed after the messages are fixed and the commitment input contains their digest.
//!
//! Any failure of a barrier, of a coin flip or of an opening comparison poisons the engine:
//! the flag is set before any buffer is cleared, it is never reset, and every later
//! evaluation, check, coin or opening returns [`Rss256Error::Poisoned`].
//!
//! ### Product proof
//! Each party proves, to the other two, that every gate message it sent was computed from the
//! shares and pads it holds. For sender `p` with `q = p + 1`, verifier `V1 = p - 1` holds slot
//! `p` (`a_p`, `b_p`, `rho_p`) and the received message `u_p`; verifier `V2 = p + 1` holds
//! slot `q` (`a_q`, `b_q`, `rho_q`). The gate relation is
//! `(u_p + a_p b_p + rho_p) + rho_q = a_p b_q + a_q b_p`: a term `V1` computes alone, a term
//! `V2` computes alone, and an inner product between a vector `V1` holds and one `V2` holds.
//!
//! * **Batching.** Gate planes are grouped 128 at a time and each 256-lane plane is two
//!   128-bit blocks. Block `J` is weighted by `chi^J` and bit `i` of a block by `x^i`, so a
//!   block of 128 relations enters as one field element of
//!   `GF(2)[x] / (x^128 + x^7 + x^2 + x + 1)`. If any relation of the batch is false the
//!   weighted error is a nonzero polynomial in `chi` of degree below the number of blocks
//!   `B`, so it vanishes with probability at most `B / 2^128`.
//! * **Tensor round.** The seven plane-index bits inside a group are bound in one round: the
//!   prover sends the `3^7 - 1` sums of word ANDs over the points `{0, 1, slope}^7` (the
//!   remaining one follows from the claim), then seven challenges are drawn.
//! * **Folding rounds.** The bound vectors have one field element per lane and group. The
//!   first two rounds bind two index bits each (`k = 4`, `3^2 - 1` sums); every later round
//!   binds four (`k = 16`, `3^4 - 1` sums). After each round the challenges are drawn and
//!   both verifiers fold their own vectors.
//! * **Final check.** One element per vector remains. The prover sends the two cross
//!   coefficients of a masked product, a last challenge `tau` is drawn, and the verifiers
//!   exchange `r + tau * value` for their folded elements together with their claim shares.
//!
//! Every prover message is split additively between the two verifiers: `V1`'s share is the
//! output of the pad generator keyed by slot `p`, which `V2` does not hold, and `V2` receives
//! the difference. The final openings are masked by `r` values drawn from a slot key the
//! receiving verifier does not hold. Each verifier's view of a proof is therefore a one-time
//! pad of the prover's messages, like its view of the gate messages.
//!
//! One pass accepts a false batch with probability at most
//! `(B + 2 * 7 + 8 * R + 2) / 2^128` for `R` folding rounds (weights, tensor round,
//! folding rounds, final check). Two passes with independent `chi` and independent round
//! challenges run side by side and both must accept. A barrier over eight full waves has
//! `B = 614,400` and `R = 6`: below `2^-108` per pass and `2^-217` for the barrier.
//!
//! The corrupted party is the prover of exactly one proof, where both verifiers are honest.
//! As a verifier of another party's proof it can only cause an abort.
//!
//! ### What this module is not
//! The three parties run in one process here, and each share slot is stored once.
//! * A sender that deviates is modelled as changing the gate message itself: the value the
//!   receiver holds, uses from then on, and contributes to the product proof as `V1`. That
//!   is what the fault tests exercise.
//! * Replica comparisons run in every build. Opened shares and Mode 1A mask-difference
//!   streams are compared between two materialised copies, one per holder. A gate-message
//!   stream is hashed once, because both holders hold the same buffer in this process, and
//!   the comparison is between the two announced digests.
//! * Message routing, round counts and byte counts are tracked ([`WireStats`]) and can be
//!   priced against a network model, but no networked execution has been measured, and
//!   one-process time is not one party's time.

use alloc::boxed::Box;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use qsag_asm::{BitPlane256, KeccakState4x};

use crate::keccak_mpc::{KeccakMpcError, RssKeyShare256, RssSlhMpcCluster};
use crate::preprocessing::{PartyPrivateRng, PreprocessError, run_commit_and_open_coin_with_hook};
use crate::sponge::keccak::{
    Cshake256Xof, KECCAK_ROTATION_OFFSETS, KECCAK_ROUND_CONSTANTS, SHAKE256_RATE_BYTES,
};

/// One bit plane across the 256 lanes of a wave.
pub type Plane = BitPlane256;
/// Lanes per wave.
pub const LANES: usize = 256;
/// Bit planes per `Keccak-f[1600]` state.
pub const STATE_PLANES: usize = 1600;
/// Bit planes of a 32-byte value.
pub const DIGEST_PLANES: usize = 256;
/// Chi AND planes per permutation.
pub const AND_PLANES_PER_PERM: usize = 24 * STATE_PLANES;

const SHAKE256_RATE_WORDS: usize = SHAKE256_RATE_BYTES / 8;
const WORDS_PER_X4: usize = 4 * SHAKE256_RATE_WORDS;

/// Pad-stream purposes; the purpose is the top byte of the 64-bit PRG domain.
const PURPOSE_CHI_PAD: u64 = 1;
const PURPOSE_BANK_A: u64 = 2;
const PURPOSE_BANK_B: u64 = 3;
const PURPOSE_BANK_PAD: u64 = 4;
/// Product proof: the share of every prover message that verifier `V1` derives.
const PURPOSE_PROOF_SHARE: u64 = 5;
/// Product proof: masks of the final openings of `V1` and of `V2`.
const PURPOSE_PROOF_MASK_V1: u64 = 6;
const PURPOSE_PROOF_MASK_V2: u64 = 7;
/// Wave counters must leave the purpose byte free.
const MAX_WAVE_COUNTER: u64 = (1u64 << 56) - 1;

/// Share slots whose pad streams enter the gate message of sender `p`.
#[inline]
pub const fn sender_pad_slots(p: usize) -> [usize; 2] {
    [p % 3, (p + 1) % 3]
}

/// Share slots (and slot keys) held by `party`.
#[inline]
pub const fn slots_held_by(party: usize) -> [usize; 2] {
    [party % 3, (party + 1) % 3]
}

/// Masked product share of one plane word (see the module documentation).
#[inline(always)]
const fn and_message(a_p: u64, a_q: u64, b_p: u64, b_q: u64, pad_p: u64, pad_q: u64) -> u64 {
    (a_p & (b_p ^ b_q)) ^ (a_q & b_p) ^ pad_p ^ pad_q
}

/// Errors of the 256-lane engine. `InvalidParameters`, `OpenBeforeCheck`,
/// `BeaverBankExhausted` and a `WaveCounterOverflow` raised before any gate is evaluated leave
/// the engine usable. Every other error poisons it (see [`Rss256Error::Poisoned`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Rss256Error {
    InvalidParameters,
    /// Error from the shared key ceremony or the product proof.
    Mpc(KeccakMpcError),
    /// The two holders of a gate-message stream announced different transcript digests.
    TranscriptMismatch {
        slot: usize,
    },
    /// A coin-flip opening did not match its commitment.
    CoinOpeningRejected {
        party: usize,
    },
    /// The product proof rejected the gate messages of this barrier.
    MultiplicationCheckFailed,
    /// Mode 1A: two holders disagree on an opened mask-difference share.
    OpeningConsistencyFailed {
        slot: usize,
    },
    /// An opening was requested while unverified gates exist.
    OpenBeforeCheck,
    /// The two holders of an opened share sent different values.
    OpenShareMismatch {
        slot: usize,
    },
    /// Mode 1A was asked for more triples than were staged. Triples are never reused.
    BeaverBankExhausted,
    WaveCounterOverflow,
    /// A barrier, coin flip or opening comparison failed earlier in this session. The engine
    /// evaluates, checks and opens nothing from then on.
    Poisoned,
}

impl From<KeccakMpcError> for Rss256Error {
    fn from(e: KeccakMpcError) -> Self {
        Self::Mpc(e)
    }
}

impl fmt::Display for Rss256Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidParameters => f.write_str("invalid engine parameters"),
            Self::Mpc(e) => write!(f, "replicated engine error: {e}"),
            Self::TranscriptMismatch { slot } => {
                write!(f, "gate-message transcript mismatch on slot {slot}")
            }
            Self::CoinOpeningRejected { party } => {
                write!(f, "coin-flip opening of party {party} rejected")
            }
            Self::MultiplicationCheckFailed => f.write_str("multiplication check failed"),
            Self::OpeningConsistencyFailed { slot } => {
                write!(f, "mask-difference openings disagree on slot {slot}")
            }
            Self::OpenBeforeCheck => f.write_str("opening requested before the barrier check"),
            Self::OpenShareMismatch { slot } => write!(f, "opened share mismatch on slot {slot}"),
            Self::BeaverBankExhausted => f.write_str("staged triple bank exhausted"),
            Self::WaveCounterOverflow => f.write_str("wave counter overflow"),
            Self::Poisoned => f.write_str("engine poisoned by an earlier failed check"),
        }
    }
}

impl core::error::Error for Rss256Error {}

/// Counter-mode `SHAKE256` pad generator with explicit domain framing.
///
/// Block `c` is the first 136 bytes of `SHAKE256(key[32] || session_id[32] || domain_le[8] ||
/// counter_le[8])`. The domain and the counter are separate 64-bit fields of the absorbed
/// block, so no field can shift into or out of another, and streams with different keys,
/// sessions or domains never share a block input. Four blocks are produced per permutation.
pub struct Shake256Prg256 {
    base: [u64; 9],
    counter: u64,
    buf: KeccakState4x,
    next: usize,
}

impl Drop for Shake256Prg256 {
    fn drop(&mut self) {
        qsag_asm::volatile_fill(&mut self.base, 0);
        qsag_asm::volatile_fill(&mut self.buf.0, [0; 4]);
    }
}

impl Shake256Prg256 {
    pub fn new(key: &[u8; 32], session_id: &[u8; 32], domain: u64) -> Self {
        let mut base = [0u64; 9];
        for (word, chunk) in base[..4].iter_mut().zip(key.as_chunks::<8>().0) {
            *word = u64::from_le_bytes(*chunk);
        }
        for (word, chunk) in base[4..8].iter_mut().zip(session_id.as_chunks::<8>().0) {
            *word = u64::from_le_bytes(*chunk);
        }
        base[8] = domain;
        Self {
            base,
            counter: 0,
            buf: KeccakState4x::default(),
            next: WORDS_PER_X4,
        }
    }

    fn refill(&mut self) {
        for (lane, row) in self.buf.0.iter_mut().enumerate() {
            *row = match lane {
                0..=8 => [self.base[lane]; 4],
                9 => core::array::from_fn(|i| self.counter.wrapping_add(i as u64)),
                // SHAKE256 domain suffix after the 80 input bytes, and the final rate bit.
                10 => [0x1F; 4],
                16 => [1u64 << 63; 4],
                _ => [0; 4],
            };
        }
        qsag_asm::keccak_f1600_x4(&mut self.buf);
        self.counter = self.counter.wrapping_add(4);
        self.next = 0;
    }

    /// Fill `out` with the next stream words: word `w` of block `c` is word `c % 4` of rate
    /// lane `w` of the permutation that produced blocks `c - c % 4 ..`, read lane-major.
    pub fn fill_words(&mut self, out: &mut [u64]) {
        let mut written = 0usize;
        while written < out.len() {
            if self.next == WORDS_PER_X4 {
                self.refill();
            }
            let take = (WORDS_PER_X4 - self.next).min(out.len() - written);
            let rate = self.buf.0[..SHAKE256_RATE_WORDS].as_flattened();
            out[written..written + take].copy_from_slice(&rate[self.next..self.next + take]);
            self.next += take;
            written += take;
        }
    }

    /// Fill the low `words` words of every plane; the remaining words are set to zero.
    fn fill_planes(&mut self, out: &mut [Plane], words: usize) {
        for plane in out.iter_mut() {
            *plane = [0; 4];
            self.fill_words(&mut plane[..words]);
        }
    }
}

/// Four interleaved `SHAKE256`-rate sponges over 64-bit words, combined by one `SHAKE256`.
/// Used only to bind transmitted gate messages; word `k` goes to sponge `k % 4`.
struct TranscriptHasher4 {
    st: KeccakState4x,
    fill: usize,
    total: u64,
}

impl TranscriptHasher4 {
    fn new(label: u64, prev: &[u8; 32]) -> Self {
        let mut st = KeccakState4x::default();
        // Distinct capacity initialisation per sponge and per stream label.
        st.0[24] = core::array::from_fn(|i| (label << 8) | (i as u64 + 1));
        let mut h = Self {
            st,
            fill: 0,
            total: 0,
        };
        let mut words = [0u64; 4];
        for (w, chunk) in words.iter_mut().zip(prev.as_chunks::<8>().0) {
            *w = u64::from_le_bytes(*chunk);
        }
        // Each sponge absorbs the previous digest so barriers form a chain.
        for w in words {
            h.absorb_words(&[w; 4]);
        }
        h
    }

    #[inline]
    fn absorb_words(&mut self, words: &[u64]) {
        for &w in words {
            self.st.0[self.fill / 4][self.fill % 4] ^= w;
            self.fill += 1;
            if self.fill == WORDS_PER_X4 {
                qsag_asm::keccak_f1600_x4(&mut self.st);
                self.fill = 0;
            }
        }
        self.total = self.total.wrapping_add(words.len() as u64);
    }

    fn finalize(mut self) -> [u8; 32] {
        let total = self.total;
        // Length strengthening: pad to a block boundary, then one block holding the length.
        while self.fill != 0 {
            self.absorb_words(&[0]);
        }
        self.st.0[0] = core::array::from_fn(|i| self.st.0[0][i] ^ total);
        self.st.0[1] = core::array::from_fn(|i| self.st.0[1][i] ^ 0x1F);
        self.st.0[SHAKE256_RATE_WORDS - 1] =
            core::array::from_fn(|i| self.st.0[SHAKE256_RATE_WORDS - 1][i] ^ (1u64 << 63));
        qsag_asm::keccak_f1600_x4(&mut self.st);
        let mut xof = Cshake256Xof::new_shake256();
        xof.absorb(b"QSAG-WAVE-STREAM-v1");
        for lane in &self.st.0[..4] {
            for word in lane { xof.absorb(&word.to_le_bytes()); }
        }
        let mut out = [0u8; 32];
        xof.squeeze(&mut out);
        out
    }
}

fn boxed_planes<const N: usize>() -> Box<[Plane; N]> {
    Box::new([[0u64; 4]; N])
}

/// Lane mask with the low `lanes` bits set.
pub fn active_lane_mask(lanes: usize) -> Plane {
    core::array::from_fn(|w| {
        let lo = 64 * w;
        if lanes >= lo + 64 {
            u64::MAX
        } else if lanes > lo {
            (1u64 << (lanes - lo)) - 1
        } else {
            0
        }
    })
}

/// Replicated bitsliced state of one wave: `slot[j][i]` is share slot `j` of state bit `i`
/// across the 256 lanes. Wiped on drop.
pub struct SharedState256 {
    pub(crate) slot: [Box<[Plane; STATE_PLANES]>; 3],
}

impl Drop for SharedState256 {
    fn drop(&mut self) {
        for s in &mut self.slot {
            qsag_asm::volatile_fill(&mut s[..], [0; 4]);
        }
    }
}

impl SharedState256 {
    /// State whose every lane holds the public sponge state `midstate` xor that lane's public
    /// rate-block `frame`; lanes beyond `frames.len()` hold the bare midstate.
    pub fn from_public_frames(
        midstate: &[u64; 25],
        frames: &[[u8; SHAKE256_RATE_BYTES]],
    ) -> Result<Self, Rss256Error> {
        if frames.len() > LANES {
            return Err(Rss256Error::InvalidParameters);
        }
        let mut mid = [0u8; 200];
        for (chunk, word) in mid.as_chunks_mut::<8>().0.iter_mut().zip(midstate) {
            *chunk = word.to_le_bytes();
        }
        let mut states: Box<[[u8; 200]; LANES]> = Box::new([mid; LANES]);
        for (state, frame) in states.iter_mut().zip(frames) {
            for (dst, src) in state.iter_mut().zip(frame) {
                *dst ^= *src;
            }
        }
        let mut slot0 = boxed_planes::<STATE_PLANES>();
        qsag_asm::pack_256x200_bitslice(&states, &mut slot0);
        Ok(Self {
            slot: [slot0, boxed_planes(), boxed_planes()],
        })
    }

    /// Xor a shared 32-byte value into every lane at byte offset `byte_off`.
    pub fn xor_shared_digest(&mut self, byte_off: usize, value: &SharedDigest256) {
        debug_assert!(8 * byte_off + DIGEST_PLANES <= STATE_PLANES);
        for (dst, src) in self.slot.iter_mut().zip(&value.slot) {
            for (d, s) in dst[8 * byte_off..8 * byte_off + DIGEST_PLANES].iter_mut().zip(&src[..])
            {
                for (x, y) in d.iter_mut().zip(s) {
                    *x ^= *y;
                }
            }
        }
    }

    /// Xor one replicated 32-byte key into the lanes selected by `lane_mask` at byte offset
    /// `byte_off`; `key_slots[j]` is share slot `j` of the key.
    pub fn xor_shared_key(
        &mut self,
        byte_off: usize,
        key_slots: [&[u8]; 3],
        lane_mask: &Plane,
    ) -> Result<(), Rss256Error> {
        if key_slots.iter().any(|k| k.len() != 32) || byte_off + 32 > SHAKE256_RATE_BYTES {
            return Err(Rss256Error::InvalidParameters);
        }
        for (dst, key) in self.slot.iter_mut().zip(key_slots) {
            for (byte_idx, byte) in key.iter().enumerate() {
                for bit in 0..8 {
                    let take = 0u64.wrapping_sub(u64::from((byte >> bit) & 1));
                    let plane = &mut dst[8 * (byte_off + byte_idx) + bit];
                    for (x, m) in plane.iter_mut().zip(lane_mask) {
                        *x ^= take & m;
                    }
                }
            }
        }
        Ok(())
    }

    /// The first 32 bytes of every lane, still shared.
    pub fn digest(&self) -> SharedDigest256 {
        let mut out = SharedDigest256::zeroed();
        for (dst, src) in out.slot.iter_mut().zip(&self.slot) {
            dst.copy_from_slice(&src[..DIGEST_PLANES]);
        }
        out
    }
}

/// Replicated 32-byte value per lane, in bitsliced form. Wiped on drop.
pub struct SharedDigest256 {
    pub(crate) slot: [Box<[Plane; DIGEST_PLANES]>; 3],
}

impl Drop for SharedDigest256 {
    fn drop(&mut self) {
        for s in &mut self.slot {
            qsag_asm::volatile_fill(&mut s[..], [0; 4]);
        }
    }
}

impl SharedDigest256 {
    pub fn zeroed() -> Self {
        Self {
            slot: [boxed_planes(), boxed_planes(), boxed_planes()],
        }
    }

    /// `self ^= src` on the lanes selected by `lane_mask`.
    pub fn xor_masked(&mut self, src: &Self, lane_mask: &Plane) {
        for (dst, s) in self.slot.iter_mut().zip(&src.slot) {
            for (d, v) in dst.iter_mut().zip(&s[..]) {
                for ((x, y), m) in d.iter_mut().zip(v).zip(lane_mask) {
                    *x ^= *y & m;
                }
            }
        }
    }

    /// Replace the lanes selected by `lane_mask` with those of `src`.
    pub fn assign_masked(&mut self, src: &Self, lane_mask: &Plane) {
        for (dst, s) in self.slot.iter_mut().zip(&src.slot) {
            for (d, v) in dst.iter_mut().zip(&s[..]) {
                for ((x, y), m) in d.iter_mut().zip(v).zip(lane_mask) {
                    *x = (*x & !m) | (*y & m);
                }
            }
        }
    }
}

/// Convert opened digest planes into one 32-byte value per lane.
pub fn digests_from_planes(planes: &[Plane], lanes: usize) -> Vec<[u8; 32]> {
    debug_assert_eq!(planes.len(), DIGEST_PLANES);
    let mut out = vec![[0u8; 32]; lanes.min(LANES)];
    for (lane, digest) in out.iter_mut().enumerate() {
        for (i, plane) in planes.iter().enumerate() {
            let bit = ((plane[lane / 64] >> (lane % 64)) & 1) as u8;
            digest[i / 8] |= bit << (i % 8);
        }
    }
    out
}

/// AND-gate protocol of [`Rss256Engine::permute`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AndMode {
    /// Mode 1B: one masked product share per gate, verified at the barrier.
    InlineCnf,
    /// Mode 1A: pre-staged, pre-verified triples; two opened bits per gate online.
    BeaverBank,
}

/// Single-use bank of verified AND triples (Mode 1A). Each entry is consumed once and wiped.
pub struct BeaverBank256 {
    a: [Vec<Plane>; 3],
    b: [Vec<Plane>; 3],
    c: [Vec<Plane>; 3],
    cursor: usize,
}

impl Drop for BeaverBank256 {
    fn drop(&mut self) {
        for s in 0..3 {
            qsag_asm::volatile_fill(&mut self.a[s], [0; 4]);
            qsag_asm::volatile_fill(&mut self.b[s], [0; 4]);
            qsag_asm::volatile_fill(&mut self.c[s], [0; 4]);
        }
    }
}

impl BeaverBank256 {
    fn empty() -> Self {
        Self {
            a: [Vec::new(), Vec::new(), Vec::new()],
            b: [Vec::new(), Vec::new(), Vec::new()],
            c: [Vec::new(), Vec::new(), Vec::new()],
            cursor: 0,
        }
    }

    /// Plane triples not yet consumed.
    pub fn remaining_planes(&self) -> usize {
        self.a[0].len() - self.cursor
    }
}

/// Communication counters of one engine. Bytes are per party.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct WireStats {
    /// Sequentially dependent permutation levels declared by the caller (24 AND rounds each).
    pub perm_levels: u64,
    /// Lane-permutations evaluated online.
    pub lane_perms: u64,
    /// Online gate traffic.
    pub and_bytes: u64,
    /// Barrier checks run online.
    pub checks: u64,
    /// Of those, the barriers the caller placed at cut points; the others were forced by
    /// the memory bound.
    pub cut_checks: u64,
    /// Message hops of the barriers the caller placed at cut points. Cut barriers are
    /// sequential, so their hops add up, and inside one barrier the coin, the product proof
    /// and the Mode 1A comparison follow one another. A barrier forced by the memory bound in
    /// the middle of a sweep adds bytes but no hops: its proof opens nothing the following
    /// gate rounds wait for, and it is shorter than the 24 gate rounds of the level it
    /// overlaps.
    pub check_hops: u64,
    /// Barrier traffic.
    pub check_bytes: u64,
    /// Opening rounds.
    pub open_rounds: u64,
    /// Opening traffic.
    pub open_bytes: u64,
    /// Lane-permutations spent staging Mode 1A triples (offline).
    pub staged_lane_perms: u64,
    /// Offline traffic of staging, including its barrier.
    pub staged_bytes: u64,
    /// Triple material a party must hold for the staged bank (two of three slots).
    pub staged_state_bytes: u64,
}

impl WireStats {
    /// Online message hops: gate rounds, cut-barrier hops and opening rounds.
    pub const fn online_hops(&self) -> u64 {
        24 * self.perm_levels + self.check_hops + self.open_rounds
    }

    /// Online bytes sent by one party.
    pub const fn online_bytes(&self) -> u64 {
        self.and_bytes + self.check_bytes + self.open_bytes
    }
}

/// Adversarial deviations of one corrupted party, for tests.
#[cfg(test)]
#[derive(Clone, Copy, Debug)]
pub(crate) enum Fault256 {
    /// Xor `mask` into the gate message of `sender` at `(wave, round, plane)`.
    GateMessage {
        wave: u64,
        round: usize,
        plane: usize,
        sender: usize,
        mask: Plane,
    },
    /// Mode 1A: xor `mask` into the mask-difference share of `slot` that its forwarding
    /// holder reports at `(wave, round, plane)`.
    BeaverOpening {
        wave: u64,
        round: usize,
        plane: usize,
        slot: usize,
        mask: Plane,
    },
    /// `party` opens a coin share that differs from its commitment at the next barrier.
    CoinReveal { party: usize },
    /// One holder of `slot` announces a different transcript digest at the next barrier.
    TranscriptDigest { slot: usize },
    /// One holder of `slot` sends a different share of opened plane `plane`.
    OpenShare {
        slot: usize,
        plane: usize,
        mask: Plane,
    },
    /// `prover` sends a wrong value to `V2` in round `round` of proof pass `pass` (round 0
    /// is the tensor round; the last round carries the masked cross coefficients).
    ProofMessage {
        prover: usize,
        pass: usize,
        round: u32,
    },
}

/// Mode 1A opened mask-difference shares awaiting the consistency check: the stream of
/// each slot as each of its two holders reported it (two field words per plane).
struct OpenedShares {
    /// Copy of the primary holder (party `slot`).
    reference: [Vec<[u64; 2]>; 3],
    /// Copy the forwarding holder (party `slot - 1`) sent to the party that lacks the slot.
    forwarded: [Vec<[u64; 2]>; 3],
}

impl OpenedShares {
    fn new() -> Self {
        Self {
            reference: [Vec::new(), Vec::new(), Vec::new()],
            forwarded: [Vec::new(), Vec::new(), Vec::new()],
        }
    }

    fn is_empty(&self) -> bool {
        self.reference[0].is_empty()
    }

    fn clear(&mut self) {
        for s in 0..3 {
            qsag_asm::volatile_fill(&mut self.reference[s], [0; 2]);
            qsag_asm::volatile_fill(&mut self.forwarded[s], [0; 2]);
            self.reference[s].clear();
            self.forwarded[s].clear();
        }
    }
}

fn gf128_mul(a: [u64; 2], b: [u64; 2]) -> [u64; 2] {
    let mut acc = [0u64; 2];
    qsag_asm::gf2_128_mul_acc_batch(&mut acc, &[a], &[b]);
    acc
}

#[cfg(test)]
fn gf128_pow(base: [u64; 2], mut exp: usize) -> [u64; 2] {
    let mut result = [1u64, 0];
    let mut sq = base;
    while exp > 0 {
        if exp & 1 == 1 {
            result = gf128_mul(result, sq);
        }
        sq = gf128_mul(sq, sq);
        exp >>= 1;
    }
    result
}

const HORNER_CHUNK: usize = 512;

/// `sum_k words[k] * point^(n - k)` for `n = words.len()`.
fn horner_eval(words: &[[u64; 2]], point: [u64; 2]) -> [u64; 2] {
    // rev[i] = point^(HORNER_CHUNK - i)
    let mut rev = vec![[0u64; 2]; HORNER_CHUNK];
    let mut p = point;
    for slot in rev.iter_mut().rev() {
        *slot = p;
        p = gf128_mul(p, point);
    }
    let mut acc = [0u64; 2];
    for chunk in words.chunks(HORNER_CHUNK) {
        let pows = &rev[HORNER_CHUNK - chunk.len()..];
        acc = gf128_mul(acc, pows[0]);
        qsag_asm::gf2_128_mul_acc_batch(&mut acc, chunk, pows);
    }
    acc
}

// ---------------------------------------------------------------------------------------
// Product proof (see the module documentation)
// ---------------------------------------------------------------------------------------

/// Element of `GF(2)[x] / (x^128 + x^7 + x^2 + x + 1)`: `[low 64 coefficients, high 64]`.
type Fe = [u64; 2];
const FE_ZERO: Fe = [0, 0];
const FE_ONE: Fe = [1, 0];

/// Plane-index bits bound by the tensor round.
const TENSOR_BITS: usize = 7;
/// Gate planes per proof group.
const GROUP_PLANES: usize = 1 << TENSOR_BITS;
/// Points `{0, 1, slope}^TENSOR_BITS` of the tensor round.
const TENSOR_POINTS: usize = 3usize.pow(TENSOR_BITS as u32);
/// Index bits bound per folding round (`k = 16`).
const FOLD_BITS: usize = 4;
/// Index bits bound by each of the first folding rounds (`k = 4`), while the vectors still
/// hold more than [`WEIGHTED_BLOCK_ELEMS`] elements per block. A round over `b` bits costs
/// the prover `2 (3^b - 1) / 2^b` products per element: 4 for `b = 2`, 10 for `b = 4`. The
/// long vectors are therefore folded with the small arity and the short ones with `k = 16`.
const FIRST_FOLD_BITS: usize = 2;
/// Elements per block at which the block weights are multiplied into the vectors.
const WEIGHTED_BLOCK_ELEMS: usize = 8;
/// The tensor round's plane-index bits split into low bits, expanded per group and point
/// block, and high bits, expanded once per group.
const TENSOR_LOW_BITS: usize = 4;
const TENSOR_HIGH_BITS: usize = TENSOR_BITS - TENSOR_LOW_BITS;
const TENSOR_LOW_POINTS: usize = 3usize.pow(TENSOR_LOW_BITS as u32);
const TENSOR_HIGH_POINTS: usize = 3usize.pow(TENSOR_HIGH_BITS as u32);
/// Lanes of one 128-bit block; a block shares one batching weight.
const BLOCK_LANES: usize = 128;
/// Groups whose tensor products are multiplied by their weights in one kernel call.
const TENSOR_BATCH: usize = 32;
/// Chunks per kernel call of an unweighted folding round.
const FOLD_BATCH_CHUNKS: usize = 64;
/// Weighted batches accumulated before their weights are applied.
const WEIGHTED_FLUSH: usize = 64;

const _: () = assert!(LANES == 2 * BLOCK_LANES);
// Two first rounds bring a block from 128 elements to `WEIGHTED_BLOCK_ELEMS`, and a block
// is never split across the chunks of a weighted round.
const _: () = assert!(BLOCK_LANES >> (2 * FIRST_FOLD_BITS) == WEIGHTED_BLOCK_ELEMS);
const _: () = assert!(BLOCK_LANES >> FIRST_FOLD_BITS <= FOLD_BATCH_CHUNKS);

#[inline(always)]
fn fe_add(a: Fe, b: Fe) -> Fe {
    [a[0] ^ b[0], a[1] ^ b[1]]
}

fn fe_from_xof(xof: &mut Cshake256Xof) -> Fe {
    let mut raw = [0u8; 16];
    xof.squeeze(&mut raw);
    let [lo, hi] = *raw.as_chunks::<8>().0 else {
        unreachable!("16 bytes are two 8-byte chunks")
    };
    [u64::from_le_bytes(lo), u64::from_le_bytes(hi)]
}

/// `v * x^i` for `i < 128`.
#[inline]
fn fe_mul_x_pow(v: Fe, i: u32) -> Fe {
    debug_assert!(i < 128);
    let v = u128::from(v[0]) | (u128::from(v[1]) << 64);
    let low = v << i;
    // The coefficients pushed past x^127, as a polynomial of degree below `i`.
    let high = (v >> 1) >> (127 - i);
    // x^128 = x^7 + x^2 + x + 1; a second fold absorbs what the first pushes out again.
    let fold = |h: u128| h ^ (h << 1) ^ (h << 2) ^ (h << 7);
    let again = (high >> 127) ^ (high >> 126) ^ (high >> 121);
    let r = low ^ fold(high) ^ fold(again);
    [r as u64, (r >> 64) as u64]
}

/// Values that can be combined along the points `{0, 1, slope}`.
trait TensorCell: Copy {
    fn xor(self, other: Self) -> Self;
}

impl TensorCell for Fe {
    #[inline(always)]
    fn xor(self, other: Self) -> Self {
        fe_add(self, other)
    }
}

impl TensorCell for Plane {
    #[inline(always)]
    fn xor(self, other: Self) -> Self {
        [self[0] ^ other[0], self[1] ^ other[1], self[2] ^ other[2], self[3] ^ other[3]]
    }
}

/// Expand `2^bits` rows of `row` cells, indexed by the binary value `u`, into `3^bits` rows
/// indexed by `e = sum_l d_l 3^l` with digits `d_l` in `{0, 1, 2}`: digit `0` or `1` fixes bit
/// `l` of `u`, digit `2` is the sum of both. `buf` holds the input in its first `2^bits` rows
/// and must have room for `3^bits` rows.
fn ternary_expand<E: TensorCell>(buf: &mut [E], bits: usize, row: usize) {
    // Top bit first. A region of `3^level` rows holds `2^level` input rows; its two halves
    // go to the first and second third and their sum to the last third (which starts at or
    // beyond the end of the input). The thirds are the regions of the next level.
    let mut regions = 1usize;
    for level in (1..=bits).rev() {
        let half = (1usize << (level - 1)) * row;
        let third = 3usize.pow(level as u32 - 1) * row;
        for region in buf[..regions * 3 * third].chunks_exact_mut(3 * third) {
            let (input, sums) = region.split_at_mut(2 * third);
            let (low, high) = input[..2 * half].split_at(half);
            for ((sum, a), b) in sums[..half].iter_mut().zip(low).zip(high) {
                *sum = a.xor(*b);
            }
            region.copy_within(half..2 * half, third);
        }
        regions *= 3;
    }
}

/// Index of the point whose digits are the bits of `u`.
fn boolean_point(u: usize, bits: usize) -> usize {
    let mut idx = 0usize;
    let mut scale = 1usize;
    for l in 0..bits {
        idx += ((u >> l) & 1) * scale;
        scale *= 3;
    }
    idx
}

/// `eq[u] = prod_l (bit l of u ? gamma_l : 1 + gamma_l)`: the weights that bind `gammas.len()`
/// index bits of a vector.
fn eq_table(gammas: &[Fe]) -> Vec<Fe> {
    let mut eq = vec![FE_ZERO; 1 << gammas.len()];
    eq[0] = FE_ONE;
    for (l, gamma) in gammas.iter().enumerate() {
        let one_plus = fe_add(FE_ONE, *gamma);
        for u in 0..1usize << l {
            eq[u | (1 << l)] = gf128_mul(eq[u], *gamma);
            eq[u] = gf128_mul(eq[u], one_plus);
        }
    }
    eq
}

/// Coefficients of the round polynomial at the challenge point: entry `e` is
/// `prod_l basis(d_l, gamma_l)` with `basis(0) = 1 + gamma`, `basis(1) = gamma`,
/// `basis(2) = gamma + gamma^2`, so that `sum_e coeff[e] * s(e)` is the value at `gammas` of
/// the polynomial that is quadratic in every variable and has the sums `s`.
fn round_coefficients(gammas: &[Fe]) -> Vec<Fe> {
    let mut coeff = vec![FE_ONE];
    for gamma in gammas {
        let basis = [
            fe_add(FE_ONE, *gamma),
            *gamma,
            fe_add(*gamma, gf128_mul(*gamma, *gamma)),
        ];
        let mut next = Vec::with_capacity(3 * coeff.len());
        for b in basis {
            next.extend(coeff.iter().map(|c| gf128_mul(*c, b)));
        }
        coeff = next;
    }
    coeff
}

/// One verifier's share of the claim after a round. `share[e]` is its share of the sum at
/// point `e >= 1`; the sum at point `0` follows from the incoming claim
/// `sum_u weight(u) * s(point(u))` over the Boolean points, with `weight(0) = 1`. The new
/// claim is the value at the challenge point of the polynomial with those sums.
fn next_claim(claim: Fe, share: &[Fe], boolean_weights: &[(usize, Fe)], coeff: &[Fe]) -> Fe {
    let mut s0 = claim;
    for (point, weight) in boolean_weights {
        s0 = fe_add(s0, gf128_mul(*weight, share[*point]));
    }
    let mut acc = gf128_mul(coeff[0], s0);
    qsag_asm::gf2_128_mul_acc_batch(&mut acc, &share[1..], &coeff[1..]);
    acc
}

/// Batching weights of one proof pass.
struct PassWeights {
    /// `chi^u` for the plane index `u` inside a group.
    plane: [Fe; GROUP_PLANES],
    /// `(chi^128)^j` for block `j = 2 * group + half`.
    block: Vec<Fe>,
}

impl PassWeights {
    fn new(chi: Fe, blocks: usize) -> Self {
        let mut plane = [FE_ONE; GROUP_PLANES];
        for u in 1..GROUP_PLANES {
            plane[u] = gf128_mul(plane[u - 1], chi);
        }
        let kappa = gf128_mul(plane[GROUP_PLANES - 1], chi);
        let mut block = vec![FE_ONE; blocks];
        for j in 1..blocks {
            block[j] = gf128_mul(block[j - 1], kappa);
        }
        Self { plane, block }
    }

    /// `(point, chi^u)` for every nonzero plane index `u`.
    fn boolean_weights(&self) -> Vec<(usize, Fe)> {
        (1..GROUP_PLANES)
            .map(|u| (boolean_point(u, TENSOR_BITS), self.plane[u]))
            .collect()
    }
}

/// Gate relations recorded since the last barrier, one entry per AND plane and share slot:
/// the input shares, the gate message of sender `slot`, and the pad plane of slot `slot`.
/// Lanes outside the wave are zero in all four, which satisfies the relation.
struct PendingGates {
    a: [Vec<Plane>; 3],
    b: [Vec<Plane>; 3],
    msg: [Vec<Plane>; 3],
    pad: [Vec<Plane>; 3],
}

impl PendingGates {
    fn new() -> Self {
        Self {
            a: [Vec::new(), Vec::new(), Vec::new()],
            b: [Vec::new(), Vec::new(), Vec::new()],
            msg: [Vec::new(), Vec::new(), Vec::new()],
            pad: [Vec::new(), Vec::new(), Vec::new()],
        }
    }

    /// Recorded gate planes.
    fn len(&self) -> usize {
        self.a[0].len()
    }

    fn clear_and_wipe(&mut self) {
        for s in 0..3 {
            for planes in [&mut self.a[s], &mut self.b[s], &mut self.msg[s], &mut self.pad[s]] {
                qsag_asm::volatile_fill(planes, [0; 4]);
                planes.clear();
            }
        }
    }

    fn pad_to_group(&mut self) {
        let padded = self.len().div_ceil(GROUP_PLANES) * GROUP_PLANES;
        for s in 0..3 {
            for planes in [&mut self.a[s], &mut self.b[s], &mut self.msg[s], &mut self.pad[s]] {
                planes.resize(padded, [0; 4]);
            }
        }
    }
}

impl Drop for PendingGates {
    fn drop(&mut self) {
        self.clear_and_wipe();
    }
}

/// Weighted single-verifier terms of both passes: entry `[pass][slot]` is
/// `[sum_J chi^J block_J(msg + pad + a & b), sum_J chi^J block_J(pad)]` over slot `slot`. The
/// first is the initial claim share of `V1` in the proof of sender `slot`; the second is the
/// initial claim share of `V2` in the proof of sender `slot - 1`.
fn linear_terms(
    pending: &PendingGates,
    groups: usize,
    weights: &[PassWeights; 2],
) -> [[[Fe; 2]; 3]; 2] {
    let mut out = [[[FE_ZERO; 2]; 3]; 2];
    let mut half = [FE_ZERO; GROUP_PLANES];
    let mut sums: [[Vec<Fe>; 2]; 2] =
        core::array::from_fn(|_| core::array::from_fn(|_| vec![FE_ZERO; 2 * groups]));
    for s in 0..3 {
        for pass in &mut sums {
            for term in pass.iter_mut() {
                term.fill(FE_ZERO);
            }
        }
        for g in 0..groups {
            let base = g * GROUP_PLANES;
            for h in 0..2 {
                for (u, cell) in half.iter_mut().enumerate() {
                    let (m, r) = (&pending.msg[s][base + u], &pending.pad[s][base + u]);
                    let (a, b) = (&pending.a[s][base + u], &pending.b[s][base + u]);
                    *cell = core::array::from_fn(|w| {
                        m[2 * h + w] ^ r[2 * h + w] ^ (a[2 * h + w] & b[2 * h + w])
                    });
                }
                for (pass, w) in sums.iter_mut().zip(weights) {
                    qsag_asm::gf2_128_mul_acc_batch(&mut pass[0][2 * g + h], &half, &w.plane);
                }
                for (u, cell) in half.iter_mut().enumerate() {
                    let r = &pending.pad[s][base + u];
                    *cell = [r[2 * h], r[2 * h + 1]];
                }
                for (pass, w) in sums.iter_mut().zip(weights) {
                    qsag_asm::gf2_128_mul_acc_batch(&mut pass[1][2 * g + h], &half, &w.plane);
                }
            }
        }
        for (k, (pass, w)) in sums.iter().zip(weights).enumerate() {
            for (term, sum) in pass.iter().enumerate() {
                qsag_asm::gf2_128_mul_acc_batch(&mut out[k][s][term], sum, &w.block);
            }
        }
    }
    qsag_asm::volatile_fill(&mut half, FE_ZERO);
    for pass in &mut sums {
        for term in pass.iter_mut() {
            qsag_asm::volatile_fill(term, FE_ZERO);
        }
    }
    out
}

/// Tensor-round sums of every prover for both passes: entry `[pass][p][e]` is
/// `sum_g (kappa^(2g) T_lo + kappa^(2g + 1) T_hi)` where `T = a_p,e & b_q,e ^ a_q,e & b_p,e`
/// is the cross product of group `g` at point `e` (each operand is the GF(2) combination of
/// the group's 128 planes selected by `e`) and `T_lo`, `T_hi` are its two 128-bit blocks read
/// as field elements. Point `0` is left zero: it is never sent.
///
/// A group is expanded on its three high index bits once (27 rows of 16 planes). For each of
/// those rows the 16 planes of every group of a batch are expanded together on the four low
/// bits (81 points), the products are staged point by point, and one kernel call per point,
/// prover and pass applies the block weights.
fn tensor_tables(
    pending: &PendingGates,
    groups: usize,
    weights: &[PassWeights; 2],
) -> [[Vec<Fe>; 3]; 2] {
    const LOW_PLANES: usize = 1 << TENSOR_LOW_BITS;
    const HIGH_CELLS: usize = TENSOR_HIGH_POINTS * LOW_PLANES;
    let mut tabs: [[Vec<Fe>; 3]; 2] =
        core::array::from_fn(|_| core::array::from_fn(|_| vec![FE_ZERO; TENSOR_POINTS]));
    let mut high_a: [Vec<Plane>; 3] =
        core::array::from_fn(|_| vec![[0u64; 4]; TENSOR_BATCH * HIGH_CELLS]);
    let mut high_b: [Vec<Plane>; 3] =
        core::array::from_fn(|_| vec![[0u64; 4]; TENSOR_BATCH * HIGH_CELLS]);
    // Low-bit expansions of one high point: row `j` holds point `j` of every group of the batch.
    let low_cells = TENSOR_LOW_POINTS * TENSOR_BATCH;
    let mut low_a: [Vec<Plane>; 3] = core::array::from_fn(|_| vec![[0u64; 4]; low_cells]);
    let mut low_b: [Vec<Plane>; 3] = core::array::from_fn(|_| vec![[0u64; 4]; low_cells]);
    let row = 2 * TENSOR_BATCH;
    let mut stage: [Vec<Fe>; 3] =
        core::array::from_fn(|_| vec![FE_ZERO; TENSOR_LOW_POINTS * row]);
    for g0 in (0..groups).step_by(TENSOR_BATCH) {
        let count = TENSOR_BATCH.min(groups - g0);
        for gi in 0..count {
            let base = (g0 + gi) * GROUP_PLANES;
            let cells = gi * HIGH_CELLS..(gi + 1) * HIGH_CELLS;
            for s in 0..3 {
                for (src, dst) in [(&pending.a[s], &mut high_a[s]), (&pending.b[s], &mut high_b[s])] {
                    let dst = &mut dst[cells.clone()];
                    dst[..GROUP_PLANES].copy_from_slice(&src[base..base + GROUP_PLANES]);
                    ternary_expand(dst, TENSOR_HIGH_BITS, LOW_PLANES);
                }
            }
        }
        for h in 0..TENSOR_HIGH_POINTS {
            for s in 0..3 {
                for (high, low) in [(&high_a[s], &mut low_a[s]), (&high_b[s], &mut low_b[s])] {
                    for u in 0..LOW_PLANES {
                        for gi in 0..count {
                            low[u * count + gi] = high[gi * HIGH_CELLS + h * LOW_PLANES + u];
                        }
                    }
                    ternary_expand(&mut low[..TENSOR_LOW_POINTS * count], TENSOR_LOW_BITS, count);
                }
            }
            for (p, staged) in stage.iter_mut().enumerate() {
                let q = (p + 1) % 3;
                for j in 0..TENSOR_LOW_POINTS {
                    let cells = j * count..(j + 1) * count;
                    let (ap, aq) = (&low_a[p][cells.clone()], &low_a[q][cells.clone()]);
                    let (bp, bq) = (&low_b[p][cells.clone()], &low_b[q][cells]);
                    let out = staged[j * row..j * row + 2 * count].as_chunks_mut::<2>().0;
                    for ((((t, ap), aq), bp), bq) in out.iter_mut().zip(ap).zip(aq).zip(bp).zip(bq) {
                        let v: Plane = core::array::from_fn(|w| (ap[w] & bq[w]) ^ (aq[w] & bp[w]));
                        *t = [[v[0], v[1]], [v[2], v[3]]];
                    }
                }
            }
            for (p, staged) in stage.iter().enumerate() {
                for j in 0..TENSOR_LOW_POINTS {
                    let e = TENSOR_LOW_POINTS * h + j;
                    if e == 0 {
                        continue;
                    }
                    let products = &staged[j * row..j * row + 2 * count];
                    for (tab, w) in tabs.iter_mut().zip(weights) {
                        qsag_asm::gf2_128_mul_acc_batch(
                            &mut tab[p][e],
                            products,
                            &w.block[2 * g0..2 * (g0 + count)],
                        );
                    }
                }
            }
        }
    }
    for s in 0..3 {
        qsag_asm::volatile_fill(&mut high_a[s], [0; 4]);
        qsag_asm::volatile_fill(&mut high_b[s], [0; 4]);
        qsag_asm::volatile_fill(&mut low_a[s], [0; 4]);
        qsag_asm::volatile_fill(&mut low_b[s], [0; 4]);
        qsag_asm::volatile_fill(&mut stage[s], FE_ZERO);
    }
    tabs
}

/// Bind the plane index inside every group: element `256 g + lane` of `out` is
/// `sum_u eq[u] * bit(planes[128 g + u], lane)`, times `x^(lane % 128)` when `lane_weights`.
///
/// The sum is a GF(2)-linear map of the 128 planes with a public matrix (the bits of `eq`),
/// evaluated on all 256 lanes at once: output bit plane `t` is the XOR of the planes `u` with
/// bit `t` of `eq[u]` set, taken four planes at a time from tables of their 16 combinations.
/// Table indices and loop bounds depend only on `eq`.
fn bind_planes(planes: &[Plane], eq: &[Fe], lane_weights: bool, out: &mut [Fe]) {
    const NIBBLES: usize = GROUP_PLANES / 4;
    debug_assert_eq!(eq.len(), GROUP_PLANES);
    debug_assert_eq!(planes.len() / GROUP_PLANES * LANES, out.len());
    // `pattern[t][n]`: which of planes `4n .. 4n + 4` enter output bit plane `t`.
    let mut pattern = [[0u8; NIBBLES]; 128];
    for (t, row) in pattern.iter_mut().enumerate() {
        for (n, nibble) in row.iter_mut().enumerate() {
            for d in 0..4 {
                *nibble |= (((eq[4 * n + d][t / 64] >> (t % 64)) & 1) as u8) << d;
            }
        }
    }
    let mut tables = [[[0u64; 4]; 16]; NIBBLES];
    let mut lo = [[0u64; 4]; 64];
    let mut hi = [[0u64; 4]; 64];
    let groups = planes.as_chunks::<GROUP_PLANES>().0.iter();
    for (src, dst) in groups.zip(out.as_chunks_mut::<LANES>().0) {
        for (n, table) in tables.iter_mut().enumerate() {
            for v in 1..16usize {
                let rest = table[v & (v - 1)];
                table[v] = rest.xor(src[4 * n + v.trailing_zeros() as usize]);
            }
        }
        for (t, row) in pattern.iter().enumerate() {
            let mut acc = [0u64; 4];
            for (table, nibble) in tables.iter().zip(row) {
                acc = acc.xor(table[usize::from(*nibble & 15)]);
            }
            if t < 64 {
                lo[t] = acc;
            } else {
                hi[t - 64] = acc;
            }
        }
        // Bit `r` of `lo[c][q]` becomes bit `c` of output plane `r`, word `q`: the low half
        // of the element of lane `64 q + c`.
        qsag_asm::transpose64x256(&mut lo);
        qsag_asm::transpose64x256(&mut hi);
        for q in 0..4 {
            for c in 0..64 {
                let lane = 64 * q + c;
                let v = [lo[c][q], hi[c][q]];
                dst[lane] = if lane_weights {
                    fe_mul_x_pow(v, (lane % BLOCK_LANES) as u32)
                } else {
                    v
                };
            }
        }
    }
    qsag_asm::volatile_fill(&mut tables, [[0; 4]; 16]);
    qsag_asm::volatile_fill(&mut lo, [0; 4]);
    qsag_asm::volatile_fill(&mut hi, [0; 4]);
}

/// Scratch of [`fold_round_sums`]: the expansions of both vectors of every slot.
struct FoldScratch {
    ex: [Vec<Fe>; 3],
    ey: [Vec<Fe>; 3],
    pending: Vec<Fe>,
}

impl FoldScratch {
    fn new() -> Self {
        let cells = 3usize.pow(FOLD_BITS as u32) * FOLD_BATCH_CHUNKS;
        Self {
            ex: core::array::from_fn(|_| vec![FE_ZERO; cells]),
            ey: core::array::from_fn(|_| vec![FE_ZERO; cells]),
            pending: Vec::new(),
        }
    }
}

impl Drop for FoldScratch {
    fn drop(&mut self) {
        for s in 0..3 {
            qsag_asm::volatile_fill(&mut self.ex[s], FE_ZERO);
            qsag_asm::volatile_fill(&mut self.ey[s], FE_ZERO);
        }
        qsag_asm::volatile_fill(&mut self.pending, FE_ZERO);
    }
}

/// Sums of one folding round over the low `bits` index bits of the vectors `x`, `y` of
/// length `len`: entry `[p][e]` is
/// `sum_c w_c (x_p,e[c] * y_q,e[c] + x_q,e[c] * y_p,e[c])` over the chunks `c` of `2^bits`
/// elements, where `v_e[c]` combines the chunk's elements as point `e` prescribes.
/// Chunks are processed `batch_chunks` at a time; with `batch_weights`, batch `b` carries the
/// weight `batch_weights[b]`, otherwise every weight is one. Point `0` is left zero.
fn fold_round_sums(
    x: &[Vec<Fe>; 3],
    y: &[Vec<Fe>; 3],
    len: usize,
    bits: usize,
    batch_chunks: usize,
    batch_weights: Option<&[Fe]>,
    scratch: &mut FoldScratch,
) -> [Vec<Fe>; 3] {
    debug_assert!(bits <= FOLD_BITS && batch_chunks <= FOLD_BATCH_CHUNKS);
    let points = 3usize.pow(bits as u32);
    let size = 1usize << bits;
    let chunks = len.div_ceil(size);
    let batches = chunks.div_ceil(batch_chunks);
    let mut tabs: [Vec<Fe>; 3] = core::array::from_fn(|_| vec![FE_ZERO; points]);
    let FoldScratch { ex, ey, pending } = scratch;
    pending.clear();
    pending.resize(3 * points * WEIGHTED_FLUSH, FE_ZERO);
    let row = batch_chunks;
    for b in 0..batches {
        let c0 = b * batch_chunks;
        for s in 0..3 {
            for (src, dst) in [(&x[s], &mut ex[s]), (&y[s], &mut ey[s])] {
                for u in 0..size {
                    for k in 0..row {
                        let idx = (c0 + k) * size + u;
                        dst[u * row + k] = if idx < len { src[idx] } else { FE_ZERO };
                    }
                }
                ternary_expand(&mut dst[..points * row], bits, row);
            }
        }
        let slot = b % WEIGHTED_FLUSH;
        for p in 0..3 {
            let q = (p + 1) % 3;
            for e in 1..points {
                let cells = e * row..(e + 1) * row;
                let mut acc = FE_ZERO;
                qsag_asm::gf2_128_mul_acc_batch(&mut acc, &ex[p][cells.clone()], &ey[q][cells.clone()]);
                qsag_asm::gf2_128_mul_acc_batch(&mut acc, &ex[q][cells.clone()], &ey[p][cells]);
                if batch_weights.is_some() {
                    pending[(p * points + e) * WEIGHTED_FLUSH + slot] = acc;
                } else {
                    tabs[p][e] = fe_add(tabs[p][e], acc);
                }
            }
        }
        if let Some(weights) = batch_weights
            && (slot + 1 == WEIGHTED_FLUSH || b + 1 == batches)
        {
            let first = b - slot;
            for (p, tab) in tabs.iter_mut().enumerate() {
                for (e, sum) in tab.iter_mut().enumerate().skip(1) {
                    let o = (p * points + e) * WEIGHTED_FLUSH;
                    qsag_asm::gf2_128_mul_acc_batch(
                        sum,
                        &pending[o..o + slot + 1],
                        &weights[first..first + slot + 1],
                    );
                }
            }
        }
    }
    tabs
}

/// Bind the low `eq.len().ilog2()` index bits of `v[..len]` in place and return the new length.
fn fold_vector(v: &mut [Fe], len: usize, eq: &[Fe]) -> usize {
    let size = eq.len();
    let chunks = len.div_ceil(size);
    for c in 0..chunks {
        let lo = c * size;
        let hi = (lo + size).min(len);
        let mut acc = FE_ZERO;
        qsag_asm::gf2_128_mul_acc_batch(&mut acc, &v[lo..hi], &eq[..hi - lo]);
        v[c] = acc;
    }
    qsag_asm::volatile_fill(&mut v[chunks..len], FE_ZERO);
    chunks
}

/// Bytes one party sends in the product proof of one barrier and the message hops it takes,
/// for `rounds` folding rounds after the tensor round with `sums` prover values in total per
/// pass. A round is one hop carrying the prover values together with the commitments of the
/// next coin, and one hop opening that coin. The final check is three hops: the masked cross
/// coefficients with coin commitments, the coin opening, and the verifiers' openings.
fn product_proof_cost(rounds: u64, sums: u64) -> (u64, u64) {
    let per_pass = 16 * (sums + 2) + 6 * 16;
    let coins = 64 * (1 + rounds + 1);
    (2 * (per_pass + coins), 2 * (2 * (1 + rounds) + 3))
}

/// What one party observes of the product proofs it verifies, for tests: the shares it is
/// sent as `V2` and the openings it receives from the other verifier.
#[cfg(test)]
#[derive(Default)]
pub(crate) struct ProofView {
    pub(crate) received: [Vec<Fe>; 3],
}

/// The 256-lane replicated engine (see the module documentation).
