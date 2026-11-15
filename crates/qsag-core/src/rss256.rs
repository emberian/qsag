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
    Cshake256WordStream4, Cshake256Xof, KECCAK_ROTATION_OFFSETS, KECCAK_ROUND_CONSTANTS,
    SHAKE256_RATE_BYTES, SHAKE256_RATE_LANES,
};
use crate::wipe::{
    SecretBuffer, secret_vec_extend_from_slice, secret_vec_push, secret_vec_reserve,
};

#[cfg(feature = "std")]
#[inline]
fn rss256_worker_threads() -> usize {
    std::thread::available_parallelism()
        .map(|n| n.get().clamp(1, 16))
        .unwrap_or(1)
}

/// One bit plane across the 256 lanes of a wave.
pub type Plane = BitPlane256;
/// Lanes per wave.
pub const LANES: usize = qsag_asm::BITSLICE_LANES;
/// Bit planes per `Keccak-f[1600]` state.
pub const STATE_PLANES: usize = qsag_asm::KECCAK_STATE_BITS;
/// Bit planes of a 32-byte value.
pub const DIGEST_PLANES: usize = 256;
/// Chi AND planes per permutation.
pub const AND_PLANES_PER_PERM: usize = 24 * STATE_PLANES;

const WORDS_PER_X4: usize = Cshake256WordStream4::WORDS_PER_BLOCK;

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
    exhausted: bool,
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
            exhausted: false,
            buf: KeccakState4x::default(),
            next: WORDS_PER_X4,
        }
    }

    fn refill(&mut self) {
        assert!(
            !self.exhausted,
            "Shake256Prg256: 64-bit block counter exhausted"
        );
        if self.counter > u64::MAX - 3 {
            self.exhausted = true;
            panic!("Shake256Prg256: 64-bit block counter overflow");
        }
        for (lane, row) in self.buf.0.iter_mut().enumerate() {
            *row = match lane {
                0..=8 => [self.base[lane]; 4],
                9 => core::array::from_fn(|i| self.counter + (i as u64)),
                // SHAKE256 domain suffix after the 80 input bytes, and the final rate bit.
                10 => [0x1F; 4],
                16 => [1u64 << 63; 4],
                _ => [0; 4],
            };
        }
        qsag_asm::keccak_f1600_x4(&mut self.buf);
        match self.counter.checked_add(4) {
            Some(next) => self.counter = next,
            None => self.exhausted = true,
        }
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
            let rate = self.buf.0[..SHAKE256_RATE_LANES].as_flattened();
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
        self.st.0[SHAKE256_RATE_LANES - 1] =
            core::array::from_fn(|i| self.st.0[SHAKE256_RATE_LANES - 1][i] ^ (1u64 << 63));
        qsag_asm::keccak_f1600_x4(&mut self.st);
        let mut xof = Cshake256Xof::new_shake256();
        xof.absorb(b"QSAG-WAVE-STREAM-v1");
        for lane in &self.st.0[..4] {
            for word in lane {
                xof.absorb(&word.to_le_bytes());
            }
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
    pub fn xor_shared_digest(
        &mut self,
        byte_off: usize,
        value: &SharedDigest256,
    ) -> Result<(), Rss256Error> {
        if byte_off > (STATE_PLANES / 8) - 32 {
            return Err(Rss256Error::InvalidParameters);
        }
        let bit_off = 8 * byte_off;
        for (dst, src) in self.slot.iter_mut().zip(&value.slot) {
            for (d, s) in dst[bit_off..bit_off + DIGEST_PLANES]
                .iter_mut()
                .zip(&src[..])
            {
                for (x, y) in d.iter_mut().zip(s) {
                    *x ^= *y;
                }
            }
        }
        Ok(())
    }

    /// Xor one replicated 32-byte key into the lanes selected by `lane_mask` at byte offset
    /// `byte_off`; `key_slots[j]` is share slot `j` of the key.
    pub fn xor_shared_key(
        &mut self,
        byte_off: usize,
        key_slots: [&[u8]; 3],
        lane_mask: &Plane,
    ) -> Result<(), Rss256Error> {
        if key_slots.iter().any(|k| k.len() != 32) || byte_off > SHAKE256_RATE_BYTES - 32 {
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
pub fn digests_from_planes(planes: &[Plane], lanes: usize) -> Result<Vec<[u8; 32]>, Rss256Error> {
    if planes.len() != DIGEST_PLANES {
        return Err(Rss256Error::InvalidParameters);
    }
    let mut out = vec![[0u8; 32]; lanes.min(LANES)];
    for (lane, digest) in out.iter_mut().enumerate() {
        for (i, plane) in planes.iter().enumerate() {
            let bit = ((plane[lane / 64] >> (lane % 64)) & 1) as u8;
            digest[i / 8] |= bit << (i % 8);
        }
    }
    Ok(out)
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
        [
            self[0] ^ other[0],
            self[1] ^ other[1],
            self[2] ^ other[2],
            self[3] ^ other[3],
        ]
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
            for planes in [
                &mut self.a[s],
                &mut self.b[s],
                &mut self.msg[s],
                &mut self.pad[s],
            ] {
                qsag_asm::volatile_fill(planes, [0; 4]);
                planes.clear();
            }
        }
    }

    fn pad_to_group(&mut self) {
        let padded = self.len().div_ceil(GROUP_PLANES) * GROUP_PLANES;
        for s in 0..3 {
            for planes in [
                &mut self.a[s],
                &mut self.b[s],
                &mut self.msg[s],
                &mut self.pad[s],
            ] {
                secret_vec_reserve(planes, padded.saturating_sub(planes.len()));
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

fn linear_terms_slot_range(
    pending: &PendingGates,
    s: usize,
    g_range: core::ops::Range<usize>,
    weights: &[PassWeights; 2],
) -> [[Fe; 2]; 2] {
    let mut slot_out = [[FE_ZERO; 2]; 2];
    if g_range.is_empty() {
        return slot_out;
    }
    let chunk_groups = g_range.len();
    let mut half = SecretBuffer([FE_ZERO; GROUP_PLANES]);
    let mut sums = SecretBuffer(core::array::from_fn::<[Vec<Fe>; 2], 2, _>(|_| {
        core::array::from_fn(|_| vec![FE_ZERO; 2 * chunk_groups])
    }));
    let a_slot = &pending.a[s];
    for (local_g, g) in g_range.clone().enumerate() {
        let base = g * GROUP_PLANES;
        for h in 0..2 {
            for (u, cell) in half.iter_mut().enumerate() {
                let (m, r) = (&pending.msg[s][base + u], &pending.pad[s][base + u]);
                let (a, b) = (&a_slot[base + u], &pending.b[s][base + u]);
                *cell = core::array::from_fn(|w| {
                    m[2 * h + w] ^ r[2 * h + w] ^ (a[2 * h + w] & b[2 * h + w])
                });
            }
            for (pass, w) in sums.iter_mut().zip(weights) {
                qsag_asm::gf2_128_mul_acc_batch(&mut pass[0][2 * local_g + h], &*half, &w.plane);
            }
            for (u, cell) in half.iter_mut().enumerate() {
                let r = &pending.pad[s][base + u];
                *cell = [r[2 * h], r[2 * h + 1]];
            }
            for (pass, w) in sums.iter_mut().zip(weights) {
                qsag_asm::gf2_128_mul_acc_batch(&mut pass[1][2 * local_g + h], &*half, &w.plane);
            }
        }
    }
    let blk_slice = (2 * g_range.start)..(2 * g_range.end);
    for (k, (pass, w)) in sums.iter().zip(weights).enumerate() {
        for (term, sum) in pass.iter().enumerate() {
            qsag_asm::gf2_128_mul_acc_batch(
                &mut slot_out[k][term],
                sum,
                &w.block[blk_slice.clone()],
            );
        }
    }
    slot_out
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
    if groups == 0 {
        return out;
    }
    #[cfg(feature = "std")]
    {
        let workers = rss256_worker_threads();
        if workers > 1 && groups >= 16 {
            let chunks_per_slot = (workers / 3).max(1).min(groups);
            let chunk_size = groups.div_ceil(chunks_per_slot);
            let partials: Vec<(usize, [[Fe; 2]; 2])> = std::thread::scope(|scope| {
                let mut handles = Vec::with_capacity(3 * chunks_per_slot);
                for s in 0..3 {
                    for c in 0..chunks_per_slot {
                        let start = c * chunk_size;
                        if start >= groups {
                            break;
                        }
                        let end = (start + chunk_size).min(groups);
                        handles.push(scope.spawn(move || {
                            (s, linear_terms_slot_range(pending, s, start..end, weights))
                        }));
                    }
                }
                handles
                    .into_iter()
                    .map(|h| h.join().expect("rss256 linear_terms worker panicked"))
                    .collect()
            });
            let partials = SecretBuffer(partials);
            for &(s, part) in partials.iter() {
                for k in 0..2 {
                    for term in 0..2 {
                        out[k][s][term] = fe_add(out[k][s][term], part[k][term]);
                    }
                }
            }
            return out;
        }
    }
    #[expect(
        clippy::needless_range_loop,
        reason = "Transpose two proof terms into three party slots"
    )]
    for s in 0..3 {
        let part = linear_terms_slot_range(pending, s, 0..groups, weights);
        for k in 0..2 {
            out[k][s] = part[k];
        }
    }
    out
}

fn tensor_tables_batch_range(
    pending: &PendingGates,
    groups: usize,
    batch_range: core::ops::Range<usize>,
    weights: &[PassWeights; 2],
) -> [[Vec<Fe>; 3]; 2] {
    const LOW_PLANES: usize = 1 << TENSOR_LOW_BITS;
    const HIGH_CELLS: usize = TENSOR_HIGH_POINTS * LOW_PLANES;
    let mut tabs: [[Vec<Fe>; 3]; 2] =
        core::array::from_fn(|_| core::array::from_fn(|_| vec![FE_ZERO; TENSOR_POINTS]));
    if batch_range.is_empty() {
        return tabs;
    }
    let mut high_a = SecretBuffer(core::array::from_fn::<Vec<Plane>, 3, _>(|_| {
        vec![[0u64; 4]; TENSOR_BATCH * HIGH_CELLS]
    }));
    let mut high_b = SecretBuffer(core::array::from_fn::<Vec<Plane>, 3, _>(|_| {
        vec![[0u64; 4]; TENSOR_BATCH * HIGH_CELLS]
    }));
    let low_cells = TENSOR_LOW_POINTS * TENSOR_BATCH;
    let mut low_a = SecretBuffer(core::array::from_fn::<Vec<Plane>, 3, _>(|_| {
        vec![[0u64; 4]; low_cells]
    }));
    let mut low_b = SecretBuffer(core::array::from_fn::<Vec<Plane>, 3, _>(|_| {
        vec![[0u64; 4]; low_cells]
    }));
    let row = 2 * TENSOR_BATCH;
    let mut stage = SecretBuffer(core::array::from_fn::<Vec<Fe>, 3, _>(|_| {
        vec![FE_ZERO; TENSOR_LOW_POINTS * row]
    }));
    for bi in batch_range {
        let g0 = bi * TENSOR_BATCH;
        if g0 >= groups {
            break;
        }
        let count = TENSOR_BATCH.min(groups - g0);
        for gi in 0..count {
            let base = (g0 + gi) * GROUP_PLANES;
            let cells = gi * HIGH_CELLS..(gi + 1) * HIGH_CELLS;
            for s in 0..3 {
                for (src, dst) in [
                    (&pending.a[s], &mut high_a[s]),
                    (&pending.b[s], &mut high_b[s]),
                ] {
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
                    ternary_expand(
                        &mut low[..TENSOR_LOW_POINTS * count],
                        TENSOR_LOW_BITS,
                        count,
                    );
                }
            }
            for (p, staged) in stage.iter_mut().enumerate() {
                let q = (p + 1) % 3;
                for j in 0..TENSOR_LOW_POINTS {
                    let cells = j * count..(j + 1) * count;
                    let (ap, aq) = (&low_a[p][cells.clone()], &low_a[q][cells.clone()]);
                    let (bp, bq) = (&low_b[p][cells.clone()], &low_b[q][cells]);
                    let out = staged[j * row..j * row + 2 * count].as_chunks_mut::<2>().0;
                    for ((((t, ap), aq), bp), bq) in out.iter_mut().zip(ap).zip(aq).zip(bp).zip(bq)
                    {
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
    tabs
}

/// Tensor-round sums of every prover for both passes: entry `[pass][p][e]` is
/// `sum_g (kappa^(2g) T_lo + kappa^(2g + 1) T_hi)` where `T = a_p,e & b_q,e ^ a_q,e & b_p,e`
/// is the cross product of group `g` at point `e` (each operand is the GF(2) combination of
/// the group's 128 planes selected by `e`) and `T_lo`, `T_hi` are its two 128-bit blocks read
/// as field elements. Point `0` is left zero: it is never sent.
fn tensor_tables(
    pending: &PendingGates,
    groups: usize,
    weights: &[PassWeights; 2],
) -> [[Vec<Fe>; 3]; 2] {
    let num_batches = groups.div_ceil(TENSOR_BATCH);
    #[cfg(feature = "std")]
    {
        let workers = rss256_worker_threads().min(num_batches);
        if workers > 1 {
            let chunk_size = num_batches.div_ceil(workers);
            let partials = SecretBuffer(std::thread::scope(|scope| {
                let mut handles = Vec::with_capacity(workers);
                for w_idx in 0..workers {
                    let start = w_idx * chunk_size;
                    if start >= num_batches {
                        break;
                    }
                    let end = (start + chunk_size).min(num_batches);
                    handles.push(scope.spawn(move || {
                        tensor_tables_batch_range(pending, groups, start..end, weights)
                    }));
                }
                handles
                    .into_iter()
                    .map(|h| h.join().expect("rss256 tensor_tables worker panicked"))
                    .collect::<Vec<[[Vec<Fe>; 3]; 2]>>()
            }));
            let mut tabs: [[Vec<Fe>; 3]; 2] =
                core::array::from_fn(|_| core::array::from_fn(|_| vec![FE_ZERO; TENSOR_POINTS]));
            for part in partials.iter() {
                for pass in 0..2 {
                    for p in 0..3 {
                        for e in 1..TENSOR_POINTS {
                            tabs[pass][p][e] = fe_add(tabs[pass][p][e], part[pass][p][e]);
                        }
                    }
                }
            }
            return tabs;
        }
    }
    tensor_tables_batch_range(pending, groups, 0..num_batches, weights)
}

fn bind_planes_chunk(
    planes: &[Plane],
    pattern: &[[u8; GROUP_PLANES / 4]; 128],
    lane_weights: bool,
    out: &mut [Fe],
) {
    const NIBBLES: usize = GROUP_PLANES / 4;
    let mut tables = SecretBuffer([[[0u64; 4]; 16]; NIBBLES]);
    let mut lo = SecretBuffer([[0u64; 4]; 64]);
    let mut hi = SecretBuffer([[0u64; 4]; 64]);
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
}

/// Bind the plane index inside every group: element `256 g + lane` of `out` is
/// `sum_u eq[u] * bit(planes[128 g + u], lane)`, times `x^(lane % 128)` when `lane_weights`.
fn bind_planes(planes: &[Plane], eq: &[Fe], lane_weights: bool, out: &mut [Fe]) {
    const NIBBLES: usize = GROUP_PLANES / 4;
    debug_assert_eq!(eq.len(), GROUP_PLANES);
    debug_assert_eq!(planes.len() / GROUP_PLANES * LANES, out.len());
    let mut pattern = [[0u8; NIBBLES]; 128];
    for (t, row) in pattern.iter_mut().enumerate() {
        for (n, nibble) in row.iter_mut().enumerate() {
            for d in 0..4 {
                *nibble |= (((eq[4 * n + d][t / 64] >> (t % 64)) & 1) as u8) << d;
            }
        }
    }
    #[cfg(feature = "std")]
    {
        let num_groups = planes.len() / GROUP_PLANES;
        let sub_workers = (rss256_worker_threads() / 3).max(1).min(num_groups);
        if sub_workers > 1 && num_groups >= 32 {
            let groups_per_worker = num_groups.div_ceil(sub_workers);
            std::thread::scope(|scope| {
                let mut rest_planes = planes;
                let mut rest_out = out;
                while !rest_planes.is_empty() {
                    let take_g = groups_per_worker.min(rest_planes.len() / GROUP_PLANES);
                    let (p_head, p_tail) = rest_planes.split_at(take_g * GROUP_PLANES);
                    let (o_head, o_tail) = rest_out.split_at_mut(take_g * LANES);
                    rest_planes = p_tail;
                    rest_out = o_tail;
                    let pat_ref = &pattern;
                    scope.spawn(move || {
                        bind_planes_chunk(p_head, pat_ref, lane_weights, o_head);
                    });
                }
            });
            return;
        }
    }
    bind_planes_chunk(planes, &pattern, lane_weights, out);
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
                qsag_asm::gf2_128_mul_acc_batch(
                    &mut acc,
                    &ex[p][cells.clone()],
                    &ey[q][cells.clone()],
                );
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
pub struct Rss256Engine {
    cluster: RssSlhMpcCluster,
    mode: AndMode,
    /// Relation words per barrier before a check is forced (bounds proof memory).
    max_pending_words: usize,
    pending: PendingGates,
    transcript: [TranscriptHasher4; 3],
    prev_digest: [u8; 32],
    last_seed: [u8; 32],
    barrier_index: u64,
    unverified: bool,
    /// Set by the first failed barrier, coin flip or opening comparison; never cleared.
    poison_latch: qsag_verified::VerifiedRssPoisonLatch,
    staging: bool,
    wave_index: u64,
    bank: BeaverBank256,
    opened: OpenedShares,
    stats: WireStats,
    #[cfg(test)]
    faults: Vec<Fault256>,
    #[cfg(test)]
    captured_messages: Option<[Vec<Plane>; 3]>,
    #[cfg(test)]
    proof_view: Option<ProofView>,
}

impl Rss256Engine {
    /// Default bound on relation words buffered between barriers: 400,000 gate planes, a
    /// little over ten full waves. The buffer holds twelve planes per gate plane (about
    /// 150 MiB at the bound) and the proof adds about 80 MiB of bound vectors per pass.
    pub const DEFAULT_MAX_PENDING_WORDS: usize = 1_600_000;

    pub fn new(
        session_id: [u8; 32],
        keys: [RssKeyShare256; 3],
        party_rngs: [PartyPrivateRng; 3],
    ) -> Result<Self, Rss256Error> {
        let cluster = RssSlhMpcCluster::new(session_id, keys, party_rngs)?;
        let prev_digest = [0u8; 32];
        Ok(Self {
            cluster,
            mode: AndMode::InlineCnf,
            max_pending_words: Self::DEFAULT_MAX_PENDING_WORDS,
            pending: PendingGates::new(),
            transcript: core::array::from_fn(|s| TranscriptHasher4::new(s as u64, &prev_digest)),
            prev_digest,
            last_seed: [0u8; 32],
            barrier_index: 0,
            unverified: false,
            poison_latch: qsag_verified::VerifiedRssPoisonLatch::new_clean(),
            staging: false,
            wave_index: 0,
            bank: BeaverBank256::empty(),
            opened: OpenedShares::new(),
            stats: WireStats::default(),
            #[cfg(test)]
            faults: Vec::new(),
            #[cfg(test)]
            captured_messages: None,
            #[cfg(test)]
            proof_view: None,
        })
    }

    pub fn session_id(&self) -> &[u8; 32] {
        &self.cluster.session_id
    }

    pub fn keys(&self) -> &[RssKeyShare256; 3] {
        &self.cluster.keys
    }

    pub fn mode(&self) -> AndMode {
        self.mode
    }

    /// Record, in all three key shares, the identity of the hash-signature key they were
    /// generated for (see [`RssKeyShare256::bind_scheme_identity`]). Refused if a share is
    /// already bound to a different identity.
    pub fn bind_key_identity(&mut self, identity: &[u8; 32]) -> Result<(), Rss256Error> {
        self.guard()?;
        if self
            .cluster
            .keys
            .iter()
            .any(|k| k.scheme_identity().is_some_and(|bound| bound != identity))
        {
            return Err(Rss256Error::Mpc(KeccakMpcError::KeyBindingMismatch));
        }
        for key in &mut self.cluster.keys {
            key.bind_scheme_identity(identity)?;
        }
        Ok(())
    }

    /// The identity all three key shares are bound to, or `None` if none is bound. Shares
    /// that disagree are an error.
    pub fn key_identity(&self) -> Result<Option<[u8; 32]>, Rss256Error> {
        let first = self.cluster.keys[0].scheme_identity().copied();
        if self
            .cluster
            .keys
            .iter()
            .any(|k| k.scheme_identity().copied() != first)
        {
            return Err(Rss256Error::Mpc(KeccakMpcError::KeyBindingMismatch));
        }
        Ok(first)
    }

    /// True once a barrier, coin flip or opening comparison has failed. Permanent.
    pub fn is_poisoned(&self) -> bool {
        self.poison_latch.is_poisoned()
    }

    #[inline]
    fn guard(&self) -> Result<(), Rss256Error> {
        if self.poison_latch.is_poisoned() {
            Err(Rss256Error::Poisoned)
        } else {
            Ok(())
        }
    }

    /// Latch the poison flag, then drop everything that was awaiting verification.
    fn poison<T>(&mut self, error: Rss256Error) -> Result<T, Rss256Error> {
        let latch = core::mem::replace(
            &mut self.poison_latch,
            qsag_verified::VerifiedRssPoisonLatch::new_clean(),
        );
        self.poison_latch = latch.record_check_result(false).0;
        self.cluster.poison();
        self.pending.clear_and_wipe();
        self.opened.clear();
        self.bank = BeaverBank256::empty();
        Err(error)
    }

    /// Select the AND protocol for subsequent waves. Requires a verified state.
    pub fn set_mode(&mut self, mode: AndMode) -> Result<(), Rss256Error> {
        self.guard()?;
        if self.unverified {
            return Err(Rss256Error::OpenBeforeCheck);
        }
        self.mode = mode;
        Ok(())
    }

    /// Bound on buffered relation words (64 relations each; a gate plane is four words).
    pub fn set_max_pending_words(&mut self, words: usize) {
        self.max_pending_words = words.max(4 * GROUP_PLANES);
    }

    fn pending_words(&self) -> usize {
        4 * self.pending.len()
    }

    pub fn stats(&self) -> WireStats {
        self.stats
    }

    pub fn bank(&self) -> &BeaverBank256 {
        &self.bank
    }

    /// Seed of the most recent barrier (public after the coin is opened).
    pub fn last_check_seed(&self) -> &[u8; 32] {
        &self.last_seed
    }

    /// True while gates exist that no barrier has accepted.
    pub fn has_unverified_gates(&self) -> bool {
        self.unverified
    }

    /// Declare that the waves evaluated next depend on the outputs of earlier waves: one more
    /// sequential permutation level (24 gate rounds) for the round count.
    pub fn mark_sequential_level(&mut self) {
        self.stats.perm_levels += 1;
    }

    /// Declare one opening round: every opening requested until the next call travels in it.
    pub fn mark_open_round(&mut self) {
        self.stats.open_rounds += 1;
    }

    /// Account for a broadcast outside the engine's own protocol (for example a latch echo).
    pub fn charge_broadcast(&mut self, bytes: u64, hops: u64) {
        self.stats.open_bytes += bytes;
        self.stats.open_rounds += hops;
    }

    /// Share slots of the replicated `sk_seed`.
    pub(crate) fn sk_seed_slots(&self) -> [&[u8]; 3] {
        core::array::from_fn(|s| self.cluster.keys[s].sk_seed_shares().0)
    }

    /// Share slots of the replicated `sk_prf`.
    pub(crate) fn sk_prf_slots(&self) -> [&[u8]; 3] {
        core::array::from_fn(|s| self.cluster.keys[s].sk_prf_shares().0)
    }

    pub fn pk_seed(&self) -> [u8; 32] {
        self.cluster.keys[0].pk_seed
    }

    /// Fresh 32-byte value from a commit-then-open coin flip bound to `binding`.
    pub fn joint_coin(
        &mut self,
        label: &[u8],
        binding: &[u8; 32],
    ) -> Result<[u8; 32], Rss256Error> {
        self.guard()?;
        self.stats.check_hops += 2;
        self.stats.check_bytes += 64;
        match run_commit_and_open_coin_with_hook(
            &self.cluster.session_id,
            label,
            binding,
            &mut self.cluster.party_rngs,
            |_, _| {},
        ) {
            Ok(coin) => Ok(coin),
            Err(e) => self.poison(Rss256Error::Mpc(KeccakMpcError::from(e))),
        }
    }

    fn pad_stream(&self, slot: usize, purpose: u64, wave_ctr: u64) -> Shake256Prg256 {
        Shake256Prg256::new(
            &self.cluster.mask_session.prim[slot],
            &self.cluster.session_id,
            (purpose << 56) | wave_ctr,
        )
    }

    fn next_wave_counter(&mut self) -> Result<u64, Rss256Error> {
        let ctr = self.cluster.next_ctr();
        if ctr > MAX_WAVE_COUNTER {
            return Err(Rss256Error::WaveCounterOverflow);
        }
        Ok(ctr)
    }

    #[cfg(test)]
    pub(crate) fn inject_fault(&mut self, fault: Fault256) {
        self.faults.push(fault);
    }

    /// Like [`Self::inject_fault`], with a gate fault's `wave` counted from the next wave.
    #[cfg(test)]
    pub(crate) fn inject_fault_next_wave(&mut self, fault: Fault256) {
        let fault = match fault {
            Fault256::GateMessage {
                wave,
                round,
                plane,
                sender,
                mask,
            } => Fault256::GateMessage {
                wave: wave + self.wave_index,
                round,
                plane,
                sender,
                mask,
            },
            other => other,
        };
        self.faults.push(fault);
    }

    #[cfg(test)]
    pub(crate) fn capture_next_messages(&mut self) {
        self.captured_messages = Some([Vec::new(), Vec::new(), Vec::new()]);
    }

    #[cfg(test)]
    pub(crate) fn take_captured_messages(&mut self) -> Option<[Vec<Plane>; 3]> {
        self.captured_messages.take()
    }

    #[cfg(test)]
    pub(crate) fn capture_proof_view(&mut self) {
        self.proof_view = Some(ProofView::default());
    }

    #[cfg(test)]
    pub(crate) fn take_proof_view(&mut self) -> Option<ProofView> {
        self.proof_view.take()
    }

    #[cfg(test)]
    fn gate_fault(&self, wave: u64, round: usize, plane: usize, sender: usize) -> Plane {
        let mut out = [0u64; 4];
        for f in &self.faults {
            if let Fault256::GateMessage {
                wave: w,
                round: r,
                plane: p,
                sender: s,
                mask,
            } = *f
                && w == wave
                && r == round
                && p == plane
                && s == sender
            {
                for (o, m) in out.iter_mut().zip(mask) {
                    *o ^= m;
                }
            }
        }
        out
    }

    /// Evaluate `Keccak-f[1600]` on the low `lanes` lanes of `st`. Outputs stay shared; the
    /// gates are unverified until [`Self::check`].
    pub fn permute(&mut self, st: &mut SharedState256, lanes: usize) -> Result<(), Rss256Error> {
        self.guard()?;
        if lanes == 0 || lanes > LANES {
            return Err(Rss256Error::InvalidParameters);
        }
        match self.mode {
            AndMode::InlineCnf => self.permute_inline(st, lanes)?,
            AndMode::BeaverBank => self.permute_bank(st, lanes)?,
        }
        self.stats.lane_perms += lanes as u64;
        self.wave_index += 1;
        if self.pending_words() >= self.max_pending_words {
            self.run_barrier(false)?;
        }
        Ok(())
    }

    fn permute_inline(&mut self, st: &mut SharedState256, lanes: usize) -> Result<(), Rss256Error> {
        let active = active_lane_mask(lanes);
        let words = lanes.div_ceil(64);
        let wave_ctr = self.next_wave_counter()?;
        let mut pads: [Shake256Prg256; 3] =
            core::array::from_fn(|s| self.pad_stream(s, PURPOSE_CHI_PAD, wave_ctr));
        let mut lin: [Box<[Plane; STATE_PLANES]>; 3] = core::array::from_fn(|_| boxed_planes());
        let mut pad: [Box<[Plane; STATE_PLANES]>; 3] = core::array::from_fn(|_| boxed_planes());
        let mut msg: [Box<[Plane; STATE_PLANES]>; 3] = core::array::from_fn(|_| boxed_planes());
        for s in 0..3 {
            for planes in [
                &mut self.pending.a[s],
                &mut self.pending.b[s],
                &mut self.pending.msg[s],
                &mut self.pending.pad[s],
            ] {
                secret_vec_reserve(planes, AND_PLANES_PER_PERM);
            }
        }

        for (round, &rc) in KECCAK_ROUND_CONSTANTS.iter().enumerate() {
            for s in 0..3 {
                keccak_linear_layer(&st.slot[s], &mut lin[s]);
                pads[s].fill_planes(&mut pad[s][..], words);
                // Lanes outside the wave carry no gate: their pads are not used.
                for plane in pad[s].iter_mut() {
                    for (x, m) in plane.iter_mut().zip(&active) {
                        *x &= m;
                    }
                }
            }
            for p in 0..3 {
                let [pad_p, pad_q] = sender_pad_slots(p);
                let q = pad_q;
                for lane in 0..25 {
                    let row = 5 * (lane / 5);
                    let l1 = (row + (lane + 1) % 5) * 64;
                    let l2 = (row + (lane + 2) % 5) * 64;
                    let l0 = lane * 64;
                    for z in 0..64 {
                        let ap = &lin[p][l1 + z];
                        let aq = &lin[q][l1 + z];
                        let bp = &lin[p][l2 + z];
                        let bq = &lin[q][l2 + z];
                        let rp = &pad[pad_p][l0 + z];
                        let rq = &pad[pad_q][l0 + z];
                        #[cfg(test)]
                        let fault = self.gate_fault(self.wave_index, round, l0 + z, p);
                        let out = &mut msg[p][l0 + z];
                        for w in 0..4 {
                            let u =
                                and_message(ap[w], aq[w], bp[w], bq[w], rp[w], rq[w]) & active[w];
                            #[cfg(test)]
                            let u = u ^ fault[w];
                            out[w] = u;
                        }
                    }
                }
            }
            #[cfg(not(test))]
            let _ = round;
            self.record_and_apply(st, &lin, &msg, &pad, &active, words, rc);
        }
        for s in 0..3 {
            qsag_asm::volatile_fill(&mut lin[s][..], [0; 4]);
            qsag_asm::volatile_fill(&mut pad[s][..], [0; 4]);
            qsag_asm::volatile_fill(&mut msg[s][..], [0; 4]);
        }
        let gate_bytes = (AND_PLANES_PER_PERM * lanes).div_ceil(8) as u64;
        if self.staging {
            self.stats.staged_bytes += gate_bytes;
        } else {
            self.stats.and_bytes += gate_bytes;
        }
        self.unverified = true;
        Ok(())
    }

    /// Bind the round's gate messages, record its AND relations and finish chi and iota.
    #[expect(
        clippy::too_many_arguments,
        reason = "one gate round: state, linear layer, messages, pads, lane mask and round constant"
    )]
    fn record_and_apply(
        &mut self,
        st: &mut SharedState256,
        lin: &[Box<[Plane; STATE_PLANES]>; 3],
        msg: &[Box<[Plane; STATE_PLANES]>; 3],
        pad: &[Box<[Plane; STATE_PLANES]>; 3],
        active: &Plane,
        words: usize,
        rc: u64,
    ) {
        for s in 0..3 {
            for plane in msg[s].iter() {
                self.transcript[s].absorb_words(&plane[..words]);
            }
            #[cfg(test)]
            if let Some(cap) = &mut self.captured_messages {
                cap[s].extend_from_slice(&msg[s][..]);
            }
            secret_vec_extend_from_slice(&mut self.pending.msg[s], &msg[s][..]);
            secret_vec_extend_from_slice(&mut self.pending.pad[s], &pad[s][..]);
            for lane in 0..25 {
                let row = 5 * (lane / 5);
                let l1 = (row + (lane + 1) % 5) * 64;
                let l2 = (row + (lane + 2) % 5) * 64;
                let l0 = lane * 64;
                for z in 0..64 {
                    let a = &lin[s][l1 + z];
                    let b = &lin[s][l2 + z];
                    let t = &msg[s][l0 + z];
                    secret_vec_push(
                        &mut self.pending.a[s],
                        core::array::from_fn(|w| a[w] & active[w]),
                    );
                    secret_vec_push(
                        &mut self.pending.b[s],
                        core::array::from_fn(|w| b[w] & active[w]),
                    );
                    let out = &mut st.slot[s][l0 + z];
                    for w in 0..4 {
                        out[w] = lin[s][l0 + z][w] ^ b[w] ^ t[w];
                    }
                }
            }
        }
        for (z, plane) in st.slot[0][..64].iter_mut().enumerate() {
            if (rc >> z) & 1 == 1 {
                for (x, m) in plane.iter_mut().zip(active) {
                    *x ^= m;
                }
            }
        }
    }

    fn permute_bank(&mut self, st: &mut SharedState256, lanes: usize) -> Result<(), Rss256Error> {
        if self.bank.remaining_planes() < AND_PLANES_PER_PERM {
            return Err(Rss256Error::BeaverBankExhausted);
        }
        let active = active_lane_mask(lanes);
        let mut lin: [Box<[Plane; STATE_PLANES]>; 3] = core::array::from_fn(|_| boxed_planes());
        for (round, &rc) in KECCAK_ROUND_CONSTANTS.iter().enumerate() {
            #[cfg(not(test))]
            let _ = round;
            for (src, dst) in st.slot.iter().zip(lin.iter_mut()) {
                keccak_linear_layer(src, dst);
            }
            let base = self.bank.cursor;
            for lane in 0..25 {
                let row = 5 * (lane / 5);
                let l1 = (row + (lane + 1) % 5) * 64;
                let l2 = (row + (lane + 2) % 5) * 64;
                let l0 = lane * 64;
                for z in 0..64 {
                    let g = base + l0 + z;
                    // Mask differences d = a + t_a and e = b + t_b, opened slot by slot. The
                    // party that lacks slot `s` receives it from the forwarding holder and
                    // computes with that copy; the primary holder's copy is kept alongside.
                    let mut d_pub = [0u64; 4];
                    let mut e_pub = [0u64; 4];
                    #[allow(
                        clippy::needless_range_loop,
                        reason = "one slot index addresses several parallel per-slot tables"
                    )]
                    for s in 0..3 {
                        let d: Plane = core::array::from_fn(|w| {
                            (lin[s][l1 + z][w] ^ self.bank.a[s][g][w]) & active[w]
                        });
                        let e: Plane = core::array::from_fn(|w| {
                            (lin[s][l2 + z][w] ^ self.bank.b[s][g][w]) & active[w]
                        });
                        self.opened.reference[s].extend_from_slice(&[
                            [d[0], d[1]],
                            [d[2], d[3]],
                            [e[0], e[1]],
                            [e[2], e[3]],
                        ]);
                        #[cfg_attr(
                            not(test),
                            expect(unused_mut, reason = "mutated by test faults")
                        )]
                        let mut sent = d;
                        #[cfg(test)]
                        for f in &self.faults {
                            if let Fault256::BeaverOpening {
                                wave,
                                round: r,
                                plane,
                                slot,
                                mask,
                            } = *f
                                && wave == self.wave_index
                                && r == round
                                && plane == l0 + z
                                && slot == s
                            {
                                // The forwarding holder reports a different share of `d`.
                                for (x, m) in sent.iter_mut().zip(mask) {
                                    *x ^= m;
                                }
                            }
                        }
                        self.opened.forwarded[s].extend_from_slice(&[
                            [sent[0], sent[1]],
                            [sent[2], sent[3]],
                            [e[0], e[1]],
                            [e[2], e[3]],
                        ]);
                        for w in 0..4 {
                            d_pub[w] ^= sent[w];
                            e_pub[w] ^= e[w];
                        }
                        self.transcript[s].absorb_words(&sent);
                        self.transcript[s].absorb_words(&e);
                    }
                    #[allow(
                        clippy::needless_range_loop,
                        reason = "one slot index addresses several parallel per-slot tables"
                    )]
                    for s in 0..3 {
                        let ta = self.bank.a[s][g];
                        let tb = self.bank.b[s][g];
                        let tc = self.bank.c[s][g];
                        let out = &mut st.slot[s][l0 + z];
                        for w in 0..4 {
                            let mut prod = tc[w] ^ (d_pub[w] & tb[w]) ^ (e_pub[w] & ta[w]);
                            if s == 0 {
                                prod ^= d_pub[w] & e_pub[w];
                            }
                            out[w] = lin[s][l0 + z][w] ^ lin[s][l2 + z][w] ^ (prod & active[w]);
                        }
                    }
                }
            }
            for s in 0..3 {
                qsag_asm::volatile_fill(&mut self.bank.a[s][base..base + STATE_PLANES], [0; 4]);
                qsag_asm::volatile_fill(&mut self.bank.b[s][base..base + STATE_PLANES], [0; 4]);
                qsag_asm::volatile_fill(&mut self.bank.c[s][base..base + STATE_PLANES], [0; 4]);
            }
            self.bank.cursor += STATE_PLANES;
            for (z, plane) in st.slot[0][..64].iter_mut().enumerate() {
                if (rc >> z) & 1 == 1 {
                    for (x, m) in plane.iter_mut().zip(&active) {
                        *x ^= m;
                    }
                }
            }
        }
        for l in &mut lin {
            qsag_asm::volatile_fill(&mut l[..], [0; 4]);
        }
        // Two opened bits per gate and party.
        self.stats.and_bytes += 2 * (AND_PLANES_PER_PERM * lanes).div_ceil(8) as u64;
        self.unverified = true;
        Ok(())
    }

    /// Stage and verify enough single-use triples for `perms` 256-lane permutations
    /// (Mode 1A). This is offline work: it costs what evaluating those permutations in
    /// Mode 1B costs, and each party must store two of the three slots of every triple.
    /// A failed proof poisons the engine and discards the bank.
    pub fn stage_beaver_bank(&mut self, perms: usize) -> Result<(), Rss256Error> {
        self.guard()?;
        if self.unverified || self.mode != AndMode::InlineCnf {
            return Err(Rss256Error::OpenBeforeCheck);
        }
        let active = [u64::MAX; 4];
        self.staging = true;
        let result = self.stage_inner(perms, &active);
        let checked = result.and_then(|()| self.check());
        self.staging = false;
        match checked {
            Ok(()) => Ok(()),
            // Already poisoned by the barrier, or a counter overflow before it: either way
            // the partly staged bank is never used.
            Err(e) => self.poison(e),
        }
    }

    fn stage_inner(&mut self, perms: usize, active: &Plane) -> Result<(), Rss256Error> {
        let mut ta: [Box<[Plane; STATE_PLANES]>; 3] = core::array::from_fn(|_| boxed_planes());
        let mut tb: [Box<[Plane; STATE_PLANES]>; 3] = core::array::from_fn(|_| boxed_planes());
        let mut pad: [Box<[Plane; STATE_PLANES]>; 3] = core::array::from_fn(|_| boxed_planes());
        for _ in 0..perms {
            let wave_ctr = self.next_wave_counter()?;
            let mut sa: [Shake256Prg256; 3] =
                core::array::from_fn(|s| self.pad_stream(s, PURPOSE_BANK_A, wave_ctr));
            let mut sb: [Shake256Prg256; 3] =
                core::array::from_fn(|s| self.pad_stream(s, PURPOSE_BANK_B, wave_ctr));
            let mut sp: [Shake256Prg256; 3] =
                core::array::from_fn(|s| self.pad_stream(s, PURPOSE_BANK_PAD, wave_ctr));
            for _round in 0..24 {
                for s in 0..3 {
                    // Both holders of slot `s` derive the same random triple-input shares.
                    sa[s].fill_planes(&mut ta[s][..], 4);
                    sb[s].fill_planes(&mut tb[s][..], 4);
                    sp[s].fill_planes(&mut pad[s][..], 4);
                }
                for g in 0..STATE_PLANES {
                    let mut msgs = [[0u64; 4]; 3];
                    for (p, msg) in msgs.iter_mut().enumerate() {
                        let [pad_p, pad_q] = sender_pad_slots(p);
                        let q = pad_q;
                        for w in 0..4 {
                            msg[w] = and_message(
                                ta[p][g][w],
                                ta[q][g][w],
                                tb[p][g][w],
                                tb[q][g][w],
                                pad[pad_p][g][w],
                                pad[pad_q][g][w],
                            ) & active[w];
                        }
                    }
                    for s in 0..3 {
                        self.transcript[s].absorb_words(&msgs[s]);
                        secret_vec_push(&mut self.pending.a[s], ta[s][g]);
                        secret_vec_push(&mut self.pending.b[s], tb[s][g]);
                        secret_vec_push(&mut self.pending.msg[s], msgs[s]);
                        secret_vec_push(&mut self.pending.pad[s], pad[s][g]);
                        secret_vec_push(&mut self.bank.a[s], ta[s][g]);
                        secret_vec_push(&mut self.bank.b[s], tb[s][g]);
                        secret_vec_push(&mut self.bank.c[s], msgs[s]);
                    }
                }
                self.unverified = true;
                if self.pending_words() >= self.max_pending_words {
                    self.run_barrier(false)?;
                }
            }
            self.stats.staged_lane_perms += LANES as u64;
            self.stats.staged_bytes += (AND_PLANES_PER_PERM * LANES / 8) as u64;
            // Two slots of (a, b, c) per plane triple.
            self.stats.staged_state_bytes += (2 * 3 * AND_PLANES_PER_PERM * 32) as u64;
        }
        for s in 0..3 {
            qsag_asm::volatile_fill(&mut ta[s][..], [0; 4]);
            qsag_asm::volatile_fill(&mut tb[s][..], [0; 4]);
            qsag_asm::volatile_fill(&mut pad[s][..], [0; 4]);
        }
        Ok(())
    }

    /// The verification barrier (see the module documentation). A failure poisons the engine:
    /// nothing evaluated in this session can be opened afterwards.
    pub fn check(&mut self) -> Result<(), Rss256Error> {
        self.guard()?;
        self.run_barrier(true)
    }

    fn run_barrier(&mut self, at_cut: bool) -> Result<(), Rss256Error> {
        self.guard()?;
        if !self.unverified {
            return Ok(());
        }
        match self.run_barrier_steps(at_cut) {
            Ok(()) => Ok(()),
            Err(e) => self.poison(e),
        }
    }

    fn run_barrier_steps(&mut self, at_cut: bool) -> Result<(), Rss256Error> {
        // 1. Per-sender transcript digests, announced by both holders of each stream: the
        // sender (party `s`) and the receiver (party `s - 1`).
        let mut digests = [[0u8; 32]; 3];
        for (s, digest) in digests.iter_mut().enumerate() {
            let fresh = TranscriptHasher4::new(s as u64, &self.prev_digest);
            *digest = core::mem::replace(&mut self.transcript[s], fresh).finalize();
        }
        #[cfg_attr(not(test), expect(unused_mut, reason = "mutated by test faults"))]
        let mut announced: [[[u8; 32]; 2]; 3] = core::array::from_fn(|s| [digests[s]; 2]);
        #[cfg(test)]
        for f in &self.faults {
            if let Fault256::TranscriptDigest { slot } = *f {
                announced[slot][1][0] ^= 1;
            }
        }
        for (slot, pair) in announced.iter().enumerate() {
            if !qsag_asm::ct_eq_32(&pair[0], &pair[1]) {
                return Err(Rss256Error::TranscriptMismatch { slot });
            }
        }
        let mut xof = Cshake256Xof::new_shake256();
        xof.absorb(b"QSAG-WAVE-TRANSCRIPT-v1");
        xof.absorb(&self.cluster.session_id);
        xof.absorb(&self.prev_digest);
        xof.absorb(&self.barrier_index.to_le_bytes());
        xof.absorb(&(self.pending.len() as u64).to_le_bytes());
        xof.absorb(&(self.opened.reference[0].len() as u64).to_le_bytes());
        for d in &digests {
            xof.absorb(d);
        }
        let mut transcript_digest = [0u8; 32];
        xof.squeeze(&mut transcript_digest);

        // 2. Coin flip: commitments are bound to the transcript digest and opened afterwards.
        #[cfg(test)]
        let coin_fault = self.faults.iter().find_map(|f| match *f {
            Fault256::CoinReveal { party } => Some(party),
            _ => None,
        });
        #[cfg(not(test))]
        let coin_fault: Option<usize> = None;
        let coin = run_commit_and_open_coin_with_hook(
            &self.cluster.session_id,
            b"QSAG-WAVE-CHECK-COIN-v1",
            &transcript_digest,
            &mut self.cluster.party_rngs,
            |party, share| {
                if coin_fault == Some(party) {
                    share[0] ^= 1;
                }
            },
        )
        .map_err(|e| match e {
            PreprocessError::CoinCommitMismatch { party_id } => {
                Rss256Error::CoinOpeningRejected { party: party_id }
            }
            other => Rss256Error::Mpc(KeccakMpcError::from(other)),
        })?;
        let mut xof = Cshake256Xof::new_shake256();
        xof.absorb(b"QSAG-WAVE-CHECK-v1");
        xof.absorb(&transcript_digest);
        xof.absorb(&coin);
        let mut seed = [0u8; 32];
        xof.squeeze(&mut seed);
        self.last_seed = seed;

        // 3a. Mode 1B (and bank staging): product proof under two seed-derived challenges.
        let mut bytes = 64 + 64u64;
        let mut hops = 2u64;
        if self.pending.len() > 0 {
            let (b, h) = self.product_proof(&seed)?;
            bytes += b;
            hops += h;
        }

        // 3b. Mode 1A: for every slot, the primary holder's and the forwarding holder's copy
        // of the opened mask-difference shares are evaluated at two seed-derived points; the
        // evaluations must agree at both.
        if !self.opened.is_empty() {
            let mut xof = Cshake256Xof::new_shake256();
            xof.absorb(b"QSAG-WAVE-HORNER-v1");
            xof.absorb(&seed);
            let points = [fe_from_xof(&mut xof), fe_from_xof(&mut xof)];
            for slot in 0..3 {
                for point in points {
                    let primary = horner_eval(&self.opened.reference[slot], point);
                    let forwarded = horner_eval(&self.opened.forwarded[slot], point);
                    if (primary[0] ^ forwarded[0]) | (primary[1] ^ forwarded[1]) != 0 {
                        return Err(Rss256Error::OpeningConsistencyFailed { slot });
                    }
                }
            }
            self.opened.clear();
            bytes += 2 * 16;
            // One more hop, after the product proof if both ran.
            hops += 1;
        }

        if self.staging {
            self.stats.staged_bytes += bytes;
        } else {
            self.stats.checks += 1;
            if at_cut {
                self.stats.cut_checks += 1;
                self.stats.check_hops += hops;
            }
            self.stats.check_bytes += bytes;
        }
        self.prev_digest = transcript_digest;
        self.barrier_index += 1;
        self.unverified = false;
        Ok(())
    }

    /// Joint coin of one product-proof round, bound to the barrier seed and the round.
    fn proof_coin(
        &mut self,
        seed: &[u8; 32],
        pass: usize,
        round: u32,
    ) -> Result<[u8; 32], Rss256Error> {
        let mut xof = Cshake256Xof::new_shake256();
        xof.absorb(b"QSAG-WAVE-PRODUCT-ROUND-v2");
        xof.absorb(&(pass as u64).to_le_bytes());
        xof.absorb(seed);
        xof.absorb(&round.to_le_bytes());
        let mut binding = [0u8; 32];
        xof.squeeze(&mut binding);
        run_commit_and_open_coin_with_hook(
            &self.cluster.session_id,
            b"QSAG-WAVE-PRODUCT-COIN-v1",
            &binding,
            &mut self.cluster.party_rngs,
            |_, _| {},
        )
        .map_err(|e| Rss256Error::Mpc(KeccakMpcError::from(e)))
    }

    /// Split the prover values `values[1..]` of proof `p` between its verifiers: `V1`
    /// derives its share from `stream` (keyed by slot `p`, which `V2` does not hold) and `V2`
    /// is sent the difference. Entry `0` of both shares is zero.
    fn split_message(
        &mut self,
        p: usize,
        pass: usize,
        round: u32,
        values: &[Fe],
        stream: &mut Shake256Prg256,
    ) -> (Vec<Fe>, Vec<Fe>) {
        let mut v1 = vec![FE_ZERO; values.len()];
        stream.fill_words(v1[1..].as_flattened_mut());
        let mut v2: Vec<Fe> = values
            .iter()
            .zip(&v1)
            .map(|(v, m)| fe_add(*v, *m))
            .collect();
        v2[0] = FE_ZERO;
        #[cfg(test)]
        {
            for f in &self.faults {
                if let Fault256::ProofMessage {
                    prover,
                    pass: fp,
                    round: fr,
                } = *f
                    && prover == p
                    && fp == pass
                    && fr == round
                {
                    v2[1][0] ^= 1;
                }
            }
            if let Some(view) = &mut self.proof_view {
                view.received[(p + 1) % 3].extend_from_slice(&v2[1..]);
            }
        }
        #[cfg(not(test))]
        let _ = (p, pass, round);
        (v1, v2)
    }

    /// The product proof over every recorded gate relation (see the module documentation).
    /// Returns the bytes one party sends and the message hops. The recorded relations are
    /// consumed.
    ///
    /// The two passes are independent proofs with common round structure; in a deployment
    /// each round coin is freshly committed and opened after that pass sends its values.
    /// Pass and round are bound separately, including in this sequential emulator.
    fn product_proof(&mut self, seed: &[u8; 32]) -> Result<(u64, u64), Rss256Error> {
        self.pending.pad_to_group();
        let groups = self.pending.len() / GROUP_PLANES;
        let blocks = 2 * groups;
        let elems = groups * LANES;
        let ctr = self.next_wave_counter()?;

        let mut xof = Cshake256Xof::new_shake256();
        xof.absorb(b"QSAG-WAVE-PRODUCT-WEIGHTS-v1");
        xof.absorb(seed);
        let weights: [PassWeights; 2] =
            core::array::from_fn(|_| PassWeights::new(fe_from_xof(&mut xof), blocks));

        // Per proof `p`: the stream `V1` shares with the prover (slot key `p`) for message
        // shares and for the masks of its openings, and the stream `V2` shares with the
        // prover (slot key `p + 1`) for the masks of its openings.
        let mut share_prg: [Shake256Prg256; 3] =
            core::array::from_fn(|p| self.pad_stream(p, PURPOSE_PROOF_SHARE, ctr));
        let mut mask1_prg: [Shake256Prg256; 3] =
            core::array::from_fn(|p| self.pad_stream(p, PURPOSE_PROOF_MASK_V1, ctr));
        let mut mask2_prg: [Shake256Prg256; 3] =
            core::array::from_fn(|p| self.pad_stream((p + 1) % 3, PURPOSE_PROOF_MASK_V2, ctr));

        let linear = SecretBuffer(linear_terms(&self.pending, groups, &weights));
        let tensor = SecretBuffer(tensor_tables(&self.pending, groups, &weights));

        let mut rounds = 0u64;
        let mut sums = 0u64;
        let mut accepted = true;
        for pass in 0..2 {
            let w = &weights[pass];
            // Claim shares of the two verifiers of every proof.
            let mut claim1 = SecretBuffer(core::array::from_fn::<Fe, 3, _>(|p| linear[pass][p][0]));
            let mut claim2 = SecretBuffer(core::array::from_fn::<Fe, 3, _>(|p| {
                linear[pass][(p + 1) % 3][1]
            }));
            let mut round = 0u32;
            let challenges = |coin: &[u8; 32], count: usize| -> Vec<Fe> {
                let mut xof = Cshake256Xof::new_shake256();
                xof.absorb(b"QSAG-WAVE-PRODUCT-CHALLENGE-v1");
                xof.absorb(coin);
                xof.absorb(&[pass as u8]);
                (0..count).map(|_| fe_from_xof(&mut xof)).collect()
            };

            // Tensor round: bind the plane index inside every group.
            let shares = SecretBuffer(core::array::from_fn::<(Vec<Fe>, Vec<Fe>), 3, _>(|p| {
                self.split_message(p, pass, round, &tensor[pass][p], &mut share_prg[p])
            }));
            let gammas = challenges(&self.proof_coin(seed, pass, round)?, TENSOR_BITS);
            let coeff = round_coefficients(&gammas);
            let boolean = w.boolean_weights();
            for p in 0..3 {
                claim1[p] = next_claim(claim1[p], &shares[p].0, &boolean, &coeff);
                claim2[p] = next_claim(claim2[p], &shares[p].1, &boolean, &coeff);
            }
            drop(shares);
            if pass == 0 {
                sums += (TENSOR_POINTS - 1) as u64;
            }
            round += 1;

            // Bound vectors: `x` carries the lane weights, `y` does not. The block weights
            // are applied to the round sums of the first fold and to `x` after it.
            let eq = eq_table(&gammas);
            let mut x = SecretBuffer(core::array::from_fn::<Vec<Fe>, 3, _>(|_| {
                vec![FE_ZERO; elems]
            }));
            let mut y = SecretBuffer(core::array::from_fn::<Vec<Fe>, 3, _>(|_| {
                vec![FE_ZERO; elems]
            }));
            #[cfg(feature = "std")]
            if rss256_worker_threads() > 1 && groups >= 8 {
                let pending_ref = &self.pending;
                let eq_ref = &eq;
                let ([x0, x1, x2], [y0, y1, y2]) = (&mut *x, &mut *y);
                std::thread::scope(|scope| {
                    scope.spawn(|| bind_planes(&pending_ref.a[0], eq_ref, true, x0));
                    scope.spawn(|| bind_planes(&pending_ref.a[1], eq_ref, true, x1));
                    scope.spawn(|| bind_planes(&pending_ref.a[2], eq_ref, true, x2));
                    scope.spawn(|| bind_planes(&pending_ref.b[0], eq_ref, false, y0));
                    scope.spawn(|| bind_planes(&pending_ref.b[1], eq_ref, false, y1));
                    scope.spawn(|| bind_planes(&pending_ref.b[2], eq_ref, false, y2));
                });
            } else {
                for s in 0..3 {
                    bind_planes(&self.pending.a[s], &eq, true, &mut x[s]);
                    bind_planes(&self.pending.b[s], &eq, false, &mut y[s]);
                }
            }
            #[cfg(not(feature = "std"))]
            for s in 0..3 {
                bind_planes(&self.pending.a[s], &eq, true, &mut x[s]);
                bind_planes(&self.pending.b[s], &eq, false, &mut y[s]);
            }
            let block_weights = &w.block;

            // Folding rounds. While a block still spans more than `WEIGHTED_BLOCK_ELEMS`
            // elements the round sums are accumulated block by block under the block
            // weights; then the weights are multiplied into `x` and the rounds are plain.
            let mut scratch = FoldScratch::new();
            let mut len = elems;
            let mut per_block = BLOCK_LANES;
            while len > 1 {
                let weighted = per_block > WEIGHTED_BLOCK_ELEMS;
                let bits = if weighted {
                    FIRST_FOLD_BITS
                } else {
                    FOLD_BITS.min((len - 1).ilog2() as usize + 1)
                };
                let tabs = SecretBuffer(if weighted {
                    fold_round_sums(
                        &x,
                        &y,
                        len,
                        bits,
                        per_block >> bits,
                        Some(block_weights),
                        &mut scratch,
                    )
                } else {
                    fold_round_sums(&x, &y, len, bits, FOLD_BATCH_CHUNKS, None, &mut scratch)
                });
                let shares = SecretBuffer(core::array::from_fn::<(Vec<Fe>, Vec<Fe>), 3, _>(|p| {
                    self.split_message(p, pass, round, &tabs[p], &mut share_prg[p])
                }));
                drop(tabs);
                let gammas = challenges(&self.proof_coin(seed, pass, round)?, bits);
                let coeff = round_coefficients(&gammas);
                let boolean: Vec<(usize, Fe)> = (1..1usize << bits)
                    .map(|u| (boolean_point(u, bits), FE_ONE))
                    .collect();
                for p in 0..3 {
                    claim1[p] = next_claim(claim1[p], &shares[p].0, &boolean, &coeff);
                    claim2[p] = next_claim(claim2[p], &shares[p].1, &boolean, &coeff);
                }
                drop(shares);
                let eq = eq_table(&gammas);
                let mut next = len;
                for s in 0..3 {
                    next = fold_vector(&mut x[s], len, &eq);
                    fold_vector(&mut y[s], len, &eq);
                }
                len = next;
                if weighted {
                    per_block >>= bits;
                    if per_block <= WEIGHTED_BLOCK_ELEMS {
                        for xs in x.iter_mut() {
                            for (j, v) in xs[..len].iter_mut().enumerate() {
                                *v = gf128_mul(block_weights[j / per_block], *v);
                            }
                        }
                    }
                }
                if pass == 0 {
                    sums += 3u64.pow(bits as u32) - 1;
                }
                round += 1;
            }
            if pass == 0 {
                rounds = u64::from(round) - 1;
            }

            // Final check of `x_p y_q + x_q y_p == claim` for every proof `p`, with the
            // verifiers' elements masked by `r` values the other verifier does not hold.
            let xf = SecretBuffer(core::array::from_fn::<Fe, 3, _>(|s| x[s][0]));
            let yf = SecretBuffer(core::array::from_fn::<Fe, 3, _>(|s| y[s][0]));
            let mut masks = SecretBuffer([[FE_ZERO; 4]; 3]);
            let mut cross = SecretBuffer(core::array::from_fn::<(Vec<Fe>, Vec<Fe>), 3, _>(|_| {
                (Vec::new(), Vec::new())
            }));
            for p in 0..3 {
                let q = (p + 1) % 3;
                mask1_prg[p].fill_words(masks[p][..2].as_flattened_mut());
                mask2_prg[p].fill_words(masks[p][2..].as_flattened_mut());
                let [r1x, r1y, r2x, r2y] = masks[p];
                let c0 = fe_add(gf128_mul(r1x, r2y), gf128_mul(r2x, r1y));
                let c1 = fe_add(
                    fe_add(gf128_mul(r1x, yf[q]), gf128_mul(xf[p], r2y)),
                    fe_add(gf128_mul(r2x, yf[p]), gf128_mul(xf[q], r1y)),
                );
                cross[p] =
                    self.split_message(p, pass, round, &[FE_ZERO, c0, c1], &mut share_prg[p]);
            }
            let tau = challenges(&self.proof_coin(seed, pass, round)?, 1)[0];
            let tau_sq = gf128_mul(tau, tau);
            for p in 0..3 {
                let q = (p + 1) % 3;
                let [r1x, r1y, r2x, r2y] = masks[p];
                let open = |r: Fe, v: Fe| fe_add(r, gf128_mul(tau, v));
                let masked_claim = |c: &[Fe], claim: Fe| {
                    fe_add(fe_add(c[1], gf128_mul(tau, c[2])), gf128_mul(tau_sq, claim))
                };
                // `V1` opens its slot-`p` elements and claim share, `V2` its slot-`q` ones.
                let from_v1 = [
                    open(r1x, xf[p]),
                    open(r1y, yf[p]),
                    masked_claim(&cross[p].0, claim1[p]),
                ];
                let from_v2 = [
                    open(r2x, xf[q]),
                    open(r2y, yf[q]),
                    masked_claim(&cross[p].1, claim2[p]),
                ];
                #[cfg(test)]
                if let Some(view) = &mut self.proof_view {
                    view.received[q].extend_from_slice(&from_v1);
                    view.received[(p + 2) % 3].extend_from_slice(&from_v2);
                }
                let lhs = fe_add(
                    gf128_mul(from_v1[0], from_v2[1]),
                    gf128_mul(from_v2[0], from_v1[1]),
                );
                let rhs = fe_add(from_v1[2], from_v2[2]);
                accepted &= (lhs[0] ^ rhs[0]) | (lhs[1] ^ rhs[1]) == 0;
            }
        }
        drop(tensor);
        drop(linear);
        self.pending.clear_and_wipe();
        if !accepted {
            return Err(Rss256Error::MultiplicationCheckFailed);
        }
        Ok(product_proof_cost(rounds, sums))
    }

    /// Open shared planes. Refused while unverified gates exist. Each slot share reaches the
    /// party that lacks it from both of its holders; the two copies are compared and a
    /// difference poisons the engine before anything is reconstructed.
    pub fn open_planes(&mut self, shares: [&[Plane]; 3]) -> Result<Vec<Plane>, Rss256Error> {
        self.guard()?;
        if self.unverified {
            return Err(Rss256Error::OpenBeforeCheck);
        }
        let n = shares[0].len();
        if shares[1].len() != n || shares[2].len() != n {
            return Err(Rss256Error::InvalidParameters);
        }
        let session_id = self.cluster.session_id;
        let salt = self.prev_digest;
        let mut out = vec![[0u64; 4]; n];
        for (slot, share) in shares.iter().enumerate() {
            // Commit each cut share before receiving its holder's echo. Only a gate's
            // released bytes enter reconstruction. `unverified == false` above is the
            // successful product-proof barrier; no pending chi relation may bypass it.
            let gates: Vec<_> = share
                .iter()
                .map(|plane| {
                    let bytes =
                        core::array::from_fn::<_, 32, _>(|i| plane[i / 8].to_le_bytes()[i % 8]);
                    let commitment = qsag_verified::compute_rss_mask_commitment(
                        &session_id,
                        slot as u8,
                        &bytes,
                        &salt,
                    );
                    qsag_verified::RssCutGateSession::new_round1_committed(session_id, commitment)
                })
                .collect();
            let mut echo: Vec<Plane> = share.to_vec();
            #[cfg(test)]
            for f in &self.faults {
                if let Fault256::OpenShare {
                    slot: fs,
                    plane,
                    mask,
                } = *f
                    && fs == slot
                    && plane < n
                {
                    for (x, m) in echo[plane].iter_mut().zip(mask) {
                        *x ^= m;
                    }
                }
            }
            for ((gate, plane), output) in gates.into_iter().zip(&echo).zip(&mut out) {
                let bytes = core::array::from_fn::<_, 32, _>(|i| plane[i / 8].to_le_bytes()[i % 8]);
                let commitment = qsag_verified::compute_rss_mask_commitment(
                    &session_id,
                    slot as u8,
                    &bytes,
                    &salt,
                );
                let (gate, bound) = gate.advance_round2_chi(session_id, commitment, bytes);
                if bound.is_err() {
                    qsag_asm::volatile_fill(&mut echo, [0; 4]);
                    qsag_asm::volatile_fill(&mut out, [0; 4]);
                    return self.poison(Rss256Error::OpenShareMismatch { slot });
                }
                // The product proof and both holder comparisons have accepted. This
                // engine uses replicated product proofs, with no SPDZ MAC residual.
                let (gate, checked) = gate.advance_round3_verify_consistency(session_id, 0, 0, 0);
                let (_, released) = gate.open_verified_cut(session_id);
                let Ok(mut released) = released else {
                    qsag_asm::volatile_fill(&mut echo, [0; 4]);
                    qsag_asm::volatile_fill(&mut out, [0; 4]);
                    return self.poison(Rss256Error::OpenShareMismatch { slot });
                };
                if checked.is_err() {
                    qsag_asm::volatile_fill(&mut released, 0);
                    return self.poison(Rss256Error::OpenShareMismatch { slot });
                }
                for (word, bytes) in output.iter_mut().zip(released.as_chunks::<8>().0.iter()) {
                    *word ^= u64::from_le_bytes(*bytes);
                }
                qsag_asm::volatile_fill(&mut released, 0);
            }
            qsag_asm::volatile_fill(&mut echo, [0; 4]);
        }
        // One slot share per party plus a digest of the copy it holds as second holder.
        self.stats.open_bytes += (n * 32) as u64 + 32;
        Ok(out)
    }

    /// Open the lanes of `value` selected by `lane_mask` as 32-byte values (lanes outside the
    /// mask are never revealed: every party masks its shares before sending).
    pub fn open_digests(
        &mut self,
        value: &SharedDigest256,
        lane_mask: &Plane,
        lanes: usize,
    ) -> Result<Vec<[u8; 32]>, Rss256Error> {
        let mut masked = SharedDigest256::zeroed();
        masked.xor_masked(value, lane_mask);
        let bytes_before = self.stats.open_bytes;
        let planes = self.open_planes([
            &masked.slot[0][..],
            &masked.slot[1][..],
            &masked.slot[2][..],
        ])?;
        // Only the selected lanes carry data, so charge those.
        let selected: u32 = lane_mask.iter().map(|w| w.count_ones()).sum();
        // This API accounts compact digest payloads, not the full-plane opening frame.
        self.stats.open_bytes = bytes_before + 32 * u64::from(selected);
        digests_from_planes(&planes, lanes)
    }
}

/// Bitsliced theta, rho and pi on one share slot of a wave (`plane = 64 * lane + bit`).
fn keccak_linear_layer(st: &[Plane; STATE_PLANES], out: &mut [Plane; STATE_PLANES]) {
    let mut c = [[[0u64; 4]; 64]; 5];
    for (x, column) in c.iter_mut().enumerate() {
        for (z, parity) in column.iter_mut().enumerate() {
            for w in 0..4 {
                parity[w] = st[x * 64 + z][w]
                    ^ st[(x + 5) * 64 + z][w]
                    ^ st[(x + 10) * 64 + z][w]
                    ^ st[(x + 15) * 64 + z][w]
                    ^ st[(x + 20) * 64 + z][w];
            }
        }
    }
    let mut d = [[[0u64; 4]; 64]; 5];
    for (x, column) in d.iter_mut().enumerate() {
        let prev = &c[(x + 4) % 5];
        let next = &c[(x + 1) % 5];
        for (z, value) in column.iter_mut().enumerate() {
            let rotated = &next[(z + 63) & 63];
            for w in 0..4 {
                value[w] = prev[z][w] ^ rotated[w];
            }
        }
    }
    for source in 0..25 {
        let x = source % 5;
        let y = source / 5;
        let target = y + 5 * ((2 * x + 3 * y) % 5);
        let rot = KECCAK_ROTATION_OFFSETS[source] as usize;
        for z in 0..64 {
            let src_z = (z + 64 - rot) & 63;
            let dst = &mut out[target * 64 + z];
            for w in 0..4 {
                dst[w] = st[source * 64 + src_z][w] ^ d[x][src_z][w];
            }
        }
    }
    qsag_asm::volatile_fill(&mut c, [[0; 4]; 64]);
    qsag_asm::volatile_fill(&mut d, [[0; 4]; 64]);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::keccak_mpc::{TSW_SUITE_MIDSTATE, run_dealerless_rss_dkg_2of3};
    use crate::sponge::keccak::{keccak_f1600, shake256_xof};

    fn rngs(tag: u8) -> [PartyPrivateRng; 3] {
        core::array::from_fn(|p| {
            PartyPrivateRng::from_seed([tag ^ ((p as u8) << 4); 32], b"rss256")
        })
    }

    fn engine(tag: u8) -> Rss256Engine {
        let sid = [tag; 32];
        let mut r = rngs(tag);
        let (keys, _) = run_dealerless_rss_dkg_2of3(sid, 32, &mut r).unwrap();
        Rss256Engine::new(sid, keys, r).unwrap()
    }

    #[test]
    fn independent_pass_coins_and_compact_open_accounting() {
        let mut e0 = engine(0x45);
        let mut e1 = engine(0x45);
        // Identical entropy positions: pass-domain binding itself changes the coin.
        let first = e0.proof_coin(&[9; 32], 0, 0).unwrap();
        let second = e1.proof_coin(&[9; 32], 1, 0).unwrap();
        assert_ne!(first, second);
        let before = e0.stats.open_bytes;
        let digest = SharedDigest256::zeroed();
        e0.open_digests(&digest, &active_lane_mask(3), 3).unwrap();
        assert_eq!(e0.stats.open_bytes - before, 3 * 32);
    }

    fn test_frames(n: usize, tag: u8) -> Vec<[u8; SHAKE256_RATE_BYTES]> {
        (0..n)
            .map(|lane| {
                let seed = [tag, lane as u8, (lane >> 8) as u8];
                let bytes = shake256_xof(SHAKE256_RATE_BYTES, &seed);
                bytes.try_into().unwrap()
            })
            .collect()
    }

    /// Reference: the same absorb of public frame and secret key, then the permutation.
    fn reference_states(
        frames: &[[u8; SHAKE256_RATE_BYTES]],
        key: &[u8; 32],
        key_off: usize,
    ) -> Vec<[u64; 25]> {
        frames
            .iter()
            .map(|frame| {
                let mut bytes = [0u8; 200];
                for (chunk, word) in bytes
                    .as_chunks_mut::<8>()
                    .0
                    .iter_mut()
                    .zip(&TSW_SUITE_MIDSTATE)
                {
                    *chunk = word.to_le_bytes();
                }
                for (b, f) in bytes.iter_mut().zip(frame) {
                    *b ^= *f;
                }
                for (i, k) in key.iter().enumerate() {
                    bytes[key_off + i] ^= *k;
                }
                let mut st = [0u64; 25];
                for (word, chunk) in st.iter_mut().zip(bytes.as_chunks::<8>().0) {
                    *word = u64::from_le_bytes(*chunk);
                }
                keccak_f1600(&mut st);
                st
            })
            .collect()
    }

    fn reconstruct_key(engine: &Rss256Engine) -> [u8; 32] {
        let slots = engine.sk_seed_slots();
        core::array::from_fn(|i| slots[0][i] ^ slots[1][i] ^ slots[2][i])
    }

    fn load(engine: &Rss256Engine, frames: &[[u8; SHAKE256_RATE_BYTES]]) -> SharedState256 {
        let mut st = SharedState256::from_public_frames(&TSW_SUITE_MIDSTATE, frames).unwrap();
        let mask = active_lane_mask(frames.len());
        st.xor_shared_key(40, engine.sk_seed_slots(), &mask)
            .unwrap();
        st
    }

    fn open_all(engine: &mut Rss256Engine, st: &SharedState256) -> Vec<Plane> {
        engine
            .open_planes([&st.slot[0][..], &st.slot[1][..], &st.slot[2][..]])
            .unwrap()
    }

    fn assert_matches_reference(planes: &[Plane], want: &[[u64; 25]]) {
        for (lane, state) in want.iter().enumerate() {
            for (i, plane) in planes.iter().enumerate() {
                let got = (plane[lane / 64] >> (lane % 64)) & 1;
                let exp = (state[i / 64] >> (i % 64)) & 1;
                assert_eq!(got, exp, "lane {lane} bit {i}");
            }
        }
    }

    #[test]
    fn prg_blocks_are_shake256_of_the_framed_nonce_and_domains_never_alias() {
        let key = [0x11u8; 32];
        let sid = [0x22u8; 32];
        let domain = (PURPOSE_CHI_PAD << 56) | 0x0123_4567;
        let mut prg = Shake256Prg256::new(&key, &sid, domain);
        let mut words = [0u64; 3 * WORDS_PER_X4];
        prg.fill_words(&mut words);
        for counter in 0..12u64 {
            let mut input = Vec::new();
            input.extend_from_slice(&key);
            input.extend_from_slice(&sid);
            input.extend_from_slice(&domain.to_le_bytes());
            input.extend_from_slice(&counter.to_le_bytes());
            let want = shake256_xof(SHAKE256_RATE_BYTES, &input);
            let call = (counter / 4) as usize;
            let lane = (counter % 4) as usize;
            for w in 0..SHAKE256_RATE_LANES {
                let got = words[call * WORDS_PER_X4 + 4 * w + lane];
                let exp = u64::from_le_bytes(want[8 * w..8 * w + 8].try_into().unwrap());
                assert_eq!(got, exp, "counter {counter} word {w}");
            }
        }
        // Worker tags `t` and `t + 16` under a 20-bit shift used to collide after a further
        // 40-bit shift; here the whole 64-bit domain is absorbed, so they cannot.
        let first = |domain: u64| {
            let mut p = Shake256Prg256::new(&key, &sid, domain);
            let mut w = [0u64; 8];
            p.fill_words(&mut w);
            w
        };
        for t in 0..8u64 {
            assert_ne!(first(t << 20), first((t + 16) << 20));
        }
        assert_ne!(first(1), first(1 << 56));
    }

    #[test]
    fn inline_mode_matches_keccak_f1600_on_full_and_partial_waves() {
        for (tag, lanes) in [(0x31u8, 256usize), (0x32, 58), (0x33, 1), (0x34, 129)] {
            let mut e = engine(tag);
            let frames = test_frames(lanes, tag);
            let key = reconstruct_key(&e);
            let mut st = load(&e, &frames);
            e.permute(&mut st, lanes).unwrap();
            // Opening before the barrier is refused.
            assert_eq!(
                e.open_planes([&st.slot[0][..], &st.slot[1][..], &st.slot[2][..]]),
                Err(Rss256Error::OpenBeforeCheck)
            );
            e.check().unwrap();
            let planes = open_all(&mut e, &st);
            assert_matches_reference(&planes, &reference_states(&frames, &key, 40));
            assert_eq!(
                e.stats().and_bytes,
                (AND_PLANES_PER_PERM * lanes).div_ceil(8) as u64
            );
        }
    }

    #[test]
    #[ignore = "replicated 2-of-3 permutation performance measurement"]
    fn measurement_replicated_wave() {
        extern crate std;
        for (tag, lanes) in [(0x51u8, 64usize), (0x52, 256)] {
            let mut e = engine(tag);
            let frames = test_frames(lanes, tag);
            let key = reconstruct_key(&e);
            let mut st = load(&e, &frames);
            let started = std::time::Instant::now();
            e.permute(&mut st, lanes).unwrap();
            e.check().unwrap();
            let elapsed = started.elapsed();
            std::eprintln!("replicated 2-of-3 {lanes}-lane permutation with barrier: {elapsed:?}");
            let planes = open_all(&mut e, &st);
            assert_matches_reference(&planes, &reference_states(&frames, &key, 40));
        }
    }

    #[test]
    fn chained_waves_and_masked_digest_opening_match_reference() {
        let lanes = 70;
        let mut e = engine(0x35);
        let frames = test_frames(lanes, 0x35);
        let key = reconstruct_key(&e);
        let mut st = load(&e, &frames);
        e.permute(&mut st, lanes).unwrap();
        let first = st.digest();
        // Second wave: every lane absorbs the first wave's 32-byte output at offset 8.
        let frames2 = test_frames(lanes, 0x36);
        let mut st2 = SharedState256::from_public_frames(&TSW_SUITE_MIDSTATE, &frames2).unwrap();
        st2.xor_shared_digest(8, &first).unwrap();
        e.permute(&mut st2, lanes).unwrap();
        e.check().unwrap();
        // Open only the odd lanes of the second output.
        let mut mask = [0u64; 4];
        for lane in (1..lanes).step_by(2) {
            mask[lane / 64] |= 1 << (lane % 64);
        }
        let opened = e.open_digests(&st2.digest(), &mask, lanes).unwrap();
        let ref1 = reference_states(&frames, &key, 40);
        for lane in 0..lanes {
            let mut d1 = [0u8; 32];
            for (chunk, word) in d1.as_chunks_mut::<8>().0.iter_mut().zip(&ref1[lane][..4]) {
                *chunk = word.to_le_bytes();
            }
            let want = reference_states(&frames2[lane..lane + 1], &d1, 8)[0];
            let mut d2 = [0u8; 32];
            for (chunk, word) in d2.as_chunks_mut::<8>().0.iter_mut().zip(&want[..4]) {
                *chunk = word.to_le_bytes();
            }
            if lane % 2 == 1 {
                assert_eq!(opened[lane], d2, "lane {lane}");
            } else {
                assert_eq!(
                    opened[lane], [0u8; 32],
                    "unselected lane {lane} must stay hidden"
                );
            }
        }
    }

    #[test]
    fn beaver_bank_mode_matches_reference_is_single_use_and_counts_double_wire() {
        let lanes = 256;
        let mut e = engine(0x41);
        e.stage_beaver_bank(2).unwrap();
        assert_eq!(e.bank().remaining_planes(), 2 * AND_PLANES_PER_PERM);
        assert_eq!(e.stats().and_bytes, 0);
        assert_eq!(e.stats().staged_lane_perms, 512);
        assert_eq!(
            e.stats().staged_state_bytes,
            (2 * 2 * 3 * AND_PLANES_PER_PERM * 32) as u64
        );
        e.set_mode(AndMode::BeaverBank).unwrap();
        let key = reconstruct_key(&e);
        for round in 0..2u8 {
            let frames = test_frames(lanes, 0x42 + round);
            let mut st = load(&e, &frames);
            e.permute(&mut st, lanes).unwrap();
            e.check().unwrap();
            let planes = open_all(&mut e, &st);
            assert_matches_reference(&planes, &reference_states(&frames, &key, 40));
        }
        assert_eq!(
            e.stats().and_bytes,
            2 * 2 * (AND_PLANES_PER_PERM * lanes / 8) as u64
        );
        assert_eq!(e.bank().remaining_planes(), 0);
        // Consumed triples are gone; a third permutation must not reuse any.
        let frames = test_frames(lanes, 0x44);
        let mut st = load(&e, &frames);
        assert_eq!(
            e.permute(&mut st, lanes),
            Err(Rss256Error::BeaverBankExhausted)
        );
    }

    #[test]
    fn check_seed_is_bound_to_every_transmitted_gate_message_and_to_the_coin() {
        let run = |fault: Option<Fault256>, rng_tag: u8| {
            let sid = [0x51; 32];
            let mut r = rngs(0x51);
            let (keys, _) = run_dealerless_rss_dkg_2of3(sid, 32, &mut r).unwrap();
            // Fresh coin randomness per run, same keys and inputs.
            let coin_rngs = rngs(rng_tag);
            let mut e = Rss256Engine::new(sid, keys, coin_rngs).unwrap();
            if let Some(f) = fault {
                e.inject_fault(f);
            }
            let frames = test_frames(4, 0x51);
            let mut st = load(&e, &frames);
            e.permute(&mut st, 4).unwrap();
            let result = e.check();
            (*e.last_check_seed(), result)
        };
        let (seed_a, ok_a) = run(None, 0x60);
        let (seed_a2, _) = run(None, 0x60);
        let (seed_b, ok_b) = run(None, 0x61);
        assert!(ok_a.is_ok() && ok_b.is_ok());
        assert_eq!(seed_a, seed_a2);
        assert_ne!(
            seed_a, seed_b,
            "fresh party randomness must change the seed"
        );
        // One flipped message bit: the transcript digest, hence the seed, changes, and the
        // proof run under that seed rejects.
        let (seed_c, bad) = run(
            Some(Fault256::GateMessage {
                wave: 0,
                round: 23,
                plane: 1599,
                sender: 2,
                mask: [1, 0, 0, 0],
            }),
            0x60,
        );
        assert_ne!(seed_c, seed_a);
        assert_eq!(bad, Err(Rss256Error::MultiplicationCheckFailed));
    }

    /// Every deviation of one corrupted party is caught at the barrier (or at the opening
    /// replica comparison), before any opening succeeds.
    #[test]
    fn active_faults_abort_before_any_opening() {
        let lanes = 256usize;
        let all = [u64::MAX; 4];
        let mut cases: Vec<(&str, Vec<Fault256>, Rss256Error)> = Vec::new();
        let gate = |wave, round, plane, sender, mask| Fault256::GateMessage {
            wave,
            round,
            plane,
            sender,
            mask,
        };
        // Single-bit flips: first/last round, first/last plane, every sender, every word.
        for (i, (round, plane, sender, word, bit)) in [
            (0usize, 0usize, 0usize, 0usize, 0u32),
            (0, 1599, 1, 3, 63),
            (23, 0, 2, 1, 17),
            (23, 1599, 0, 2, 5),
            (11, 777, 1, 0, 40),
            (5, 64, 2, 3, 0),
            (17, 1535, 0, 1, 63),
            (12, 800, 1, 2, 31),
        ]
        .into_iter()
        .enumerate()
        {
            let mut mask = [0u64; 4];
            mask[word] = 1 << bit;
            let _ = i;
            cases.push((
                "single-bit gate flip",
                vec![gate(0, round, plane, sender, mask)],
                Rss256Error::MultiplicationCheckFailed,
            ));
        }
        // Second wave of the same barrier.
        cases.push((
            "single-bit flip in a later wave",
            vec![gate(1, 3, 100, 0, [0, 1, 0, 0])],
            Rss256Error::MultiplicationCheckFailed,
        ));
        // Multi-bit patterns across the 256 lanes of chi gates.
        cases.push((
            "whole plane flipped",
            vec![gate(0, 7, 320, 1, all)],
            Rss256Error::MultiplicationCheckFailed,
        ));
        cases.push((
            "same gate flipped in two lanes",
            vec![gate(0, 9, 5, 2, [0b11, 0, 0, 0])],
            Rss256Error::MultiplicationCheckFailed,
        ));
        cases.push((
            "one chi row flipped in every lane",
            (0..5).map(|x| gate(0, 2, 64 * x + 9, 0, all)).collect(),
            Rss256Error::MultiplicationCheckFailed,
        ));
        cases.push((
            "same plane flipped in all 24 rounds",
            (0..24).map(|r| gate(0, r, 1234, 1, all)).collect(),
            Rss256Error::MultiplicationCheckFailed,
        ));
        cases.push((
            "130 scattered bits",
            (0..130usize)
                .map(|i| {
                    let mut mask = [0u64; 4];
                    mask[i % 4] = 1 << (i % 64);
                    gate(0, i % 24, (i * 37) % 1600, 2, mask)
                })
                .collect(),
            Rss256Error::MultiplicationCheckFailed,
        ));
        cases.push((
            "alternating-lane stripe over a full round",
            (0..1600)
                .map(|p| gate(0, 20, p, 0, [0x5555_5555_5555_5555; 4]))
                .collect(),
            Rss256Error::MultiplicationCheckFailed,
        ));
        cases.push((
            "pair of flips in successive rounds of one lane",
            vec![
                gate(0, 4, 10, 1, [1, 0, 0, 0]),
                gate(0, 5, 10, 1, [1, 0, 0, 0]),
            ],
            Rss256Error::MultiplicationCheckFailed,
        ));
        // Coin flip and transcript deviations.
        for party in 0..3 {
            cases.push((
                "bad coin-flip opening",
                vec![Fault256::CoinReveal { party }],
                Rss256Error::CoinOpeningRejected { party },
            ));
        }
        cases.push((
            "transcript digest disagreement",
            vec![Fault256::TranscriptDigest { slot: 1 }],
            Rss256Error::TranscriptMismatch { slot: 1 },
        ));
        assert!(cases.len() >= 20);

        for (idx, (name, faults, want)) in cases.into_iter().enumerate() {
            let mut e = engine(0x70 + idx as u8);
            for f in faults {
                e.inject_fault(f);
            }
            let frames = test_frames(lanes, 0x70);
            let mut st = load(&e, &frames);
            e.permute(&mut st, lanes).unwrap();
            let mut st2 = load(&e, &frames);
            e.permute(&mut st2, lanes).unwrap();
            assert_eq!(e.check(), Err(want), "case {idx}: {name}");
            // The barrier failed: the engine is poisoned and nothing can be opened, also
            // not after asking for the check again.
            assert!(
                e.has_unverified_gates() && e.is_poisoned(),
                "case {idx}: {name}"
            );
            assert_eq!(e.check(), Err(Rss256Error::Poisoned), "case {idx}: {name}");
            assert_eq!(
                e.open_planes([&st.slot[0][..], &st.slot[1][..], &st.slot[2][..]]),
                Err(Rss256Error::Poisoned),
                "case {idx}: {name}"
            );
        }
    }

    #[test]
    fn beaver_bank_and_opening_faults_are_caught() {
        // A corrupted product share while staging: the bank is rejected and discarded.
        let mut e = engine(0x81);
        e.inject_fault(Fault256::CoinReveal { party: 1 });
        assert_eq!(
            e.stage_beaver_bank(1),
            Err(Rss256Error::CoinOpeningRejected { party: 1 })
        );
        assert_eq!(e.bank().remaining_planes(), 0);

        // A forwarding holder lies about one opened mask-difference share.
        for (slot, round, plane, mask) in [
            (0usize, 0usize, 0usize, [1u64, 0, 0, 0]),
            (1, 13, 900, [0, 0, 1 << 63, 0]),
            (2, 23, 1599, [u64::MAX; 4]),
        ] {
            let mut e = engine(0x82 + slot as u8);
            e.stage_beaver_bank(1).unwrap();
            e.set_mode(AndMode::BeaverBank).unwrap();
            e.inject_fault(Fault256::BeaverOpening {
                wave: 0,
                round,
                plane,
                slot,
                mask,
            });
            let frames = test_frames(256, 0x82);
            let mut st = load(&e, &frames);
            e.permute(&mut st, 256).unwrap();
            assert_eq!(
                e.check(),
                Err(Rss256Error::OpeningConsistencyFailed { slot })
            );
            assert_eq!(e.check(), Err(Rss256Error::Poisoned));
            assert_eq!(
                e.open_planes([&st.slot[0][..], &st.slot[1][..], &st.slot[2][..]]),
                Err(Rss256Error::Poisoned)
            );
        }

        // After a clean barrier, one holder sends a different copy of an opened share.
        let mut e = engine(0x86);
        let frames = test_frames(8, 0x86);
        let mut st = load(&e, &frames);
        e.permute(&mut st, 8).unwrap();
        e.check().unwrap();
        e.inject_fault(Fault256::OpenShare {
            slot: 2,
            plane: 3,
            mask: [1, 0, 0, 0],
        });
        assert_eq!(
            e.open_planes([&st.slot[0][..], &st.slot[1][..], &st.slot[2][..]]),
            Err(Rss256Error::OpenShareMismatch { slot: 2 })
        );
        // The mismatch is terminal as well.
        assert_eq!(
            e.open_planes([&st.slot[0][..], &st.slot[1][..], &st.slot[2][..]]),
            Err(Rss256Error::Poisoned)
        );
    }

    /// A failed barrier cannot be retried into success: the relation evidence is gone, so
    /// the engine must refuse everything afterwards instead of accepting an empty check.
    #[test]
    fn a_failed_check_is_terminal_for_checks_openings_coins_and_evaluation() {
        let mut e = engine(0xA1);
        e.inject_fault(Fault256::GateMessage {
            wave: 0,
            round: 6,
            plane: 42,
            sender: 1,
            mask: [0, 0, 4, 0],
        });
        let frames = test_frames(16, 0xA1);
        let mut st = load(&e, &frames);
        e.permute(&mut st, 16).unwrap();
        assert!(!e.is_poisoned());
        assert_eq!(e.check(), Err(Rss256Error::MultiplicationCheckFailed));
        assert!(e.is_poisoned());
        // Second check: must not pass on the emptied relation buffer.
        assert_eq!(e.check(), Err(Rss256Error::Poisoned));
        assert_eq!(
            e.open_planes([&st.slot[0][..], &st.slot[1][..], &st.slot[2][..]]),
            Err(Rss256Error::Poisoned)
        );
        assert_eq!(
            e.open_digests(&st.digest(), &active_lane_mask(16), 16),
            Err(Rss256Error::Poisoned)
        );
        assert_eq!(e.joint_coin(b"label", &[0; 32]), Err(Rss256Error::Poisoned));
        assert_eq!(e.set_mode(AndMode::BeaverBank), Err(Rss256Error::Poisoned));
        assert_eq!(e.stage_beaver_bank(1), Err(Rss256Error::Poisoned));
        let mut st2 = load(&e, &frames);
        assert_eq!(e.permute(&mut st2, 16), Err(Rss256Error::Poisoned));
        assert!(e.is_poisoned() && e.has_unverified_gates());
    }

    /// A prover that deviates inside the proof (with honest gate messages) is rejected in
    /// every round and pass: the verifiers act on what they are sent.
    #[test]
    fn a_wrong_proof_message_is_rejected_in_every_round_and_pass() {
        // One 4-lane wave: 300 groups, six folding rounds, then the masked cross round.
        for (i, (prover, pass, round)) in [
            (0usize, 0usize, 0u32),
            (1, 1, 0),
            (2, 0, 1),
            (0, 1, 2),
            (1, 0, 3),
            (2, 1, 6),
            (0, 0, 7),
            (1, 1, 7),
        ]
        .into_iter()
        .enumerate()
        {
            let mut e = engine(0xB0 + i as u8);
            e.inject_fault(Fault256::ProofMessage {
                prover,
                pass,
                round,
            });
            let frames = test_frames(4, 0xB0);
            let mut st = load(&e, &frames);
            e.permute(&mut st, 4).unwrap();
            assert_eq!(
                e.check(),
                Err(Rss256Error::MultiplicationCheckFailed),
                "prover {prover} pass {pass} round {round}"
            );
            assert!(e.is_poisoned());
        }
        // A round index past the last round touches nothing: the proof accepts.
        let mut e = engine(0xBF);
        e.inject_fault(Fault256::ProofMessage {
            prover: 0,
            pass: 0,
            round: 8,
        });
        let frames = test_frames(4, 0xB0);
        let mut st = load(&e, &frames);
        e.permute(&mut st, 4).unwrap();
        e.check().unwrap();
    }

    fn test_elems(stream: &mut Shake256Prg256, n: usize) -> Vec<Fe> {
        let mut v = vec![FE_ZERO; n];
        stream.fill_words(v.as_flattened_mut());
        v
    }

    #[test]
    fn monomial_multiplication_and_ternary_expansion_match_their_definitions() {
        let mut stream = Shake256Prg256::new(&[5; 32], &[6; 32], 7);
        for v in test_elems(&mut stream, 8) {
            for i in 0..128u32 {
                let monomial = if i < 64 {
                    [1u64 << i, 0]
                } else {
                    [0, 1u64 << (i - 64)]
                };
                assert_eq!(fe_mul_x_pow(v, i), gf128_mul(v, monomial), "x^{i}");
            }
        }
        for (bits, row) in [(1usize, 1usize), (2, 5), (3, 16), (4, 3), (TENSOR_BITS, 1)] {
            let points = 3usize.pow(bits as u32);
            let src = test_elems(&mut stream, (1 << bits) * row);
            let mut buf = vec![FE_ZERO; points * row];
            buf[..src.len()].copy_from_slice(&src);
            ternary_expand(&mut buf, bits, row);
            for e in 0..points {
                for k in 0..row {
                    let mut want = FE_ZERO;
                    for u in 0..1usize << bits {
                        let mut digits = e;
                        let mut selected = true;
                        for l in 0..bits {
                            let d = digits % 3;
                            digits /= 3;
                            selected &= d == 2 || d == (u >> l) & 1;
                        }
                        if selected {
                            want = fe_add(want, src[u * row + k]);
                        }
                    }
                    assert_eq!(buf[e * row + k], want, "bits {bits} point {e} cell {k}");
                }
            }
            for u in 0..1usize << bits {
                let e = boolean_point(u, bits);
                assert_eq!(&buf[e * row..(e + 1) * row], &src[u * row..(u + 1) * row]);
            }
        }
    }

    #[test]
    fn bound_vectors_are_the_weighted_sums_of_the_selected_planes() {
        let mut stream = Shake256Prg256::new(&[8; 32], &[9; 32], 10);
        let groups = 2;
        let mut planes = vec![[0u64; 4]; groups * GROUP_PLANES];
        stream.fill_planes(&mut planes, 4);
        let eq = test_elems(&mut stream, GROUP_PLANES);
        for lane_weights in [false, true] {
            let mut out = vec![FE_ZERO; groups * LANES];
            bind_planes(&planes, &eq, lane_weights, &mut out);
            for g in 0..groups {
                for lane in 0..LANES {
                    let mut want = FE_ZERO;
                    for (u, weight) in eq.iter().enumerate() {
                        let plane = &planes[g * GROUP_PLANES + u];
                        if (plane[lane / 64] >> (lane % 64)) & 1 == 1 {
                            want = fe_add(want, *weight);
                        }
                    }
                    if lane_weights {
                        want = fe_mul_x_pow(want, (lane % BLOCK_LANES) as u32);
                    }
                    assert_eq!(out[g * LANES + lane], want, "group {g} lane {lane}");
                }
            }
        }
    }

    /// One folding round maps a true claim about the vectors to a true claim about the
    /// folded vectors, with and without batch weights and with a partial last chunk.
    #[test]
    fn a_folding_round_carries_the_claim_to_the_folded_vectors() {
        let mut stream = Shake256Prg256::new(&[11; 32], &[12; 32], 13);
        let cross =
            |x: &[Vec<Fe>; 3], y: &[Vec<Fe>; 3], len: usize, p: usize, w: &dyn Fn(usize) -> Fe| {
                let q = (p + 1) % 3;
                let mut acc = FE_ZERO;
                for j in 0..len {
                    let term = fe_add(gf128_mul(x[p][j], y[q][j]), gf128_mul(x[q][j], y[p][j]));
                    acc = fe_add(acc, gf128_mul(w(j), term));
                }
                acc
            };
        for (len, bits, batch_chunks, weighted) in [
            (256usize, 4usize, 8usize, true),
            (512, 2, 32, true),
            (128, 2, 8, true),
            (300, 4, 64, false),
            (19, 4, 64, false),
            (5, 3, 64, false),
            (2, 1, 64, false),
        ] {
            let mut x: [Vec<Fe>; 3] = core::array::from_fn(|_| test_elems(&mut stream, len));
            let mut y: [Vec<Fe>; 3] = core::array::from_fn(|_| test_elems(&mut stream, len));
            let size = 1usize << bits;
            let batches = len.div_ceil(size).div_ceil(batch_chunks);
            let weights = test_elems(&mut stream, batches);
            let weight_of = |j: usize| {
                if weighted {
                    weights[j / (size * batch_chunks)]
                } else {
                    FE_ONE
                }
            };
            let mut scratch = FoldScratch::new();
            let tabs = fold_round_sums(
                &x,
                &y,
                len,
                bits,
                batch_chunks,
                weighted.then_some(&weights[..]),
                &mut scratch,
            );
            let gammas = test_elems(&mut stream, bits);
            let coeff = round_coefficients(&gammas);
            let boolean: Vec<(usize, Fe)> = (1..size)
                .map(|u| (boolean_point(u, bits), FE_ONE))
                .collect();
            let claims: [Fe; 3] = core::array::from_fn(|p| cross(&x, &y, len, p, &weight_of));
            let eq = eq_table(&gammas);
            let mut folded = len;
            for s in 0..3 {
                folded = fold_vector(&mut x[s], len, &eq);
                fold_vector(&mut y[s], len, &eq);
            }
            assert_eq!(folded, len.div_ceil(size));
            let folded_weight = |c: usize| weight_of(c * size);
            for p in 0..3 {
                let next = next_claim(claims[p], &tabs[p], &boolean, &coeff);
                assert_eq!(
                    next,
                    cross(&x, &y, folded, p, &folded_weight),
                    "len {len} bits {bits} prover {p}"
                );
                // A false claim stays false.
                let wrong = next_claim(fe_add(claims[p], FE_ONE), &tabs[p], &boolean, &coeff);
                assert_ne!(wrong, next);
            }
        }
    }

    /// The tensor round maps the weighted gate claim to a claim about the bound vectors.
    #[test]
    fn the_tensor_round_carries_the_gate_claim_to_the_bound_vectors() {
        let mut stream = Shake256Prg256::new(&[14; 32], &[15; 32], 16);
        let groups = 3;
        let mut pending = PendingGates::new();
        for s in 0..3 {
            for planes in [
                &mut pending.a[s],
                &mut pending.b[s],
                &mut pending.msg[s],
                &mut pending.pad[s],
            ] {
                planes.resize(groups * GROUP_PLANES, [0; 4]);
                stream.fill_planes(planes, 4);
            }
        }
        let chi = test_elems(&mut stream, 2);
        let weights = [
            PassWeights::new(chi[0], 2 * groups),
            PassWeights::new(chi[1], 2 * groups),
        ];
        let tabs = tensor_tables(&pending, groups, &weights);
        let linear = linear_terms(&pending, groups, &weights);
        // Weight of bit `i` of block `h` of plane `u` of group `g`.
        let block_sum = |w: &PassWeights, f: &dyn Fn(usize) -> Plane| {
            let mut acc = FE_ZERO;
            for g in 0..groups {
                for u in 0..GROUP_PLANES {
                    let plane = f(g * GROUP_PLANES + u);
                    for h in 0..2 {
                        let weight = gf128_mul(w.block[2 * g + h], w.plane[u]);
                        acc = fe_add(acc, gf128_mul(weight, [plane[2 * h], plane[2 * h + 1]]));
                    }
                }
            }
            acc
        };
        for (pass, w) in weights.iter().enumerate() {
            let gammas = test_elems(&mut stream, TENSOR_BITS);
            let coeff = round_coefficients(&gammas);
            let eq = eq_table(&gammas);
            let mut x: [Vec<Fe>; 3] = core::array::from_fn(|_| vec![FE_ZERO; groups * LANES]);
            let mut y: [Vec<Fe>; 3] = core::array::from_fn(|_| vec![FE_ZERO; groups * LANES]);
            for s in 0..3 {
                bind_planes(&pending.a[s], &eq, true, &mut x[s]);
                bind_planes(&pending.b[s], &eq, false, &mut y[s]);
            }
            for p in 0..3 {
                let q = (p + 1) % 3;
                // The single-verifier terms are the weighted sums of their definitions.
                let v1 = block_sum(w, &|k| {
                    core::array::from_fn(|i| {
                        pending.msg[p][k][i]
                            ^ pending.pad[p][k][i]
                            ^ (pending.a[p][k][i] & pending.b[p][k][i])
                    })
                });
                assert_eq!(linear[pass][p][0], v1);
                assert_eq!(linear[pass][q][1], block_sum(w, &|k| pending.pad[q][k]));
                // Weighted cross-product claim, then the round.
                let claim = block_sum(w, &|k| {
                    core::array::from_fn(|i| {
                        (pending.a[p][k][i] & pending.b[q][k][i])
                            ^ (pending.a[q][k][i] & pending.b[p][k][i])
                    })
                });
                let next = next_claim(claim, &tabs[pass][p], &w.boolean_weights(), &coeff);
                let mut want = FE_ZERO;
                for j in 0..groups * LANES {
                    let term = fe_add(gf128_mul(x[p][j], y[q][j]), gf128_mul(x[q][j], y[p][j]));
                    want = fe_add(want, gf128_mul(w.block[j / BLOCK_LANES], term));
                }
                assert_eq!(next, want, "pass {pass} prover {p}");
            }
        }
    }

    /// Key wiring and one-time-pad structure of the product proof, and the balance of what
    /// each party is sent in it.
    #[test]
    fn proof_messages_and_openings_are_padded_by_keys_the_observer_does_not_hold() {
        // Proof of sender `p`: `V1 = p - 1` derives its shares and opening masks from slot key
        // `p`; `V2 = p + 1` derives its opening masks from slot key `p + 1`.
        for p in 0..3 {
            let (v1, v2) = ((p + 2) % 3, (p + 1) % 3);
            assert!(slots_held_by(p).contains(&p) && slots_held_by(v1).contains(&p));
            assert!(
                !slots_held_by(v2).contains(&p),
                "V2 must not hold the share-stream key"
            );
            assert!(slots_held_by(p).contains(&v2) && slots_held_by(v2).contains(&v2));
            assert!(
                !slots_held_by(v1).contains(&v2),
                "V1 must not hold V2's mask key"
            );
        }

        // The value sent to `V2` is the prover value plus a stream word `V2` cannot compute:
        // for any two prover values a shift of that word gives the same message. The same
        // holds for an opening `r + tau * value` and its mask `r`.
        let mut stream = Shake256Prg256::new(&[17; 32], &[18; 32], 19);
        for _ in 0..32 {
            let [v_a, v_b, mask, tau] = test_elems(&mut stream, 4)[..] else {
                unreachable!()
            };
            let sent = fe_add(v_a, mask);
            assert_eq!(fe_add(v_b, fe_add(mask, fe_add(v_a, v_b))), sent);
            let opened = fe_add(mask, gf128_mul(tau, v_a));
            let shifted = fe_add(mask, gf128_mul(tau, fe_add(v_a, v_b)));
            assert_eq!(fe_add(shifted, gf128_mul(tau, v_b)), opened);
        }

        // Everything a party is sent in the proofs of a real barrier (its shares as `V2`, the
        // other verifier's openings) should look uniform: the count of ones stays within six
        // standard deviations of one half, and no value repeats.
        let mut e = engine(0xC1);
        let frames = test_frames(256, 0xC1);
        let mut st = load(&e, &frames);
        e.permute(&mut st, 256).unwrap();
        e.capture_proof_view();
        e.check().unwrap();
        let view = e.take_proof_view().unwrap();
        for (party, received) in view.received.iter().enumerate() {
            // Two passes: tensor sums, folding rounds of 8, 8, 80, 80, 80 and 2 sums (76,800
            // elements fold to 19,200, 4,800, 300, 19, 2, 1), two cross coefficients, and
            // three openings from each of the two proofs it verifies.
            assert_eq!(
                received.len(),
                2 * (TENSOR_POINTS - 1 + 2 * 8 + 3 * 80 + 2 + 2 + 6)
            );
            let bits = (128 * received.len()) as f64;
            let ones: u32 = received.iter().flatten().map(|w| w.count_ones()).sum();
            let dev = (f64::from(ones) - bits / 2.0).abs();
            assert!(
                dev < 6.0 * (bits / 4.0).sqrt(),
                "party {party}: {ones} ones"
            );
            let mut sorted = received.clone();
            sorted.sort_unstable();
            sorted.dedup();
            assert_eq!(
                sorted.len(),
                received.len(),
                "party {party}: repeated value"
            );
        }
    }

    /// Pad-key wiring and one-time-pad structure of the gate messages.
    #[test]
    fn no_observer_holds_both_pads_and_each_view_is_a_shift_of_the_missing_pad() {
        // Wiring: for every sender and every other party, at least one pad of the sender's
        // message is keyed by a slot the observer does not hold.
        for sender in 0..3 {
            for observer in 0..3 {
                if observer == sender {
                    continue;
                }
                let held = slots_held_by(observer);
                let unknown: Vec<usize> = sender_pad_slots(sender)
                    .into_iter()
                    .filter(|s| !held.contains(s))
                    .collect();
                assert_eq!(
                    unknown.len(),
                    1,
                    "observer {observer} must miss exactly one pad of sender {sender}"
                );
            }
            // The receiver of `u_sender` is party `sender - 1`: it misses pad `sender + 1`,
            // the slot it also holds no share of.
            let receiver = (sender + 2) % 3;
            assert!(!slots_held_by(receiver).contains(&((sender + 1) % 3)));
        }

        // One-time pad: fix everything the receiver knows (the sender's slot-`p` inputs and
        // pad `p`). For any two values of the slot-`q` inputs the receiver does not hold,
        // shifting the missing pad by a fixed difference yields the identical message, so the
        // message is a bijective image of a uniform pad and independent of those inputs.
        let mut stream = Shake256Prg256::new(&[7; 32], &[9; 32], 1);
        let mut w = [0u64; 9];
        for _ in 0..64 {
            stream.fill_words(&mut w);
            let [a_p, b_p, pad_p, a_q1, b_q1, a_q2, b_q2, pad_q, _] = w;
            let m1 = and_message(a_p, a_q1, b_p, b_q1, pad_p, pad_q);
            let m2 = and_message(a_p, a_q2, b_p, b_q2, pad_p, pad_q);
            let shift = m1 ^ m2;
            assert_eq!(and_message(a_p, a_q2, b_p, b_q2, pad_p, pad_q ^ shift), m1);
        }

        // The three messages of a gate reconstruct the product: the pads cancel.
        for _ in 0..64 {
            let mut v = [0u64; 9];
            stream.fill_words(&mut v);
            let (a, b, r) = ([v[0], v[1], v[2]], [v[3], v[4], v[5]], [v[6], v[7], v[8]]);
            let mut sum = 0u64;
            for p in 0..3 {
                let q = (p + 1) % 3;
                sum ^= and_message(a[p], a[q], b[p], b[q], r[p], r[q]);
            }
            assert_eq!(sum, (a[0] ^ a[1] ^ a[2]) & (b[0] ^ b[1] ^ b[2]));
        }
    }

    #[test]
    fn engine_gate_messages_are_balanced_for_fixed_inputs() {
        // With all inputs fixed, each sender's message stream over a full wave should look
        // uniform: the count of ones stays within six standard deviations of one half.
        let mut e = engine(0x91);
        let frames = test_frames(256, 0x91);
        let mut st = load(&e, &frames);
        e.capture_next_messages();
        e.permute(&mut st, 256).unwrap();
        let captured = e.take_captured_messages().unwrap();
        e.check().unwrap();
        let bits = (AND_PLANES_PER_PERM * 256) as f64;
        for (sender, planes) in captured.iter().enumerate() {
            assert_eq!(planes.len(), AND_PLANES_PER_PERM);
            let ones: u64 = planes
                .iter()
                .flat_map(|p| p.iter())
                .map(|w| u64::from(w.count_ones()))
                .sum();
            let dev = (ones as f64 - bits / 2.0).abs();
            assert!(
                dev < 6.0 * (bits / 4.0).sqrt(),
                "sender {sender}: {ones} ones"
            );
        }
    }

    #[test]
    fn horner_eval_matches_naive_powers() {
        let mut stream = Shake256Prg256::new(&[3; 32], &[4; 32], 5);
        for n in [1usize, 2, 511, 512, 513, 1500] {
            let mut flat = vec![0u64; 2 * n + 2];
            stream.fill_words(&mut flat);
            let point = [flat[0], flat[1]];
            let words: Vec<[u64; 2]> = flat[2..].as_chunks::<2>().0.to_vec();
            let mut want = [0u64; 2];
            for (k, w) in words.iter().enumerate() {
                let term = gf128_mul(*w, gf128_pow(point, n - k));
                want[0] ^= term[0];
                want[1] ^= term[1];
            }
            assert_eq!(horner_eval(&words, point), want, "n = {n}");
        }
    }

    #[test]
    fn malformed_offsets_and_digest_planes_rejected() {
        let frames = test_frames(4, 0x77);
        let mut st = SharedState256::from_public_frames(&TSW_SUITE_MIDSTATE, &frames).unwrap();
        let d = SharedDigest256::zeroed();
        assert_eq!(
            st.xor_shared_digest(169, &d),
            Err(Rss256Error::InvalidParameters)
        );
        assert_eq!(
            st.xor_shared_digest(usize::MAX, &d),
            Err(Rss256Error::InvalidParameters)
        );
        let key = [0u8; 32];
        assert_eq!(
            st.xor_shared_key(usize::MAX - 10, [&key, &key, &key], &[1, 0, 0, 0]),
            Err(Rss256Error::InvalidParameters)
        );
        let bad_planes = vec![[0u64; 4]; 257];
        assert_eq!(
            digests_from_planes(&bad_planes, 1),
            Err(Rss256Error::InvalidParameters)
        );
    }
}
