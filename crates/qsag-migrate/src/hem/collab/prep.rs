//! Dealerless preprocessing for [`super::engine`]: the quorum members produce their own
//! [`Preprocessing`] stores (shares of the two Goldilocks MAC keys, Beaver triples and
//! uniform values), with no party that knows a key or a shared value.
//!
//! The target is security with abort against any `m - 1` actively corrupted members of
//! an `m`-member quorum. All parties' steps run in one process on separated per-party
//! state (the model of `qsag_core::preprocessing::run_dealerless_pi_triple_f2`); data
//! that one party sends to another is absorbed into a transcript chain, and every
//! challenge is expanded from a commit-and-open coin drawn over that chain after the
//! checked data has been sent. It is an in-process ceremony driver, not a wire protocol.
//!
//! # Where this comes from
//!
//! This is the Goldilocks part of the ceremony of the earlier general-quorum engine,
//! `threshold_prep/dealerless.rs` (removed; last present in commit 894d7dc), carried over
//! as self-contained code. Copied from that file, specialised to Goldilocks and otherwise
//! unchanged in what is sent, checked and erased: `xof`, `element_from`, `pad_element`,
//! `Prg` (its field stream), `Challenges`, `commitment`, `Transcript`, `Pair`,
//! `FieldQueue`, `Check`, `Fault`, and of `Ceremony` the methods `coin`,
//! `commit_then_open`, `sample`, `field_key_for` (here `key_for`), `sample_field_keys`
//! (`sample_keys`), `establish_pairs`, `cope`, `authenticate`, `open`, `expect_zero`,
//! `check_field_queue` (`check_queue`), `multiply`, `sacrifice` and the triple, random
//! and key-consistency part of `field_stage`. The share arithmetic (`mac_add`, `mac_sub`,
//! `mac_scale`) is that of `threshold_mpc.rs` for Goldilocks.
//!
//! Not carried over, because nothing of [`super::engine`] uses it: Boolean triples and
//! the Boolean MAC key, doubly authenticated bits (with the bit proof `prove_bits`, the
//! cross-domain check and the XOR chain), the 255- to 381-bit fields, and the per-peer
//! `BlindOtPeer` correlation that the earlier online engine used to blind its MAC-check
//! openings.
//!
//! Changed: the base OT batch of a pair has 192 OTs instead of 1472 (two key words and
//! the zero word; see the review below); a share is `[value, MAC_0, MAC_1]` of
//! `Goldilocks` instead of two six-limb values; commit-then-open payloads carry two words
//! per MAC instead of six; every domain-separation string is new
//! (`QSAG.COLLAB.PREP.*/v1`); and a demand is produced in batches (below). The output of
//! the two ceremonies is therefore not byte-identical for equal inputs.
//!
//! # The sharing
//!
//! As in the earlier ceremony and as [`super::engine`] expects: a value `x` is held as
//! additive shares of `x`, `alpha_0 x` and `alpha_1 x` over the quorum, for two
//! independent Goldilocks keys whose shares are additive too. The share of a public
//! constant puts the value at party 0.
//!
//! # Building blocks
//!
//! * **Base correlation.** For every ordered pair (owner `o`, holder `h`) one batch of
//!   192 random OTs from the mesh, with `h` as receiver and the bits of `h`'s two key
//!   shares as choice bits. Each pad seeds a cSHAKE256 stream; all later authentications
//!   between the pair read these streams, so the key `h` uses towards `o` is fixed once
//!   (COPE, MASCOT: Keller, Orsini, Scholl, CCS 2016, ePrint 2016/505, Section 3). The
//!   last 64 OTs have choice bit 0: their first pads are common to the pair and mask the
//!   openings of the key-consistency check.
//! * **Authentication** (`Ceremony::authenticate`). The owner sends, per key bit,
//!   `t0 - t1 + x`; the holder obtains `t0 + bit x`. Summed with weights `2^l` this
//!   shares `key_h x`. An opened random combination with an authenticated mask and a
//!   commit-then-open MAC check makes the owner's inputs consistent (MASCOT Section 4,
//!   Input and Check).
//! * **Triples** (`Ceremony::multiply`, MASCOT Section 5, Protocol 4): the party holding
//!   `a` is the OT receiver with the bits of `a` as choices, the sender's correlation is
//!   its `b`; privacy amplification over `tau` components, authentication, sacrifice.
//! * **Key consistency**: a holder is bound to one key towards all owners by opening
//!   and MAC-checking the sum over the owners of one uniform item per key.
//!
//! # Parameters
//!
//! Quoted from the module documentation of `threshold_prep/dealerless.rs`, with
//! `k = log2 |F| = 64`:
//!
//! * [`TAU`] and the number [`SACRIFICES`] of sacrificial triples. A corrupted sender in
//!   `Ceremony::multiply` can use different correlations in different OTs and learns,
//!   from whether the sacrifice passes, a predicate of the receiver's `a` in `F^tau`.
//!   Conditioning a uniform source on an event of probability `q` costs `log2(1/q)` bits
//!   of min-entropy, and the event itself has probability `q`. The combination
//!   `a -> (<a,r>, <a,r^_1>, ..., <a,r^_sigma>)` with coin-chosen `r, r^` is a universal
//!   hash onto `F^(1+sigma)` (the `r^` components are masks of the opened `s a - a^`). By
//!   the leftover hash lemma the output is within
//!   `q 1/2 2^-((tau k - log2(1/q) - (1+sigma) k)/2) <= 1/2 2^-((tau-1-sigma) k/2)` of
//!   uniform. `sigma` is fixed by sacrifice soundness `|F|^-sigma`: `sigma = 2` for
//!   Goldilocks (`2^-128`). Then `tau = 7` gives `2^-129` (`tau = 6` would give only
//!   `2^-97`).
//! * Goldilocks carries two independent 64-bit MAC keys. Every random combination is
//!   drawn independently per key, or (owner input check) twice with every instance
//!   checked under both keys, so that no event of probability `2^-64` defeats both.
//! * Batch MAC check: a wrong opened value passes with probability at most `2/|F|` per
//!   key, `2^-126`. Key consistency: `2^-128`. Input check: see the review below.
//!
//! None of this is machine-checked, and the ceremony relies on the security of the
//! `qsag-core` OT mesh and commit-and-open coin.
//!
//! # Batches
//!
//! The earlier ceremony ran one stage per field for the whole demand, which holds the
//! pads of `448 * triples` OTs per ordered pair in memory at once (144 bytes each). A
//! zk-Hem proof needs millions of triples, so here the demand is produced in batches of
//! at most [`BATCH_TRIPLES`] triples: the keys and the base correlation are established
//! once, and each batch is one complete run of the stage (multiplication, authentication
//! with its input check, key-consistency check, sacrifice with its MAC check) on fresh
//! coins over the one transcript chain. This is this module's change, not the earlier
//! file's; the per-batch checks are the same checks, and the earlier ceremony already
//! authenticated several batches on one base correlation (its second authentication of
//! a stage).
//!
//! # Review: the base correlation, and selective failure across batches
//!
//! References: **MASCOT** `[KOS16]` (Keller, Orsini, Scholl, CCS 2016, ePrint 2016/505);
//! **KOS** `[KOS15]` (Keller, Orsini, Scholl, CRYPTO 2015, ePrint 2015/546); **Roy**
//! `[Roy22]` (Roy, *SoftSpokenOT*, CRYPTO 2022, ePrint 2022/192, rev. 2025-11-18).
//! "Theorem" below means a statement proven in a cited paper; "claim" means an argument
//! of this module that no paper states in this form.
//!
//! ## What the 192 base OTs are, and why the count is not a security parameter
//!
//! The 192 OTs of a pair are not the base OTs of an OT extension. They are 192 OTs
//! taken *from* the mesh's extension (three choice words; the mesh works in 64-bit
//! words), used as the Initialize step of COPE (MASCOT Section 3, Protocol 1): one OT
//! per bit of the holder's key share, the holder choosing with that bit. COPE needs
//! exactly `k = 64` OTs per key, no more and no fewer, so `2 * 64 = 128` OTs carry the
//! two Goldilocks keys; of the third (zero) word only OT 128 is used, for the pair's
//! common mask stream, and OTs 129..191 are drawn and never read. The earlier file's
//! 1,472 were 23 words for the keys of five fields and the Boolean key plus the same
//! zero word (its `BASE_WORDS`); 192 is that count restricted to Goldilocks, which is
//! all [`super::engine`] has. Nothing was traded away, and no larger count would buy
//! anything: there is no bound in which this count appears.
//!
//! What stands in for the count is the length of what is derived from the 128 pads.
//! Theorem (MASCOT Theorem 1, proven as Lemma 1 of its Appendix A): COPE realises its
//! functionality in the OT-hybrid model for any number of Extend calls if the function
//! expanding the pads is a PRF. Here a pad is 48 bytes and its PRF is the cSHAKE256
//! stream of `Prg`; a batch reads `7 t + r + 4` elements from each stream, so one HASH160
//! statement (2,228,208 triples) reads about `1.6 * 10^7` elements, 125 MB, per stream.
//! Claim: what a corrupted party of a pair gains from this reuse is its advantage in
//! distinguishing that much cSHAKE256 output under an unknown 384-bit seed from uniform,
//! per stream; the batches do not enter otherwise, because the streams are read on, never
//! restarted.
//!
//! The OTs of the triple multiplication (448 per triple and ordered pair, `10^9` per
//! pair for one statement) are not derived from the 192: every batch draws them fresh
//! from the mesh.
//!
//! ## The extension underneath: IKNP columns with the SoftSpokenOT consistency check
//!
//! Every OT above comes from one `qsag-core` mesh channel per ordered pair: 128
//! base OTs (combined from 384 Ring-LWE OTs), one correlation `Delta` in `GF(2)^128`
//! fixed for the life of the mesh, IKNP columns, and per frame the consistency check of
//! Roy Fig. 9 for the length-128 repetition code: a `GF(2)`-linear universal hash
//! `[X | I_256]` (a two-point polynomial hash over `GF(2^128)` plus 256 sacrificial
//! rows) of the receiver's choice bits and of each of its 128 columns, keyed by the
//! sender after the columns arrived, compared by the sender column by column; the
//! channel is poisoned for good on a failed check. Rows are hashed into pads with a
//! tweak that is distinct for every extended OT of a channel. The construction, the
//! proof obligations and the tests are in the module doc of
//! `qsag_core::preprocessing` ("Correlated OT extension and its consistency
//! check"); what follows is what this module relies on. Paper: Roy, revision of
//! 2025-11-18, `2022-roy-softspokenot-2022-192-rev20251118`.
//!
//! Theorem (Roy Theorem 4.5): the columns with that check realise subspace VOLE
//! against malicious parties, with selective-abort leakage an affine subspace of
//! `GF(2)^128` and distinguishing advantage at most `eps q/(q-1) + q^(-t-1)`. With the
//! mesh's parameters (`q = 2`, at most 8,190 hashed blocks per frame, so
//! `eps < 2^-230`, and `t = 116.7`) that is `2^-229 + 2^-117.7` per frame. Claim of the
//! mesh, not of the paper: the second term belongs to the pre-commitment property,
//! which Roy Theorem 5.1 uses only for extended OTs that share a tweak, and no two do,
//! so the check costs `2 eps < 2^-229`. Theorem (Roy Theorem 5.1 with Proposition
//! 2.6): the hashed rows are malicious random OTs with no leakage to their consumer,
//! at an advantage of at most `(q_H + q'/2) 2^-128` for `q_H` hash queries and `q'`
//! extended OTs when the pad hash is a random oracle; that term already contains the
//! selective abort (guessing `c` bits of `Delta` passes with probability `2^-c` and
//! leaves `2^(128-c)` work), independently of how many frames reuse `Delta`. Claim of
//! the mesh: its single-block Keccak pad hash is modelled as that oracle.
//!
//! So the security of this ceremony against a corrupted OT receiver (the holder in
//! COPE, the holder of `a` in a multiplication) rests on proven statements: 128-bit
//! computational security in the random-oracle model, with the statistical terms
//! above. This replaces the correlation check of KOS Fig. 7, which the mesh ran
//! before and whose Theorem 1 has no valid proof (Roy, Section 4.1.3 and Appendix D);
//! an earlier version of this section had to call the same property conjectured.
//!
//! What a receiver would gain from a channel's `Delta`, and so what the bound above
//! protects: both pads of every OT the other party ever sent on that channel, hence,
//! as COPE holder, every value the owner authenticated (its shares of all triples and
//! uniform values of the ceremony), and as multiplication receiver the sender's `b`
//! shares. The MAC keys are not exposed this way (an honest party's key share is its
//! *choice* input, and the extension never lets a sender test a receiver's choice
//! bits: the sender sends nothing but the hash key, and every key keeps the hashed
//! choice bits hidden behind the sacrificial rows).
//!
//! ## Selective failure across batches
//!
//! Three checks can fail depending on a secret of an honest party. Every failure
//! aborts the ceremony, and the keys and all material of the run are discarded; so a
//! predicate is learnt for good only by passing, and what must be bounded is the
//! probability of passing times what passing is worth.
//!
//! 1. *Input check of `Ceremony::authenticate`: bits of an honest holder's key share.*
//!    A corrupted owner may encode different values under different key bits of an honest
//!    holder (MASCOT Section 4.1). The sum of the opened check shares is then, per key
//!    and instance, a function fixed by the owner's messages and the coin
//!    (`sum_l 2^l bit_l E_l` minus what the owner adds), linear in the *bits* of the
//!    honest holders' shares of that one key. All of it is independent of the key shares, which are
//!    uniform in `F`. Claim: after any number of input checks, in any number of batches,
//!    chosen adaptively, the event "all passed" is `key in S` for a set `S = S_0 x S_1`
//!    (one factor per key, since no equation mixes the keys) that the adversary's view
//!    determines; it has probability `|S_0| |S_1| / |F|^2`, and given it the keys are
//!    uniform on `S`. That is the whole cross-batch argument: the batches intersect sets,
//!    and the probability of an intersection is its size. "Guessing `c` key bits succeeds
//!    with probability `2^-c`" is the special case of coordinate sets; an `S` need not be
//!    one, but its cost is always its density. A later forgery against key `j` (a MAC
//!    share for a value other than the committed one) amounts to naming the sum of the
//!    honest parties' shares of key `j`, so `Pr[all checks pass and key j is forged]` is
//!    at most the largest probability of one value of that sum, `1/|F|`, whatever was
//!    guessed, and `|F|^-2`, about `2^-128`, for a forgery under both keys, which is
//!    what the engine's MAC check and the batch MAC check here require (the check
//!    shares of both keys must sum to zero). A key whose 64 bits were all guessed
//!    (probability `2^-64`) leaves the other key untouched. MASCOT proves the
//!    single-check version of this as Theorem 2 (Appendix B, with Lemma 2 for prime
//!    fields, where bit vectors and field elements do not correspond one to one); the
//!    extension to repeated checks on one key, which MASCOT also performs (every Input
//!    call reuses the COPE instance), and to two keys is this module's claim.
//!
//!    Binding is a second matter. A check that passes without any guess still
//!    commits the owner to one value per item only
//!    if no two of the up to 64 per-bit encodings collide under the random combination.
//!    Theorem (MASCOT Theorem 2): one check gives statistical security
//!    `log|F| - 2 log log|F|`, which is 52 bits for Goldilocks, not 64, and "a repeated
//!    check would suffice for security parameter `log |F|`" (Section 4.1). This module
//!    runs two instances with independent coefficients and masks, each under both keys.
//!    Claim: to keep two encodings of one key open the same pair must collide in both
//!    instances, probability at most `C(64,2) |F|^-2 < 2^-116` per owner, key and
//!    batch, below `2^-102` over the 2,178 batches of a HASH160 statement for three
//!    members.
//!
//! 2. *Sacrifice: bits of an honest receiver's `a`.* A corrupted sender of
//!    `Ceremony::multiply` learns a predicate of the `tau = 7` components of `a` of the
//!    triples it attacked (MASCOT Section 5.1). Those components are fresh per triple,
//!    so nothing accumulates across batches except the abort. Theorem (MASCOT Theorem
//!    3, Appendix C): with one sacrificial pair, `tau = 4` gives statistical security
//!    `k`. Claim (the parameter item above): with two pairs and `tau = 7` each output
//!    triple is within `2^-129` of uniform to the adversary, `2^-107` summed over the
//!    `2^21.1` triples of a statement; a wrong triple survives both sacrificial pairs
//!    with probability `2^-128`, once for the whole ceremony since a failure aborts.
//!
//! 3. *The mesh's consistency check: bits of a sender's `Delta`.* See the previous
//!    section: a passing guess is an affine subspace containing `Delta`, and a failed
//!    check poisons the channel, so the guesses over all frames, all batches and all
//!    ceremonies on one mesh are one attempt, already counted in that section's bound.
//!
//! The key-consistency check and the batch MAC checks fail on the adversary's own
//! deviation only, independently of honest secrets.
//!
//! Against the targets: per MAC key the bound is `1/|F|`, `2^-64`, and for both keys
//! together `2^-128` up to the `2^-102` binding term, per ceremony, for any number of
//! batches. A ceremony that aborts teaches the adversary nothing it can use against a
//! rerun (fresh keys), but each rerun is a new attempt, so these are per-attempt
//! figures. All of it holds in the hybrid model with ideal OTs, coins, commitments and
//! broadcast; the first of these is what the theorems of the previous section provide,
//! at the advantage stated there.

#![allow(clippy::needless_range_loop, clippy::type_complexity)]

#[path = "prep_wire.rs"]
mod wire;
pub use wire::run_party_preprocessing;

use alloc::{vec, vec::Vec};

use qsag_accel::keccak::{Shake256, cshake256_framed_32, finalize_cshake256, init_cshake256};
use qsag_core::{
    field::goldilocks::Goldilocks,
    preprocessing::{
        MAX_FRAME_BUDGET, OtBatchPads, OtMesh, PartyPrivateRng, run_commit_and_open_coin,
    },
    wipe::{SecretBuffer as Secret, SecretScratch as SecretVec, wipe_bytes},
};

use super::engine::{Preprocessing, Sb};

type F = Goldilocks;
/// One party's MAC share, or its key share: one component per key.
type Mac = [F; 2];
/// One party's share of an authenticated value: `[value, MAC_0, MAC_1]`.
type Share = [F; 3];

/// Components of `a` per raw triple (see the module documentation).
pub const TAU: usize = 7;
/// Sacrificial triples per output triple; soundness `|F|^-SACRIFICES`.
pub const SACRIFICES: usize = 2;
/// Largest number of triples produced by one run of the stage.
pub const BATCH_TRIPLES: usize = 1024;

/// Independent MAC keys.
const KEYS: usize = 2;
/// Values each party authenticates per triple: `a, b, c` and `SACRIFICES` pairs `(a^, c^)`.
const TRIPLE_INPUTS: usize = 3 + 2 * SACRIFICES;
/// Choice words of one base-OT batch: the two key shares and one zero word. The holder
/// receives the owner's first pad of every OT of the zero word, so the stream of such a
/// pad is known to exactly that pair.
const BASE_WORDS: usize = KEYS + 1;
/// The OT whose first pad seeds the pair's common mask stream.
const SHARED_BASE: usize = 64 * KEYS;

/// How much material every member's store must hold.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PrepDemand {
    pub triples: usize,
    pub randoms: usize,
}

/// The check that stopped a ceremony.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Check {
    /// A base or triple OT batch was rejected by the mesh.
    Ot,
    /// A commit-and-open coin did not open to its commitments.
    Coin,
    /// A commit-then-open payload did not match its commitment.
    Commitment,
    /// An owner's inputs were not the same under every key bit, or a holder's MAC share
    /// was not the one its key determines.
    InputConsistency,
    /// A holder used different keys towards different owners.
    KeyConsistency,
    /// A triple is not multiplicative, or an opening of the sacrifice was wrong.
    TripleSacrifice,
}

/// Why a ceremony returned nothing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PrepError {
    /// The party count, the mesh and the generators do not describe one quorum of 2 to
    /// 64 members, or the demand cannot be allocated.
    InvalidConfiguration,
    Transport(super::net::NetError),
    /// A check failed: some member deviated. All keys and material of the run are erased.
    Check(Check),
}

impl From<Check> for PrepError {
    fn from(check: Check) -> Self {
        Self::Check(check)
    }
}

/// A point where one party can deviate. The ceremony passes each point to the fault hook
/// with the data the party is about to use; an honest hook leaves it unchanged. Parties
/// are quorum positions.
pub enum Fault<'a> {
    /// The key share `holder` commits to in its base OTs with `owner` and uses in every
    /// check of `owner`'s inputs.
    FieldKey {
        owner: usize,
        holder: usize,
        key: &'a mut [Goldilocks; 2],
    },
    /// The values `owner` encodes for `holder` under bit `bit` of key `key`.
    CopeInput {
        owner: usize,
        holder: usize,
        key: usize,
        bit: usize,
        values: &'a mut [Goldilocks],
    },
    /// `holder`'s MAC shares of one batch of `owner`'s values.
    CopeHolderShare {
        owner: usize,
        holder: usize,
        macs: &'a mut [[Goldilocks; 2]],
    },
    /// The correlation `sender` uses in one OT of the triple multiplication.
    TripleCorrelation {
        sender: usize,
        receiver: usize,
        triple: usize,
        slot: usize,
        bit: usize,
        correlation: &'a mut Goldilocks,
    },
    /// `party`'s raw product shares, [`TAU`] per triple.
    TripleProduct {
        party: usize,
        products: &'a mut [Goldilocks],
    },
    /// The value share `party` sends in a partial opening that `check` settles.
    FieldOpening {
        party: usize,
        check: Check,
        share: &'a mut Goldilocks,
    },
    /// The check share `party` commits to for one opened item of the key-consistency
    /// check, after every party's value share of that item (`sent`, by party) is public.
    KeyConsistencySigma {
        party: usize,
        sent: &'a [Goldilocks],
        sigma: &'a mut [Goldilocks; 2],
    },
    /// The commitment `party` sends in commit-then-open invocation `invocation` of the
    /// ceremony.
    Commitment {
        invocation: u64,
        party: usize,
        commitment: &'a mut [u8; 32],
    },
    /// The nonce `party` opens its commitment of invocation `invocation` with.
    CommitmentNonce {
        invocation: u64,
        party: usize,
        nonce: &'a mut [u8; 32],
    },
}

// ============================================================================
// Encoding, sampling, share arithmetic
// ============================================================================

fn xof(label: &[u8], frames: &[&[u8]]) -> Shake256 {
    let mut sponge = init_cshake256(b"", label);
    sponge.absorb(&(frames.len() as u64).to_le_bytes());
    for frame in frames {
        sponge.absorb(&(frame.len() as u64).to_le_bytes());
        sponge.absorb(frame);
    }
    finalize_cshake256(&mut sponge, true);
    sponge
}

/// Uniform canonical element by rejection from `fill`.
fn element_from(mut fill: impl FnMut(&mut [u8])) -> F {
    let mut bytes = [0u8; 8];
    loop {
        fill(&mut bytes);
        if let Ok(value) = F::from_canonical(u64::from_le_bytes(bytes)) {
            wipe_bytes(&mut bytes);
            return value;
        }
    }
}

/// Field element from one 48-byte random-OT pad. Candidates are read from the pad until
/// one is canonical; the last is reduced. The result is within `2^-192` of uniform.
fn pad_element(pad: &[u8; 48]) -> F {
    let mut value = 0;
    for chunk in pad.chunks_exact(8) {
        value = u64::from_le_bytes(chunk.try_into().unwrap());
        if let Ok(element) = F::from_canonical(value) {
            return element;
        }
    }
    F::from_u64_reduced(value)
}

/// cSHAKE256 stream expanding one OT pad.
struct Prg(Shake256);
impl Prg {
    fn new(
        session: &[u8; 32],
        sender: usize,
        receiver: usize,
        index: usize,
        pad: &[u8; 48],
    ) -> Self {
        Self(xof(
            b"QSAG.COLLAB.PREP.PAD/v1",
            &[
                session,
                &[sender as u8, receiver as u8],
                &(index as u64).to_le_bytes(),
                pad,
            ],
        ))
    }
    fn elements(&mut self, out: &mut [F]) {
        let mut block = [0u8; 8 * 136];
        for chunk in out.chunks_mut(block.len() / 8) {
            let bytes = &mut block[..chunk.len() * 8];
            self.0.squeeze(bytes);
            // A rejected word is replaced from the stream after its block.
            for (value, raw) in chunk.iter_mut().zip(bytes.chunks_exact(8)) {
                *value = match F::from_canonical(u64::from_le_bytes(raw.try_into().unwrap())) {
                    Ok(element) => element,
                    Err(_) => element_from(|bytes| self.0.squeeze(bytes)),
                };
            }
        }
        wipe_bytes(&mut block);
    }
}

/// Public challenge expansion of one coin.
struct Challenges(Shake256);
impl Challenges {
    fn element(&mut self) -> F {
        element_from(|bytes| self.0.squeeze(bytes))
    }
}

#[inline(always)]
fn mac_is_zero(mac: Mac) -> bool {
    let [a, b] = mac_words(mac);
    qsag_accel::ct::ct_eq_u64(a | b, 0)
}

#[inline(always)]
fn mac_add(a: Mac, b: Mac) -> Mac {
    [a[0] + b[0], a[1] + b[1]]
}
#[inline(always)]
fn mac_sub(a: Mac, b: Mac) -> Mac {
    [a[0] - b[0], a[1] - b[1]]
}
/// MAC (or MAC key) times a field element.
#[inline(always)]
fn mac_scale(mac: Mac, by: F) -> Mac {
    [mac[0] * by, mac[1] * by]
}
#[inline(always)]
fn mac_of(share: Share) -> Mac {
    [share[1], share[2]]
}
#[inline(always)]
fn share_add(a: Share, b: Share) -> Share {
    [a[0] + b[0], a[1] + b[1], a[2] + b[2]]
}
#[inline(always)]
fn share_sub(a: Share, b: Share) -> Share {
    [a[0] - b[0], a[1] - b[1], a[2] - b[2]]
}
#[inline(always)]
fn share_scale(a: Share, by: F) -> Share {
    [a[0] * by, a[1] * by, a[2] * by]
}
fn to_engine(share: Share) -> Sb {
    Sb {
        v: share[0],
        m: [share[1], share[2]],
    }
}
fn mac_words(mac: Mac) -> [u64; 2] {
    [mac[0].to_canonical_u64(), mac[1].to_canonical_u64()]
}

/// Commitment of `party` to `payload` in commit-then-open invocation `invocation` of the
/// ceremony `session`. The invocation number is part of the preimage, so a commitment
/// and its opening are valid in one invocation only, whatever the label and the payload.
fn commitment(
    session: &[u8; 32],
    label: &[u8],
    invocation: u64,
    party: usize,
    payload: &[u64],
    nonce: &[u8; 32],
) -> [u8; 32] {
    let bytes: SecretVec<u8> = payload.iter().flat_map(|w| w.to_le_bytes()).collect();
    cshake256_framed_32(
        b"QSAG.COLLAB.PREP.COMMIT/v1",
        &[
            session,
            label,
            &invocation.to_le_bytes(),
            &[party as u8],
            &bytes,
            nonce,
        ],
    )
}

/// Hash chain over everything the parties send each other. The schedule of messages and
/// all lengths are public functions of the party count and the demand, so the
/// concatenation parses uniquely.
struct Transcript {
    chain: [u8; 32],
    buffer: Vec<u8>,
    sponge: Shake256,
}
impl Transcript {
    const BLOCK: usize = 64 * 136;
    fn new(session: &[u8; 32]) -> Self {
        let mut transcript = Self {
            chain: *session,
            buffer: Vec::with_capacity(Self::BLOCK + 64),
            sponge: Shake256::new(),
        };
        transcript.restart();
        transcript
    }
    fn restart(&mut self) {
        self.sponge = Shake256::new();
        self.buffer.clear();
        self.buffer
            .extend_from_slice(b"QSAG.COLLAB.PREP.TRANSCRIPT/v1");
        self.buffer.extend_from_slice(&self.chain);
    }
    fn bytes(&mut self, data: &[u8]) {
        self.buffer.extend_from_slice(data);
        if self.buffer.len() >= Self::BLOCK {
            // Whole rate blocks keep the sponge on its word-wise path.
            let full = self.buffer.len() - self.buffer.len() % 136;
            self.sponge.absorb(&self.buffer[..full]);
            self.buffer.drain(..full);
        }
    }
    fn label(&mut self, label: &[u8]) {
        self.bytes(&(label.len() as u64).to_le_bytes());
        self.bytes(label);
    }
    fn element(&mut self, value: F) {
        self.bytes(&value.to_le_bytes());
    }
    fn digest(&mut self) -> [u8; 32] {
        self.sponge.absorb(&self.buffer);
        self.sponge.finalize(0x1f);
        self.sponge.squeeze(&mut self.chain);
        self.restart();
        self.chain
    }
}

// ============================================================================
// Ceremony state
// ============================================================================

/// Base correlation of one ordered pair, indexed by choice bit.
struct Pair {
    /// Owner side: the streams of both pads.
    send: Vec<[Prg; 2]>,
    /// Holder side: the stream of the pad its key bit selected.
    receive: Vec<Prg>,
}

/// Partially opened values and values claimed to be zero, awaiting one batch MAC check.
struct FieldQueue {
    values: Vec<F>,
    /// `macs[p][entry]`.
    macs: Vec<SecretVec<Mac>>,
}
impl FieldQueue {
    fn new(parties: usize) -> Self {
        Self {
            values: Vec::new(),
            macs: (0..parties).map(|_| SecretVec::new()).collect(),
        }
    }
}

/// `shares[o][p][item]`: party `p`'s share of owner `o`'s authenticated item.
type OwnerShares = Vec<Vec<SecretVec<Share>>>;

struct Ceremony<'a> {
    session: [u8; 32],
    parties: usize,
    mesh: &'a mut OtMesh,
    rngs: &'a mut [PartyPrivateRng],
    fault: &'a mut dyn FnMut(Fault<'_>),
    transcript: Transcript,
    coins: u64,
    /// Commit-then-open invocations started so far.
    commits: u64,
    keys: SecretVec<Mac>,
    /// `[o][h]`: the key `h` committed to in its base OTs with `o`.
    pair_keys: Vec<SecretVec<Mac>>,
    pairs: Vec<Vec<Option<Pair>>>,
    /// Payload bytes each party has sent so far (see [`Ceremony::sends`]).
    sent: Vec<u64>,
}

impl<'a> Ceremony<'a> {
    fn new(
        session: [u8; 32],
        mesh: &'a mut OtMesh,
        rngs: &'a mut [PartyPrivateRng],
        fault: &'a mut dyn FnMut(Fault<'_>),
    ) -> Result<Self, PrepError> {
        let parties = rngs.len();
        if !(2..=64).contains(&parties) || mesh.n != parties {
            return Err(PrepError::InvalidConfiguration);
        }
        Ok(Self {
            transcript: Transcript::new(&session),
            session,
            parties,
            mesh,
            rngs,
            fault,
            coins: 0,
            commits: 0,
            keys: SecretVec::new(),
            pair_keys: Vec::new(),
            pairs: Vec::new(),
            sent: vec![0; parties],
        })
    }

    /// Accounts `bytes` of payload that `party` sends to each of `peers` parties. The
    /// ceremony runs in one process, so this is the size of what a wire run would carry
    /// (field elements as 8 bytes, digests and nonces as 32, no framing), with a
    /// broadcast counted once per other party.
    fn sends(&mut self, party: usize, bytes: usize, peers: usize) {
        self.sent[party] += (bytes * peers) as u64;
    }

    /// Accounts every party's broadcast of `bytes`.
    fn all_send(&mut self, bytes: usize) {
        for party in 0..self.parties {
            self.sends(party, bytes, self.parties - 1);
        }
    }

    /// One batch of `64 * choices.len()` random OTs from the mesh with `receiver`'s
    /// choice bits, and its traffic: per frame of the mesh the receiver's 128 columns
    /// over the frame's words and four sacrificial words and its 32-byte proof, and the
    /// sender's 32-byte challenge.
    fn random_ots(
        &mut self,
        sender: usize,
        receiver: usize,
        choices: &[u64],
    ) -> Result<OtBatchPads, PrepError> {
        const FRAME_WORDS: usize = MAX_FRAME_BUDGET / (128 * 8) - 4;
        let pads = self
            .mesh
            .run_correlated_ot_words(sender, receiver, choices, self.rngs)
            .map_err(|_| Check::Ot)?;
        for frame in choices.chunks(FRAME_WORDS) {
            self.sends(receiver, 128 * 8 * (frame.len() + 4) + 32, 1);
            self.sends(sender, 32, 1);
        }
        Ok(pads)
    }

    /// Jointly random public coin over the transcript so far, as a challenge stream.
    ///
    /// The mesh's chain over all OT extension batches run so far is absorbed first, so
    /// the coin also depends on every OT message sent before it.
    fn coin(&mut self, label: &[u8]) -> Result<Challenges, PrepError> {
        self.transcript.label(b"ot mesh");
        self.transcript.bytes(&self.mesh.transcript_digest());
        let digest = self.transcript.digest();
        let mut phase = label.to_vec();
        phase.extend_from_slice(&self.coins.to_le_bytes());
        self.coins = self.coins.checked_add(1).ok_or(Check::Coin)?;
        let coin = run_commit_and_open_coin(&self.session, &phase, &digest, self.rngs)
            .map_err(|_| Check::Coin)?;
        // Every party broadcasts a commitment and then its 32-byte share.
        self.all_send(64);
        self.transcript.label(b"coin");
        self.transcript.bytes(&coin);
        Ok(Challenges(xof(
            b"QSAG.COLLAB.PREP.CHALLENGE/v1",
            &[&self.session, &phase, &coin],
        )))
    }

    /// Every party commits to its payload; after all commitments are sent the payloads
    /// are opened and compared with them.
    ///
    /// Every call takes the next value of the ceremony's invocation counter, which
    /// enters each commitment and the transcript: what a party sent in one invocation
    /// opens in no other.
    fn commit_then_open(
        &mut self,
        label: &[u8],
        payloads: &[SecretVec<u64>],
    ) -> Result<(), PrepError> {
        let invocation = self.commits;
        self.commits = invocation.checked_add(1).ok_or(Check::Commitment)?;
        let mut nonces: SecretVec<[u8; 32]> = SecretVec::with_capacity(payloads.len());
        let mut commitments = Vec::with_capacity(payloads.len());
        self.transcript.label(label);
        self.transcript.bytes(&invocation.to_le_bytes());
        for (party, payload) in payloads.iter().enumerate() {
            nonces.push(self.rngs[party].next_bytes32());
            let mut digest = commitment(
                &self.session,
                label,
                invocation,
                party,
                payload,
                &nonces[party],
            );
            (self.fault)(Fault::Commitment {
                invocation,
                party,
                commitment: &mut digest,
            });
            self.transcript.bytes(&digest);
            commitments.push(digest);
        }
        for (party, payload) in payloads.iter().enumerate() {
            (self.fault)(Fault::CommitmentNonce {
                invocation,
                party,
                nonce: &mut nonces[party],
            });
            let opened = commitment(
                &self.session,
                label,
                invocation,
                party,
                payload,
                &nonces[party],
            );
            if !qsag_asm::ct_eq_32(&opened, &commitments[party]) {
                return Err(Check::Commitment.into());
            }
            for word in payload.iter() {
                self.transcript.bytes(&word.to_le_bytes());
            }
            // Commitment, then payload and nonce.
            self.sends(party, 64 + 8 * payload.len(), payloads.len() - 1);
        }
        Ok(())
    }

    fn sample(&mut self, party: usize) -> F {
        let rng = &mut self.rngs[party];
        element_from(|bytes| rng.fill_bytes(bytes))
    }

    /// The key share `party` uses in a check of material that `owner` alone input
    /// (`None`: material combined over the owners).
    fn key_for(&self, owner: Option<usize>, party: usize) -> &Mac {
        match owner {
            Some(owner) if owner != party => &self.pair_keys[owner][party],
            _ => &self.keys[party],
        }
    }

    // ------------------------------------------------------------------------
    // Keys and base correlation
    // ------------------------------------------------------------------------

    /// Every party samples its two key shares.
    fn sample_keys(&mut self) {
        for party in 0..self.parties {
            self.keys.push([F::ZERO; 2]);
            for key in 0..KEYS {
                let value = Secret(self.sample(party));
                self.keys[party][key] = *value;
            }
        }
    }

    /// One batch of random OTs per ordered pair, the holder receiving on the bits of its
    /// key shares. The holder cannot use another key for a single value later: its pads
    /// are fixed here.
    fn establish_pairs(&mut self) -> Result<(), PrepError> {
        let parties = self.parties;
        for owner in 0..parties {
            let mut keys = SecretVec::with_capacity(parties);
            let mut row = Vec::with_capacity(parties);
            for holder in 0..parties {
                let mut key = Secret(self.keys[holder]);
                if holder == owner {
                    keys.push(*key);
                    row.push(None);
                    continue;
                }
                (self.fault)(Fault::FieldKey {
                    owner,
                    holder,
                    key: &mut key,
                });
                let mut choices: SecretVec<u64> = SecretVec::with_capacity(BASE_WORDS);
                choices.extend_from_slice(&mac_words(*key));
                choices.push(0);
                let (send, receive) = self.random_ots(owner, holder, &choices)?;
                let session = &self.session;
                row.push(Some(Pair {
                    send: send
                        .iter()
                        .enumerate()
                        .map(|(index, (zero, one))| {
                            [
                                Prg::new(session, owner, holder, index, zero),
                                Prg::new(session, owner, holder, index, one),
                            ]
                        })
                        .collect(),
                    receive: receive
                        .iter()
                        .enumerate()
                        .map(|(index, pad)| Prg::new(session, owner, holder, index, pad))
                        .collect(),
                }));
                keys.push(*key);
            }
            self.pair_keys.push(keys);
            self.pairs.push(row);
        }
        Ok(())
    }

    // ------------------------------------------------------------------------
    // Authentication
    // ------------------------------------------------------------------------

    /// COPE extension of `inputs` between `owner` and `holder` under key `key`. Returns
    /// `(T, Q)` with `Q[k] = T[k] + key_h * inputs[k]`: `T` is the owner's, `Q` the
    /// holder's.
    fn cope(
        &mut self,
        owner: usize,
        holder: usize,
        key: usize,
        inputs: &[F],
    ) -> (SecretVec<F>, SecretVec<F>) {
        let count = inputs.len();
        let base = 64 * key;
        let Self {
            pairs,
            fault,
            transcript,
            pair_keys,
            sent,
            ..
        } = self;
        let key_share = Secret(pair_keys[owner][holder][key].to_canonical_u64());
        let pair = pairs[owner][holder].as_mut().unwrap();
        let zeros = || SecretVec::from(vec![F::ZERO; count]);
        let (mut t, mut q) = (zeros(), zeros());
        let (mut zero, mut one, mut chosen, mut encoded) = (zeros(), zeros(), zeros(), zeros());
        transcript.label(b"cope");
        sent[owner] += (8 * 64 * count) as u64;
        for bit in (0..64).rev() {
            pair.send[base + bit][0].elements(&mut zero);
            pair.send[base + bit][1].elements(&mut one);
            pair.receive[base + bit].elements(&mut chosen);
            encoded.copy_from_slice(inputs);
            fault(Fault::CopeInput {
                owner,
                holder,
                key,
                bit,
                values: &mut encoded,
            });
            let select = Secret(0u64.wrapping_sub((*key_share >> bit) & 1));
            for k in 0..count {
                // Owner to holder.
                let correction = zero[k] - one[k] + encoded[k];
                transcript.element(correction);
                let received =
                    chosen[k] + F::from_u64_reduced(correction.to_canonical_u64() & *select);
                t[k] = t[k] + t[k] + zero[k];
                q[k] = q[k] + q[k] + received;
            }
        }
        (t, q)
    }

    /// Every owner authenticates its `inputs[o]` (equal lengths) towards all other
    /// parties.
    ///
    /// Party `p`'s MAC share of owner `o`'s item is `Q` from the pair `(o, p)`, and
    /// `o`'s own is `key_o x - sum_h T_h`.
    ///
    /// **Input check** (MASCOT Section 4). Each owner appends uniformly random mask
    /// items. After all corrections are sent a coin fixes `r`; the owner opens
    /// `y = sum r_k x_k + mask` and every party commits to and then opens
    /// `sigma_p = sum r_k m_k + m_mask - key_p y`; the `sigma_p` must sum to zero. This
    /// runs twice with independent `r` and masks, each instance under both keys.
    ///
    /// If the owner encoded different values under different key bits of an honest
    /// holder, the holder's share is off by `sum_l 2^l bit_l e_l` with `e_l` fixed by the
    /// corrections; the sum of the `sigma` is that error (combined by `r`) plus what the
    /// owner adds without knowing the key bits. The check then passes exactly when the
    /// holder's key lies in a set `S` that the owner's messages and the coin determine,
    /// which happens with probability `|S|/|F|` because the key is independent of both.
    /// So a failed check tells the adversary that the key is outside `S` (and the
    /// ceremony's keys are then discarded), and a passed check that it is inside:
    /// guessing `c` key bits succeeds with probability `2^-c` and leaves a later forgery
    /// probability of `2^c/|F|`, the product staying at `1/|F|` per key. The check
    /// passes for every key although two encodings differ only if they collide under
    /// `r`: at most `C(64,2)/|F|`, `2^-53`, in one instance (MASCOT Theorem 2), and the
    /// same pair must collide in both. The module documentation carries this over all
    /// batches.
    /// Nothing about any shared value is revealed either way: `y` is masked, and whether
    /// the check passes depends on key bits only. A holder cannot choose its key per
    /// value (its pads are fixed), and a wrong MAC share of the holder changes the sum
    /// of the `sigma` by a nonzero amount it cannot cancel without the owner's pads.
    fn authenticate(&mut self, inputs: &[SecretVec<F>]) -> Result<OwnerShares, PrepError> {
        let parties = self.parties;
        let count = inputs[0].len();
        let total = count + KEYS;

        let mut values: Vec<SecretVec<F>> = Vec::with_capacity(parties);
        let mut macs: Vec<Vec<SecretVec<Mac>>> = Vec::with_capacity(parties);
        for owner in 0..parties {
            let mut extended: SecretVec<F> = inputs[owner].iter().copied().collect();
            for _ in count..total {
                let mask = self.sample(owner);
                extended.push(mask);
            }
            let own_key = Secret(self.keys[owner]);
            let mut shares: Vec<SecretVec<Mac>> = (0..parties)
                .map(|_| SecretVec::from(vec![[F::ZERO; 2]; total]))
                .collect();
            for k in 0..total {
                shares[owner][k] = mac_scale(*own_key, extended[k]);
            }
            for holder in (0..parties).filter(|&h| h != owner) {
                for key in 0..KEYS {
                    let (t, q) = self.cope(owner, holder, key, &extended);
                    for k in 0..total {
                        shares[owner][k][key] -= t[k];
                        shares[holder][k][key] = q[k];
                    }
                }
                (self.fault)(Fault::CopeHolderShare {
                    owner,
                    holder,
                    macs: &mut shares[holder],
                });
            }
            values.push(extended);
            macs.push(shares);
        }

        let mut challenges = self.coin(b"authenticate")?;
        let mut sigmas: Vec<SecretVec<u64>> = (0..parties).map(|_| SecretVec::new()).collect();
        self.transcript.label(b"input check");
        for owner in 0..parties {
            for instance in 0..KEYS {
                let mask = count + instance;
                let mut opened = values[owner][mask];
                let mut sigma: SecretVec<Mac> =
                    (0..parties).map(|p| macs[owner][p][mask]).collect();
                for k in 0..count {
                    let r = challenges.element();
                    opened += r * values[owner][k];
                    for p in 0..parties {
                        sigma[p] = mac_add(sigma[p], mac_scale(macs[owner][p][k], r));
                    }
                }
                // The owner broadcasts the combination.
                self.transcript.element(opened);
                self.sends(owner, 8, parties - 1);
                for p in 0..parties {
                    let keyed = Secret(mac_scale(*self.key_for(Some(owner), p), opened));
                    let share = Secret(mac_words(mac_sub(sigma[p], *keyed)));
                    sigmas[p].extend_from_slice(&*share);
                }
            }
        }
        self.commit_then_open(b"input check sigma", &sigmas)?;
        for entry in 0..parties * KEYS {
            let sum = (0..parties).fold([0u64; 2], |sum, p| {
                let share = &sigmas[p][2 * entry..2 * entry + 2];
                mac_words(mac_add(
                    [F::from_u64_reduced(sum[0]), F::from_u64_reduced(sum[1])],
                    [F::from_u64_reduced(share[0]), F::from_u64_reduced(share[1])],
                ))
            });
            if sum != [0; 2] {
                return Err(Check::InputConsistency.into());
            }
        }

        Ok((0..parties)
            .map(|owner| {
                (0..parties)
                    .map(|p| {
                        (0..count)
                            .map(|k| {
                                let mac = macs[owner][p][k];
                                [
                                    if p == owner {
                                        values[owner][k]
                                    } else {
                                        F::ZERO
                                    },
                                    mac[0],
                                    mac[1],
                                ]
                            })
                            .collect()
                    })
                    .collect()
            })
            .collect())
    }

    /// Partially open a value: every party sends its value share; the MAC shares wait in
    /// `queue`.
    fn open(
        &mut self,
        check: Check,
        queue: &mut FieldQueue,
        shares: impl Iterator<Item = Share>,
    ) -> F {
        let mut value = F::ZERO;
        for (party, mut share) in shares.enumerate() {
            (self.fault)(Fault::FieldOpening {
                party,
                check,
                share: &mut share[0],
            });
            self.transcript.element(share[0]);
            self.sends(party, 8, self.parties - 1);
            value += share[0];
            queue.macs[party].push(mac_of(share));
        }
        queue.values.push(value);
        value
    }

    /// Queue a value that must be zero: its MAC shares must sum to zero.
    fn expect_zero(queue: &mut FieldQueue, macs: impl Iterator<Item = Mac>) {
        for (party, mac) in macs.enumerate() {
            queue.macs[party].push(mac);
        }
        queue.values.push(F::ZERO);
    }

    /// Batch MAC check of `queue`: a coin drawn after all queued values are public fixes
    /// `chi` (independently per key); every party commits to and then opens
    /// `sigma_p = sum chi_j (m_j - key_p v_j)`; the sum must be zero.
    ///
    /// A wrong opened value `v + e` (or a nonzero value claimed zero) leaves
    /// `key sum chi_j e_j` in the sum, which the adversary can cancel only if
    /// `sum chi_j e_j = 0` or by predicting the key: at most `2/|F|` per key, `2^-126`.
    fn check_queue(&mut self, queue: FieldQueue, site: Check) -> Result<(), PrepError> {
        if queue.values.is_empty() {
            return Ok(());
        }
        let parties = self.parties;
        let mut challenges = self.coin(b"field mac check")?;
        let mut sigma: SecretVec<Mac> = SecretVec::from(vec![[F::ZERO; 2]; parties]);
        for key in 0..KEYS {
            for (entry, value) in queue.values.iter().enumerate() {
                let chi = challenges.element();
                for p in 0..parties {
                    let keyed = Secret(self.keys[p][key] * *value);
                    let term = queue.macs[p][entry][key] - *keyed;
                    sigma[p][key] += chi * term;
                }
            }
        }
        let payloads: Vec<SecretVec<u64>> = sigma
            .iter()
            .map(|s| mac_words(*s).into_iter().collect())
            .collect();
        self.commit_then_open(b"field sigma", &payloads)?;
        let total = sigma.iter().fold([F::ZERO; 2], |sum, s| mac_add(sum, *s));
        if !mac_is_zero(total) {
            return Err(site.into());
        }
        Ok(())
    }

    // ------------------------------------------------------------------------
    // Triples
    // ------------------------------------------------------------------------

    /// MASCOT Protocol 4, Multiply and Combine, for `count` triples. Returns per party
    /// and triple the values to authenticate: `a, b, c, a^_1, c^_1, a^_2, c^_2`.
    ///
    /// Every party samples `a` in `F^tau` and `b` in `F` per triple. For each ordered
    /// pair the party holding `a` is the OT receiver with the bits of `a` as choice
    /// bits, so its input is the same in every OT by construction; the sender offsets
    /// pad differences by its `b`. A sender that uses another offset in some OT corrupts
    /// the product only if that bit of `a` is 1, which the sacrifice then detects: the
    /// leak about `a` this allows is removed by the combination (module documentation,
    /// [`TAU`]).
    fn multiply(&mut self, count: usize) -> Result<Vec<SecretVec<F>>, PrepError> {
        let parties = self.parties;
        if count == 0 {
            return Ok((0..parties).map(|_| SecretVec::new()).collect());
        }

        let mut a: Vec<SecretVec<F>> = Vec::with_capacity(parties);
        let mut b: Vec<SecretVec<F>> = Vec::with_capacity(parties);
        let mut c: Vec<SecretVec<F>> = Vec::with_capacity(parties);
        for party in 0..parties {
            let a_p: SecretVec<F> = (0..count * TAU).map(|_| self.sample(party)).collect();
            let b_p: SecretVec<F> = (0..count).map(|_| self.sample(party)).collect();
            c.push((0..count * TAU).map(|e| a_p[e] * b_p[e / TAU]).collect());
            a.push(a_p);
            b.push(b_p);
        }
        for receiver in 0..parties {
            let choices: SecretVec<u64> = a[receiver]
                .iter()
                .map(|value| value.to_canonical_u64())
                .collect();
            for sender in (0..parties).filter(|&s| s != receiver) {
                let (send, receive) = self.random_ots(sender, receiver, &choices)?;
                self.sends(sender, 8 * 64 * count * TAU, 1);
                self.transcript.label(b"multiply");
                for e in 0..count * TAU {
                    let (mut sender_sum, mut receiver_sum) = (F::ZERO, F::ZERO);
                    let choice = choices[e];
                    for bit in (0..64).rev() {
                        let index = 64 * e + bit;
                        let (zero, one) = &send[index];
                        let zero = pad_element(zero);
                        let one = pad_element(one);
                        let chosen = pad_element(&receive[index]);
                        let mut correlation = b[sender][e / TAU];
                        (self.fault)(Fault::TripleCorrelation {
                            sender,
                            receiver,
                            triple: e / TAU,
                            slot: e % TAU,
                            bit,
                            correlation: &mut correlation,
                        });
                        // Sender to receiver.
                        let correction = zero - one + correlation;
                        self.transcript.element(correction);
                        let select = 0u64.wrapping_sub((choice >> bit) & 1);
                        let received =
                            chosen + F::from_u64_reduced(correction.to_canonical_u64() & select);
                        sender_sum = sender_sum + sender_sum + zero;
                        receiver_sum = receiver_sum + receiver_sum + received;
                    }
                    // receiver_sum - sender_sum = a_receiver[e] * b_sender.
                    c[receiver][e] += receiver_sum;
                    c[sender][e] -= sender_sum;
                }
            }
        }
        for party in 0..parties {
            (self.fault)(Fault::TripleProduct {
                party,
                products: &mut c[party],
            });
        }

        // Combine with public coefficients drawn after all corrections.
        let mut challenges = self.coin(b"combine")?;
        let combos = 1 + SACRIFICES;
        let mut out: Vec<SecretVec<F>> = (0..parties)
            .map(|_| SecretVec::with_capacity(count * TRIPLE_INPUTS))
            .collect();
        for triple in 0..count {
            let coefficients: Vec<F> = (0..combos * TAU).map(|_| challenges.element()).collect();
            for party in 0..parties {
                let combine = |values: &[F], combo: usize| {
                    (0..TAU).fold(F::ZERO, |sum, slot| {
                        sum + coefficients[combo * TAU + slot] * values[triple * TAU + slot]
                    })
                };
                out[party].push(combine(&a[party], 0));
                out[party].push(b[party][triple]);
                out[party].push(combine(&c[party], 0));
                for combo in 1..combos {
                    out[party].push(combine(&a[party], combo));
                    out[party].push(combine(&c[party], combo));
                }
            }
        }
        Ok(out)
    }

    /// MASCOT Protocol 4, Sacrifice. `joint[p]` holds party `p`'s shares of the
    /// authenticated `a, b, c, a^_1, c^_1, a^_2, c^_2` per triple. For each sacrificial
    /// pair a coin `s` (drawn after authentication), the opening `rho = s a - a^` and
    /// the zero check of `s c - c^ - rho b`.
    ///
    /// If `c = ab + e` and `c^ = a^ b + e^`, the checked value is `s e - e^`, zero with
    /// probability `1/|F|` when `e != 0`; with the independent second pair `2^-128`.
    /// The check consumes the `a^, c^` and reveals `rho`, which the uniform `a^` masks.
    fn sacrifice(
        &mut self,
        joint: &[SecretVec<Share>],
        count: usize,
    ) -> Result<Vec<SecretVec<[Share; 3]>>, PrepError> {
        let parties = self.parties;
        let per = TRIPLE_INPUTS;
        let mut queue = FieldQueue::new(parties);
        if count != 0 {
            let mut challenges = self.coin(b"sacrifice")?;
            self.transcript.label(b"sacrifice");
            for triple in 0..count {
                let at = triple * per;
                for pair in 0..SACRIFICES {
                    let s = challenges.element();
                    let hat = at + 3 + 2 * pair;
                    let rho = self.open(
                        Check::TripleSacrifice,
                        &mut queue,
                        (0..parties)
                            .map(|p| share_sub(share_scale(joint[p][at], s), joint[p][hat])),
                    );
                    Self::expect_zero(
                        &mut queue,
                        (0..parties).map(|p| {
                            let left = mac_sub(
                                mac_scale(mac_of(joint[p][at + 2]), s),
                                mac_of(joint[p][hat + 1]),
                            );
                            mac_sub(left, mac_scale(mac_of(joint[p][at + 1]), rho))
                        }),
                    );
                }
            }
        }
        self.check_queue(queue, Check::TripleSacrifice)?;
        Ok((0..parties)
            .map(|p| {
                (0..count)
                    .map(|t| {
                        [
                            joint[p][t * per],
                            joint[p][t * per + 1],
                            joint[p][t * per + 2],
                        ]
                    })
                    .collect()
            })
            .collect())
    }

    // ------------------------------------------------------------------------
    // One batch
    // ------------------------------------------------------------------------

    /// One batch of `triples` triples and `randoms` uniform values, appended to `stores`.
    fn stage(
        &mut self,
        triples: usize,
        randoms: usize,
        stores: &mut [Preprocessing],
    ) -> Result<(), PrepError> {
        let parties = self.parties;
        if triples + randoms == 0 {
            return Ok(());
        }

        // Batch: triple values, randoms, key-consistency values.
        let random_at = triples * TRIPLE_INPUTS;
        let key_at = random_at + randoms;
        let end = key_at + KEYS;
        let mut inputs = self.multiply(triples)?;
        for owner in 0..parties {
            for _ in random_at..end {
                let value = self.sample(owner);
                inputs[owner].push(value);
            }
        }
        let shares = self.authenticate(&inputs)?;
        let joint: Vec<SecretVec<Share>> = (0..parties)
            .map(|p| {
                (0..end)
                    .map(|k| {
                        (1..parties).fold(shares[0][p][k], |sum, o| share_add(sum, shares[o][p][k]))
                    })
                    .collect()
            })
            .collect();

        // Key consistency. A holder can commit to different keys in its base OTs with
        // different owners; each owner's batch is then valid under a different global
        // key. Every owner contributed two uniformly random items; the sum of each item
        // over the owners is opened and MAC-checked on its own, with no random
        // combination. If the keys towards two honest owners differ by `eps` in some
        // key, the MAC shares of an opened sum are off by `eps` times one honest owner's
        // item, which the sum does not determine: each item passes with probability
        // `1/|F|`. The two items are separate equations, so a difference in a single
        // 64-bit key is also caught except with probability `2^-128`. A failure reveals
        // nothing beyond the sacrificed items.
        //
        // The holder commits to its check share after the value shares are public, and a
        // party's value share of the sum is its own item. Sent as it is, the item of
        // each honest owner would be known in time for the holder to subtract `eps`
        // times it. So every pair adds a common mask from its shared pad stream, one
        // party with each sign: the sum is unchanged, and what two honest owners send
        // determines only the sum of their items.
        let mut blinds: Vec<SecretVec<F>> = (0..parties)
            .map(|_| SecretVec::from(vec![F::ZERO; KEYS]))
            .collect();
        let mut common = SecretVec::from(vec![F::ZERO; KEYS]);
        for low in 0..parties {
            for high in low + 1..parties {
                let pair = self.pairs[low][high].as_mut().unwrap();
                pair.send[SHARED_BASE][0].elements(&mut common);
                for (blind, mask) in blinds[low].iter_mut().zip(common.iter()) {
                    *blind += *mask;
                }
                pair.receive[SHARED_BASE].elements(&mut common);
                for (blind, mask) in blinds[high].iter_mut().zip(common.iter()) {
                    *blind -= *mask;
                }
            }
        }
        let mut sigmas: Vec<SecretVec<u64>> = (0..parties).map(|_| SecretVec::new()).collect();
        self.transcript.label(b"key consistency");
        for k in key_at..end {
            let sent: Vec<F> = (0..parties)
                .map(|p| joint[p][k][0] + blinds[p][k - key_at])
                .collect();
            let mut opened = F::ZERO;
            for share in &sent {
                self.transcript.element(*share);
                opened += *share;
            }
            self.all_send(8);
            for p in 0..parties {
                let keyed = Secret(mac_scale(self.keys[p], opened));
                let mut sigma = Secret(mac_sub(mac_of(joint[p][k]), *keyed));
                (self.fault)(Fault::KeyConsistencySigma {
                    party: p,
                    sent: &sent,
                    sigma: &mut sigma,
                });
                let words = Secret(mac_words(*sigma));
                sigmas[p].extend_from_slice(&*words);
            }
        }
        self.commit_then_open(b"key consistency sigma", &sigmas)?;
        for item in 0..KEYS {
            let sum = (0..parties).fold([F::ZERO; 2], |sum, p| {
                let share = &sigmas[p][2 * item..2 * item + 2];
                mac_add(
                    sum,
                    [F::from_u64_reduced(share[0]), F::from_u64_reduced(share[1])],
                )
            });
            if !mac_is_zero(sum) {
                return Err(Check::KeyConsistency.into());
            }
        }

        let checked = self.sacrifice(&joint, triples)?;
        for p in 0..parties {
            stores[p]
                .triples
                .extend(checked[p].iter().map(|t| t.map(to_engine)));
            stores[p].randoms.extend(
                joint[p][random_at..key_at]
                    .iter()
                    .map(|share| to_engine(*share)),
            );
        }
        Ok(())
    }

    /// The whole demand, in batches of at most `batch` triples (or `7 batch` values).
    /// Returns the stores and the payload bytes each party sent.
    fn run(
        mut self,
        demand: &PrepDemand,
        batch: usize,
    ) -> Result<(Vec<Preprocessing>, Vec<u64>), PrepError> {
        let parties = self.parties;
        self.sample_keys();
        self.establish_pairs()?;
        // The stores never reallocate: a grown `Vec` would leave its old shares behind.
        let mut stores = Vec::with_capacity(parties);
        for p in 0..parties {
            let mut store = Preprocessing {
                key: [F::ZERO; 2],
                triples: Vec::new(),
                randoms: Vec::new(),
            };
            store
                .triples
                .try_reserve_exact(demand.triples)
                .and_then(|()| store.randoms.try_reserve_exact(demand.randoms))
                .map_err(|_| PrepError::InvalidConfiguration)?;
            store.key = self.keys[p];
            stores.push(store);
        }
        let (mut triples, mut randoms) = (demand.triples, demand.randoms);
        while triples != 0 || randoms != 0 {
            let t = triples.min(batch);
            let r = randoms.min((batch - t) * TRIPLE_INPUTS);
            self.stage(t, r, &mut stores)?;
            triples -= t;
            randoms -= r;
        }
        Ok((stores, core::mem::take(&mut self.sent)))
    }
}

fn ceremony(
    session: [u8; 32],
    parties: usize,
    demand: &PrepDemand,
    mesh: &mut OtMesh,
    rngs: &mut [PartyPrivateRng],
    fault: &mut dyn FnMut(Fault<'_>),
    batch: usize,
) -> Result<(Vec<Preprocessing>, Vec<u64>), PrepError> {
    if rngs.len() != parties || batch == 0 {
        return Err(PrepError::InvalidConfiguration);
    }
    let mut encoded = [0u8; 24];
    for (slot, count) in encoded
        .chunks_exact_mut(8)
        .zip([parties, demand.triples, demand.randoms])
    {
        slot.copy_from_slice(&(count as u64).to_le_bytes());
    }
    let session = cshake256_framed_32(b"QSAG.COLLAB.PREP.DEALERLESS/v1", &[&session, &encoded]);
    Ceremony::new(session, mesh, rngs, fault)?.run(demand, batch)
}

/// Run the preprocessing ceremony of one quorum in this process and return every
/// member's store, in quorum order.
///
/// `mesh` is the OT mesh over the `parties` quorum members and `rngs` their private
/// generators, both indexed by quorum position. `session` must not repeat on one mesh.
/// All steps of all members run here on separated per-party state. On any failed check
/// the result is [`PrepError::Check`], nothing is returned, and all key shares and
/// material are erased as their owners go out of scope.
pub fn run_preprocessing(
    session: [u8; 32],
    parties: usize,
    demand: &PrepDemand,
    mesh: &mut OtMesh,
    rngs: &mut [PartyPrivateRng],
) -> Result<Vec<Preprocessing>, PrepError> {
    run_preprocessing_with_fault(session, parties, demand, mesh, rngs, &mut |_| {})
}

/// [`run_preprocessing`] with a hook that may alter what a party uses or sends at each
/// [`Fault`] point, for adversarial tests.
pub fn run_preprocessing_with_fault(
    session: [u8; 32],
    parties: usize,
    demand: &PrepDemand,
    mesh: &mut OtMesh,
    rngs: &mut [PartyPrivateRng],
    fault: &mut dyn FnMut(Fault<'_>),
) -> Result<Vec<Preprocessing>, PrepError> {
    ceremony(session, parties, demand, mesh, rngs, fault, BATCH_TRIPLES).map(|(stores, _)| stores)
}

#[cfg(test)]
mod tests {
    use super::super::engine::tests::run_parties;
    use super::super::prover::{self, tests::small_relation};
    use super::*;
    use qsag_agg::zk_hem::v2::params::Profile;
    use qsag_agg::zk_hem::v2::protocol::verify_split;
    use std::{println, time::Instant};

    /// Real OT mesh over `parties` quorum members and their private generators.
    fn setup(seed: u8, parties: usize) -> (OtMesh, Vec<PartyPrivateRng>) {
        let mut rngs: Vec<_> = (0..parties as u8)
            .map(|p| {
                PartyPrivateRng::from_seed(
                    [seed, p, 7, 1].repeat(8).try_into().unwrap(),
                    b"TEST.COLLAB.PREP",
                )
            })
            .collect();
        let mesh = OtMesh::establish([seed; 32], &mut rngs).unwrap();
        (mesh, rngs)
    }

    fn honest(_: Fault<'_>) {}

    /// Reconstructs everything from all parties' stores and asserts every relation the
    /// engine relies on. Returns the keys and the reconstructed `a`, `b` and randoms.
    fn verify_material(demand: &PrepDemand, stores: &[Preprocessing]) -> ([F; 2], Vec<F>) {
        let key = stores.iter().fold([F::ZERO; 2], |k, s| mac_add(k, s.key));
        assert_ne!(key[0], F::ZERO);
        assert_ne!(key[1], F::ZERO);
        assert_ne!(key[0], key[1], "the two keys are independent");
        let element = |shares: Vec<Sb>| {
            let total = shares.iter().fold(Sb::ZERO, |sum, s| sum + *s);
            assert_eq!(total.m, mac_scale(key, total.v), "MAC");
            total.v
        };
        let mut seen = Vec::new();
        for store in stores {
            assert_eq!(store.triples.len(), demand.triples);
            assert_eq!(store.randoms.len(), demand.randoms);
        }
        for item in 0..demand.triples {
            let [a, b, c] = [0, 1, 2]
                .map(|part| element(stores.iter().map(|s| s.triples[item][part]).collect()));
            assert_eq!(c, a * b, "triple {item}");
            seen.extend([a, b]);
        }
        for item in 0..demand.randoms {
            seen.push(element(stores.iter().map(|s| s.randoms[item]).collect()));
        }
        // Uniform values: not zero and not repeated.
        for (i, value) in seen.iter().enumerate() {
            assert_ne!(*value, F::ZERO);
            assert!(!seen[..i].contains(value));
        }
        (key, seen)
    }

    /// Runs the ceremony honestly (must succeed and satisfy the oracle), then with
    /// `fault`, and returns the deviating outcome after checking that a successful
    /// deviating run still satisfies the oracle.
    fn deviate(
        seed: u8,
        demand: &PrepDemand,
        mesh: &mut OtMesh,
        rngs: &mut [PartyPrivateRng],
        mut fault: impl FnMut(Fault<'_>) -> bool,
    ) -> Result<(), PrepError> {
        let (out, _) = ceremony(
            [seed; 32],
            3,
            demand,
            mesh,
            rngs,
            &mut honest,
            BATCH_TRIPLES,
        )
        .unwrap();
        verify_material(demand, &out);
        let mut fired = false;
        let outcome = ceremony(
            [seed ^ 0x80; 32],
            3,
            demand,
            mesh,
            rngs,
            &mut |point| fired |= fault(point),
            BATCH_TRIPLES,
        );
        assert!(fired, "the deviation was never injected");
        outcome.map(|(out, _)| {
            verify_material(demand, &out);
        })
    }

    #[test]
    fn stores_satisfy_the_share_algebra_for_two_and_three_members() {
        for parties in [2usize, 3] {
            let (mut mesh, mut rngs) = setup(30 + parties as u8, parties);
            let demand = PrepDemand {
                triples: 5,
                randoms: 4,
            };
            let first = run_preprocessing([1; 32], parties, &demand, &mut mesh, &mut rngs).unwrap();
            let (key, seen) = verify_material(&demand, &first);
            for p in 0..parties {
                for q in p + 1..parties {
                    assert_ne!(first[p].key, first[q].key);
                    assert_ne!(first[p].triples, first[q].triples);
                    assert_ne!(first[p].randoms, first[q].randoms);
                }
                // No member holds a value or a key alone.
                assert_ne!(first[p].key, key);
                assert_ne!(first[p].triples[0][0].v, seen[0]);
            }
            let second =
                run_preprocessing([2; 32], parties, &demand, &mut mesh, &mut rngs).unwrap();
            let (other_key, other) = verify_material(&demand, &second);
            assert_ne!(other_key, key);
            assert!(other.iter().all(|value| !seen.contains(value)));
            for p in 0..parties {
                assert_ne!(second[p].triples, first[p].triples);
                assert_ne!(second[p].randoms, first[p].randoms);
            }
        }
    }

    /// A demand that spans several batches, including one of randoms only, under one
    /// pair of keys.
    #[test]
    fn a_demand_larger_than_one_batch_is_consistent() {
        let (mut mesh, mut rngs) = setup(33, 3);
        let demand = PrepDemand {
            triples: 5,
            randoms: 40,
        };
        let mut stages = 0;
        let (out, sent) = ceremony(
            [3; 32],
            3,
            &demand,
            &mut mesh,
            &mut rngs,
            // One commit-then-open of this label per batch.
            &mut |point| {
                if let Fault::KeyConsistencySigma { party: 0, .. } = point {
                    stages += 1;
                }
            },
            2,
        )
        .unwrap();
        // Batches: (2, 0), (2, 0), (1, 7), (0, 14), (0, 14), (0, 5); two items each.
        assert_eq!(stages, 6 * KEYS);
        verify_material(&demand, &out);
        // Every member plays every role towards every other member equally often.
        assert_ne!(sent[0], 0);
        assert_eq!(sent, [sent[0]; 3]);
    }

    #[test]
    fn pad_elements_are_canonical() {
        let top = qsag_core::field::goldilocks::GOLDILOCKS_PRIME;
        assert_eq!(pad_element(&[0; 48]), F::ZERO);
        // Six non-canonical candidates: the last is reduced.
        assert_eq!(
            pad_element(&[0xff; 48]),
            F::from_u64_reduced(u64::MAX - top)
        );
        assert!(pad_element(&[0xff; 48]).to_canonical_u64() < top);
        let mut pad = [0xff; 48];
        pad[40..].copy_from_slice(&5u64.to_le_bytes());
        assert_eq!(pad_element(&pad), F::from_u64_reduced(5));
        pad[8..16].copy_from_slice(&(top - 1).to_le_bytes());
        assert_eq!(pad_element(&pad), F::from_u64_reduced(top - 1));
    }

    /// The pad stream yields the canonical words of its sponge in order, whatever the
    /// length of the request.
    #[test]
    fn pad_streams_do_not_depend_on_how_they_are_read() {
        let prg = || Prg::new(&[4; 32], 0, 1, 7, &[9; 48]);
        let mut whole = vec![F::ZERO; 300];
        prg().elements(&mut whole);
        let mut stream = prg();
        let mut parts = vec![F::ZERO; 300];
        let (head, tail) = parts.split_at_mut(136);
        stream.elements(head);
        stream.elements(tail);
        assert_eq!(parts, whole);
        assert!(whole.iter().any(|v| *v != whole[0]));
        let mut other = vec![F::ZERO; 300];
        Prg::new(&[4; 32], 0, 1, 8, &[9; 48]).elements(&mut other);
        assert_ne!(other, whole);
    }

    /// Authentication on its own: authenticated values reconstruct with valid MACs and
    /// only the owner holds a value share.
    #[test]
    fn owners_authenticate_their_values() {
        let (mut mesh, mut rngs) = setup(1, 3);
        let hook: &mut dyn FnMut(Fault<'_>) = &mut honest;
        let mut ceremony = Ceremony::new([1; 32], &mut mesh, &mut rngs, hook).unwrap();
        ceremony.sample_keys();
        ceremony.establish_pairs().unwrap();
        let key = (0..3).fold([F::ZERO; 2], |key, p| mac_add(key, ceremony.keys[p]));
        let inputs: Vec<SecretVec<F>> = (0..3)
            .map(|owner| {
                let mut values: SecretVec<F> = [
                    F::ZERO,
                    F::ONE,
                    F::NEG_ONE,
                    F::from_u64_reduced(owner as u64 + 2),
                ]
                .into_iter()
                .collect();
                values.push(ceremony.sample(owner));
                values
            })
            .collect();
        for _ in 0..2 {
            let shares = ceremony.authenticate(&inputs).unwrap();
            for owner in 0..3 {
                for k in 0..inputs[owner].len() {
                    let mut total = [F::ZERO; 3];
                    for p in 0..3 {
                        let share = shares[owner][p][k];
                        assert_eq!(
                            share[0] != F::ZERO,
                            p == owner && inputs[owner][k] != F::ZERO
                        );
                        total = share_add(total, share);
                    }
                    assert_eq!(total[0], inputs[owner][k]);
                    assert_eq!(mac_of(total), mac_scale(key, total[0]));
                }
            }
        }
    }

    #[test]
    fn inconsistent_owner_and_wrong_holder_share_are_caught() {
        let (mut mesh, mut rngs) = setup(2, 3);
        let demand = PrepDemand {
            triples: 0,
            randoms: 2,
        };
        // Owner 1 encodes another value under the low 16 bits of holder 2's key.
        for target in 0..KEYS {
            let outcome = deviate(20, &demand, &mut mesh, &mut rngs, |point| match point {
                Fault::CopeInput {
                    owner: 1,
                    holder: 2,
                    key,
                    bit,
                    values,
                } if key == target && bit < 16 => {
                    values[0] += F::ONE;
                    true
                }
                _ => false,
            });
            assert_eq!(
                outcome,
                Err(PrepError::Check(Check::InputConsistency)),
                "key {target}"
            );
        }
        // Holder 0 holds a MAC share of one of owner 2's values that its key does not give.
        for target in 0..KEYS {
            let outcome = deviate(21, &demand, &mut mesh, &mut rngs, |point| match point {
                Fault::CopeHolderShare {
                    owner: 2,
                    holder: 0,
                    macs,
                } => {
                    macs[0][target] += F::ONE;
                    true
                }
                _ => false,
            });
            assert_eq!(
                outcome,
                Err(PrepError::Check(Check::InputConsistency)),
                "key {target}"
            );
        }
        // Holder 2 commits to another key towards owner 0 than towards owner 1, in one
        // key or in both.
        for bump in [[1u64, 0], [0, 1], [1, 1]] {
            let outcome = deviate(22, &demand, &mut mesh, &mut rngs, |point| match point {
                Fault::FieldKey {
                    owner: 0,
                    holder: 2,
                    key,
                } => {
                    key[0] += F::from_u64_reduced(bump[0]);
                    key[1] += F::from_u64_reduced(bump[1]);
                    true
                }
                _ => false,
            });
            assert_eq!(
                outcome,
                Err(PrepError::Check(Check::KeyConsistency)),
                "{bump:?}"
            );
        }
    }

    /// The selective failure of the input check, in a later batch than the first: an
    /// owner that encodes another value under one bit of one key share of an honest
    /// holder, and does nothing else, passes exactly when that bit is zero, and then the
    /// material is intact. So a pass tells the owner one predicate of the key and a
    /// failure discards the key (module documentation, selective failure, item 1).
    #[test]
    fn a_wrong_encoding_under_one_key_bit_passes_exactly_when_the_bit_is_zero() {
        let (mut mesh, mut rngs) = setup(16, 3);
        // Batches of two triples' worth of values: (0, 14), (0, 14), (0, 2).
        let demand = PrepDemand {
            triples: 0,
            randoms: 30,
        };
        let (mut passed, mut failed) = (0, 0);
        for target in 0..KEYS {
            for bit_at in [0usize, 1, 2, 3, 31, 32, 62, 63] {
                let (mut share, mut calls) = (0u64, 0);
                let outcome = ceremony(
                    [(8 * target + bit_at) as u8; 32],
                    3,
                    &demand,
                    &mut mesh,
                    &mut rngs,
                    &mut |point| match point {
                        Fault::FieldKey {
                            owner: 1,
                            holder: 2,
                            key,
                        } => share = key[target].to_canonical_u64(),
                        Fault::CopeInput {
                            owner: 1,
                            holder: 2,
                            key,
                            bit,
                            values,
                        } if key == target && bit == bit_at => {
                            calls += 1;
                            // The second batch only.
                            if calls == 2 {
                                values[3] += F::ONE;
                            }
                        }
                        _ => {}
                    },
                    2,
                );
                if (share >> bit_at) & 1 == 0 {
                    assert_eq!(calls, 3, "one authentication per batch");
                    verify_material(&demand, &outcome.unwrap().0);
                    passed += 1;
                } else {
                    assert_eq!(calls, 2, "the second batch aborts");
                    assert_eq!(
                        outcome.err(),
                        Some(PrepError::Check(Check::InputConsistency)),
                        "key {target} bit {bit_at}"
                    );
                    failed += 1;
                }
            }
        }
        println!("wrong encodings under one key bit: {passed} passed, {failed} caught");
        assert!(passed != 0 && failed != 0);
    }

    /// A holder that used another key towards one owner knows the difference `eps`, and
    /// it commits to its check share only after the value shares are public. If an
    /// owner's share were its item, the holder could subtract `eps` times it and pass.
    /// No triple is demanded here, so no later check of the ceremony would see the
    /// inconsistency either.
    #[test]
    fn a_holder_cannot_cancel_its_key_inconsistency_from_what_the_owner_sent() {
        let (mut mesh, mut rngs) = setup(12, 3);
        let demand = PrepDemand {
            triples: 0,
            randoms: 2,
        };
        let epsilon = [F::ONE; 2];
        let mut corrected = 0;
        let outcome = deviate(60, &demand, &mut mesh, &mut rngs, |point| match point {
            Fault::FieldKey {
                owner: 0,
                holder: 2,
                key,
            } => {
                *key = mac_add(*key, epsilon);
                true
            }
            Fault::KeyConsistencySigma {
                party: 2,
                sent,
                sigma,
            } => {
                *sigma = mac_sub(*sigma, mac_scale(epsilon, sent[0]));
                corrected += 1;
                true
            }
            _ => false,
        });
        assert_eq!(corrected, KEYS);
        assert_eq!(outcome, Err(PrepError::Check(Check::KeyConsistency)));
    }

    fn commit_payloads() -> Vec<SecretVec<u64>> {
        (0..3).map(|p| [p, 7, 9].into_iter().collect()).collect()
    }

    /// One commit-then-open of a fixed label and payload by a fresh ceremony whose
    /// counter stands at `start`: party 1's commitment, its nonce, and the transcript
    /// digest. The generators are in the same state every time.
    fn commit_once(start: u64) -> ([u8; 32], [u8; 32], [u8; 32]) {
        let (mut mesh, mut rngs) = setup(13, 3);
        let (mut sent, mut opened) = ([0; 32], [0; 32]);
        let mut hook = |point: Fault<'_>| match point {
            Fault::Commitment {
                invocation,
                party: 1,
                commitment: c,
            } => {
                assert_eq!(invocation, start);
                sent = *c;
            }
            Fault::CommitmentNonce {
                party: 1, nonce, ..
            } => opened = *nonce,
            _ => {}
        };
        let mut ceremony = Ceremony::new([13; 32], &mut mesh, &mut rngs, &mut hook).unwrap();
        ceremony.commits = start;
        ceremony
            .commit_then_open(b"replay", &commit_payloads())
            .unwrap();
        assert_eq!(ceremony.commits, start + 1);
        let digest = ceremony.transcript.digest();
        drop(ceremony);
        (sent, opened, digest)
    }

    #[test]
    fn commit_then_open_binds_its_invocation_counter() {
        let (first, first_nonce, first_digest) = commit_once(0);
        assert_eq!(commit_once(0), (first, first_nonce, first_digest));
        let (later, later_nonce, later_digest) = commit_once(1);
        // Same session, label, party, payload and nonce: only the counter differs.
        assert_eq!(later_nonce, first_nonce);
        assert_ne!(later, first);
        assert_ne!(later_digest, first_digest);
        let payload = &commit_payloads()[1];
        for (invocation, sent) in [(0, first), (1, later)] {
            assert_eq!(
                sent,
                commitment(&[13; 32], b"replay", invocation, 1, payload, &first_nonce)
            );
        }
    }

    /// Two invocations with the same label and payloads. In the second, party 1 opens
    /// with its nonce of the first and sends either its commitment of the first
    /// (`stale`) or a commitment to the same payload and nonce under the second
    /// invocation.
    fn reuse_in_second_invocation(stale: bool) -> Result<(), PrepError> {
        let (mut mesh, mut rngs) = setup(14, 3);
        let session = [14; 32];
        let payloads = commit_payloads();
        let (mut sent, mut opened) = ([0; 32], [0; 32]);
        let mut hook = |point: Fault<'_>| match point {
            Fault::Commitment {
                invocation: 0,
                party: 1,
                commitment: c,
            } => sent = *c,
            Fault::CommitmentNonce {
                invocation: 0,
                party: 1,
                nonce,
            } => opened = *nonce,
            Fault::Commitment {
                invocation: 1,
                party: 1,
                commitment: c,
            } => {
                *c = if stale {
                    sent
                } else {
                    commitment(&session, b"replay", 1, 1, &payloads[1], &opened)
                };
            }
            Fault::CommitmentNonce {
                invocation: 1,
                party: 1,
                nonce,
            } => *nonce = opened,
            _ => {}
        };
        let mut ceremony = Ceremony::new(session, &mut mesh, &mut rngs, &mut hook).unwrap();
        ceremony.commit_then_open(b"replay", &payloads).unwrap();
        let outcome = ceremony.commit_then_open(b"replay", &payloads);
        assert_eq!(ceremony.commits, 2);
        outcome
    }

    #[test]
    fn a_commitment_replayed_from_an_earlier_invocation_is_rejected() {
        assert_eq!(reuse_in_second_invocation(false), Ok(()));
        assert_eq!(
            reuse_in_second_invocation(true),
            Err(PrepError::Check(Check::Commitment))
        );
    }

    #[test]
    fn the_invocation_counter_does_not_wrap() {
        let (mut mesh, mut rngs) = setup(15, 3);
        let hook: &mut dyn FnMut(Fault<'_>) = &mut honest;
        let mut ceremony = Ceremony::new([15; 32], &mut mesh, &mut rngs, hook).unwrap();
        ceremony.commits = u64::MAX - 1;
        assert_eq!(
            ceremony.commit_then_open(b"replay", &commit_payloads()),
            Ok(())
        );
        assert_eq!(
            ceremony.commit_then_open(b"replay", &commit_payloads()),
            Err(PrepError::Check(Check::Commitment))
        );
        assert_eq!(ceremony.commits, u64::MAX);
    }

    /// A coin drawn by generators in a fixed state, on the mesh of `setup(18)` as
    /// established or after one further OT batch; with the coin, the mesh's chain.
    fn coin_on_mesh(extra_batch: bool) -> (F, [u8; 32]) {
        let (mut mesh, mut rngs) = setup(18, 3);
        if extra_batch {
            mesh.run_correlated_ot_words(0, 1, &[5], &mut rngs).unwrap();
        }
        let chain = mesh.transcript_digest();
        let mut rngs: Vec<_> = (0..3u8)
            .map(|p| PartyPrivateRng::from_seed([p; 32], b"TEST.COLLAB.PREP.COIN"))
            .collect();
        let hook: &mut dyn FnMut(Fault<'_>) = &mut honest;
        let mut ceremony = Ceremony::new([18; 32], &mut mesh, &mut rngs, hook).unwrap();
        (ceremony.coin(b"test").unwrap().element(), chain)
    }

    #[test]
    fn coins_depend_on_all_ot_traffic() {
        let (coin, chain) = coin_on_mesh(false);
        assert_eq!(coin_on_mesh(false), (coin, chain));
        let (later_coin, later_chain) = coin_on_mesh(true);
        assert_ne!(later_chain, chain);
        assert_ne!(later_coin, coin);
    }

    #[test]
    fn wrong_triple_correlation_product_and_opening_are_caught() {
        let (mut mesh, mut rngs) = setup(4, 3);
        let demand = PrepDemand {
            triples: 1,
            randoms: 0,
        };
        // One wrong correlation in one OT changes the product only if the receiver's
        // choice bit is 1: each run is either caught or harmless.
        let mut caught = 0;
        for target in 0..8 {
            let outcome =
                deviate(
                    40 + target as u8,
                    &demand,
                    &mut mesh,
                    &mut rngs,
                    |point| match point {
                        Fault::TripleCorrelation {
                            sender: 1,
                            receiver: 0,
                            triple: 0,
                            slot: 0,
                            bit,
                            correlation,
                        } if bit == target => {
                            *correlation += F::ONE;
                            true
                        }
                        _ => false,
                    },
                );
            match outcome {
                Ok(()) => {}
                Err(abort) => {
                    assert_eq!(abort, PrepError::Check(Check::TripleSacrifice));
                    caught += 1;
                }
            }
        }
        println!("single wrong correlations caught: {caught} of 8");
        assert!((1..8).contains(&caught));

        let demand = PrepDemand {
            triples: 2,
            randoms: 1,
        };
        let outcome = deviate(50, &demand, &mut mesh, &mut rngs, |point| match point {
            Fault::TripleProduct { party: 2, products } => {
                products[1] += F::ONE;
                true
            }
            _ => false,
        });
        assert_eq!(outcome, Err(PrepError::Check(Check::TripleSacrifice)));

        // A wrong value share in an opening of the sacrifice.
        let mut openings = 0;
        let outcome = deviate(51, &demand, &mut mesh, &mut rngs, |point| match point {
            Fault::FieldOpening {
                party: 1,
                check: Check::TripleSacrifice,
                share,
            } => {
                openings += 1;
                if openings == 3 {
                    *share += F::ONE;
                }
                true
            }
            _ => false,
        });
        assert_eq!(openings, 2 * SACRIFICES);
        assert_eq!(outcome, Err(PrepError::Check(Check::TripleSacrifice)));
    }

    #[test]
    fn invalid_configurations_are_rejected() {
        let (mut mesh, mut rngs) = setup(9, 2);
        let demand = PrepDemand {
            triples: 1,
            randoms: 1,
        };
        // Three members claimed on a two-party mesh, and one generator too few.
        for parties in [3, 1] {
            assert_eq!(
                run_preprocessing([9; 32], parties, &demand, &mut mesh, &mut rngs).err(),
                Some(PrepError::InvalidConfiguration)
            );
        }
        let (mut wide, mut wide_rngs) = setup(10, 3);
        assert_eq!(
            run_preprocessing([9; 32], 2, &demand, &mut wide, &mut rngs).err(),
            Some(PrepError::InvalidConfiguration)
        );
        assert_eq!(
            run_preprocessing([9; 32], 2, &demand, &mut mesh, &mut wide_rngs[..1]).err(),
            Some(PrepError::InvalidConfiguration)
        );
        assert_eq!(
            run_preprocessing(
                [9; 32],
                2,
                &PrepDemand {
                    triples: usize::MAX,
                    randoms: 0
                },
                &mut mesh,
                &mut rngs
            )
            .err(),
            Some(PrepError::InvalidConfiguration)
        );
        // An empty demand still yields key shares.
        let empty = PrepDemand::default();
        let out = run_preprocessing([9; 32], 2, &empty, &mut mesh, &mut rngs).unwrap();
        verify_material(&empty, &out);
        let out = run_preprocessing([8; 32], 2, &demand, &mut mesh, &mut rngs).unwrap();
        verify_material(&demand, &out);
    }

    /// The ceremony's output drives the engine and the threshold prover: party 0 inputs
    /// a clear assignment, the quorum proves, the split verifier accepts.
    fn prove_on_ceremony_output(parties: usize) {
        let regime = Profile::default();
        let (shape, assignment) = small_relation(5);
        let publics = assignment[1..=shape.num_public].to_vec();
        let (triples, randoms) = prover::prover_demand(&shape, regime).unwrap();
        let demand = PrepDemand {
            triples,
            randoms: randoms + assignment.len() + qsag_agg::zk_hem::v2::params::LIMBS,
        };
        let started = Instant::now();
        let (mut mesh, mut rngs) = setup(60 + parties as u8, parties);
        let mesh_s = started.elapsed().as_secs_f64();
        let started = Instant::now();
        let preps = run_preprocessing([6; 32], parties, &demand, &mut mesh, &mut rngs).unwrap();
        let ceremony_s = started.elapsed().as_secs_f64();
        verify_material(&demand, &preps);

        let started = Instant::now();
        let out = run_parties(preps, |mut e| {
            let mine = (e.me() == 0).then_some(&assignment[..]);
            let z = e.input(0, mine, assignment.len()).unwrap();
            let proof = prover::prove_party(&mut e, &shape, &publics, b"stmt", regime, z);
            (proof, e.remaining(), e.has_pending(), e.stats)
        });
        let prove_s = started.elapsed().as_secs_f64();
        let proof = out[0].0.clone().unwrap();
        for (result, remaining, pending, stats) in &out {
            assert_eq!(result.as_ref(), Ok(&proof));
            assert_eq!(*remaining, (0, 0), "the demand is exact");
            assert!(!pending);
            assert_eq!(stats.triples_used as usize, demand.triples);
            assert_eq!(stats.randoms_used as usize, demand.randoms);
        }
        assert_eq!(proof.roots.len(), parties);
        assert!(proof.profile == regime && verify_split(&shape, &publics, b"stmt", regime, &proof));
        assert!(!verify_split(&shape, &publics, b"other", regime, &proof));
        println!(
            "N={parties}: {} triples, {} randoms per member; mesh {mesh_s:.2} s, ceremony \
             {ceremony_s:.2} s, input+proof {prove_s:.2} s",
            demand.triples, demand.randoms
        );
    }

    #[test]
    fn ceremony_output_drives_the_threshold_prover() {
        prove_on_ceremony_output(3);
    }

    #[test]
    fn ceremony_output_drives_the_threshold_prover_for_two_members() {
        prove_on_ceremony_output(2);
    }

    /// A store whose MAC key share is not the ceremony's makes the engine's MAC check
    /// fail: the proof above depends on the keys the ceremony returned.
    #[test]
    fn a_store_with_a_foreign_key_share_fails_the_engine_check() {
        let (mut mesh, mut rngs) = setup(70, 2);
        let demand = PrepDemand {
            triples: 1,
            randoms: 2,
        };
        let honest_run = |mesh: &mut OtMesh, rngs: &mut [PartyPrivateRng], session: u8| {
            run_preprocessing([session; 32], 2, &demand, mesh, rngs).unwrap()
        };
        let open_product = |preps: Vec<Preprocessing>| {
            run_parties(preps, |mut e| {
                let x = e.random().unwrap();
                let y = e.random().unwrap();
                let product = e.mul(&[x], &[y]).unwrap();
                let opened = e.open(&[product[0], x, y]).unwrap();
                (opened, e.check())
            })
        };
        for (opened, verdict) in open_product(honest_run(&mut mesh, &mut rngs, 1)) {
            assert_eq!(verdict, Ok(()));
            assert_eq!(opened[0], opened[1] * opened[2]);
        }
        // Member 1 keeps its material of one ceremony and takes the key of another.
        let mut mixed = honest_run(&mut mesh, &mut rngs, 2);
        let other = honest_run(&mut mesh, &mut rngs, 3);
        mixed[1].key = other[1].key;
        for (_, verdict) in open_product(mixed) {
            assert_eq!(verdict, Err(super::super::engine::MpcError::MacCheck));
        }
    }

    /// Reconstructs every triple and uniform value of `stores` and checks its MACs under
    /// the reconstructed keys and, for triples, the product. Linear in the demand.
    fn check_all_material(demand: &PrepDemand, stores: &[Preprocessing]) {
        let key = stores.iter().fold([F::ZERO; 2], |k, s| mac_add(k, s.key));
        assert_ne!(key[0], F::ZERO);
        assert_ne!(key[1], F::ZERO);
        let element = |part: &dyn Fn(&Preprocessing) -> Sb| {
            let total = stores.iter().fold(Sb::ZERO, |sum, s| sum + part(s));
            assert_eq!(total.m, mac_scale(key, total.v), "MAC");
            total.v
        };
        let mut zeros = 0;
        for store in stores {
            assert_eq!(store.triples.len(), demand.triples);
            assert_eq!(store.randoms.len(), demand.randoms);
        }
        for item in 0..demand.triples {
            let [a, b, c] = [0, 1, 2].map(|part| element(&|s| s.triples[item][part]));
            assert_eq!(c, a * b, "triple {item}");
            zeros += usize::from(a == F::ZERO) + usize::from(b == F::ZERO);
        }
        for item in 0..demand.randoms {
            zeros += usize::from(element(&|s| s.randoms[item]) == F::ZERO);
        }
        assert_eq!(zeros, 0, "uniform 64-bit values are not zero");
    }

    /// A field of `/proc/self/status` in kB (Linux; `None` elsewhere).
    fn status_kb(field: &str) -> Option<u64> {
        let status = std::fs::read_to_string("/proc/self/status").ok()?;
        let line = status.lines().find(|line| line.starts_with(field))?;
        line.split_whitespace().nth(1)?.parse().ok()
    }

    /// User plus system CPU seconds of this process, all threads (Linux, 100 ticks per
    /// second; `None` elsewhere).
    fn cpu_seconds() -> Option<f64> {
        let stat = std::fs::read_to_string("/proc/self/stat").ok()?;
        let mut fields = stat.rsplit_once(')')?.1.split_whitespace();
        let user: u64 = fields.nth(11)?.parse().ok()?;
        let system: u64 = fields.next()?.parse().ok()?;
        Some((user + system) as f64 / 100.0)
    }

    /// The real ceremony for one demand on the real mesh, with the cost figures:
    /// `cargo test --release -p qsag-migrate --features std --lib --
    /// hem::collab::prep::tests::measure_ceremony --ignored --nocapture`.
    ///
    /// `COLLAB_PREP_TRIPLES`, `COLLAB_PREP_RANDOMS` and `COLLAB_PREP_PARTIES` set the
    /// demand per member and the quorum size (default 4096, 16384, 3); one custodian's
    /// proof of the Bitcoin HASH160 ownership statement consumes 2228208 triples and
    /// 9156 uniform values. A progress line is printed every `COLLAB_PREP_PROGRESS`
    /// batches (default 64). All of the output is reconstructed and checked.
    ///
    /// The ceremony's own steps run on one thread; with `--features std` the mesh
    /// expands each OT batch on up to 16 worker threads.
    #[test]
    #[ignore = "measurement"]
    fn measure_ceremony() {
        let count = |name: &str, default: usize| {
            std::env::var(name)
                .ok()
                .and_then(|v| v.parse().ok())
                .unwrap_or(default)
        };
        let demand = PrepDemand {
            triples: count("COLLAB_PREP_TRIPLES", 4096),
            randoms: count("COLLAB_PREP_RANDOMS", 16384),
        };
        let parties = count("COLLAB_PREP_PARTIES", 3);
        let every = count("COLLAB_PREP_PROGRESS", 64).max(1);
        // The batches `Ceremony::run` forms, as (triples, randoms).
        let mut batches = Vec::new();
        let (mut triples, mut randoms) = (demand.triples, demand.randoms);
        while triples != 0 || randoms != 0 {
            let t = triples.min(BATCH_TRIPLES);
            let r = randoms.min((BATCH_TRIPLES - t) * TRIPLE_INPUTS);
            batches.push((t, r));
            triples -= t;
            randoms -= r;
        }
        println!(
            "demand per member: {} triples, {} randoms; {parties} members; {} batches of at \
             most {BATCH_TRIPLES} triples; available parallelism {}",
            demand.triples,
            demand.randoms,
            batches.len(),
            std::thread::available_parallelism().map_or(1, usize::from)
        );

        let started = Instant::now();
        let (mut mesh, mut rngs) = setup(9, parties);
        let mesh_s = started.elapsed().as_secs_f64();
        println!("OT mesh: {mesh_s:.2} s");

        // The key-consistency check runs once per batch, after the batch's
        // multiplication and authentication and before its sacrifice.
        let started = Instant::now();
        let cpu_before = cpu_seconds();
        let (mut calls, mut marks) = (0, Vec::with_capacity(batches.len()));
        let (stores, sent) = ceremony(
            [1; 32],
            parties,
            &demand,
            &mut mesh,
            &mut rngs,
            &mut |point| {
                if let Fault::KeyConsistencySigma { party: 0, .. } = point {
                    calls += 1;
                    if calls % KEYS != 0 {
                        return;
                    }
                    let elapsed = started.elapsed().as_secs_f64();
                    marks.push(elapsed);
                    let done = marks.len();
                    if done % every == 0 || done == batches.len() {
                        let triples: usize = batches[..done].iter().map(|b| b.0).sum();
                        println!(
                            "batch {done}/{}: {elapsed:.1} s, {triples} triples, RSS {} MB",
                            batches.len(),
                            status_kb("VmRSS:").map_or(0, |kb| kb / 1024)
                        );
                    }
                }
            },
            BATCH_TRIPLES,
        )
        .unwrap();
        let wall = started.elapsed().as_secs_f64();
        let cpu = cpu_seconds()
            .zip(cpu_before)
            .map(|(after, before)| after - before);
        assert_eq!(marks.len(), batches.len());

        let started = Instant::now();
        check_all_material(&demand, &stores);
        println!(
            "checked: all {} triples (product and both MACs) and {} randoms (both MACs), \
             reconstructed over {parties} members, {:.2} s",
            demand.triples,
            demand.randoms,
            started.elapsed().as_secs_f64()
        );

        println!("ceremony wall-clock: {wall:.1} s = {:.3} h", wall / 3600.0);
        match cpu {
            Some(cpu) => println!("ceremony CPU time (user + system, all threads): {cpu:.1} s"),
            None => println!("ceremony CPU time: not available on this system"),
        }
        match status_kb("VmHWM:") {
            Some(kb) => println!("peak RSS (VmHWM): {} MB", kb / 1024),
            None => println!("peak RSS: not available on this system"),
        }
        for (party, bytes) in sent.iter().enumerate() {
            println!(
                "member {party} sent {bytes} bytes = {:.3} GiB",
                *bytes as f64 / (1u64 << 30) as f64
            );
        }
        // Rates from the batches of one kind: a batch's span is from the previous
        // batch's key-consistency check to its own, so the span of the batch after a
        // triple batch holds that batch's sacrifice and is left out of the random rate.
        let span = |i: usize| marks[i] - if i == 0 { 0.0 } else { marks[i - 1] };
        let full: Vec<usize> = (1..batches.len())
            .filter(|&i| batches[i] == (BATCH_TRIPLES, 0) && batches[i - 1].1 == 0)
            .collect();
        if !full.is_empty() {
            let seconds: f64 = full.iter().map(|&i| span(i)).sum();
            println!(
                "per triple, over {} whole triple batches: {:.4} ms",
                full.len(),
                1e3 * seconds / (full.len() * BATCH_TRIPLES) as f64
            );
        }
        let plain: Vec<usize> = (1..batches.len())
            .filter(|&i| batches[i].0 == 0 && batches[i - 1].0 == 0)
            .collect();
        if !plain.is_empty() {
            let seconds: f64 = plain.iter().map(|&i| span(i)).sum();
            let randoms: usize = plain.iter().map(|&i| batches[i].1).sum();
            println!(
                "per random, over {} random-only batches ({randoms} randoms): {:.2} us",
                plain.len(),
                1e6 * seconds / randoms as f64
            );
        }
        if demand.triples != 0 {
            println!(
                "whole ceremony per triple demanded: {:.4} ms",
                1e3 * wall / demand.triples as f64
            );
        }
    }
}
