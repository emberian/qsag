//! Dealerless preprocessing ceremony for the authenticated general-quorum
//! engine: the quorum members produce their [`MacKeyShare`]s and
//! [`PartyPreprocessing`] stores themselves, with no party that knows a key
//! or a shared value.
//!
//! The target is security with abort against any `m − 1` actively corrupted
//! members of an `m`-member quorum. All parties' steps run in one process on
//! separated per-party state (the model of
//! `qsag_core::preprocessing::run_dealerless_pi_triple_f2`); data that one
//! party sends to another is absorbed into a transcript chain, and every
//! challenge is expanded from a commit-and-open coin drawn over that chain
//! after the checked data has been sent.
//!
//! # Building blocks
//!
//! * **Base correlation.** For every ordered pair (owner `o`, holder `h`) one
//!   batch of 832 random OTs from the mesh, with `h` as receiver and the bits
//!   of all of `h`'s MAC key shares as choice bits. Each pad seeds a cSHAKE256
//!   stream; all later authentications between the pair read these streams,
//!   so the key `h` uses towards `o` is fixed once (COPE, MASCOT: Keller,
//!   Orsini, Scholl, CCS 2016, ePrint 2016/505, Section 3; IKNP/KOS for the
//!   Boolean key). The last 64 OTs have choice bit 0: their first pads are
//!   common to the pair and mask the openings of the key-consistency check.
//! * **Field authentication** (`Ceremony::authenticate`). The owner sends,
//!   per key bit, `t0 − t1 + x`; the holder obtains `t0 + bit·x`. Summed with
//!   weights `2^l` this shares `key_h · x`. An opened random combination with
//!   an authenticated mask and a commit-then-open MAC check makes the owner's
//!   inputs consistent (MASCOT Section 4, Input and Check).
//! * **Bits** (`Ceremony::prove_bits`). `x² = x` for owner-known values is
//!   proved to each holder on the pairwise correlation `Q = T + key·x` by a
//!   degree-2 check (QuickSilver: Yang, Sarkar, Weng, Wang, CCS 2021,
//!   Section 4), which needs no multiplication triple.
//! * **Field triples** (`Ceremony::multiply`, MASCOT Section 5, Protocol 4):
//!   the party holding `a` is the OT receiver with the bits of `a` as choices,
//!   the sender's correlation is its `b`; privacy amplification over `τ`
//!   components, authentication, sacrifice.
//! * **Boolean material** from qsag-core's `Π_triple_f2`, run n-of-n over the
//!   quorum and converted from Shamir shares in the tower basis to additive
//!   shares in the polynomial basis.
//! * **Doubly authenticated bits**: per owner, bits authenticated under the
//!   Boolean key (holder as OT receiver on its key bits) and under the field
//!   key, proved to be bits, proved equal across the two domains, and XORed
//!   over the owners with one field triple per XOR.
//!
//! # Parameters
//!
//! Write `k = log2 |F|` (64, 256, 255).
//!
//! * `τ` and the number `σ` of sacrificial triples ([`tau`], [`sacrifices`]).
//!   A corrupted sender in `Ceremony::multiply` can use different
//!   correlations in different OTs and learns, from whether the sacrifice
//!   passes, a predicate of the receiver's `a ∈ F^τ`. Conditioning a uniform
//!   source on an event of probability `q` costs `log2(1/q)` bits of
//!   min-entropy, and the event itself has probability `q`. The combination
//!   `a ↦ (⟨a,r⟩, ⟨a,r̂_1⟩, …, ⟨a,r̂_σ⟩)` with coin-chosen `r, r̂` is a universal
//!   hash onto `F^{1+σ}` (the `r̂` components are masks of the opened
//!   `s·a − â`). By the leftover hash lemma the output is within
//!   `q · ½ · 2^{−(τk − log2(1/q) − (1+σ)k)/2} ≤ ½ · 2^{−(τ−1−σ)k/2}` of
//!   uniform. `σ` is fixed by sacrifice soundness `|F|^{−σ}`: `σ = 1` for the
//!   large fields and `σ = 2` for Goldilocks (`2^-128`). Then `τ = 3` gives
//!   `2^-128.5` for the large fields and `τ = 7` gives `2^-129` for
//!   Goldilocks (`τ = 6` would give only `2^-97`).
//! * [`CROSS_REPS`]` = 128` subset-parity repetitions of the cross-domain
//!   check; a candidate whose two forms differ survives each with probability
//!   exactly 1/2.
//! * [`MASK_BITS`]` = 128` sacrificed Boolean candidates form each uniform
//!   `GF(2^128)` mask.
//! * Goldilocks carries two independent 64-bit MAC keys. Every random
//!   combination is drawn independently per key, or (owner input check)
//!   twice with every instance checked under both keys, so that no event of
//!   probability `2^-64` defeats both.
#![allow(
    clippy::needless_range_loop,
    clippy::too_many_arguments,
    clippy::type_complexity
)]

use super::{Demand, PartyPreprocessing};
use crate::{
    circuit::{Domain, Value},
    outer_mpc::Error,
    secret::{Secret, SecretVec},
    threshold_mpc::{
        AuthWord, BlindOtPeer, BooleanTriple, DaBitWord, FieldShare, FieldTriple, MacKeyShare,
        ThresholdConfig, ThresholdField, mac_add, mac_scale, mac_sub, pack_macs,
    },
};
use alloc::{vec, vec::Vec};
use core::ops::Range;
use qsag_accel::{
    gf2_128::gf2_128_mul,
    keccak::{Shake256, cshake256_framed_32, finalize_cshake256, init_cshake256},
};
use qsag_core::{
    field::tower::{PublicGf256Matrix, TowerGf256, lagrange_weights_zero_gf256},
    preprocessing::{
        OtMesh, PartyPrivateRng, run_commit_and_open_coin,
        run_dealerless_pi_triple_f2_with_transcript,
    },
    wipe::wipe_bytes,
};

const ZERO: Value = [0; 6];
const ONE: Value = [1, 0, 0, 0, 0, 0];

/// Subset-parity repetitions of the cross-domain equality check.
pub const CROSS_REPS: usize = 128;
/// Sacrificed Boolean candidates that form one uniform `GF(2^128)` mask.
pub const MASK_BITS: usize = 128;
/// Largest number of 64-bit daBit words per field in one ceremony.
/// The 2^32-bit algebraic bound is expressed in words so it also fits a
/// 32-bit `usize` (including wasm32).
const MAX_DABIT_WORDS: usize = 1 << 26;

/// Components of `a` per raw triple (see the module documentation).
pub const fn tau(field: ThresholdField) -> usize {
    match field {
        ThresholdField::Goldilocks => 7,
        _ => 3,
    }
}
/// Sacrificial triples per output triple; soundness `|F|^-σ`.
pub const fn sacrifices(field: ThresholdField) -> usize {
    match field {
        ThresholdField::Goldilocks => 2,
        _ => 1,
    }
}
/// Independent MAC keys of the field.
const fn key_count(d: Domain) -> usize {
    if matches!(d, Domain::Gold) { 2 } else { 1 }
}
/// Values each party authenticates per triple: `a, b, c` and `σ` pairs `(â, ĉ)`.
const fn triple_inputs(field: ThresholdField) -> usize {
    3 + 2 * sacrifices(field)
}

/// Choice words of one base-OT batch: two Goldilocks keys (`2` words), the
/// secp256k1 key (`4` words), the Ed25519 key (`4` words, one OT unused), the
/// Pallas key (`4` words, one OT unused), the BLS12-381 key (`6` words, three
/// OTs unused), the Boolean key (`2` words), and one zero word. The holder
/// receives the owner's first pad of every OT of the zero word, so the stream
/// of such a pad is known to exactly that pair.
const BASE_WORDS: usize = 23;
const BOOLEAN_BASE: usize = 1280;
/// The OT whose first pad seeds the pair's common mask stream.
const SHARED_BASE: usize = 1408;
const fn field_base(field: ThresholdField, key: usize) -> usize {
    match field {
        ThresholdField::Goldilocks => 64 * key,
        ThresholdField::Secp256k1 => 128,
        ThresholdField::Ed25519 => 384,
        ThresholdField::Pallas => 640,
        ThresholdField::Bls12_381 => 896,
    }
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
    /// qsag-core's Boolean triple ceremony aborted.
    BooleanCeremony,
    /// An owner's field inputs were not the same under every key bit, or a
    /// holder's MAC share was not the one its key determines.
    InputConsistency,
    /// An owner's Boolean inputs were not the same under every key bit.
    BooleanInput,
    /// A value claimed to be a bit is not one.
    Bitness,
    /// A holder used different field keys towards different owners.
    KeyConsistency,
    /// A triple is not multiplicative, or an opening of the sacrifice was wrong.
    TripleSacrifice,
    /// A Boolean parity of the cross-domain check was opened wrongly.
    ParityOpening,
    /// A candidate's field form and Boolean form differ.
    CrossDomain,
    /// An opening of the XOR over the owners was wrong.
    XorChain,
    /// A party's Boolean key differs between the triple ceremony and the bit
    /// authentication.
    BooleanKeyConsistency,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Abort {
    Config,
    Check(Check),
}
impl From<Check> for Abort {
    fn from(check: Check) -> Self {
        Self::Check(check)
    }
}
impl From<Abort> for Error {
    fn from(abort: Abort) -> Self {
        match abort {
            Abort::Config => Error::InvalidConfiguration,
            Abort::Check(_) => Error::MultiplicationCheck,
        }
    }
}

/// A point where one party can deviate. The ceremony passes each point to the
/// fault hook with the data the party is about to use; an honest hook leaves
/// it unchanged. Parties are quorum positions.
pub enum Fault<'a> {
    /// The field key share `holder` commits to in its base OTs with `owner`
    /// and uses in every check of `owner`'s inputs.
    FieldKey {
        field: ThresholdField,
        owner: usize,
        holder: usize,
        key: &'a mut Value,
    },
    /// The Boolean key share `holder` commits to in its base OTs with `owner`
    /// and uses in every check of `owner`'s inputs.
    BooleanKey {
        owner: usize,
        holder: usize,
        key: &'a mut u128,
    },
    /// The values `owner` encodes for `holder` under bit `bit` of key `key`.
    CopeInput {
        field: ThresholdField,
        owner: usize,
        holder: usize,
        key: usize,
        bit: usize,
        values: &'a mut [Value],
    },
    /// `holder`'s MAC shares of one batch of `owner`'s values.
    CopeHolderShare {
        field: ThresholdField,
        owner: usize,
        holder: usize,
        macs: &'a mut [Value],
    },
    /// The correlation `sender` uses in one OT of the triple multiplication.
    TripleCorrelation {
        field: ThresholdField,
        sender: usize,
        receiver: usize,
        triple: usize,
        slot: usize,
        bit: usize,
        correlation: &'a mut Value,
    },
    /// `party`'s raw product shares, `τ` per triple.
    TripleProduct {
        field: ThresholdField,
        party: usize,
        products: &'a mut [Value],
    },
    /// The candidate words `owner` encodes for `holder` under one Boolean key bit.
    BooleanInput {
        owner: usize,
        holder: usize,
        bit: usize,
        words: &'a mut [u64],
    },
    /// The field form of `owner`'s candidate bits (retained, then masks).
    DaBitFieldInput {
        field: ThresholdField,
        owner: usize,
        values: &'a mut [Value],
    },
    /// The Boolean parity `owner` announces in one repetition of the
    /// cross-domain check.
    Parity {
        field: ThresholdField,
        owner: usize,
        repetition: usize,
        parity: &'a mut u64,
    },
    /// The value share `party` sends in a partial opening that `check` settles.
    FieldOpening {
        field: ThresholdField,
        party: usize,
        check: Check,
        share: &'a mut Value,
    },
    /// The check share `party` commits to for one opened item of the
    /// key-consistency check, after every party's value share of that item
    /// (`sent`, by party) is public.
    KeyConsistencySigma {
        field: ThresholdField,
        party: usize,
        sent: &'a [Value],
        sigma: &'a mut Value,
    },
    /// The commitment `party` sends in commit-then-open invocation
    /// `invocation` of the ceremony.
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

fn limbs_of(d: Domain) -> usize {
    d.width().div_ceil(64)
}

fn parse_element(d: Domain, bytes: &[u8]) -> Value {
    let mut value = ZERO;
    for (limb, chunk) in value.iter_mut().zip(bytes.chunks_exact(8)) {
        *limb = u64::from_le_bytes(chunk.try_into().unwrap());
    }
    if d == Domain::Ed || d == Domain::PallasFp {
        value[3] &= u64::MAX >> 1;
    } else if d == Domain::BlsFp {
        value[5] &= u64::MAX >> 3;
    }
    value
}

/// Uniform canonical element by rejection from `fill`.
fn element_from(d: Domain, mut fill: impl FnMut(&mut [u8])) -> Value {
    let size = 8 * limbs_of(d);
    let mut bytes = [0u8; 48];
    loop {
        fill(&mut bytes[..size]);
        let value = parse_element(d, &bytes[..size]);
        if d.canonical(value) {
            wipe_bytes(&mut bytes);
            return value;
        }
    }
}

/// Field element from one 48-byte random-OT pad. Candidates are read from
/// the pad until one is canonical; the last is reduced (or expanded via
/// wide zero-rejection reduction for `PallasFp` and `BlsFp`). The result is
/// within `2^-192` (Goldilocks), `2^-224` (secp256k1), `2^-250` (Ed25519),
/// `2^-253.8` (Pallas), and `2^-379` (BLS12-381) of uniform.
fn pad_element(d: Domain, pad: &[u8; 48]) -> Value {
    if d == Domain::Gold {
        let mut value = 0;
        for chunk in pad.chunks_exact(8) {
            value = u64::from_le_bytes(chunk.try_into().unwrap());
            if d.canonical([value, 0, 0, 0, 0, 0]) {
                return [value, 0, 0, 0, 0, 0];
            }
        }
        return [value.wrapping_sub(d.modulus()[0]), 0, 0, 0, 0, 0];
    }
    if d == Domain::PallasFp {
        let mut sponge = xof(b"QSAG.MIGRATE.PREP.WIDE_PAD.V1", &[b"pallas", pad]);
        let mut buf = [0u8; 64];
        sponge.squeeze(&mut buf);
        let mut lo = parse_element(d, &buf[..32]);
        let mut hi = parse_element(d, &buf[32..64]);
        lo[3] &= (1u64 << 62) - 1;
        hi[3] &= (1u64 << 62) - 1;
        wipe_bytes(&mut buf);
        return d.add(lo, d.mul([0, 0, 0, 1u64 << 62, 0, 0], hi));
    }
    if d == Domain::BlsFp {
        let mut sponge = xof(b"QSAG.MIGRATE.PREP.WIDE_PAD.V1", &[b"bls12_381", pad]);
        let mut buf = [0u8; 96];
        sponge.squeeze(&mut buf);
        let mut lo = parse_element(d, &buf[..48]);
        let mut hi = parse_element(d, &buf[48..96]);
        lo[5] &= (1u64 << 60) - 1;
        hi[5] &= (1u64 << 60) - 1;
        wipe_bytes(&mut buf);
        return d.add(lo, d.mul([0, 0, 0, 0, 0, 1u64 << 60], hi));
    }
    let value = parse_element(d, &pad[..32]);
    if d.canonical(value) {
        value
    } else {
        // Below 2^256 < 2p (secp256k1) or below 2^255 < 2p (Ed25519).
        crate::limbs::sbb(value, d.modulus()).0
    }
}

/// cSHAKE256 stream expanding one OT pad.
struct Prg(
    Shake256,
    Option<qsag_core::sponge::keccak::Cshake256WordStream4>,
);
impl Prg {
    fn new(
        session: &[u8; 32],
        sender: usize,
        receiver: usize,
        index: usize,
        pad: &[u8; 48],
    ) -> Self {
        Self(
            xof(
                b"QSAG.MIGRATE.PREP.PAD.V1",
                &[
                    session,
                    &[sender as u8, receiver as u8],
                    &(index as u64).to_le_bytes(),
                    pad,
                ],
            ),
            None,
        )
    }
    fn elements(&mut self, d: Domain, out: &mut [Value]) {
        let size = 8 * limbs_of(d);
        let mut block = [0u8; 8 * 136];
        for chunk in out.chunks_mut(block.len() / size) {
            let bytes = &mut block[..chunk.len() * size];
            self.0.squeeze(bytes);
            for (value, raw) in chunk.iter_mut().zip(bytes.chunks_exact(size)) {
                *value = parse_element(d, raw);
            }
            for value in chunk {
                if !d.canonical(*value) {
                    *value = element_from(d, |bytes| self.0.squeeze(bytes));
                }
            }
        }
        wipe_bytes(&mut block);
    }
    fn words(&mut self, out: &mut [u64]) {
        use qsag_core::sponge::keccak::{Cshake256WordStream4, cshake256_static_midstate};
        const MID: [u64; 25] = cshake256_static_midstate(b"QSAG.MIGRATE.PREP.WORD_PAD.V2");
        let stream = self.1.get_or_insert_with(|| {
            let mut seed = [0u8; 32];
            self.0.squeeze(&mut seed);
            let stream = Cshake256WordStream4::new(&MID, &seed);
            wipe_bytes(&mut seed);
            stream
        });
        stream.fill_words(out);
    }
}

/// Public challenge expansion of one coin.
struct Challenges(Shake256);
impl Challenges {
    fn element(&mut self, d: Domain) -> Value {
        element_from(d, |bytes| self.0.squeeze(bytes))
    }
    fn u128(&mut self) -> u128 {
        let mut bytes = [0u8; 16];
        self.0.squeeze(&mut bytes);
        u128::from_le_bytes(bytes)
    }
    fn words(&mut self, out: &mut [u64]) {
        for word in out {
            let mut bytes = [0u8; 8];
            self.0.squeeze(&mut bytes);
            *word = u64::from_le_bytes(bytes);
        }
    }
}

/// Component `key` of a MAC or key share, as a field element.
#[inline(always)]
fn part(d: Domain, mac: Value, key: usize) -> Value {
    if d == Domain::Gold {
        [mac[key], 0, 0, 0, 0, 0]
    } else {
        mac
    }
}
#[inline(always)]
fn set_part(d: Domain, mac: &mut Value, key: usize, value: Value) {
    if d == Domain::Gold {
        mac[key] = value[0];
    } else {
        *mac = value;
    }
}

/// One party's share of an authenticated field element: `[value, MAC]`.
type Share = [Value; 2];
#[inline(always)]
fn share_add(d: Domain, a: Share, b: Share) -> Share {
    [d.add(a[0], b[0]), mac_add(d, a[1], b[1])]
}
#[inline(always)]
fn share_sub(d: Domain, a: Share, b: Share) -> Share {
    [d.sub(a[0], b[0]), mac_sub(d, a[1], b[1])]
}
#[inline(always)]
fn share_scale(d: Domain, a: Share, by: Value) -> Share {
    [d.mul(a[0], by), mac_scale(d, a[1], by)]
}

/// `Σ_l X^l · bit_l` for the 128 bits of `words[at..at + 2]`.
fn mask_value(words: &[u64], at: usize) -> u128 {
    (words[at] as u128) | ((words[at + 1] as u128) << 64)
}
/// `Σ_l X^l · macs[l]` over 128 per-bit MAC shares.
fn mask_mac(macs: &[u128]) -> u128 {
    let low: &[u128; 64] = macs[..64].try_into().unwrap();
    let high: &[u128; 64] = macs[64..128].try_into().unwrap();
    pack_macs(low, u64::MAX) ^ gf2_128_mul(pack_macs(high, u64::MAX), 1 << 64)
}

/// Commitment of `party` to `payload` in commit-then-open invocation
/// `invocation` of the ceremony `session`. The invocation number is part of
/// the preimage, so a commitment and its opening are valid in one invocation
/// only, whatever the label and the payload.
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
        b"QSAG.MIGRATE.PREP.COMMIT.V2",
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

/// Hash chain over everything the parties send each other. The schedule of
/// messages and all lengths are public functions of the configuration and
/// the demand, so the concatenation parses uniquely.
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
            .extend_from_slice(b"QSAG.MIGRATE.PREP.TRANSCRIPT.V1");
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
    fn element(&mut self, d: Domain, value: &Value) {
        for limb in &value[..limbs_of(d)] {
            self.bytes(&limb.to_le_bytes());
        }
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

/// Partially opened field values and values claimed to be zero, awaiting one
/// batch MAC check.
struct FieldQueue {
    values: Vec<Value>,
    /// `macs[p][entry]`.
    macs: Vec<SecretVec<Value>>,
    /// The owner whose inputs alone make up the entry, if any.
    owners: Vec<Option<usize>>,
}
impl FieldQueue {
    fn new(parties: usize) -> Self {
        Self {
            values: Vec::new(),
            macs: (0..parties).map(|_| SecretVec::new()).collect(),
            owners: Vec::new(),
        }
    }
}

struct BooleanQueue {
    values: Vec<u128>,
    macs: Vec<SecretVec<u128>>,
    owners: Vec<Option<usize>>,
}
impl BooleanQueue {
    fn new(parties: usize) -> Self {
        Self {
            values: Vec::new(),
            macs: (0..parties).map(|_| SecretVec::new()).collect(),
            owners: Vec::new(),
        }
    }
}

/// Bit offsets of every owner's Boolean candidates: per field the retained
/// bits followed by [`CROSS_REPS`] parity masks, then the mask of the input
/// check, then the mask of the key-consistency check.
struct Layout {
    retained: [usize; 5],
    at: [usize; 5],
    input_mask: usize,
    key_mask: usize,
    total: usize,
}
impl Layout {
    fn new(demand: &Demand) -> Result<Self, Abort> {
        let mut at = [0; 5];
        let mut retained = [0; 5];
        let mut next = 0usize;
        for i in 0..5 {
            if demand.dabits[i] > MAX_DABIT_WORDS {
                return Err(Abort::Config);
            }
            at[i] = next;
            retained[i] = demand.dabits[i].checked_mul(64).ok_or(Abort::Config)?;
            if retained[i] != 0 {
                next = next
                    .checked_add(retained[i])
                    .and_then(|n| n.checked_add(CROSS_REPS))
                    .ok_or(Abort::Config)?;
            }
        }
        Ok(Self {
            retained,
            at,
            input_mask: next,
            key_mask: next.checked_add(MASK_BITS).ok_or(Abort::Config)?,
            total: next.checked_add(2 * MASK_BITS).ok_or(Abort::Config)?,
        })
    }
}

/// Every owner's Boolean candidates and all parties' MAC shares of them.
struct Candidates {
    /// `bits[o]`: owner `o`'s candidate words.
    bits: Vec<SecretVec<u64>>,
    /// `macs[o][p][bit]`: party `p`'s MAC share of owner `o`'s candidate.
    macs: Vec<Vec<SecretVec<u128>>>,
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
    boolean_keys: SecretVec<u128>,
    field_keys: SecretVec<[Value; 5]>,
    /// `[o][h]`: the keys `h` committed to in its base OTs with `o`.
    pair_boolean_keys: Vec<SecretVec<u128>>,
    pair_field_keys: Vec<SecretVec<[Value; 5]>>,
    pairs: Vec<Vec<Option<Pair>>>,
}

impl<'a> Ceremony<'a> {
    fn new(
        session: [u8; 32],
        mesh: &'a mut OtMesh,
        rngs: &'a mut [PartyPrivateRng],
        fault: &'a mut dyn FnMut(Fault<'_>),
    ) -> Result<Self, Abort> {
        let parties = rngs.len();
        if !(2..=64).contains(&parties) || mesh.n != parties {
            return Err(Abort::Config);
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
            boolean_keys: SecretVec::new(),
            field_keys: SecretVec::new(),
            pair_boolean_keys: Vec::new(),
            pair_field_keys: Vec::new(),
            pairs: Vec::new(),
        })
    }

    /// Jointly random public coin over the transcript so far, as a challenge
    /// stream.
    ///
    /// The mesh's chain over all OT extension batches run so far is absorbed
    /// first, so the coin also depends on every OT message sent before it.
    fn coin(&mut self, label: &[u8]) -> Result<Challenges, Abort> {
        self.transcript.label(b"ot mesh");
        self.transcript.bytes(&self.mesh.transcript_digest());
        let digest = self.transcript.digest();
        let mut phase = label.to_vec();
        phase.extend_from_slice(&self.coins.to_le_bytes());
        self.coins = self.coins.checked_add(1).ok_or(Check::Coin)?;
        let coin = run_commit_and_open_coin(&self.session, &phase, &digest, self.rngs)
            .map_err(|_| Check::Coin)?;
        self.transcript.label(b"coin");
        self.transcript.bytes(&coin);
        Ok(Challenges(xof(
            b"QSAG.MIGRATE.PREP.CHALLENGE.V1",
            &[&self.session, &phase, &coin],
        )))
    }

    /// Every party commits to its payload; after all commitments are sent the
    /// payloads are opened and compared with them.
    ///
    /// Every call takes the next value of the ceremony's invocation counter,
    /// which enters each commitment and the transcript: what a party sent in
    /// one invocation opens in no other.
    fn commit_then_open(&mut self, label: &[u8], payloads: &[SecretVec<u64>]) -> Result<(), Abort> {
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
            if opened != commitments[party] {
                return Err(Check::Commitment.into());
            }
            for word in payload.iter() {
                self.transcript.bytes(&word.to_le_bytes());
            }
        }
        Ok(())
    }

    fn sample(&mut self, party: usize, d: Domain) -> Value {
        let rng = &mut self.rngs[party];
        element_from(d, |bytes| rng.fill_bytes(bytes))
    }

    /// The key share `party` uses in a check of material that `owner` alone
    /// input (`None`: material combined over the owners).
    fn field_key_for(&self, field: ThresholdField, owner: Option<usize>, party: usize) -> &Value {
        match owner {
            Some(owner) if owner != party => &self.pair_field_keys[owner][party][field.index()],
            _ => &self.field_keys[party][field.index()],
        }
    }
    fn boolean_key_for(&self, owner: Option<usize>, party: usize) -> &u128 {
        match owner {
            Some(owner) if owner != party => &self.pair_boolean_keys[owner][party],
            _ => &self.boolean_keys[party],
        }
    }

    // ------------------------------------------------------------------------
    // Keys and base correlation
    // ------------------------------------------------------------------------

    /// Every party samples its field key shares (two for Goldilocks).
    fn sample_field_keys(&mut self) {
        for party in 0..self.parties {
            self.field_keys.push([ZERO; 5]);
            for field in ThresholdField::ALL {
                let d = field.domain();
                for key in 0..key_count(d) {
                    let value = Secret(self.sample(party, d));
                    set_part(d, &mut self.field_keys[party][field.index()], key, *value);
                }
            }
        }
    }

    /// One batch of random OTs per ordered pair, the holder receiving on the
    /// bits of its key shares. The holder cannot use another key for a single
    /// value later: its pads are fixed here.
    fn establish_pairs(&mut self) -> Result<(), Abort> {
        let parties = self.parties;
        for owner in 0..parties {
            let mut boolean_keys = SecretVec::with_capacity(parties);
            let mut field_keys = SecretVec::with_capacity(parties);
            let mut row = Vec::with_capacity(parties);
            for holder in 0..parties {
                let mut boolean = Secret(self.boolean_keys[holder]);
                let mut fields = Secret(self.field_keys[holder]);
                if holder == owner {
                    boolean_keys.push(*boolean);
                    field_keys.push(*fields);
                    row.push(None);
                    continue;
                }
                (self.fault)(Fault::BooleanKey {
                    owner,
                    holder,
                    key: &mut boolean,
                });
                for field in ThresholdField::ALL {
                    (self.fault)(Fault::FieldKey {
                        field,
                        owner,
                        holder,
                        key: &mut fields[field.index()],
                    });
                }
                let mut choices: SecretVec<u64> = SecretVec::with_capacity(BASE_WORDS);
                choices.extend_from_slice(&fields[0][..2]);
                choices.extend_from_slice(&fields[1][..4]);
                choices.extend_from_slice(&fields[2][..4]);
                choices.extend_from_slice(&fields[3][..4]);
                choices.extend_from_slice(&fields[4][..6]);
                choices.push(*boolean as u64);
                choices.push((*boolean >> 64) as u64);
                choices.push(0);
                let (send, receive) = self
                    .mesh
                    .run_correlated_ot_words(owner, holder, &choices, self.rngs)
                    .map_err(|_| Check::Ot)?;
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
                boolean_keys.push(*boolean);
                field_keys.push(*fields);
            }
            self.pair_boolean_keys.push(boolean_keys);
            self.pair_field_keys.push(field_keys);
            self.pairs.push(row);
        }
        Ok(())
    }

    // ------------------------------------------------------------------------
    // Field authentication
    // ------------------------------------------------------------------------

    /// COPE extension of `inputs` between `owner` and `holder` under key
    /// `key`. Returns `(T, Q)` with `Q[k] = T[k] + key_h · inputs[k]`: `T` is
    /// the owner's, `Q` the holder's.
    fn cope(
        &mut self,
        field: ThresholdField,
        owner: usize,
        holder: usize,
        key: usize,
        inputs: &[Value],
    ) -> (SecretVec<Value>, SecretVec<Value>) {
        let d = field.domain();
        let count = inputs.len();
        let base = field_base(field, key);
        let Self {
            pairs,
            fault,
            transcript,
            pair_field_keys,
            ..
        } = self;
        let key_share = &pair_field_keys[owner][holder][field.index()];
        // A Goldilocks key is one limb of the share; the other keys are the share.
        let word = |bit: usize| if d == Domain::Gold { key } else { bit / 64 };
        let pair = pairs[owner][holder].as_mut().unwrap();
        let zeros = || SecretVec::from(vec![ZERO; count]);
        let (mut t, mut q) = (zeros(), zeros());
        let (mut zero, mut one, mut chosen, mut encoded) = (zeros(), zeros(), zeros(), zeros());
        transcript.label(b"cope");
        for bit in (0..d.width()).rev() {
            pair.send[base + bit][0].elements(d, &mut zero);
            pair.send[base + bit][1].elements(d, &mut one);
            pair.receive[base + bit].elements(d, &mut chosen);
            encoded.copy_from_slice(inputs);
            fault(Fault::CopeInput {
                field,
                owner,
                holder,
                key,
                bit,
                values: &mut encoded,
            });
            let select = Secret(0u64.wrapping_sub((key_share[word(bit)] >> (bit % 64)) & 1));
            for k in 0..count {
                // Owner to holder.
                let correction = d.add(d.sub(zero[k], one[k]), encoded[k]);
                transcript.element(d, &correction);
                let received = d.add(chosen[k], correction.map(|limb| limb & *select));
                t[k] = d.add(d.add(t[k], t[k]), zero[k]);
                q[k] = d.add(d.add(q[k], q[k]), received);
            }
        }
        (t, q)
    }

    /// Every owner authenticates its `inputs[o]` (equal lengths) towards all
    /// other parties; the items in `bits` are also proved to be 0 or 1.
    ///
    /// Party `p`'s MAC share of owner `o`'s item is `Q` from the pair
    /// `(o, p)`, and `o`'s own is `key_o · x − Σ_h T_h`.
    ///
    /// **Input check** (MASCOT Section 4). Each owner appends uniformly
    /// random mask items. After all corrections are sent a coin fixes `r`;
    /// the owner opens `y = Σ r_k x_k + mask` and every party commits to and
    /// then opens `σ_p = Σ r_k m_k + m_mask − key_p · y`; the `σ_p` must sum
    /// to zero. For Goldilocks this runs twice with independent `r` and
    /// masks, each instance under both keys.
    ///
    /// If the owner encoded different values under different key bits of an
    /// honest holder, the holder's share is off by `Σ_l 2^l · bit_l · e_l`
    /// with `e_l` fixed by the corrections; the sum of the `σ` is that error
    /// (combined by `r`) plus what the owner adds without knowing the key
    /// bits. Either the combined `e_l` vanish for the bits where they could
    /// matter (probability at most `1/|F|` per instance over `r`), or the
    /// check passes exactly when the holder's key lies in a set `S` that the
    /// adversary fixed in advance, which happens with probability `|S|/|F|`.
    /// So a failed check tells the adversary that the key is outside `S`
    /// (and the ceremony's keys are then discarded), and a passed check that
    /// it is inside: guessing `c` key bits succeeds with probability `2^-c`
    /// and leaves a later forgery probability of `2^c/|F|`, the product
    /// staying at `1/|F|` per key. Nothing about any shared value is
    /// revealed either way: `y` is masked, and whether the check passes
    /// depends on key bits only. A holder cannot choose its key per value
    /// (its pads are fixed), and a wrong MAC share of the holder changes the
    /// sum of the `σ` by a nonzero amount it cannot cancel without the
    /// owner's pads.
    fn authenticate(
        &mut self,
        field: ThresholdField,
        inputs: &[SecretVec<Value>],
        bits: Range<usize>,
    ) -> Result<OwnerShares, Abort> {
        let d = field.domain();
        let parties = self.parties;
        let keys = key_count(d);
        let count = inputs[0].len();
        let bit_masks = if bits.is_empty() {
            0
        } else {
            (parties - 1) * keys
        };
        let masked = count + bit_masks;
        let total = masked + keys;

        let mut values: Vec<SecretVec<Value>> = Vec::with_capacity(parties);
        let mut macs: Vec<Vec<SecretVec<Value>>> = Vec::with_capacity(parties);
        // `pads[o][holder slot][key] = (T, Q)`.
        let mut pads: Vec<Vec<Vec<(SecretVec<Value>, SecretVec<Value>)>>> =
            Vec::with_capacity(parties);
        for owner in 0..parties {
            let mut extended: SecretVec<Value> = inputs[owner].iter().copied().collect();
            for _ in count..total {
                let mask = self.sample(owner, d);
                extended.push(mask);
            }
            let own_key = &self.field_keys[owner][field.index()];
            let mut shares: Vec<SecretVec<Value>> = (0..parties)
                .map(|_| SecretVec::from(vec![ZERO; total]))
                .collect();
            for k in 0..total {
                shares[owner][k] = mac_scale(d, *own_key, extended[k]);
            }
            let mut owner_pads = Vec::with_capacity(parties - 1);
            for holder in (0..parties).filter(|&h| h != owner) {
                let mut by_key = Vec::with_capacity(keys);
                for key in 0..keys {
                    let (t, q) = self.cope(field, owner, holder, key, &extended);
                    for k in 0..total {
                        let own = d.sub(part(d, shares[owner][k], key), t[k]);
                        set_part(d, &mut shares[owner][k], key, own);
                        set_part(d, &mut shares[holder][k], key, q[k]);
                    }
                    by_key.push((t, q));
                }
                (self.fault)(Fault::CopeHolderShare {
                    field,
                    owner,
                    holder,
                    macs: &mut shares[holder],
                });
                owner_pads.push(by_key);
            }
            values.push(extended);
            macs.push(shares);
            pads.push(owner_pads);
        }

        let mut challenges = self.coin(b"authenticate")?;
        let mut sigmas: Vec<SecretVec<u64>> = (0..parties).map(|_| SecretVec::new()).collect();
        self.transcript.label(b"input check");
        for owner in 0..parties {
            for instance in 0..keys {
                let mask = masked + instance;
                let mut opened = values[owner][mask];
                let mut sigma: SecretVec<Value> =
                    (0..parties).map(|p| macs[owner][p][mask]).collect();
                for k in 0..masked {
                    let r = challenges.element(d);
                    opened = d.add(opened, d.mul(r, values[owner][k]));
                    for p in 0..parties {
                        sigma[p] = mac_add(d, sigma[p], mac_scale(d, macs[owner][p][k], r));
                    }
                }
                // The owner broadcasts the combination.
                self.transcript.element(d, &opened);
                for p in 0..parties {
                    let keyed = Secret(mac_scale(
                        d,
                        *self.field_key_for(field, Some(owner), p),
                        opened,
                    ));
                    let share = mac_sub(d, sigma[p], *keyed);
                    sigmas[p].extend_from_slice(&share);
                }
            }
        }
        self.commit_then_open(b"input check sigma", &sigmas)?;
        for entry in 0..parties * keys {
            let sum = (0..parties).fold(ZERO, |sum, p| {
                let share: Value = sigmas[p][6 * entry..6 * entry + 6].try_into().unwrap();
                mac_add(d, sum, share)
            });
            if sum != ZERO {
                return Err(Check::InputConsistency.into());
            }
        }

        if !bits.is_empty() {
            self.prove_bits(field, &values, &pads, bits, count, &mut challenges)?;
        }

        Ok((0..parties)
            .map(|owner| {
                (0..parties)
                    .map(|p| {
                        (0..count)
                            .map(|k| {
                                [
                                    if p == owner { values[owner][k] } else { ZERO },
                                    macs[owner][p][k],
                                ]
                            })
                            .collect()
                    })
                    .collect()
            })
            .collect())
    }

    /// Each owner proves to each holder, under each of the holder's keys,
    /// that its items in `bits` satisfy `x² = x`.
    ///
    /// The pair holds `Q_k = T_k + key · x_k` (`T`, `x` with the owner, `Q`,
    /// `key` with the holder). Then
    /// `Q_k² − key·Q_k = T_k² + key·(2x_k − 1)·T_k + key²·(x_k² − x_k)`.
    /// With coin `χ` (drawn after the corrections that fix `Q`, `T`, `x`) and
    /// one authenticated random mask `(x*, T*, Q*)` per holder and key, the
    /// owner sends `U = Σ χ_k T_k² + T*` and `V = Σ χ_k (2x_k − 1) T_k + x*`,
    /// and the holder accepts iff `Σ χ_k (Q_k² − key·Q_k) + Q* = U + key·V`.
    ///
    /// Soundness (QuickSilver, Section 4, degree-2 case): if some `x_k` is
    /// not a bit, `Σ χ_k (x_k² − x_k) ≠ 0` except with probability `1/|F|`,
    /// and then the acceptance equation is a quadratic in the holder's key
    /// with nonzero leading coefficient that the owner fixed without knowing
    /// the key: at most 2 roots. Error at most `3/|F|` per key; the two
    /// Goldilocks keys use independent `χ` and both must accept, `2^-124`.
    /// Zero knowledge: `(U, V)` is uniform on the line the holder's equation
    /// defines, because `x*` is uniform and used once. A failed check tells a
    /// corrupted owner that its guess of the holder's key missed.
    fn prove_bits(
        &mut self,
        field: ThresholdField,
        values: &[SecretVec<Value>],
        pads: &[Vec<Vec<(SecretVec<Value>, SecretVec<Value>)>>],
        bits: Range<usize>,
        count: usize,
        challenges: &mut Challenges,
    ) -> Result<(), Abort> {
        let d = field.domain();
        let parties = self.parties;
        let keys = key_count(d);
        let mut accepted = true;
        self.transcript.label(b"bit proof");
        for owner in 0..parties {
            let chi: Vec<Vec<Value>> = (0..keys)
                .map(|_| bits.clone().map(|_| challenges.element(d)).collect())
                .collect();
            for (slot, holder) in (0..parties).filter(|&h| h != owner).enumerate() {
                for key in 0..keys {
                    let (t, q) = &pads[owner][slot][key];
                    let mask = count + slot * keys + key;
                    // Owner.
                    let mut u = t[mask];
                    let mut v = values[owner][mask];
                    for (chi, k) in chi[key].iter().zip(bits.clone()) {
                        let x = values[owner][k];
                        let slope = d.mul(d.sub(d.add(x, x), ONE), t[k]);
                        u = d.add(u, d.mul(*chi, d.mul(t[k], t[k])));
                        v = d.add(v, d.mul(*chi, slope));
                    }
                    self.transcript.element(d, &u);
                    self.transcript.element(d, &v);
                    // Holder.
                    let alpha = Secret(part(
                        d,
                        self.pair_field_keys[owner][holder][field.index()],
                        key,
                    ));
                    let mut left = q[mask];
                    for (chi, k) in chi[key].iter().zip(bits.clone()) {
                        let term = d.mul(q[k], d.sub(q[k], *alpha));
                        left = d.add(left, d.mul(*chi, term));
                    }
                    let keyed = Secret(d.mul(*alpha, v));
                    accepted &= left == d.add(u, *keyed);
                }
            }
        }
        if accepted {
            Ok(())
        } else {
            Err(Check::Bitness.into())
        }
    }

    /// Partially open a value: every party sends its value share; the MAC
    /// shares wait in `queue`.
    fn open(
        &mut self,
        field: ThresholdField,
        check: Check,
        queue: &mut FieldQueue,
        shares: impl Iterator<Item = Share>,
    ) -> Value {
        let d = field.domain();
        let mut value = ZERO;
        for (party, mut share) in shares.enumerate() {
            (self.fault)(Fault::FieldOpening {
                field,
                party,
                check,
                share: &mut share[0],
            });
            self.transcript.element(d, &share[0]);
            value = d.add(value, share[0]);
            queue.macs[party].push(share[1]);
        }
        queue.values.push(value);
        queue.owners.push(None);
        value
    }

    /// Queue a value that must be zero: its MAC shares must sum to zero.
    fn expect_zero(
        queue: &mut FieldQueue,
        owner: Option<usize>,
        macs: impl Iterator<Item = Value>,
    ) {
        for (party, mac) in macs.enumerate() {
            queue.macs[party].push(mac);
        }
        queue.values.push(ZERO);
        queue.owners.push(owner);
    }

    /// Batch MAC check of `queue`: a coin drawn after all queued values are
    /// public fixes `χ` (independently per key); every party commits to and
    /// then opens `σ_p = Σ χ_j (m_j − key_p · v_j)`; the sum must be zero.
    ///
    /// A wrong opened value `v + e` (or a nonzero value claimed zero) leaves
    /// `key · Σ χ_j e_j` in the sum, which the adversary can cancel only if
    /// `Σ χ_j e_j = 0` or by predicting the key: at most `2/|F|` per key,
    /// `2^-126` for Goldilocks and below `2^-253` for the large fields.
    fn check_field_queue(
        &mut self,
        field: ThresholdField,
        queue: FieldQueue,
        site: Check,
    ) -> Result<(), Abort> {
        if queue.values.is_empty() {
            return Ok(());
        }
        let d = field.domain();
        let parties = self.parties;
        let mut challenges = self.coin(b"field mac check")?;
        let mut sigma: SecretVec<Value> = SecretVec::from(vec![ZERO; parties]);
        for key in 0..key_count(d) {
            for (entry, value) in queue.values.iter().enumerate() {
                let chi = challenges.element(d);
                for p in 0..parties {
                    let share_key = Secret(part(
                        d,
                        *self.field_key_for(field, queue.owners[entry], p),
                        key,
                    ));
                    let keyed = Secret(d.mul(*share_key, *value));
                    let term = d.sub(part(d, queue.macs[p][entry], key), *keyed);
                    let sum = d.add(part(d, sigma[p], key), d.mul(chi, term));
                    set_part(d, &mut sigma[p], key, sum);
                }
            }
        }
        let payloads: Vec<SecretVec<u64>> =
            sigma.iter().map(|s| s.iter().copied().collect()).collect();
        self.commit_then_open(b"field sigma", &payloads)?;
        if sigma.iter().fold(ZERO, |sum, s| mac_add(d, sum, *s)) != ZERO {
            return Err(site.into());
        }
        Ok(())
    }

    // ------------------------------------------------------------------------
    // Field triples
    // ------------------------------------------------------------------------

    /// MASCOT Protocol 4, Multiply and Combine, for `count` triples. Returns
    /// per party and triple the values to authenticate:
    /// `a, b, c, â_1, ĉ_1, …`.
    ///
    /// Every party samples `a ∈ F^τ` and `b ∈ F` per triple. For each ordered
    /// pair the party holding `a` is the OT receiver with the bits of `a` as
    /// choice bits, so its input is the same in every OT by construction; the
    /// sender offsets pad differences by its `b`. A sender that uses another
    /// offset in some OT corrupts the product only if that bit of `a` is 1,
    /// which the sacrifice then detects: the leak about `a` this allows is
    /// removed by the combination (module documentation, `τ`).
    fn multiply(
        &mut self,
        field: ThresholdField,
        count: usize,
    ) -> Result<Vec<SecretVec<Value>>, Abort> {
        let d = field.domain();
        let parties = self.parties;
        let tau = tau(field);
        let per = triple_inputs(field);
        if count == 0 {
            return Ok((0..parties).map(|_| SecretVec::new()).collect());
        }
        let width = d.width();
        let words = limbs_of(d);

        let mut a: Vec<SecretVec<Value>> = Vec::with_capacity(parties);
        let mut b: Vec<SecretVec<Value>> = Vec::with_capacity(parties);
        let mut c: Vec<SecretVec<Value>> = Vec::with_capacity(parties);
        for party in 0..parties {
            let a_p: SecretVec<Value> = (0..count * tau).map(|_| self.sample(party, d)).collect();
            let b_p: SecretVec<Value> = (0..count).map(|_| self.sample(party, d)).collect();
            c.push(
                (0..count * tau)
                    .map(|e| d.mul(a_p[e], b_p[e / tau]))
                    .collect(),
            );
            a.push(a_p);
            b.push(b_p);
        }
        for receiver in 0..parties {
            let choices: SecretVec<u64> = a[receiver]
                .iter()
                .flat_map(|value| value[..words].iter().copied())
                .collect();
            for sender in (0..parties).filter(|&s| s != receiver) {
                let (send, receive) = self
                    .mesh
                    .run_correlated_ot_words(sender, receiver, &choices, self.rngs)
                    .map_err(|_| Check::Ot)?;
                self.transcript.label(b"multiply");
                for e in 0..count * tau {
                    let (mut sender_sum, mut receiver_sum) = (ZERO, ZERO);
                    let choice = a[receiver][e];
                    for bit in (0..width).rev() {
                        let index = 64 * words * e + bit;
                        let (zero, one) = &send[index];
                        let zero = pad_element(d, zero);
                        let one = pad_element(d, one);
                        let chosen = pad_element(d, &receive[index]);
                        let mut correlation = b[sender][e / tau];
                        (self.fault)(Fault::TripleCorrelation {
                            field,
                            sender,
                            receiver,
                            triple: e / tau,
                            slot: e % tau,
                            bit,
                            correlation: &mut correlation,
                        });
                        // Sender to receiver.
                        let correction = d.add(d.sub(zero, one), correlation);
                        self.transcript.element(d, &correction);
                        let select = 0u64.wrapping_sub((choice[bit / 64] >> (bit % 64)) & 1);
                        let received = d.add(chosen, correction.map(|limb| limb & select));
                        sender_sum = d.add(d.add(sender_sum, sender_sum), zero);
                        receiver_sum = d.add(d.add(receiver_sum, receiver_sum), received);
                    }
                    // receiver_sum − sender_sum = a_receiver[e] · b_sender.
                    c[receiver][e] = d.add(c[receiver][e], receiver_sum);
                    c[sender][e] = d.sub(c[sender][e], sender_sum);
                }
            }
        }
        for party in 0..parties {
            (self.fault)(Fault::TripleProduct {
                field,
                party,
                products: &mut c[party],
            });
        }

        // Combine with public coefficients drawn after all corrections.
        let mut challenges = self.coin(b"combine")?;
        let combos = 1 + sacrifices(field);
        let mut out: Vec<SecretVec<Value>> = (0..parties)
            .map(|_| SecretVec::with_capacity(count * per))
            .collect();
        for triple in 0..count {
            let coefficients: Vec<Value> =
                (0..combos * tau).map(|_| challenges.element(d)).collect();
            for party in 0..parties {
                let combine = |values: &[Value], combo: usize| {
                    (0..tau).fold(ZERO, |sum, slot| {
                        d.add(
                            sum,
                            d.mul(
                                coefficients[combo * tau + slot],
                                values[triple * tau + slot],
                            ),
                        )
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

    /// MASCOT Protocol 4, Sacrifice. `joint[p]` holds party `p`'s shares of
    /// the authenticated `a, b, c, â_1, ĉ_1, …` per triple. For each
    /// sacrificial pair a coin `s` (drawn after authentication), the opening
    /// `ρ = s·a − â` and the zero check of `s·c − ĉ − ρ·b`.
    ///
    /// If `c = ab + e` and `ĉ = âb + ê`, the checked value is `s·e − ê`,
    /// zero with probability `1/|F|` when `e ≠ 0`; with the independent
    /// second pair for Goldilocks `2^-128`. The check consumes the `â, ĉ`
    /// and reveals `ρ`, which the uniform `â` masks.
    fn sacrifice(
        &mut self,
        field: ThresholdField,
        joint: &[SecretVec<Share>],
        count: usize,
    ) -> Result<Vec<SecretVec<[Share; 3]>>, Abort> {
        let d = field.domain();
        let parties = self.parties;
        let per = triple_inputs(field);
        let mut queue = FieldQueue::new(parties);
        if count != 0 {
            let mut challenges = self.coin(b"sacrifice")?;
            self.transcript.label(b"sacrifice");
            for triple in 0..count {
                let at = triple * per;
                for pair in 0..sacrifices(field) {
                    let s = challenges.element(d);
                    let hat = at + 3 + 2 * pair;
                    let rho = self.open(
                        field,
                        Check::TripleSacrifice,
                        &mut queue,
                        (0..parties)
                            .map(|p| share_sub(d, share_scale(d, joint[p][at], s), joint[p][hat])),
                    );
                    Self::expect_zero(
                        &mut queue,
                        None,
                        (0..parties).map(|p| {
                            let left = mac_sub(
                                d,
                                mac_scale(d, joint[p][at + 2][1], s),
                                joint[p][hat + 1][1],
                            );
                            mac_sub(d, left, mac_scale(d, joint[p][at + 1][1], rho))
                        }),
                    );
                }
            }
        }
        self.check_field_queue(field, queue, Check::TripleSacrifice)?;
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
    // Boolean material
    // ------------------------------------------------------------------------

    /// Run qsag-core's `Π_triple_f2` n-of-n over the quorum for `count`
    /// triple words and convert every party's vault. Sets the Boolean key
    /// shares. Returns `[p][triple] = [a, b, c]`.
    ///
    /// The ceremony shares each bit as a degree-`(m − 1)` Shamir sharing of
    /// 0 or 1 in `GF(2^8)` with MACs under a two-lane key in the tower basis.
    /// Scaling party `p`'s shares by its Lagrange weight at zero gives
    /// additive shares; the bit is coefficient 0 of the scaled value share.
    /// One key lane is kept (soundness `2^-128` per check), and the MAC and
    /// key shares are mapped to the polynomial basis by the field
    /// isomorphism, which preserves `Σ m_p = bit · key`.
    fn boolean_stage(&mut self, count: usize) -> Result<Vec<Vec<[AuthWord; 3]>>, Abort> {
        let parties = self.parties;
        if count == 0 {
            for party in 0..parties {
                let key = Secret(self.rngs[party].next_u128());
                self.boolean_keys.push(*key);
            }
            return Ok((0..parties).map(|_| Vec::new()).collect());
        }
        let points: Vec<TowerGf256> = (1..=parties as u8).map(TowerGf256).collect();
        let weights = lagrange_weights_zero_gf256(&points).ok_or(Abort::Config)?;
        let session = cshake256_framed_32(b"QSAG.MIGRATE.PREP.BOOLEAN.V1", &[&self.session]);
        let (vaults, broadcasts) = run_dealerless_pi_triple_f2_with_transcript(
            session, parties, &points, count, self.mesh, self.rngs,
        )
        .map_err(|_| Check::BooleanCeremony)?;
        self.transcript.label(b"boolean ceremony");
        self.transcript.bytes(&broadcasts);
        let mut out = Vec::with_capacity(parties);
        for (vault, &weight) in vaults.iter().zip(&weights) {
            if vault.triples_slice().len() != count {
                return Err(Check::BooleanCeremony.into());
            }
            let mut key = Secret([vault.mac_alpha_lanes[0].mul_gf256(weight).0]);
            qsag_asm::tower128_to_poly128_batch_ct(&mut *key);
            self.boolean_keys.push(key[0]);
            let scale = PublicGf256Matrix::from_public_scalar(weight);
            let word = |planes: &[u64; 8], tags: &[qsag_core::field::tower::Tower128; 64]| {
                let mut macs: [u128; 64] =
                    core::array::from_fn(|lane| tags[lane].mul_gf256(weight).0);
                qsag_asm::tower128_to_poly128_x64_ct(&mut macs);
                AuthWord {
                    share: scale.scale_planes(planes)[0],
                    macs,
                }
            };
            out.push(
                vault
                    .triples_slice()
                    .iter()
                    .map(|t| {
                        [
                            word(&t.a, &t.a_mac[0]),
                            word(&t.b, &t.b_mac[0]),
                            word(&t.c, &t.c_mac[0]),
                        ]
                    })
                    .collect(),
            );
        }
        Ok(out)
    }

    /// Every owner samples its candidate bits and authenticates them under
    /// the Boolean key: for each holder and each of the holder's 128 key
    /// bits the owner sends `t0 ⊕ t1 ⊕ bits`, the holder obtains
    /// `t0 ⊕ keybit · bits`, and bit `l` of a MAC share is taken from key
    /// bit `l`. The holder's share is `T ⊕ bit · key_h`, the owner's is
    /// `T ⊕ bit · key_o` over all holders' `T`.
    ///
    /// **Input check** (the correlation check of KOS, Keller, Orsini, Scholl,
    /// CRYPTO 2015, in MASCOT's opened form). A coin fixes `χ_k ∈ GF(2^128)`;
    /// the owner opens `y = Σ χ_k b_k ⊕ Σ_l X^l · mask_l` over the candidates
    /// and [`MASK_BITS`] sacrificed mask candidates, and every party commits
    /// to and opens `σ_p = Σ χ_k m_k ⊕ Σ X^l m_mask,l ⊕ y · key_p`; the XOR
    /// must be zero. As in [`Self::authenticate`], an owner that encodes
    /// different bits under different key bits passes only if the holder's
    /// key lies in a set fixed in advance, so a failure leaks only that the
    /// key lies outside it; `y` is uniformly masked.
    fn boolean_candidates(&mut self, layout: &Layout) -> Result<Candidates, Abort> {
        let parties = self.parties;
        let total = layout.total;
        let words = total / 64;
        let mut bits: Vec<SecretVec<u64>> = Vec::with_capacity(parties);
        let mut macs: Vec<Vec<SecretVec<u128>>> = Vec::with_capacity(parties);
        for owner in 0..parties {
            let own: SecretVec<u64> = (0..words).map(|_| self.rngs[owner].next_u64()).collect();
            let own_key = &self.boolean_keys[owner];
            let mut shares: Vec<SecretVec<u128>> = (0..parties)
                .map(|_| SecretVec::from(vec![0u128; total]))
                .collect();
            for k in 0..total {
                shares[owner][k] =
                    *own_key & 0u128.wrapping_sub(((own[k / 64] >> (k % 64)) & 1) as u128);
            }
            for holder in (0..parties).filter(|&h| h != owner) {
                let Self {
                    pairs,
                    fault,
                    transcript,
                    pair_boolean_keys,
                    ..
                } = self;
                let key = &pair_boolean_keys[owner][holder];
                let pair = pairs[owner][holder].as_mut().unwrap();
                // Each independent base-OT column is expanded once. Keep columns until
                // the 64x128 transpose, instead of scattering every bit into a u128 tag.
                let mut zero_cols = SecretVec::from(vec![0u64; 128 * words]);
                let mut recv_cols = SecretVec::from(vec![0u64; 128 * words]);
                let zeros = || SecretVec::from(vec![0u64; words]);
                let (mut one, mut chosen, mut encoded) = (zeros(), zeros(), zeros());
                let mut correction_bytes = SecretVec::from(vec![0u8; words * 8]);
                transcript.label(b"boolean cope");
                for bit in 0..128 {
                    let zero = &mut zero_cols[bit * words..(bit + 1) * words];
                    let received = &mut recv_cols[bit * words..(bit + 1) * words];
                    pair.send[BOOLEAN_BASE + bit][0].words(zero);
                    pair.send[BOOLEAN_BASE + bit][1].words(&mut one);
                    pair.receive[BOOLEAN_BASE + bit].words(&mut chosen);
                    encoded.copy_from_slice(&own);
                    fault(Fault::BooleanInput {
                        owner,
                        holder,
                        bit,
                        words: &mut encoded,
                    });
                    let select = Secret(0u64.wrapping_sub(((*key >> bit) & 1) as u64));
                    for w in 0..words {
                        let correction = zero[w] ^ one[w] ^ encoded[w];
                        correction_bytes[8 * w..8 * w + 8]
                            .copy_from_slice(&correction.to_le_bytes());
                        received[w] = chosen[w] ^ (correction & *select);
                    }
                    transcript.bytes(&correction_bytes);
                }
                for w in 0..words {
                    let mut planes =
                        qsag_asm::wipe::SecretBuffer(core::array::from_fn::<_, 64, _>(|b| {
                            [
                                zero_cols[b * words + w],
                                zero_cols[(64 + b) * words + w],
                                recv_cols[b * words + w],
                                recv_cols[(64 + b) * words + w],
                            ]
                        }));
                    qsag_asm::transpose64x256(&mut planes);
                    for (lane, row) in planes.iter().enumerate() {
                        shares[owner][64 * w + lane] ^=
                            u128::from(row[0]) | (u128::from(row[1]) << 64);
                        shares[holder][64 * w + lane] =
                            u128::from(row[2]) | (u128::from(row[3]) << 64);
                    }
                }
            }
            bits.push(own);
            macs.push(shares);
        }

        let mut challenges = self.coin(b"boolean input")?;
        let mut sigmas: Vec<SecretVec<u64>> = (0..parties).map(|_| SecretVec::new()).collect();
        self.transcript.label(b"boolean input check");
        let mask = layout.input_mask;
        let checked = (0..total).filter(move |k| !(mask..mask + MASK_BITS).contains(k));
        for owner in 0..parties {
            let chi: Vec<u128> = checked.clone().map(|_| challenges.u128()).collect();
            let mut opened = mask_value(&bits[owner], mask / 64);
            for (chi, k) in chi.iter().zip(checked.clone()) {
                opened ^= chi & 0u128.wrapping_sub(((bits[owner][k / 64] >> (k % 64)) & 1) as u128);
            }
            self.transcript.bytes(&opened.to_le_bytes());
            for p in 0..parties {
                let row = &macs[owner][p];
                let selected: SecretVec<u128> = checked.clone().map(|k| row[k]).collect();
                let keyed = Secret(gf2_128_mul(*self.boolean_key_for(Some(owner), p), opened));
                let sigma = qsag_asm::gf2_128_dot(&chi, &selected)
                    ^ mask_mac(&row[mask..mask + MASK_BITS])
                    ^ *keyed;
                sigmas[p].extend_from_slice(&[sigma as u64, (sigma >> 64) as u64]);
            }
        }
        self.commit_then_open(b"boolean input sigma", &sigmas)?;
        for owner in 0..parties {
            let sum = (0..parties).fold([0u64; 2], |sum, p| {
                [
                    sum[0] ^ sigmas[p][2 * owner],
                    sum[1] ^ sigmas[p][2 * owner + 1],
                ]
            });
            if sum != [0; 2] {
                return Err(Check::BooleanInput.into());
            }
        }
        Ok(Candidates { bits, macs })
    }

    /// Batch MAC check of partially opened Boolean values, as
    /// [`Self::check_field_queue`]; soundness `2^-127`.
    fn check_boolean_queue(&mut self, queue: BooleanQueue, site: Check) -> Result<(), Abort> {
        if queue.values.is_empty() {
            return Ok(());
        }
        let parties = self.parties;
        let mut challenges = self.coin(b"boolean mac check")?;
        let chi: Vec<u128> = queue.values.iter().map(|_| challenges.u128()).collect();
        let mut sigmas: Vec<SecretVec<u64>> = Vec::with_capacity(parties);
        for p in 0..parties {
            let mut sigma = qsag_asm::gf2_128_dot(&chi, &queue.macs[p]);
            for (entry, value) in queue.values.iter().enumerate() {
                let keyed = Secret(gf2_128_mul(
                    *self.boolean_key_for(queue.owners[entry], p),
                    gf2_128_mul(chi[entry], *value),
                ));
                sigma ^= *keyed;
            }
            sigmas.push([sigma as u64, (sigma >> 64) as u64].into_iter().collect());
        }
        self.commit_then_open(b"boolean sigma", &sigmas)?;
        if sigmas
            .iter()
            .fold([0u64; 2], |sum, s| [sum[0] ^ s[0], sum[1] ^ s[1]])
            != [0; 2]
        {
            return Err(site.into());
        }
        Ok(())
    }

    /// The Boolean key each party used as a holder in
    /// [`Self::boolean_candidates`] must be its key share of the triple
    /// ceremony. With `X3 = Σ X^l · bit_l` over 128 sacrificed bits of the
    /// triple ceremony and `X4 = Σ_o Σ X^l · candidate_{o,l}` over every
    /// owner's sacrificed key-mask candidates, the parties open
    /// `Y = X3 ⊕ X4` and MAC-check it under their key shares.
    ///
    /// If corrupted holders used keys towards honest owner `o` that differ
    /// from their shares by `ε_o` in total, the MAC shares sum to
    /// `Y · key ⊕ Σ_o X4_o · ε_o`. `X3` is uniform and unknown to the
    /// adversary, so `Y` hides every honest `X4_o`, and for some `ε_o ≠ 0`
    /// the error is uniform in `GF(2^128)`: the check passes with
    /// probability `2^-128`. Both sides are sacrificed, so `Y` reveals
    /// nothing about the output.
    fn check_boolean_keys(
        &mut self,
        candidates: &Candidates,
        layout: &Layout,
        spare: &[&[AuthWord; 3]],
    ) -> Result<(), Abort> {
        let parties = self.parties;
        let at = layout.key_mask;
        let mut opened = 0u128;
        let mut sigmas: Vec<SecretVec<u64>> = Vec::with_capacity(parties);
        let mut macs: SecretVec<u128> = SecretVec::with_capacity(parties);
        self.transcript.label(b"boolean key check");
        for p in 0..parties {
            let [a, b, _] = spare[p];
            let share = (a.share as u128) | ((b.share as u128) << 64);
            let share = share ^ mask_value(&candidates.bits[p], at / 64);
            let mut mac =
                pack_macs(&a.macs, u64::MAX) ^ gf2_128_mul(pack_macs(&b.macs, u64::MAX), 1 << 64);
            for owner in 0..parties {
                mac ^= mask_mac(&candidates.macs[owner][p][at..at + MASK_BITS]);
            }
            self.transcript.bytes(&share.to_le_bytes());
            opened ^= share;
            macs.push(mac);
        }
        for p in 0..parties {
            let keyed = Secret(gf2_128_mul(self.boolean_keys[p], opened));
            let sigma = macs[p] ^ *keyed;
            sigmas.push([sigma as u64, (sigma >> 64) as u64].into_iter().collect());
        }
        self.commit_then_open(b"boolean key sigma", &sigmas)?;
        if sigmas
            .iter()
            .fold([0u64; 2], |sum, s| [sum[0] ^ s[0], sum[1] ^ s[1]])
            != [0; 2]
        {
            return Err(Check::BooleanKeyConsistency.into());
        }
        Ok(())
    }

    // ------------------------------------------------------------------------
    // One field
    // ------------------------------------------------------------------------

    /// All material of one field: triples, randoms and doubly authenticated
    /// bits, appended to `stores`.
    fn field_stage(
        &mut self,
        field: ThresholdField,
        demand: &Demand,
        candidates: Option<&Candidates>,
        layout: &Layout,
        stores: &mut [PartyPreprocessing],
    ) -> Result<(), Abort> {
        let d = field.domain();
        let index = field.index();
        let parties = self.parties;
        let retained = layout.retained[index];
        let output_triples = demand.field_triples[index];
        let triples = output_triples + (parties - 1) * retained;
        let randoms = demand.field_randoms[index];
        if triples + randoms + retained == 0 {
            return Ok(());
        }
        let keys = key_count(d);
        let per = triple_inputs(field);
        let candidate_count = if retained == 0 {
            0
        } else {
            retained + CROSS_REPS
        };

        // Batch: triple values, randoms, key-consistency values, candidate bits.
        let random_at = triples * per;
        let key_at = random_at + randoms;
        let bit_at = key_at + keys;
        let mut inputs = self.multiply(field, triples)?;
        for owner in 0..parties {
            for _ in random_at..bit_at {
                let value = self.sample(owner, d);
                inputs[owner].push(value);
            }
            if let Some(candidates) = candidates.filter(|_| retained != 0) {
                let bits = &candidates.bits[owner];
                for k in layout.at[index]..layout.at[index] + candidate_count {
                    inputs[owner].push([(bits[k / 64] >> (k % 64)) & 1, 0, 0, 0, 0, 0]);
                }
                (self.fault)(Fault::DaBitFieldInput {
                    field,
                    owner,
                    values: &mut inputs[owner][bit_at..],
                });
            }
        }
        let shares = self.authenticate(field, &inputs, bit_at..bit_at + candidate_count)?;
        let joint: Vec<SecretVec<Share>> = (0..parties)
            .map(|p| {
                (0..bit_at)
                    .map(|k| {
                        (1..parties)
                            .fold(shares[0][p][k], |sum, o| share_add(d, sum, shares[o][p][k]))
                    })
                    .collect()
            })
            .collect();

        // Key consistency. A holder can commit to different keys in its base
        // OTs with different owners; each owner's batch is then valid under a
        // different global key. Every owner contributed uniformly random
        // items (two for Goldilocks); the sum of each item over the owners is
        // opened and MAC-checked on its own, with no random combination. If
        // the keys towards two honest owners differ by `ε` in some key, the
        // MAC shares of an opened sum are off by `ε` times one honest
        // owner's item, which the sum does not determine: each item passes
        // with probability `1/|F|`. The two Goldilocks items are separate
        // equations, so a difference in a single 64-bit key is also caught
        // except with probability `2^-128`. A failure reveals nothing beyond
        // the sacrificed items.
        //
        // The holder commits to its check share after the value shares are
        // public, and a party's value share of the sum is its own item. Sent
        // as it is, the item of each honest owner would be known in time for
        // the holder to subtract `ε` times it. So every pair adds a common
        // mask from its shared pad stream, one party with each sign: the sum
        // is unchanged, and what two honest owners send determines only the
        // sum of their items.
        let mut blinds: Vec<SecretVec<Value>> = (0..parties)
            .map(|_| SecretVec::from(vec![ZERO; keys]))
            .collect();
        let mut common = SecretVec::from(vec![ZERO; keys]);
        for low in 0..parties {
            for high in low + 1..parties {
                let pair = self.pairs[low][high].as_mut().unwrap();
                pair.send[SHARED_BASE][0].elements(d, &mut common);
                for (blind, mask) in blinds[low].iter_mut().zip(common.iter()) {
                    *blind = d.add(*blind, *mask);
                }
                pair.receive[SHARED_BASE].elements(d, &mut common);
                for (blind, mask) in blinds[high].iter_mut().zip(common.iter()) {
                    *blind = d.sub(*blind, *mask);
                }
            }
        }
        let mut sigmas: Vec<SecretVec<u64>> = (0..parties).map(|_| SecretVec::new()).collect();
        self.transcript.label(b"key consistency");
        for k in key_at..bit_at {
            let sent: Vec<Value> = (0..parties)
                .map(|p| d.add(joint[p][k][0], blinds[p][k - key_at]))
                .collect();
            let mut opened = ZERO;
            for share in &sent {
                self.transcript.element(d, share);
                opened = d.add(opened, *share);
            }
            for p in 0..parties {
                let keyed = Secret(mac_scale(d, self.field_keys[p][index], opened));
                let mut sigma = mac_sub(d, joint[p][k][1], *keyed);
                (self.fault)(Fault::KeyConsistencySigma {
                    field,
                    party: p,
                    sent: &sent,
                    sigma: &mut sigma,
                });
                sigmas[p].extend_from_slice(&sigma);
            }
        }
        self.commit_then_open(b"key consistency sigma", &sigmas)?;
        for item in 0..keys {
            let sum = (0..parties).fold(ZERO, |sum, p| {
                let share: Value = sigmas[p][6 * item..6 * item + 6].try_into().unwrap();
                mac_add(d, sum, share)
            });
            if sum != ZERO {
                return Err(Check::KeyConsistency.into());
            }
        }

        let checked = self.sacrifice(field, &joint, triples)?;
        for p in 0..parties {
            stores[p].add_field_triples(
                field,
                checked[p][..output_triples]
                    .iter()
                    .map(|t| FieldTriple(t.map(FieldShare))),
            );
            stores[p].add_field_randoms(
                field,
                joint[p][random_at..key_at].iter().map(|s| FieldShare(*s)),
            );
        }
        let Some(candidates) = candidates.filter(|_| retained != 0) else {
            return Ok(());
        };
        let base = layout.at[index];

        // Cross-domain equality. Every candidate's field form is a bit
        // (proved in `authenticate`). A coin fixes CROSS_REPS subsets of the
        // retained candidates. For subset `S` and its own mask candidate the
        // owner opens the Boolean parity `π = ⊕_S b ⊕ b_mask` and
        // authenticates (as bits) the binary digits `w` of
        // `(Σ_S β + β_mask − π) / 2`; the parties check
        // `Σ_S β + β_mask − π − 2·Σ 2^l w_l = 0` on the field shares. All
        // terms are bits and the weights are small, so the relation holds
        // over the integers, and the parity of the field forms equals the
        // opened parity of the Boolean forms. With `δ_k = β_k ⊕ b_k` fixed
        // before the coin, a repetition passes iff `⊕_S δ ⊕ δ_mask = 0`:
        // probability exactly 1/2 unless every retained `δ_k` is zero,
        // `2^-128` over the repetitions. Only `π` is opened, and the unused
        // mask bit makes it uniform; the digits stay shared.
        let subset_words = retained / 64;
        let mut challenges = self.coin(b"cross domain")?;
        let mut subsets = vec![0u64; CROSS_REPS * subset_words];
        challenges.words(&mut subsets);
        let digits = (usize::BITS - retained.div_ceil(2).leading_zeros()) as usize;
        let member =
            |rep: usize, k: usize| (subsets[rep * subset_words + k / 64] >> (k % 64)) & 1 != 0;

        let mut parities = vec![vec![0u64; CROSS_REPS]; parties];
        let mut digit_inputs: Vec<SecretVec<Value>> = Vec::with_capacity(parties);
        self.transcript.label(b"parities");
        for owner in 0..parties {
            let bits = &candidates.bits[owner];
            let bit = |k: usize| (bits[(base + k) / 64] >> ((base + k) % 64)) & 1;
            let mut values = SecretVec::with_capacity(CROSS_REPS * digits);
            for rep in 0..CROSS_REPS {
                let mut parity = bit(retained + rep);
                let mut weight = inputs[owner][bit_at + retained + rep][0];
                for k in (0..retained).filter(|&k| member(rep, k)) {
                    parity ^= bit(k);
                    weight = weight.wrapping_add(inputs[owner][bit_at + k][0]);
                }
                (self.fault)(Fault::Parity {
                    field,
                    owner,
                    repetition: rep,
                    parity: &mut parity,
                });
                parity &= 1;
                // The owner broadcasts its parity.
                self.transcript.bytes(&[parity as u8]);
                parities[owner][rep] = parity;
                let half = weight.wrapping_sub(parity) >> 1;
                for digit in 0..digits {
                    values.push([(half >> digit) & 1, 0, 0, 0, 0, 0]);
                }
            }
            digit_inputs.push(values);
        }
        let digit_shares = self.authenticate(field, &digit_inputs, 0..CROSS_REPS * digits)?;

        let mut boolean_queue = BooleanQueue::new(parties);
        let mut queue = FieldQueue::new(parties);
        for owner in 0..parties {
            for rep in 0..CROSS_REPS {
                let parity = parities[owner][rep];
                let members: Vec<usize> = (0..retained).filter(|&k| member(rep, k)).collect();
                boolean_queue.values.push(parity as u128);
                boolean_queue.owners.push(Some(owner));
                for p in 0..parties {
                    let macs = &candidates.macs[owner][p];
                    let mac = members
                        .iter()
                        .fold(macs[base + retained + rep], |sum, &k| sum ^ macs[base + k]);
                    boolean_queue.macs[p].push(mac);

                    let row = &shares[owner][p];
                    let mut sum = members
                        .iter()
                        .fold(row[bit_at + retained + rep][1], |sum, &k| {
                            mac_add(d, sum, row[bit_at + k][1])
                        });
                    let keyed = Secret(mac_scale(
                        d,
                        *self.field_key_for(field, Some(owner), p),
                        [parity, 0, 0, 0, 0, 0],
                    ));
                    sum = mac_sub(d, sum, *keyed);
                    for digit in 0..digits {
                        let weight = [2u64 << digit, 0, 0, 0, 0, 0];
                        let mac = digit_shares[owner][p][rep * digits + digit][1];
                        sum = mac_sub(d, sum, mac_scale(d, mac, weight));
                    }
                    queue.macs[p].push(sum);
                }
                queue.values.push(ZERO);
                queue.owners.push(Some(owner));
            }
        }
        self.check_boolean_queue(boolean_queue, Check::ParityOpening)?;
        self.check_field_queue(field, queue, Check::CrossDomain)?;

        // XOR over the owners: free on the Boolean side, `x + y − 2xy` with
        // one checked triple per owner after the first on the field side.
        let mut bits: Vec<SecretVec<Share>> = (0..parties)
            .map(|p| {
                shares[0][p][bit_at..bit_at + retained]
                    .iter()
                    .copied()
                    .collect()
            })
            .collect();
        let mut queue = FieldQueue::new(parties);
        self.transcript.label(b"xor chain");
        for owner in 1..parties {
            for k in 0..retained {
                let triple = output_triples + (owner - 1) * retained + k;
                let delta = self.open(
                    field,
                    Check::XorChain,
                    &mut queue,
                    (0..parties).map(|p| share_sub(d, bits[p][k], checked[p][triple][0])),
                );
                let epsilon = self.open(
                    field,
                    Check::XorChain,
                    &mut queue,
                    (0..parties)
                        .map(|p| share_sub(d, shares[owner][p][bit_at + k], checked[p][triple][1])),
                );
                let constant = d.mul(delta, epsilon);
                for p in 0..parties {
                    let [a, b, c] = checked[p][triple];
                    let public = Secret([
                        if p == 0 { constant } else { ZERO },
                        mac_scale(d, self.field_keys[p][index], constant),
                    ]);
                    let product = share_add(
                        d,
                        share_add(d, c, *public),
                        share_add(d, share_scale(d, b, delta), share_scale(d, a, epsilon)),
                    );
                    let sum = share_add(d, bits[p][k], shares[owner][p][bit_at + k]);
                    bits[p][k] = share_sub(d, sum, share_add(d, product, product));
                }
            }
        }
        self.check_field_queue(field, queue, Check::XorChain)?;

        for p in 0..parties {
            stores[p].add_dabits(
                field,
                (0..retained / 64).map(|word| DaBitWord {
                    bits: AuthWord {
                        share: candidates.bits[p][base / 64 + word],
                        macs: core::array::from_fn(|lane| {
                            (0..parties).fold(0, |sum, owner| {
                                sum ^ candidates.macs[owner][p][base + 64 * word + lane]
                            })
                        }),
                    },
                    field: core::array::from_fn(|lane| FieldShare(bits[p][64 * word + lane])),
                }),
            );
        }
        Ok(())
    }

    fn run(mut self, demand: &Demand) -> Result<Vec<(MacKeyShare, PartyPreprocessing)>, Abort> {
        let parties = self.parties;
        let layout = Layout::new(demand)?;
        let dabits = demand.dabits.iter().any(|&words| words != 0);
        let word_triples = demand.auth_words.div_ceil(2);
        let boolean_count = demand
            .boolean_triples
            .checked_add(word_triples)
            .and_then(|n| n.checked_add(usize::from(dabits)))
            .ok_or(Abort::Config)?;
        let mut boolean = self.boolean_stage(boolean_count)?;
        self.sample_field_keys();
        self.establish_pairs()?;

        let candidates = if dabits {
            Some(self.boolean_candidates(&layout)?)
        } else {
            None
        };
        let mut stores: Vec<PartyPreprocessing> =
            (0..parties).map(|_| PartyPreprocessing::new()).collect();
        for field in ThresholdField::ALL {
            self.field_stage(field, demand, candidates.as_ref(), &layout, &mut stores)?;
        }
        if let Some(candidates) = &candidates {
            let spare: Vec<&[AuthWord; 3]> =
                boolean.iter().map(|row| row.last().unwrap()).collect();
            self.check_boolean_keys(candidates, &layout, &spare)?;
        }

        // Establish per-peer 128-column active KOS15 + OLE correlation seeds for
        // multiplicatively blinding online `SpdzEngine::check()` MAC openings.
        let slot_of =
            |owner: usize, peer: usize| -> usize { if peer < owner { peer } else { peer - 1 } };
        let mut blind_ot: Vec<Vec<BlindOtPeer>> = (0..parties)
            .map(|_| {
                (0..parties.saturating_sub(1))
                    .map(|_| BlindOtPeer {
                        sender_delta: 0,
                        sender_seeds: [[0u8; 32]; 128],
                        receiver_seeds: [[[0u8; 32]; 2]; 128],
                        counter: 0,
                    })
                    .collect()
            })
            .collect();
        for sender in 0..parties {
            for receiver in 0..parties {
                if sender == receiver {
                    continue;
                }
                let delta = Secret(self.rngs[sender].next_u128());
                let choices = Secret([*delta as u64, (*delta >> 64) as u64]);
                let (send, receive) = self
                    .mesh
                    .run_correlated_ot_words(receiver, sender, &*choices, self.rngs)
                    .map_err(|_| Check::Ot)?;
                let hash_pad = |pad: &[u8; 48], col: usize| -> [u8; 32] {
                    cshake256_framed_32(
                        b"QSAG.MIGRATE.PREP.BLIND_OT.V1",
                        &[
                            &self.session,
                            &[sender as u8, receiver as u8],
                            &(col as u64).to_le_bytes(),
                            pad,
                        ],
                    )
                };
                let s_slot = slot_of(sender, receiver);
                let r_slot = slot_of(receiver, sender);
                blind_ot[sender][s_slot].sender_delta = *delta;
                for col in 0..128 {
                    let (ref zero, ref one) = send[col];
                    blind_ot[receiver][r_slot].receiver_seeds[col] =
                        [hash_pad(zero, col), hash_pad(one, col)];
                    blind_ot[sender][s_slot].sender_seeds[col] = hash_pad(&receive[col], col);
                }
            }
        }

        // Boolean triples first; then both uniform inputs of further triples
        // as authenticated words, their products discarded.
        let mut out = Vec::with_capacity(parties);
        for ((p, mut store), peer_blind_ot) in stores.into_iter().enumerate().zip(blind_ot) {
            let mut words = Vec::with_capacity(2 * word_triples);
            let mut row = core::mem::take(&mut boolean[p]).into_iter();
            store.add_boolean_triples(
                row.by_ref()
                    .take(demand.boolean_triples)
                    .map(|[a, b, c]| BooleanTriple { a, b, c }),
            );
            for [a, b, _] in row.by_ref().take(word_triples) {
                words.push(a);
                words.push(b);
            }
            words.truncate(demand.auth_words);
            store.add_auth_words(words);
            out.push((
                MacKeyShare {
                    boolean: self.boolean_keys[p],
                    field: self.field_keys[p],
                    blind_ot: peer_blind_ot,
                },
                store,
            ));
        }
        Ok(out)
    }
}

fn ceremony(
    session: [u8; 32],
    config: &ThresholdConfig,
    demand: &Demand,
    mesh: &mut OtMesh,
    rngs: &mut [PartyPrivateRng],
    fault: &mut dyn FnMut(Fault<'_>),
) -> Result<Vec<(MacKeyShare, PartyPreprocessing)>, Abort> {
    if rngs.len() != config.quorum().len() {
        return Err(Abort::Config);
    }
    let mut encoded = Vec::with_capacity(8 * 17);
    for count in [demand.boolean_triples, demand.auth_words]
        .into_iter()
        .chain(demand.field_triples)
        .chain(demand.field_randoms)
        .chain(demand.dabits)
    {
        encoded.extend_from_slice(&(count as u64).to_le_bytes());
    }
    let session = cshake256_framed_32(
        b"QSAG.MIGRATE.PREP.DEALERLESS.V1",
        &[&session, &config.binding(), &encoded],
    );
    Ceremony::new(session, mesh, rngs, fault)?.run(demand)
}

/// Run the preprocessing ceremony of one quorum in this process and return
/// every member's key shares and material, in quorum order.
///
/// `mesh` is the OT mesh over the quorum members and `rngs` their private
/// generators, both indexed by quorum position. All steps of all members run
/// here on separated per-party state. On any failed check the result is
/// [`Error::MultiplicationCheck`], nothing is returned, and all key shares
/// and material are erased as their owners go out of scope.
pub fn run_dealerless_preprocessing(
    session: [u8; 32],
    config: &ThresholdConfig,
    demand: &Demand,
    mesh: &mut OtMesh,
    rngs: &mut [PartyPrivateRng],
) -> Result<Vec<(MacKeyShare, PartyPreprocessing)>, Error> {
    run_dealerless_preprocessing_with_fault(session, config, demand, mesh, rngs, &mut |_| {})
}

/// [`run_dealerless_preprocessing`] with a hook that may alter what a party
/// uses or sends at each [`Fault`] point, for adversarial tests.
pub fn run_dealerless_preprocessing_with_fault(
    session: [u8; 32],
    config: &ThresholdConfig,
    demand: &Demand,
    mesh: &mut OtMesh,
    rngs: &mut [PartyPrivateRng],
    fault: &mut dyn FnMut(Fault<'_>),
) -> Result<Vec<(MacKeyShare, PartyPreprocessing)>, Error> {
    Ok(ceremony(session, config, demand, mesh, rngs, fault)?)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        outer_mpc::{Core, Gadgets},
        threshold_mpc::{
            mac_canonical,
            tests::{engine, run_stored},
        },
    };
    use std::{println, time::Instant};

    fn quorum() -> ThresholdConfig {
        ThresholdConfig::new(3, 5, vec![0, 2, 4]).unwrap()
    }

    #[test]
    fn oversized_dabit_layout_fails_before_allocation() {
        for words in [MAX_DABIT_WORDS + 1, usize::MAX / 64 + 1, usize::MAX] {
            let mut demand = Demand::default();
            demand.dabits[0] = words;
            assert!(matches!(Layout::new(&demand), Err(Abort::Config)));
        }
        let demand = Demand {
            dabits: [MAX_DABIT_WORDS; 5],
            ..Demand::default()
        };
        #[cfg(target_pointer_width = "32")]
        assert!(matches!(Layout::new(&demand), Err(Abort::Config)));
        #[cfg(target_pointer_width = "64")]
        assert!(Layout::new(&demand).is_ok());
    }

    /// Real OT mesh over three quorum members and their private generators.
    fn setup(seed: u8) -> (OtMesh, Vec<PartyPrivateRng>) {
        let mut rngs: Vec<_> = (0..3u8)
            .map(|p| {
                PartyPrivateRng::from_seed(
                    [seed, p, 7, 1].repeat(8).try_into().unwrap(),
                    b"TEST.PREP",
                )
            })
            .collect();
        let mesh = OtMesh::establish([seed; 32], &mut rngs).unwrap();
        (mesh, rngs)
    }

    fn honest(_: Fault<'_>) {}

    /// Reconstructs everything from all parties' shares and asserts every
    /// relation the online engine relies on; the stores are left as found.
    fn verify_material(demand: &Demand, parties: &mut [(MacKeyShare, PartyPreprocessing)]) {
        let boolean_key = parties.iter().fold(0, |key, (k, _)| key ^ k.boolean);
        assert_ne!(boolean_key, 0);
        let field_key = |field: ThresholdField| {
            parties.iter().fold(ZERO, |key, (k, _)| {
                assert!(mac_canonical(field.domain(), k.field[field.index()]));
                mac_add(field.domain(), key, k.field[field.index()])
            })
        };
        let field_keys = ThresholdField::ALL.map(field_key);
        let n_parties = parties.len();
        for sender in 0..n_parties {
            assert_eq!(parties[sender].0.blind_ot.len(), n_parties - 1);
            for receiver in 0..n_parties {
                if sender == receiver {
                    continue;
                }
                let s_slot = if receiver < sender {
                    receiver
                } else {
                    receiver - 1
                };
                let r_slot = if sender < receiver {
                    sender
                } else {
                    sender - 1
                };
                let delta = parties[sender].0.blind_ot[s_slot].sender_delta;
                for col in 0..128 {
                    let bit = ((delta >> col) & 1) as usize;
                    assert_eq!(
                        parties[sender].0.blind_ot[s_slot].sender_seeds[col],
                        parties[receiver].0.blind_ot[r_slot].receiver_seeds[col][bit]
                    );
                }
            }
        }
        for (_, store) in parties.iter() {
            assert_eq!(store.remaining(), *demand);
        }
        let word = |shares: &[&AuthWord]| {
            let value = shares.iter().fold(0, |word, share| word ^ share.share);
            for lane in 0..64 {
                let mac = shares.iter().fold(0, |mac, share| mac ^ share.macs[lane]);
                let expected = if (value >> lane) & 1 == 1 {
                    boolean_key
                } else {
                    0
                };
                assert_eq!(mac, expected, "Boolean MAC of lane {lane}");
            }
            value
        };
        let element = |field: ThresholdField, shares: &[&FieldShare]| {
            let d = field.domain();
            let mut value = ZERO;
            let mut mac = ZERO;
            for share in shares {
                assert!(d.canonical(share.0[0]) && mac_canonical(d, share.0[1]));
                value = d.add(value, share.0[0]);
                mac = mac_add(d, mac, share.0[1]);
            }
            assert_eq!(
                mac,
                mac_scale(d, field_keys[field.index()], value),
                "{field:?} MAC"
            );
            value
        };
        fn column<V>(rows: &[Vec<V>], item: usize) -> Vec<&V> {
            rows.iter().map(|row| &row[item]).collect()
        }

        let rows: Vec<_> = parties
            .iter_mut()
            .map(|(_, s)| s.take_boolean_triples(demand.boolean_triples).unwrap())
            .collect();
        let mut seen = Vec::new();
        for item in 0..demand.boolean_triples {
            let shares = column(&rows, item);
            let part = |f: fn(&BooleanTriple) -> &AuthWord| {
                word(&shares.iter().map(|t| f(t)).collect::<Vec<_>>())
            };
            let (a, b, c) = (part(|t| &t.a), part(|t| &t.b), part(|t| &t.c));
            assert_eq!(c, a & b);
            seen.push(a);
            seen.push(b);
        }
        for ((_, store), row) in parties.iter_mut().zip(rows) {
            store.add_boolean_triples(row);
        }
        let rows: Vec<_> = parties
            .iter_mut()
            .map(|(_, s)| s.take_auth_words(demand.auth_words).unwrap())
            .collect();
        for item in 0..demand.auth_words {
            seen.push(word(&column(&rows, item)));
        }
        for ((_, store), row) in parties.iter_mut().zip(rows) {
            store.add_auth_words(row);
        }
        for field in ThresholdField::ALL {
            let d = field.domain();
            let i = field.index();
            let rows: Vec<_> = parties
                .iter_mut()
                .map(|(_, s)| {
                    s.take_field_triples(field, demand.field_triples[i])
                        .unwrap()
                })
                .collect();
            for item in 0..demand.field_triples[i] {
                let shares = column(&rows, item);
                let [a, b, c] = [0, 1, 2].map(|part| {
                    element(
                        field,
                        &shares.iter().map(|t| &t.0[part]).collect::<Vec<_>>(),
                    )
                });
                assert_eq!(c, d.mul(a, b));
                assert_ne!(a, ZERO);
                assert_ne!(b, ZERO);
            }
            for ((_, store), row) in parties.iter_mut().zip(rows) {
                store.add_field_triples(field, row);
            }
            let rows: Vec<_> = parties
                .iter_mut()
                .map(|(_, s)| {
                    s.take_field_randoms(field, demand.field_randoms[i])
                        .unwrap()
                })
                .collect();
            for item in 0..demand.field_randoms[i] {
                assert_ne!(element(field, &column(&rows, item)), ZERO);
            }
            for ((_, store), row) in parties.iter_mut().zip(rows) {
                store.add_field_randoms(field, row);
            }
            let rows: Vec<_> = parties
                .iter_mut()
                .map(|(_, s)| s.take_dabits(field, demand.dabits[i]).unwrap())
                .collect();
            for item in 0..demand.dabits[i] {
                let shares = column(&rows, item);
                let bits = word(&shares.iter().map(|w| &w.bits).collect::<Vec<_>>());
                for lane in 0..64 {
                    let value = element(
                        field,
                        &shares.iter().map(|w| &w.field[lane]).collect::<Vec<_>>(),
                    );
                    assert_eq!(
                        value,
                        [(bits >> lane) & 1, 0, 0, 0, 0, 0],
                        "{field:?} daBit lane {lane}"
                    );
                }
                seen.push(bits);
            }
            for ((_, store), row) in parties.iter_mut().zip(rows) {
                store.add_dabits(field, row);
            }
        }
        // Random words: not constant and not repeated.
        for (i, word) in seen.iter().enumerate() {
            assert!(*word != 0 && *word != u64::MAX);
            assert!(!seen[..i].contains(word));
        }
        for (_, store) in parties.iter() {
            assert_eq!(store.remaining(), *demand);
        }
    }

    /// Runs the ceremony honestly (must succeed and satisfy the oracle), then
    /// with `fault`, and returns the deviating outcome after checking that a
    /// successful deviating run still satisfies the oracle.
    fn deviate(
        seed: u8,
        demand: &Demand,
        mesh: &mut OtMesh,
        rngs: &mut [PartyPrivateRng],
        mut fault: impl FnMut(Fault<'_>) -> bool,
    ) -> Result<(), Abort> {
        let config = quorum();
        let mut out = ceremony([seed; 32], &config, demand, mesh, rngs, &mut honest).unwrap();
        verify_material(demand, &mut out);
        let mut fired = false;
        let outcome = ceremony(
            [seed ^ 0x80; 32],
            &config,
            demand,
            mesh,
            rngs,
            &mut |point| fired |= fault(point),
        );
        assert!(fired, "the deviation was never injected");
        outcome.map(|mut out| verify_material(demand, &mut out))
    }

    fn bump(d: Domain, value: &mut Value) {
        *value = mac_add(
            d,
            *value,
            if d == Domain::Gold {
                [1, 1, 0, 0, 0, 0]
            } else {
                ONE
            },
        );
    }

    #[test]
    fn tower_to_polynomial_map_is_a_field_isomorphism() {
        use qsag_core::field::tower::Tower128;
        let mut rng = PartyPrivateRng::from_seed([3; 32], b"TEST.ISO");
        for _ in 0..64 {
            let (x, y) = (rng.next_tower128(), rng.next_tower128());
            let mut mapped = [x.0, y.0, x.mul(y).0, x.add(y).0, 1];
            qsag_asm::tower128_to_poly128_batch_ct(&mut mapped);
            assert_eq!(mapped[2], gf2_128_mul(mapped[0], mapped[1]));
            assert_eq!(mapped[3], mapped[0] ^ mapped[1]);
            assert_eq!(mapped[4], 1);
            let mut lanes = [Tower128(0).0; 64];
            lanes[5] = x.0;
            qsag_asm::tower128_to_poly128_x64_ct(&mut lanes);
            assert_eq!(lanes[5], mapped[0]);
        }
    }

    #[test]
    fn pad_elements_are_canonical() {
        for d in Domain::ALL_FIELDS {
            assert!(d.canonical(pad_element(d, &[0xff; 48])));
            assert!(d.canonical(pad_element(d, &[0; 48])));
            let mut pad = [0xff; 48];
            pad[40..].copy_from_slice(&5u64.to_le_bytes());
            let value = pad_element(d, &pad);
            assert!(d.canonical(value));
            if d == Domain::Gold {
                assert_eq!(value, [5, 0, 0, 0, 0, 0]);
            }
        }
    }

    /// Stage 1 on its own: authenticated values reconstruct with valid MACs,
    /// bits are accepted as bits, and a non-bit is rejected.
    #[test]
    fn owners_authenticate_their_values_in_every_field() {
        let (mut mesh, mut rngs) = setup(1);
        let hook: &mut dyn FnMut(Fault<'_>) = &mut honest;
        let mut ceremony = Ceremony::new([1; 32], &mut mesh, &mut rngs, hook).unwrap();
        ceremony.boolean_stage(0).unwrap();
        ceremony.sample_field_keys();
        ceremony.establish_pairs().unwrap();
        for field in ThresholdField::ALL {
            let d = field.domain();
            let key = (0..3).fold(ZERO, |key, p| {
                mac_add(d, key, ceremony.field_keys[p][field.index()])
            });
            let top = d.sub(ZERO, ONE);
            let inputs: Vec<SecretVec<Value>> = (0..3)
                .map(|owner| {
                    let mut values: SecretVec<Value> =
                        [ZERO, ONE, top, [owner as u64 + 2, 0, 0, 0, 0, 0], ONE, ZERO]
                            .into_iter()
                            .collect();
                    values.push(ceremony.sample(owner, d));
                    values
                })
                .collect();
            for bits in [0..0, 4..6, 0..2] {
                let shares = ceremony.authenticate(field, &inputs, bits).unwrap();
                for owner in 0..3 {
                    for k in 0..inputs[owner].len() {
                        let mut total = [ZERO; 2];
                        for p in 0..3 {
                            let share = shares[owner][p][k];
                            assert!(d.canonical(share[0]) && mac_canonical(d, share[1]));
                            assert_eq!(share[0] != ZERO, p == owner && inputs[owner][k] != ZERO);
                            total = share_add(d, total, share);
                        }
                        assert_eq!(total[0], inputs[owner][k]);
                        assert_eq!(total[1], mac_scale(d, key, total[0]), "{field:?}");
                    }
                }
            }
            assert_eq!(
                ceremony.authenticate(field, &inputs, 2..5).err(),
                Some(Abort::Check(Check::Bitness)),
                "{field:?}: p - 1 and 2.. are not bits"
            );
        }
    }

    #[test]
    fn inconsistent_owner_and_wrong_holder_share_are_caught() {
        let (mut mesh, mut rngs) = setup(2);
        let demand = Demand {
            field_randoms: [2, 1, 1, 1, 1],
            ..Demand::default()
        };
        for target in ThresholdField::ALL {
            let d = target.domain();
            // Owner 1 encodes another value under the low 16 bits of holder 2's key.
            let outcome = deviate(20, &demand, &mut mesh, &mut rngs, |point| match point {
                Fault::CopeInput {
                    field,
                    owner: 1,
                    holder: 2,
                    key: 0,
                    bit,
                    values,
                } if field == target && bit < 16 => {
                    values[0] = d.add(values[0], ONE);
                    true
                }
                _ => false,
            });
            assert_eq!(
                outcome,
                Err(Abort::Check(Check::InputConsistency)),
                "{target:?}"
            );
            // Holder 0 holds a MAC share of one of owner 2's values that its key does not give.
            let outcome = deviate(21, &demand, &mut mesh, &mut rngs, |point| match point {
                Fault::CopeHolderShare {
                    field,
                    owner: 2,
                    holder: 0,
                    macs,
                } if field == target => {
                    bump(d, &mut macs[0]);
                    true
                }
                _ => false,
            });
            assert_eq!(
                outcome,
                Err(Abort::Check(Check::InputConsistency)),
                "{target:?}"
            );
            // Holder 2 commits to another key towards owner 0 than towards owner 1.
            let outcome = deviate(22, &demand, &mut mesh, &mut rngs, |point| match point {
                Fault::FieldKey {
                    field,
                    owner: 0,
                    holder: 2,
                    key,
                } if field == target => {
                    bump(d, key);
                    true
                }
                _ => false,
            });
            assert_eq!(
                outcome,
                Err(Abort::Check(Check::KeyConsistency)),
                "{target:?}"
            );
        }
    }

    /// A holder that used another key towards one owner knows the difference
    /// `ε`, and it commits to its check share only after the value shares are
    /// public. If an owner's share were its item, the holder could subtract
    /// `ε` times it and pass. No triple is demanded here, so no later check
    /// of the ceremony would see the inconsistency either.
    #[test]
    fn a_holder_cannot_cancel_its_key_inconsistency_from_what_the_owner_sent() {
        let (mut mesh, mut rngs) = setup(12);
        let demand = Demand {
            field_randoms: [2, 1, 1, 1, 1],
            ..Demand::default()
        };
        for target in ThresholdField::ALL {
            let d = target.domain();
            let mut epsilon = ZERO;
            bump(d, &mut epsilon);
            let mut corrected = 0;
            let outcome = deviate(60, &demand, &mut mesh, &mut rngs, |point| match point {
                Fault::FieldKey {
                    field,
                    owner: 0,
                    holder: 2,
                    key,
                } if field == target => {
                    bump(d, key);
                    true
                }
                Fault::KeyConsistencySigma {
                    field,
                    party: 2,
                    sent,
                    sigma,
                } if field == target => {
                    *sigma = mac_sub(d, *sigma, mac_scale(d, epsilon, sent[0]));
                    corrected += 1;
                    true
                }
                _ => false,
            });
            assert_eq!(corrected, key_count(d), "{target:?}");
            assert_eq!(
                outcome,
                Err(Abort::Check(Check::KeyConsistency)),
                "{target:?}"
            );
        }
    }

    fn commit_payloads() -> Vec<SecretVec<u64>> {
        (0..3).map(|p| [p, 7, 9].into_iter().collect()).collect()
    }

    /// One commit-then-open of a fixed label and payload by a fresh ceremony
    /// whose counter stands at `start`: party 1's commitment, its nonce, and
    /// the transcript digest. The generators are in the same state every time.
    fn commit_once(start: u64) -> ([u8; 32], [u8; 32], [u8; 32]) {
        let (mut mesh, mut rngs) = setup(13);
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

    /// Two invocations with the same label and payloads. In the second,
    /// party 1 opens with its nonce of the first and sends either its
    /// commitment of the first (`stale`) or a commitment to the same payload
    /// and nonce under the second invocation.
    fn reuse_in_second_invocation(stale: bool) -> Result<(), Abort> {
        let (mut mesh, mut rngs) = setup(14);
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
            Err(Abort::Check(Check::Commitment))
        );
    }

    #[test]
    fn the_invocation_counter_does_not_wrap() {
        let (mut mesh, mut rngs) = setup(15);
        let hook: &mut dyn FnMut(Fault<'_>) = &mut honest;
        let mut ceremony = Ceremony::new([15; 32], &mut mesh, &mut rngs, hook).unwrap();
        ceremony.commits = u64::MAX - 1;
        assert_eq!(
            ceremony.commit_then_open(b"replay", &commit_payloads()),
            Ok(())
        );
        assert_eq!(
            ceremony.commit_then_open(b"replay", &commit_payloads()),
            Err(Abort::Check(Check::Commitment))
        );
        assert_eq!(ceremony.commits, u64::MAX);
    }

    /// The ceremony transcript after a Boolean stage of `count` triple words
    /// run by the parties of `setup(seed)` in a fixed session.
    fn digest_after_boolean_stage(seed: u8, count: usize) -> [u8; 32] {
        let (mut mesh, mut rngs) = setup(seed);
        let hook: &mut dyn FnMut(Fault<'_>) = &mut honest;
        let mut ceremony = Ceremony::new([16; 32], &mut mesh, &mut rngs, hook).unwrap();
        ceremony.boolean_stage(count).unwrap();
        ceremony.transcript.digest()
    }

    #[test]
    fn the_boolean_ceremony_transcript_is_chained() {
        let first = digest_after_boolean_stage(16, 1);
        assert_eq!(first, digest_after_boolean_stage(16, 1));
        assert_ne!(first, digest_after_boolean_stage(17, 1));
        // Without a ceremony nothing of the parties' randomness is sent.
        assert_eq!(
            digest_after_boolean_stage(16, 0),
            digest_after_boolean_stage(17, 0)
        );
    }

    /// A coin drawn by generators in a fixed state, on the mesh of
    /// `setup(18)` as established or after one further OT batch; with the
    /// coin, the mesh's chain.
    fn coin_on_mesh(extra_batch: bool) -> (u128, [u8; 32]) {
        let (mut mesh, mut rngs) = setup(18);
        if extra_batch {
            mesh.run_correlated_ot_words(0, 1, &[5], &mut rngs).unwrap();
        }
        let chain = mesh.transcript_digest();
        let mut rngs: Vec<_> = (0..3u8)
            .map(|p| PartyPrivateRng::from_seed([p; 32], b"TEST.PREP.COIN"))
            .collect();
        let hook: &mut dyn FnMut(Fault<'_>) = &mut honest;
        let mut ceremony = Ceremony::new([18; 32], &mut mesh, &mut rngs, hook).unwrap();
        (ceremony.coin(b"test").unwrap().u128(), chain)
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
    fn field_triples_and_randoms_satisfy_the_oracle() {
        let (mut mesh, mut rngs) = setup(3);
        let demand = Demand {
            field_triples: [3, 2, 2, 1, 1],
            field_randoms: [3, 2, 1, 1, 1],
            ..Demand::default()
        };
        let started = Instant::now();
        let mut out =
            run_dealerless_preprocessing([3; 32], &quorum(), &demand, &mut mesh, &mut rngs)
                .unwrap();
        println!("triples+randoms {demand:?}: {:?}", started.elapsed());
        verify_material(&demand, &mut out);
    }

    #[test]
    fn wrong_triple_correlation_and_product_are_caught() {
        let (mut mesh, mut rngs) = setup(4);
        let demand = Demand {
            field_triples: [1, 0, 0, 0, 0],
            ..Demand::default()
        };
        // One wrong correlation in one OT changes the product only if the
        // receiver's choice bit is 1: each run is either caught or harmless.
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
                            ..
                        } if bit == target => {
                            *correlation = Domain::Gold.add(*correlation, ONE);
                            true
                        }
                        _ => false,
                    },
                );
            match outcome {
                Ok(()) => {}
                Err(abort) => {
                    assert_eq!(abort, Abort::Check(Check::TripleSacrifice));
                    caught += 1;
                }
            }
        }
        println!("single wrong correlations caught: {caught} of 8");
        assert!(caught >= 1);
        for target in [
            ThresholdField::Goldilocks,
            ThresholdField::Ed25519,
            ThresholdField::Pallas,
            ThresholdField::Bls12_381,
        ] {
            let demand = Demand {
                field_triples: [1, 0, 1, 1, 1],
                ..Demand::default()
            };
            let outcome = deviate(50, &demand, &mut mesh, &mut rngs, |point| match point {
                Fault::TripleProduct {
                    field,
                    party: 2,
                    products,
                } if field == target => {
                    products[1] = target.domain().add(products[1], ONE);
                    true
                }
                _ => false,
            });
            assert_eq!(
                outcome,
                Err(Abort::Check(Check::TripleSacrifice)),
                "{target:?}"
            );
        }
    }

    #[test]
    fn boolean_material_satisfies_the_oracle() {
        let (mut mesh, mut rngs) = setup(5);
        let demand = Demand {
            boolean_triples: 3,
            auth_words: 5,
            ..Demand::default()
        };
        let mut out =
            run_dealerless_preprocessing([5; 32], &quorum(), &demand, &mut mesh, &mut rngs)
                .unwrap();
        verify_material(&demand, &mut out);
    }

    #[test]
    fn dabits_satisfy_the_oracle_in_every_field() {
        let (mut mesh, mut rngs) = setup(6);
        let demand = Demand {
            boolean_triples: 1,
            auth_words: 1,
            dabits: [2, 1, 1, 1, 1],
            ..Demand::default()
        };
        let started = Instant::now();
        let mut out =
            run_dealerless_preprocessing([6; 32], &quorum(), &demand, &mut mesh, &mut rngs)
                .unwrap();
        println!("dabits {demand:?}: {:?}", started.elapsed());
        verify_material(&demand, &mut out);
    }

    #[test]
    fn dabit_deviations_are_caught() {
        let (mut mesh, mut rngs) = setup(7);
        let demand = Demand {
            dabits: [1, 0, 0, 0, 0],
            ..Demand::default()
        };
        let cases: [(&str, Check, fn(Fault<'_>) -> bool); 7] = [
            (
                "wrong Boolean parity",
                Check::ParityOpening,
                |point| match point {
                    Fault::Parity {
                        owner: 1,
                        repetition: 5,
                        parity,
                        ..
                    } => {
                        *parity ^= 1;
                        true
                    }
                    _ => false,
                },
            ),
            (
                "wrong share in an opening of the XOR over the owners",
                Check::XorChain,
                |point| match point {
                    Fault::FieldOpening {
                        party: 2,
                        check: Check::XorChain,
                        share,
                        ..
                    } => {
                        *share = Domain::Gold.add(*share, ONE);
                        true
                    }
                    _ => false,
                },
            ),
            (
                "field form differs from Boolean form",
                Check::CrossDomain,
                |point| match point {
                    Fault::DaBitFieldInput {
                        owner: 1, values, ..
                    } => {
                        values[9][0] ^= 1;
                        true
                    }
                    _ => false,
                },
            ),
            (
                "mask candidate differs across the domains",
                Check::CrossDomain,
                |point| match point {
                    Fault::DaBitFieldInput {
                        owner: 0, values, ..
                    } => {
                        values[64 + 17][0] ^= 1;
                        true
                    }
                    _ => false,
                },
            ),
            (
                "field form is not a bit",
                Check::Bitness,
                |point| match point {
                    Fault::DaBitFieldInput {
                        owner: 2, values, ..
                    } => {
                        values[3][0] = 2;
                        true
                    }
                    _ => false,
                },
            ),
            (
                "Boolean key differs between the stages",
                Check::BooleanKeyConsistency,
                |point| match point {
                    Fault::BooleanKey {
                        owner: 0,
                        holder: 1,
                        key,
                    } => {
                        *key ^= 1 << 77;
                        true
                    }
                    _ => false,
                },
            ),
            (
                "Boolean inputs differ between key bits",
                Check::BooleanInput,
                |point| match point {
                    Fault::BooleanInput {
                        owner: 2,
                        holder: 0,
                        bit,
                        words,
                    } if bit < 16 => {
                        words[0] ^= 1;
                        true
                    }
                    _ => false,
                },
            ),
        ];
        for (case, (name, check, fault)) in cases.into_iter().enumerate() {
            let outcome = deviate(70 + case as u8, &demand, &mut mesh, &mut rngs, fault);
            assert_eq!(outcome, Err(Abort::Check(check)), "{name}");
        }
    }

    #[test]
    fn invalid_configurations_are_rejected() {
        let mut rngs: Vec<_> = (0..2u8)
            .map(|p| PartyPrivateRng::from_seed([p; 32], b"TEST.PREP"))
            .collect();
        let mut mesh = OtMesh::establish([9; 32], &mut rngs).unwrap();
        // A three-member quorum on a two-party mesh.
        assert_eq!(
            run_dealerless_preprocessing(
                [9; 32],
                &quorum(),
                &Demand::default(),
                &mut mesh,
                &mut rngs
            )
            .err(),
            Some(Error::InvalidConfiguration)
        );
        let pair = ThresholdConfig::new(2, 2, vec![0, 1]).unwrap();
        let demand = Demand {
            boolean_triples: 1,
            field_triples: [1, 0, 0, 0, 0],
            dabits: [1, 0, 0, 0, 0],
            ..Demand::default()
        };
        let mut out =
            run_dealerless_preprocessing([9; 32], &pair, &demand, &mut mesh, &mut rngs).unwrap();
        verify_material(&demand, &mut out);
    }

    /// The whole ceremony for a 3-member quorum of a 5-party roster, consumed
    /// by the online engine. `encode` adds a Goldilocks `field_to_bits`,
    /// which draws 64 daBit words (8192 field triples for the XOR over three
    /// owners) and 256 Boolean triple words.
    fn drive_online_engine(seed: u8, encode: bool) {
        let (mut mesh, mut rngs) = setup(seed);
        let config = quorum();
        let demand = Demand {
            boolean_triples: 1 + if encode { 256 } else { 0 },
            auth_words: 3,
            field_triples: [64, 64, 0, 64, 64],
            field_randoms: [128, 128, 0, 128, 128],
            dabits: [1 + if encode { 64 } else { 0 }, 1, 0, 1, 1],
        };
        let started = Instant::now();
        let parties =
            run_dealerless_preprocessing([seed; 32], &config, &demand, &mut mesh, &mut rngs)
                .unwrap();
        println!("end-to-end ceremony {demand:?}: {:?}", started.elapsed());
        let contribution = |p: usize, k: u64| k.wrapping_mul(p as u64 + 1) ^ (k << 17);
        let total = |k| {
            config
                .quorum()
                .iter()
                .fold(0, |v, &p| v ^ contribution(p, k))
        };
        run_stored(config.clone(), parties, |party, mac_keys, network| {
            let mut engine = engine(&config, party, mac_keys, network);
            engine.agree([17; 32]).unwrap();
            let a = engine.share(&[contribution(party, 0xa55a_1234)]).unwrap();
            let b = engine.share(&[contribution(party, 0x81f0_4321)]).unwrap();
            let c = engine.and(&[(a[0], b[0])]).unwrap();
            let product = total(0xa55a_1234) & total(0x81f0_4321);
            assert_ne!(product, 0);
            assert_eq!(
                engine.open(&[c[0], a[0]]).unwrap(),
                vec![product, total(0xa55a_1234)]
            );
            let mask = 0x00ff_00ff_0f0f_3333;
            assert_eq!(
                engine.open_lanes(&[b[0]], mask).unwrap(),
                vec![total(0x81f0_4321) & mask]
            );
            for d in [Domain::Gold, Domain::Secp, Domain::PallasFp, Domain::BlsFp] {
                let r = engine.frandom(d).unwrap();
                let s = engine.frandom(d).unwrap();
                let p = engine.fmul(&r, &s, d).unwrap();
                let lifted = engine.lift_bits_many(&[c[0]], d).unwrap().pop().unwrap();
                let opened = engine.fopen_many(&[p, r.clone(), s, lifted], d).unwrap();
                for lane in 0..64 {
                    assert_eq!(opened[0][lane], d.mul(opened[1][lane], opened[2][lane]));
                    assert_ne!(opened[1][lane], opened[2][lane]);
                    assert_eq!(opened[3][lane], [(product >> lane) & 1, 0, 0, 0, 0, 0]);
                }
                if encode && d == Domain::Gold {
                    let bits = engine.field_to_bits(&r, d).unwrap();
                    let encoding = engine.open(&bits).unwrap();
                    assert_eq!(encoding.len(), 64);
                    for (bit, word) in encoding.iter().enumerate() {
                        let expected = (0..64)
                            .fold(0, |w, lane| w | (((opened[1][lane][0] >> bit) & 1) << lane));
                        assert_eq!(*word, expected, "bit {bit}");
                    }
                }
            }
            engine.agree([18; 32]).unwrap();
        });
    }

    #[test]
    fn ceremony_output_drives_the_online_engine() {
        drive_online_engine(8, false);
    }

    /// As above with a Goldilocks `field_to_bits`. Its ceremony runs about
    /// 22.6 million OTs: measured 22 s on the idle build box and 65 s under
    /// load, against under 3 s for the test above.
    #[test]
    #[ignore = "8448 Goldilocks triples: 22 s to over a minute"]
    fn ceremony_output_drives_field_to_bits() {
        drive_online_engine(11, true);
    }

    /// Cost measurements on the real mesh (run with `--ignored --nocapture`).
    #[test]
    #[ignore = "measurement"]
    fn measure_costs() {
        let started = Instant::now();
        let (mut mesh, mut rngs) = setup(9);
        println!("OT mesh, 3 parties: {:?}", started.elapsed());
        let config = quorum();
        let mut run = |name: &str, demand: Demand, items: usize| {
            let started = Instant::now();
            run_dealerless_preprocessing([9; 32], &config, &demand, &mut mesh, &mut rngs).unwrap();
            let elapsed = started.elapsed();
            println!(
                "{name}: {items} items in {elapsed:?} ({:?} each)",
                elapsed / items as u32
            );
        };
        run(
            "fixed cost (one Goldilocks random)",
            Demand {
                field_randoms: [1, 0, 0, 0, 0],
                ..Demand::default()
            },
            1,
        );
        for (i, name) in ["Goldilocks", "secp256k1", "Ed25519", "Pallas", "BLS12-381"]
            .into_iter()
            .enumerate()
        {
            let mut demand = Demand::default();
            demand.field_triples[i] = 256;
            run(&std::format!("{name} triples"), demand, 256);
            let mut demand = Demand::default();
            demand.field_randoms[i] = 4096;
            run(&std::format!("{name} randoms"), demand, 4096);
            let mut demand = Demand::default();
            demand.dabits[i] = 4;
            run(&std::format!("{name} daBit words"), demand, 4);
        }
        run(
            "Boolean triple words",
            Demand {
                boolean_triples: 4096,
                ..Demand::default()
            },
            4096,
        );
        run(
            "authenticated words",
            Demand {
                auth_words: 4096,
                ..Demand::default()
            },
            4096,
        );
    }

    #[test]
    #[ignore = "measurement"]
    fn measure_phases() {
        let (mut mesh, mut rngs) = setup(10);
        let words = vec![0x1234_5678_9abc_def0u64; 256 * 7];
        let started = Instant::now();
        for (s, r) in [(0, 1), (1, 0), (0, 2), (2, 0), (1, 2), (2, 1)] {
            mesh.run_correlated_ot_words(s, r, &words, &mut rngs)
                .unwrap();
        }
        println!(
            "raw OTs for 256 Goldilocks triples: {:?}",
            started.elapsed()
        );
        let hook: &mut dyn FnMut(Fault<'_>) = &mut honest;
        let mut ceremony = Ceremony::new([1; 32], &mut mesh, &mut rngs, hook).unwrap();
        ceremony.boolean_stage(0).unwrap();
        ceremony.sample_field_keys();
        ceremony.establish_pairs().unwrap();
        for field in [ThresholdField::Goldilocks, ThresholdField::Secp256k1] {
            let started = Instant::now();
            let inputs = ceremony.multiply(field, 256).unwrap();
            println!("{field:?} multiply 256: {:?}", started.elapsed());
            let started = Instant::now();
            let shares = ceremony.authenticate(field, &inputs, 0..0).unwrap();
            println!(
                "{field:?} authenticate {}: {:?}",
                inputs[0].len(),
                started.elapsed()
            );
            let d = field.domain();
            let joint: Vec<SecretVec<Share>> = (0..3)
                .map(|p| {
                    (0..inputs[0].len())
                        .map(|k| {
                            (1..3)
                                .fold(shares[0][p][k], |sum, o| share_add(d, sum, shares[o][p][k]))
                        })
                        .collect()
                })
                .collect();
            let started = Instant::now();
            ceremony.sacrifice(field, &joint, 256).unwrap();
            println!("{field:?} sacrifice: {:?}", started.elapsed());
            let started = Instant::now();
            let _ = ceremony.transcript.digest();
            println!("{field:?} digest: {:?}", started.elapsed());
        }
    }
}
