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
//!   batch of 768 random OTs from the mesh, with `h` as receiver and the bits
//!   of all of `h`'s MAC key shares as choice bits. Each pad seeds a cSHAKE256
//!   stream; all later authentications between the pair read these streams,
//!   so the key `h` uses towards `o` is fixed once (COPE, MASCOT: Keller,
//!   Orsini, Scholl, CCS 2016, ePrint 2016/505, Section 3; IKNP/KOS for the
//!   Boolean key).
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
    secret::SecretVec,
    threshold_mpc::{
        AuthWord, BooleanTriple, DaBitWord, FieldShare, FieldTriple, MacKeyShare, ThresholdConfig,
        ThresholdField, mac_add, mac_scale, mac_sub, pack_macs,
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
        OtMesh, PartyPrivateRng, run_commit_and_open_coin, run_dealerless_pi_triple_f2,
    },
    wipe::{wipe_bytes, wipe_bytes32},
};

const ZERO: Value = [0; 4];
const ONE: Value = [1, 0, 0, 0];

/// Subset-parity repetitions of the cross-domain equality check.
pub const CROSS_REPS: usize = 128;
/// Sacrificed Boolean candidates that form one uniform `GF(2^128)` mask.
pub const MASK_BITS: usize = 128;
/// Largest number of doubly authenticated bits per field in one ceremony.
/// Keeps every integer of the cross-domain check far below each modulus.
const MAX_DABITS: usize = 1 << 32;

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

/// Choice words of one base-OT batch: two Goldilocks keys, the secp256k1 key,
/// the Ed25519 key (255 bits, one OT unused), the Boolean key.
const BASE_WORDS: usize = 12;
const BOOLEAN_BASE: usize = 640;
const fn field_base(field: ThresholdField, key: usize) -> usize {
    match field {
        ThresholdField::Goldilocks => 64 * key,
        ThresholdField::Secp256k1 => 128,
        ThresholdField::Ed25519 => 384,
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
    if d == Domain::Ed {
        value[3] &= u64::MAX >> 1;
    }
    value
}

/// Uniform canonical element by rejection from `fill`.
fn element_from(d: Domain, mut fill: impl FnMut(&mut [u8])) -> Value {
    let size = 8 * limbs_of(d);
    let mut bytes = [0u8; 32];
    loop {
        fill(&mut bytes[..size]);
        let value = parse_element(d, &bytes[..size]);
        if d.canonical(value) {
            wipe_bytes32(&mut bytes);
            return value;
        }
    }
}

/// Field element from one 48-byte random-OT pad. Candidates are read from
/// the pad until one is canonical; the last is reduced. The result is within
/// `2^-192` (Goldilocks: six 64-bit candidates, each rejected with
/// probability `2^-32`), `2^-224` (secp256k1) and `2^-250` (Ed25519) of
/// uniform.
fn pad_element(d: Domain, pad: &[u8; 48]) -> Value {
    if d == Domain::Gold {
        let mut value = 0;
        for chunk in pad.chunks_exact(8) {
            value = u64::from_le_bytes(chunk.try_into().unwrap());
            if d.canonical([value, 0, 0, 0]) {
                return [value, 0, 0, 0];
            }
        }
        return [value.wrapping_sub(d.modulus()[0]), 0, 0, 0];
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
            b"QSAG.MIGRATE.PREP.PAD.V1",
            &[
                session,
                &[sender as u8, receiver as u8],
                &(index as u64).to_le_bytes(),
                pad,
            ],
        ))
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
        let mut block = [0u8; 8 * 136];
        for chunk in out.chunks_mut(block.len() / 8) {
            let bytes = &mut block[..chunk.len() * 8];
            self.0.squeeze(bytes);
            for (word, raw) in chunk.iter_mut().zip(bytes.chunks_exact(8)) {
                *word = u64::from_le_bytes(raw.try_into().unwrap());
            }
        }
        wipe_bytes(&mut block);
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
        [mac[key], 0, 0, 0]
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
