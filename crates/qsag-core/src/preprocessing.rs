//! 100% Dealerless Post-Quantum Active-Security Preprocessing (`0` trusted dealers, `0` single-seed
//! cleartext tuple generators):
//! 1. **`RlweBaseOt` (`RLWE_N = 1024, q = 12289, η = 1`)**: Fujisaki–Okamoto active-checked
//!    Ring-LWE 1-out-of-2 base OT over $R_q = \mathbb{Z}_{12289}[X]/(X^{1024} + 1)$ (`> 200`-bit PQ
//!    Core-SVP) with deterministic `(seed_b || rho_b)` re-encryption verification, `0` decryption
//!    failure ($\|(e_1 r_c - e_2 s_R + e_3)\|_\infty \le 2049 < 3072 = \lfloor q/4 \rfloor$), split
//!    per-party round state machines, and a post-Base-OT $384 \to 128$ 2-universal `[I_128 | R]`
//!    Leftover-Hash combiner eliminating Chou–Orlandi (`ePrint 2015/267`) selective-failure leakage
//!    to $< 2^{-128}$.
//! 2. **Interactive `KosOtExtension`**: 3-message interactive challenge-response `cSHAKE256` KOS OT
//!    extension (`KosOtUColsMsg` $\to$ `KosOtChallengeMsg` $\to$ `KosOtProofMsg`) with transcript-bound
//!    correlation-robust hashing and immediate channel poison-and-wipe on failure, eliminating the
//!    Roy (`CRYPTO 2022` / `ePrint 2022/192`) Fiat–Shamir grinding & column-probe attacks.
//! 3. **Dealerless `Π_triple_f2` (`PreprocessedKeccakVault`)**: Pairwise OT cross-terms
//!    (`ole_pairwise_cross_sum_eq_mul`) + degree-$<t$ `TowerGf256` Shamir sharing + 2-lane `Tower128`
//!    BDOZ MAC cross-terms ($\alpha_i \cdot [x]_j$) + commit-and-open `Π_coin` + Booleanity check
//!    ($a^2 \oplus a = 0$) + 2-lane `Tower128` companion triple sacrifice (`triple_f2_sacrifice_sound`,
//!    cheating probability $\le 2^{-128}$ per lane / $\le 2^{-256}$ across both lanes).
//! 4. **Dealerless `Π_pow7` & Canonical `< p` A2B Bit-Masks (`PreprocessedPoseidonVault`)**:
//!    Joint `Π_rand` (`dealerless_joint_mask_uniform`) + pairwise 64-bit Gilboa `Goldilocks` OLE +
//!    `GoldilocksExt2` BDOZ MAC cross-terms + companion triple sacrifice (`pow7_sacrifice_sound`,
//!    cheating probability $1/p^2 < 2^{-127} < 2^{-125}$) + 3-round parallel Beaver power-tree
//!    (`evalPow7BeaverTree`: `[r], [r^2], ..., [r^7]`) + dealerless canonical `< p` 64-bit A2B masks
//!    verified via $b_k^2 - b_k = 0$ and exact `is_ge_p == 0` predicate opening.
//! 5. Production vault entrypoints use uniform, sacrificed KOS/MASCOT correlations.
//!    The compact GGM/QC-LPN format below is experimental: its sparse reconstructed
//!    masks are not suitable for online MPC. It is retained for redesign and regression work.

// Unit tests have a host runtime even when the production library is no_std.
#[cfg(all(test, not(feature = "std")))]
extern crate std;

use alloc::boxed::Box;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;
use core::hint::black_box;

pub use crate::field::goldilocks::{
    Goldilocks, GoldilocksExt2, eval_poly_ext2_at_base, eval_poly_goldilocks,
    lagrange_weights_zero_goldilocks, wipe_ext2, wipe_goldilocks,
};
pub use crate::field::tower::{
    BitslicedGf256x64, PublicGf256Matrix, Tower128, TowerGf256, bs_gf256_extract_lane,
    bs_gf256_insert_lane, bs_gf256_mul_planes_ct, bs_gf256_scale_secret_ct, bs_gf256_xor,
    bs_gf256_xor_assign, eval_poly_gf256, lagrange_weights_zero_gf256, wipe_tower128,
};
use crate::sponge::keccak::{
    Cshake256Xof, Shake256Xof, cshake256_32, encode_multi_frame, keccak_f1600,
};
use crate::wipe::{
    ct_eq_bytes32, wipe_bytes, wipe_bytes32, wipe_u16s, wipe_u64s, wipe_u128s,
};

// ============================================================================
// 0. Preprocessing Errors & Identifiable Cheater Attribution
// ============================================================================

/// Sender's two 384-bit correlation pads for one extended OT.
pub type OtPadPair = ([u8; 48], [u8; 48]);
/// Pads for a complete correlated-OT batch, on both sides.
pub type OtBatchPads = (Vec<OtPadPair>, Vec<[u8; 48]>);
/// Party-major vectors of values of a given field/type.
pub type PartyValues<T> = Vec<Vec<T>>;
/// Two parallel 128-bit authentication lanes per party.
pub type TowerAlphaShares = Vec<[Tower128; 2]>;
/// Two-lane MACs indexed by verifier, sender and value.
pub type PairwiseTowerMacs = Vec<Vec<Vec<[Tower128; 2]>>>;
/// Value shares and two-lane MACs grouped by party.
pub type TowerMacMatrices = (PartyValues<[Tower128; 2]>, PartyValues<[Tower128; 2]>);
/// Authenticated Goldilocks Beaver material: a, b, c followed by their MACs.
pub type GoldilocksBeaverMaterial = (
    PartyValues<Goldilocks>, PartyValues<Goldilocks>, PartyValues<Goldilocks>,
    PartyValues<GoldilocksExt2>, PartyValues<GoldilocksExt2>, PartyValues<GoldilocksExt2>,
);
type BooleanMascotProducts = (PartyValues<u64>, PartyValues<[u128; 64]>, PartyValues<[u128; 64]>);
type SpcotPunctureOutput = (Vec<[u128; 2]>, Vec<([u8; 16], [u8; 16])>);

/// Preprocessing abort with deterministic attribution when a party deviates during OT, coin-flip,
/// polynomial degree verification, BDOZ/SPDZ MAC check, Booleanity check, or companion sacrifice.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PreprocessError {
    InvalidThreshold { t: usize, n: usize },
    DuplicateOrZeroEvalPoint,
    CoinCommitMismatch { party_id: usize },
    ShareCommitMismatch { phase: &'static str, party_id: usize },
    BaseOtReceiverProofFailed { sender_id: usize, receiver_id: usize },
    BaseOtFoCheckFailed { sender_id: usize, receiver_id: usize, ot_idx: u32 },
    KosOtCheckFailed { sender_id: usize, receiver_id: usize },
    ChannelPoisoned { sender_id: usize, receiver_id: usize },
    DegreeCheckFailed { phase: &'static str },
    MacCheckFailed { phase: &'static str, accused_party: Option<usize> },
    SacrificeResidualNonZero { phase: &'static str },
    NonBooleanBitDetected { phase: &'static str },
    VaultExhausted { kind: &'static str },
    VaultPoisoned { kind: &'static str },
    PcgDepthOutOfRange { depth: usize },
    PcgInvalidWireSeed,
    ExperimentalSparsePcg,
    /// The wire seed carries the magic of an earlier, no longer accepted layout.
    PcgObsoleteWireSeedFormat,
    /// The seed's identity is already recorded as expanded; nothing was expanded.
    PcgSeedAlreadyBurned,
    /// The seed burn tracker could not record the burn; nothing was expanded.
    PcgSeedBurnNotRecorded,
}

impl fmt::Display for PreprocessError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidThreshold { t, n } => {
                write!(f, "invalid threshold parameters t={}, n={}", t, n)
            }
            Self::DuplicateOrZeroEvalPoint => write!(f, "duplicate or zero Shamir evaluation point"),
            Self::CoinCommitMismatch { party_id } => {
                write!(f, "commit-and-open coin mismatch from party {}", party_id)
            }
            Self::ShareCommitMismatch { phase, party_id } => {
                write!(f, "share commitment opening mismatch in {} from party {}", phase, party_id)
            }
            Self::BaseOtReceiverProofFailed {
                sender_id,
                receiver_id,
            } => write!(
                f,
                "Ring-LWE Base-OT Receiver OR-Sigma ZKPoK failed (sender {}, receiver {})",
                sender_id, receiver_id
            ),
            Self::BaseOtFoCheckFailed {
                sender_id,
                receiver_id,
                ot_idx,
            } => write!(
                f,
                "Ring-LWE Base-OT Fujisaki-Okamoto re-encryption check failed (sender {}, receiver {}, idx {})",
                sender_id, receiver_id, ot_idx
            ),
            Self::KosOtCheckFailed {
                sender_id,
                receiver_id,
            } => write!(
                f,
                "interactive KOS OT extension correlation check failed between sender {} and receiver {}",
                sender_id, receiver_id
            ),
            Self::ChannelPoisoned {
                sender_id,
                receiver_id,
            } => write!(
                f,
                "OT extension channel ({} -> {}) permanently poisoned after prior abort",
                sender_id, receiver_id
            ),
            Self::DegreeCheckFailed { phase } => {
                write!(f, "Shamir degree < t check failed in {}", phase)
            }
            Self::MacCheckFailed {
                phase,
                accused_party,
            } => write!(
                f,
                "SPDZ/BDOZ MAC verification failed in {} (accused party {:?})",
                phase, accused_party
            ),
            Self::SacrificeResidualNonZero { phase } => {
                write!(f, "SPDZ companion sacrifice residual non-zero in {}", phase)
            }
            Self::NonBooleanBitDetected { phase } => {
                write!(f, "non-Boolean share b^2 != b detected in {}", phase)
            }
            Self::VaultExhausted { kind } => {
                write!(f, "preprocessed {} vault exhausted", kind)
            }
            Self::VaultPoisoned { kind } => {
                write!(f, "preprocessed {} vault permanently poisoned after MAC abort", kind)
            }
            Self::PcgDepthOutOfRange { depth } => {
                write!(f, "PCG GGM tree depth {} out of supported range 14..=16", depth)
            }
            Self::ExperimentalSparsePcg => write!(f, "compact PCG is unavailable: use uniform vault preprocessing"),
            Self::PcgInvalidWireSeed => write!(f, "malformed or tampered PCG wire seed"),
            Self::PcgObsoleteWireSeedFormat => write!(
                f,
                "PCG wire seed uses the obsolete QSAGDPC1 layout; re-run setup to obtain a QSAGDPC2 seed"
            ),
            Self::PcgSeedAlreadyBurned => {
                write!(f, "PCG seed was already expanded once; refusing to expand it again")
            }
            Self::PcgSeedBurnNotRecorded => {
                write!(f, "PCG seed burn could not be recorded; refusing to expand")
            }
        }
    }
}

/// Maximum accepted preprocessing frame (16 MiB), including all declared elements.
pub const MAX_FRAME_BUDGET: usize = 16 * 1024 * 1024;
pub(crate) fn validate_frame_count(count: usize, elem_bytes: usize, remaining: usize) -> Result<(), PreprocessError> {
    match count.checked_mul(elem_bytes) {
        Some(size) if size <= remaining && size <= MAX_FRAME_BUDGET => Ok(()),
        _ => Err(PreprocessError::PcgInvalidWireSeed),
    }
}

/// Secret-keyed transcript hedge. A restored counter is safe for a new transcript;
/// identical seed, counter, entropy and transcript necessarily reproduce the same bytes.
pub struct HedgedTranscriptRng { seed: [u8; 32], counter: u64 }
impl Drop for HedgedTranscriptRng { fn drop(&mut self) { wipe_bytes32(&mut self.seed); } }
impl HedgedTranscriptRng {
    pub fn new(secret_hedge_seed: [u8; 32], monotonic_counter: u64) -> Self {
        Self { seed: secret_hedge_seed, counter: monotonic_counter }
    }
    /// Fails before producing output on counter exhaustion. Variable inputs are length framed.
    pub fn fill_bytes(&mut self, caller_entropy: &[u8], session_and_msg_transcript: &[u8], out: &mut [u8]) -> Result<(), PreprocessError> {
        let next = self.counter.checked_add(1).ok_or(PreprocessError::PcgInvalidWireSeed)?;
        Self::derive(&self.seed, self.counter, caller_entropy, session_and_msg_transcript, out);
        self.counter = next;
        Ok(())
    }
    pub(crate) fn derive(seed: &[u8; 32], counter: u64, caller_entropy: &[u8], session_and_msg_transcript: &[u8], out: &mut [u8]) {
        let mut xof = Cshake256Xof::new_shake256();
        xof.absorb(b"QSAG.HEDGED_RNG.V1");
        xof.absorb(seed);
        xof.absorb(&counter.to_le_bytes());
        xof.absorb(&(caller_entropy.len() as u64).to_le_bytes());
        xof.absorb(caller_entropy);
        xof.absorb(&(session_and_msg_transcript.len() as u64).to_le_bytes());
        xof.absorb(session_and_msg_transcript);
        xof.squeeze(out);
    }
}

/// Reserve before exposing material. One cursor per material kind spans every quorum
/// and session using this non-cloneable vault; failed reservations leave it unchanged.
fn reserve_material(cursor: &mut usize, len: usize, count: usize, poisoned: bool, kind: &'static str) -> Result<core::ops::Range<usize>, PreprocessError> {
    if poisoned { return Err(PreprocessError::VaultPoisoned { kind }); }
    let end = cursor.checked_add(count).filter(|end| *end <= len).ok_or(PreprocessError::VaultExhausted { kind })?;
    let start = *cursor;
    *cursor = end;
    Ok(start..end)
}

/// Deterministic per-party CSPRNG stream backed by `cSHAKE256("QSAG.PARTY.RNG/v1", ...)`.
/// Isolated strictly to a single party's private entropy seed; wiped on `Drop`.
pub struct PartyPrivateRng {
    seed: [u8; 32],
    counter: u64,
    buf: [u8; 4 * 136],
    off: usize,
}

impl fmt::Debug for PartyPrivateRng {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("PartyPrivateRng([REDACTED])")
    }
}

impl Drop for PartyPrivateRng {
    fn drop(&mut self) {
        wipe_bytes32(&mut self.seed);
        self.buf.fill(0);
        core::hint::black_box(&mut self.buf);
    }
}

impl PartyPrivateRng {
    /// Seed from the operating system entropy source; failures are propagated.
    #[cfg(all(feature = "std", unix))]
    pub fn from_os_rng(domain_label: &[u8]) -> Result<Self, std::io::Error> {
        use std::io::Read;
        let mut seed = [0u8; 32];
        let result = std::fs::File::open("/dev/urandom").and_then(|mut f| f.read_exact(&mut seed));
        if let Err(error) = result { wipe_bytes32(&mut seed); return Err(error); }
        let rng = Self::from_seed(seed, domain_label);
        wipe_bytes32(&mut seed);
        Ok(rng)
    }

    pub fn from_seed(party_seed: [u8; 32], domain_label: &[u8]) -> Self {
        let derived = cshake256_32(
            b"QSAG.PARTY.RNG.INIT/v1",
            &encode_multi_frame(&[&party_seed, domain_label]),
        );
        Self {
            seed: derived,
            counter: 0,
            buf: [0u8; 4 * 136],
            off: 4 * 136,
        }
    }

    /// Rekey the private mask stream with a public session/message transcript.
    /// Discards buffered bytes so no pre-transcript masks escape after this call.
    pub fn hedge_transcript(&mut self, transcript: &[u8]) {
        let mut entropy = self.next_bytes32();
        let mut seed = [0; 32];
        // Each rekey resets the counter under a fresh secret key.
        HedgedTranscriptRng::derive(&self.seed, 0, &entropy, transcript, &mut seed);
        wipe_bytes32(&mut self.seed);
        self.seed = seed;
        wipe_bytes32(&mut seed);
        wipe_bytes32(&mut entropy);
        wipe_bytes(&mut self.buf);
        self.counter = 0;
        self.off = self.buf.len();
    }

    fn refill(&mut self) {
        // Four consecutive counter blocks preserve the scalar byte stream while
        // sharing one SIMD permutation. Padding and domain separation are identical.
        let mut states = [[0u64; 25]; 4];
        for state in &mut states {
            state[0] = u64::from_le_bytes(*b"QSAG.PRG");
            state[1] = u64::from_le_bytes(*b"NG.BLK\x01\x00");
            for (i, word) in state[2..6].iter_mut().enumerate() {
                *word = u64::from_le_bytes(core::array::from_fn(|j| self.seed[8 * i + j]));
            }
            state[6] = self.counter;
            state[7] = 0x1f;
            state[16] = 0x8000_0000_0000_0000;
            self.counter = self.counter.wrapping_add(1);
        }
        qsag_asm::keccak_f1600_batch(&mut states);
        for (block, state) in states.iter().enumerate() {
            for (i, word) in state[..17].iter().enumerate() {
                let offset = block * 136 + i * 8;
                self.buf[offset..offset + 8].copy_from_slice(&word.to_le_bytes());
            }
        }
        for state in &mut states { wipe_u64s(state); }
        self.off = 0;
    }

    pub fn fill_bytes(&mut self, out: &mut [u8]) {
        let mut written = 0usize;
        while written < out.len() {
            if self.off == self.buf.len() {
                self.refill();
            }
            let avail = (self.buf.len() - self.off).min(out.len() - written);
            out[written..written + avail].copy_from_slice(&self.buf[self.off..self.off + avail]);
            self.off += avail;
            written += avail;
        }
    }

    #[inline]
    pub fn next_u64(&mut self) -> u64 {
        let mut b = [0u8; 8];
        self.fill_bytes(&mut b);
        u64::from_le_bytes(b)
    }

    #[inline]
    pub fn next_u128(&mut self) -> u128 {
        let lo = self.next_u64() as u128;
        let hi = self.next_u64() as u128;
        lo | (hi << 64)
    }

    #[inline]
    pub fn next_bytes32(&mut self) -> [u8; 32] {
        let mut out = [0u8; 32];
        self.fill_bytes(&mut out);
        out
    }

    /// Constant-time 192-bit (`24`-byte) reduction in $[0, p)$ (`< 2^{-192}` statistical distance, `0` branches).
    #[inline]
    pub fn next_goldilocks(&mut self) -> Goldilocks {
        let mut b = [0u8; 24];
        self.fill_bytes(&mut b);
        let g = Goldilocks::from_bytes24_unbiased(&b);
        wipe_bytes(&mut b);
        g
    }

    #[inline]
    pub fn next_ext2(&mut self) -> GoldilocksExt2 {
        GoldilocksExt2::new(self.next_goldilocks(), self.next_goldilocks())
    }

    #[inline]
    pub fn next_gf256(&mut self) -> TowerGf256 {
        let mut b = [0u8; 1];
        self.fill_bytes(&mut b);
        TowerGf256(b[0])
    }

    #[inline]
    pub fn next_tower128(&mut self) -> Tower128 {
        Tower128(self.next_u128())
    }
}

// ============================================================================
// 1. Fujisaki–Okamoto Active-Checked Ring-LWE Base OT (`N = 1024, q = 12289, η = 1`)
//    + `384 -> 128` Universal-Hash Extractor Combiner (`0` Selective-Failure Leakage)
// ============================================================================

/// Ring dimension $N = 1024$ of $R_q = \mathbb{Z}_{12289}[X]/(X^{1024} + 1)$ (`> 200`-bit PQ Core-SVP).
pub const RLWE_N: usize = 1024;

/// Number of random-choice FO-checked Ring-LWE Base OTs combined via `[I_128 | R_{128x256}]`
/// (`384 - 128 = 256` bits of Leftover-Hash-Lemma entropy slack; joint selective-failure advantage $< 2^{-128}$).
pub const RLWE_BASE_OT_COUNT: usize = 384;

/// Number of `u64` words packing `RLWE_BASE_OT_COUNT = 384` choice bits (`6 * 64 = 384`).
pub const RLWE_BASE_OT_WORDS: usize = RLWE_BASE_OT_COUNT / 64;

/// Prime modulus $q = 12289$ ($q - 1 = 3 \times 2^{12} = 6 \times 2048$, supporting exact 2048-th roots of unity).
pub const RLWE_Q: u16 = 12289;

/// Center $\lfloor q / 2 \rfloor = 6144$ encoding bit `1` (`|e_1 r_c - e_2 s_R + e_3|_∞ <= 2049 < 3072 = floor(q/4)`).
pub const RLWE_HALF_Q: u16 = 6144;

#[inline]
const fn rlwe_add(a: u16, b: u16) -> u16 {
    let s = a + b;
    if s >= RLWE_Q { s - RLWE_Q } else { s }
}

#[inline]
const fn rlwe_sub(a: u16, b: u16) -> u16 {
    if a >= b { a - b } else { a + RLWE_Q - b }
}

#[inline]
const fn rlwe_mul(a: u16, b: u16) -> u16 {
    (((a as u32) * (b as u32)) % (RLWE_Q as u32)) as u16
}

const fn rlwe_pow(mut base: u16, mut exp: u32) -> u16 {
    let mut acc = 1u16;
    while exp > 0 {
        if (exp & 1) == 1 {
            acc = rlwe_mul(acc, base);
        }
        base = rlwe_mul(base, base);
        exp >>= 1;
    }
    acc
}

/// Primitive 2048-th root of unity $\psi_{2048} = 11^6 \bmod 12289$ ($\psi_{2048}^{1024} \equiv -1 \pmod{12289}$).
pub const RLWE_PSI_2048: u16 = {
    let psi = rlwe_pow(11, 6);
    assert!(rlwe_pow(psi, 1024) == RLWE_Q - 1);
    psi
};

/// Multiplicative inverse of $\psi_{2048}$ modulo $12289$.
pub const RLWE_PSI_INV_2048: u16 = rlwe_pow(RLWE_PSI_2048, 2047);

/// Primitive 1024-th root of unity $\omega_{1024} = \psi_{2048}^2 = 11^{12} \bmod 12289$ and its inverse.
pub const RLWE_OMEGA_1024: u16 = rlwe_mul(RLWE_PSI_2048, RLWE_PSI_2048);
pub const RLWE_OMEGA_INV_1024: u16 = rlwe_mul(RLWE_PSI_INV_2048, RLWE_PSI_INV_2048);
pub const RLWE_N_INV: u16 = rlwe_pow(RLWE_N as u16, (RLWE_Q - 2) as u32);

const PSI_POWS: [u16; RLWE_N] = {
    let mut arr = [0u16; RLWE_N];
    let mut cur = 1u16;
    let mut i = 0usize;
    while i < RLWE_N {
        arr[i] = cur;
        cur = rlwe_mul(cur, RLWE_PSI_2048);
        i += 1;
    }
    arr
};

const PSI_INV_POWS: [u16; RLWE_N] = {
    let mut arr = [0u16; RLWE_N];
    let mut cur = 1u16;
    let mut i = 0usize;
    while i < RLWE_N {
        arr[i] = cur;
        cur = rlwe_mul(cur, RLWE_PSI_INV_2048);
        i += 1;
    }
    arr
};

const OMEGA_POWS: [u16; RLWE_N / 2] = {
    let mut arr = [0u16; RLWE_N / 2];
    let mut cur = 1u16;
    let mut i = 0usize;
    while i < RLWE_N / 2 {
        arr[i] = cur;
        cur = rlwe_mul(cur, RLWE_OMEGA_1024);
        i += 1;
    }
    arr
};

const OMEGA_INV_POWS: [u16; RLWE_N / 2] = {
    let mut arr = [0u16; RLWE_N / 2];
    let mut cur = 1u16;
    let mut i = 0usize;
    while i < RLWE_N / 2 {
        arr[i] = cur;
        cur = rlwe_mul(cur, RLWE_OMEGA_INV_1024);
        i += 1;
    }
    arr
};

/// Constant-time Ring-LWE bit decoder matching `lean/Qsag/Preprocessing.lean:rlweDecodeBit`
/// (`true` iff `3072 <= z && z < 9216`, `0` secret-dependent branches).
#[inline]
pub fn rlwe_decode_bit_ct(z: u16) -> u8 {
    let z32 = black_box(z as u32);
    // ge_3072 == 1 iff z32 >= 3072 (underflow bit of z32 - 3072 is 0)
    let ge_3072 = 1u32 ^ ((z32.wrapping_sub(3072)) >> 31);
    // lt_9216 == 1 iff z32 < 9216 (underflow bit of z32 - 9216 is 1)
    let lt_9216 = (z32.wrapping_sub(9216)) >> 31;
    (ge_3072 & lt_9216) as u8
}

/// Polynomial in $R_q = \mathbb{Z}_{12289}[X]/(X^{1024} + 1)$.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct RlwePoly(pub [u16; RLWE_N]);

/// Pre-transformed negacyclic NTT representation of a public CRS polynomial for fast batch products.
#[derive(Clone, Copy)]
pub struct RlwePolyNtt([u16; RLWE_N]);

impl RlwePolyNtt {
    #[inline]
    pub fn from_ntt(&self) -> RlwePoly {
        let mut c = self.0;
        RlwePoly::ntt_cyclic(&mut c, &OMEGA_INV_POWS);
        for i in 0..RLWE_N {
            let scaled = rlwe_mul(c[i], RLWE_N_INV);
            c[i] = rlwe_mul(scaled, PSI_INV_POWS[i]);
        }
        RlwePoly(c)
    }
}

impl fmt::Debug for RlwePoly {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "RlwePoly([{}..])", self.0[0])
    }
}

impl Default for RlwePoly {
    fn default() -> Self {
        Self([0u16; RLWE_N])
    }
}

impl RlwePoly {
    pub const ZERO: Self = Self([0u16; RLWE_N]);

    pub fn add(&self, rhs: &Self) -> Self {
        let mut out = [0u16; RLWE_N];
        for (i, out_i_item) in out[..RLWE_N].iter_mut().enumerate() {
            *out_i_item = rlwe_add(self.0[i], rhs.0[i]);
        }
        Self(out)
    }

    pub fn sub(&self, rhs: &Self) -> Self {
        let mut out = [0u16; RLWE_N];
        for (i, out_i_item) in out[..RLWE_N].iter_mut().enumerate() {
            *out_i_item = rlwe_sub(self.0[i], rhs.0[i]);
        }
        Self(out)
    }

    /// Constant-time full-polynomial equality check across all 1024 coefficients (`0` early exit).
    #[inline]
    pub fn ct_eq(&self, rhs: &Self) -> bool {
        let mut diff = 0u16;
        for i in 0..RLWE_N {
            diff |= black_box(self.0[i]) ^ black_box(rhs.0[i]);
        }
        black_box(diff) == 0
    }

    /// Constant-time polynomial selection (`choice == true` -> `if_true`, else `if_false`).
    pub fn ct_select(choice: bool, if_true: &Self, if_false: &Self) -> Self {
        let mask = 0u16.wrapping_sub(black_box(choice as u16));
        let mut out = [0u16; RLWE_N];
        for (i, out_i_item) in out[..RLWE_N].iter_mut().enumerate() {
            *out_i_item = if_false.0[i] ^ (mask & (if_true.0[i] ^ if_false.0[i]));
        }
        Self(out)
    }

    fn bit_reverse_1024(a: &mut [u16; RLWE_N]) {
        for i in 0..RLWE_N {
            let rev = i.reverse_bits() >> (usize::BITS - 10);
            if i < rev {
                a.swap(i, rev);
            }
        }
    }

    fn ntt_cyclic(a: &mut [u16; RLWE_N], twiddles: &[u16; RLWE_N / 2]) {
        Self::bit_reverse_1024(a);
        let mut len = 2usize;
        while len <= RLWE_N {
            let half = len / 2;
            let step = RLWE_N / len;
            let mut start = 0usize;
            while start < RLWE_N {
                for j in 0..half {
                    let w = twiddles[j * step];
                    let u = a[start + j];
                    let v = rlwe_mul(a[start + j + half], w);
                    a[start + j] = rlwe_add(u, v);
                    a[start + j + half] = rlwe_sub(u, v);
                }
                start += len;
            }
            len <<= 1;
        }
    }

    #[inline]
    pub fn to_ntt(&self) -> RlwePolyNtt {
        let mut a = self.0;
        for i in 0..RLWE_N {
            a[i] = rlwe_mul(a[i], PSI_POWS[i]);
        }
        Self::ntt_cyclic(&mut a, &OMEGA_POWS);
        RlwePolyNtt(a)
    }

    #[inline]
    pub fn mul_ntt(&self, lhs_ntt: &RlwePolyNtt) -> Self {
        let mut b = self.0;
        for i in 0..RLWE_N {
            b[i] = rlwe_mul(b[i], PSI_POWS[i]);
        }
        Self::ntt_cyclic(&mut b, &OMEGA_POWS);
        let mut c = [0u16; RLWE_N];
        for i in 0..RLWE_N {
            c[i] = rlwe_mul(lhs_ntt.0[i], b[i]);
        }
        Self::ntt_cyclic(&mut c, &OMEGA_INV_POWS);
        for i in 0..RLWE_N {
            let scaled = rlwe_mul(c[i], RLWE_N_INV);
            c[i] = rlwe_mul(scaled, PSI_INV_POWS[i]);
        }
        wipe_u16s(&mut b);
        Self(c)
    }

    /// Fast $O(N \log N)$ negacyclic multiplication modulo $(X^{1024} + 1, 12289)$.
    pub fn mul_negacyclic(&self, rhs: &Self) -> Self {
        let mut lhs_ntt = self.to_ntt();
        let out = rhs.mul_ntt(&lhs_ntt);
        wipe_u16s(&mut lhs_ntt.0);
        out
    }

    /// Deterministically derive public CRS polynomial in $R_q$ via rejection sampling (`< 3*q = 36867 < 65536`).
    pub fn from_crs_xof(
        session_id: &[u8; 32],
        sender: usize,
        receiver: usize,
        ot_idx: u32,
        slot: u8,
    ) -> Self {
        let mut xof = Cshake256Xof::new(b"QSAG.OT.RLWE.CRS/v1");
        xof.absorb(session_id);
        xof.absorb(&(sender as u64).to_be_bytes());
        xof.absorb(&(receiver as u64).to_be_bytes());
        xof.absorb(&ot_idx.to_be_bytes());
        xof.absorb(&[slot]);
        let mut coeffs = [0u16; RLWE_N];
        let mut idx = 0usize;
        let mut buf = [0u8; 128];
        while idx < RLWE_N {
            xof.squeeze(&mut buf);
            #[expect(clippy::chunks_exact_to_as_chunks, reason = "Keep the workspace Rust 1.85 minimum; slice as_chunks requires a newer compiler")]
            for chunk in buf.chunks_exact(2) {
                if idx == RLWE_N {
                    break;
                }
                let val = u16::from_le_bytes([chunk[0], chunk[1]]);
                if val < 3 * RLWE_Q {
                    coeffs[idx] = val % RLWE_Q;
                    idx += 1;
                }
            }
        }
        Self(coeffs)
    }

    /// Deterministically expand CRS polynomial `(a_crs` or `t_crs[ot_idx])` bound to `crs_coin`.
    pub fn from_crs_xof_with_coin(
        crs_coin: &[u8; 32],
        session_id: &[u8; 32],
        sender_id: usize,
        receiver_id: usize,
        ot_idx: u32,
        role: u8,
    ) -> Self {
        let mixed_sid = if *crs_coin == [0u8; 32] {
            *session_id
        } else {
            cshake256_32(
                b"QSAG.OT.RLWE.CRS.COIN/v1",
                &encode_multi_frame(&[session_id, crs_coin]),
            )
        };
        Self::from_crs_xof(&mixed_sid, sender_id, receiver_id, ot_idx, role)
    }

    /// Sample short ternary noise polynomial in $\{-1, 0, +1\}^{1024}$ ($\eta = 1$) in strict
    /// constant time via 2-bit centered binomial `CBD_1` (`a_bit - b_bit`, `0` rejection branches!).
    pub fn sample_ternary_eta1(rng: &mut PartyPrivateRng) -> Self {
        let mut coeffs = [0u16; RLWE_N];
        let mut buf = [0u8; RLWE_N / 4]; // 256 bytes = 1024 * 2 bits
        rng.fill_bytes(&mut buf);
        for byte_idx in 0..(RLWE_N / 4) {
            let b = black_box(buf[byte_idx]);
            for sub in 0..4 {
                let pair = (b >> (2 * sub)) & 0x3;
                let a_bit = (pair & 1) as u16;
                let b_bit = ((pair >> 1) & 1) as u16;
                // a_bit - b_bit in {-1, 0, +1} mod RLWE_Q:
                // if a_bit == 1 && b_bit == 0 -> 1
                // if a_bit == 0 && b_bit == 1 -> RLWE_Q - 1
                // else -> 0
                let pos_mask = 0u16.wrapping_sub(a_bit & (1 - b_bit));
                let neg_mask = 0u16.wrapping_sub((1 - a_bit) & b_bit);
                coeffs[4 * byte_idx + sub] = (1u16 & pos_mask) | ((RLWE_Q - 1) & neg_mask);
            }
        }
        wipe_bytes(&mut buf);
        Self(coeffs)
    }
}

/// Number of parallel/sequential repetitions in [`RlweReceiverZkPok`] (`13 * 20 = 260` challenge bits; this is not an extraction theorem).
pub const RLWE_ZKPOK_REPS: usize = 13;
/// Joint Gaussian rejection parameters. Verifier bounds, modulus and joint
/// challenge space are unchanged. Key generation conditions the two CBD_1
/// polynomials on total squared norm <=1376. Their energy before conditioning
/// is Binomial(2048,1/2); the Chernoff bound exp(-2048*KL(1376/2048 || 1/2))
/// is below 2^-178. This bounds the change to the original RLWE distribution.
/// Since a challenge has two signed terms, the thirteen-repetition response shift
/// satisfies ||v||^2 <= 13*4*1376 = 71552.
///
/// Masks follow exp(-y^2/(2*700^2)) on [-3072,3071]. Accept z=y+v only in
/// [-3070,3069], with probability min(1, exp((||y||^2-||z||^2)/980000)/M),
/// where M=exp(ceil(980000 ln(512))/980000). All target responses have preimages
/// in the mask box because every shift coordinate lies in [-2,2]. Simulated
/// responses use the same Gaussian conditioned on the response box. Without
/// clipping the likelihood ratio this gives exactly witness-independent output.
/// Discrete Gaussian MGF domination bounds the clipped tail below 2^-155;
/// conditioning on the response box (mass >0.6) gives distance below 2^-154.
/// This is statistical HVZK, not perfect HVZK, and is not a QROM reduction.
///
/// Sampling uses uniform proposals and fixed-work, 192-bit Bernoulli rejection,
/// with no mask-indexed table access. Each exponential evaluation has absolute
/// error <64/2^192, including 120-digit constant generation and multiplication
/// rounding. Combining coordinates and conditioning on proof acceptance leaves
/// implementation error below 2^-160. Bounds here are per joint proof; composed
/// sessions require the usual union bound. Expected acceptance is about 1/512,
/// versus 0.000088 for uniform masks. All rejections restart the entire joint
/// transcript; no independently grindable per-repetition challenges are used.
const RLWE_ZKPOK_Z_BOUND: i16 = 3070;

/// Constant-time HVZK OR-Sigma proof of short Ring-LWE witness knowledge for [`RlweOtReceiverMsg`]:
/// proves knowledge of short `(s, e)` on EITHER `Y_0 = pk0` OR `Y_1 = pk0 + t_crs` under `a_crs`,
/// defeating malformed-`pk0` active Receiver key-extraction attacks (unchanged challenge space, statistical HVZK).
#[derive(Clone, Debug)]
pub struct RlweReceiverZkPok {
    pub chal0: [u32; RLWE_ZKPOK_REPS],
    pub chal1: [u32; RLWE_ZKPOK_REPS],
    pub z_s0: Box<[[i16; RLWE_N]; RLWE_ZKPOK_REPS]>,
    pub z_e0: Box<[[i16; RLWE_N]; RLWE_ZKPOK_REPS]>,
    pub z_s1: Box<[[i16; RLWE_N]; RLWE_ZKPOK_REPS]>,
    pub z_e1: Box<[[i16; RLWE_N]; RLWE_ZKPOK_REPS]>,
}

#[inline]
fn poly_from_chal20(u: u32) -> RlwePoly {
    let pos0 = (u & 0x1FF) as usize; // 0..512
    let sign0 = ((u >> 9) & 1) as u16;
    let pos1 = 512 + (((u >> 10) & 0x1FF) as usize); // 512..1024
    let sign1 = ((u >> 19) & 1) as u16;
    let mut coeffs = [0u16; RLWE_N];
    let value0 = 1 ^ (0u16.wrapping_sub(sign0) & (1 ^ (RLWE_Q - 1)));
    let value1 = 1 ^ (0u16.wrapping_sub(sign1) & (1 ^ (RLWE_Q - 1)));
    for (i, coeff) in coeffs.iter_mut().enumerate() {
        *coeff = (value0 & 0u16.wrapping_sub(black_box((i == pos0) as u16)))
            | (value1 & 0u16.wrapping_sub(black_box((i == pos1) as u16)));
    }
    RlwePoly(coeffs)
}

/// Multiply public `poly` by public 2-sparse `d(u)` in $R_q = \mathbb{Z}_q[X]/(X^{1024}+1)$ in $O(N)$ (`0` NTTs).
#[inline]
fn mul_chal20_public(poly: &RlwePoly, u: u32) -> RlwePoly {
    let pos0 = (u & 0x1FF) as usize;
    let neg0 = ((u >> 9) & 1) == 1;
    let pos1 = 512 + (((u >> 10) & 0x1FF) as usize);
    let neg1 = ((u >> 19) & 1) == 1;
    let mut out = [0u16; RLWE_N];
    for (pos, is_neg) in [(pos0, neg0), (pos1, neg1)] {
        for (i, &coeff) in poly.0.iter().enumerate() {
            let (dst, wrap_neg) = if i + pos < RLWE_N {
                (i + pos, is_neg)
            } else {
                (i + pos - RLWE_N, !is_neg)
            };
            let term = if wrap_neg {
                if coeff == 0 { 0 } else { RLWE_Q - coeff }
            } else {
                coeff
            };
            let sum = out[dst] + term;
            out[dst] = if sum >= RLWE_Q { sum - RLWE_Q } else { sum };
        }
    }
    RlwePoly(out)
}

#[inline]
fn signed_box_to_rlwe_poly(v: &[i16; RLWE_N]) -> RlwePoly {
    let mut out = [0u16; RLWE_N];
    for i in 0..RLWE_N {
        let x = v[i] as i32;
        let rem = x.rem_euclid(i32::from(RLWE_Q));
        out[i] = rem as u16;
    }
    RlwePoly(out)
}

#[inline]
fn center_small_mod_q(poly: &RlwePoly) -> [i16; RLWE_N] {
    let mut out = [0i16; RLWE_N];
    for (i, out_i_item) in out[..RLWE_N].iter_mut().enumerate() {
        let c = poly.0[i];
        let gt_half = ((RLWE_HALF_Q.wrapping_sub(1).wrapping_sub(c)) >> 15) & 1;
        let neg_adj = (RLWE_Q as i16) * (gt_half as i16);
        *out_i_item = (c as i16) - neg_adj;
    }
    out
}


// Fixed-point unsigned fractions in little-endian limbs, with denominator 2^192.
// The schoolbook product retains the high half, rounding toward zero.
fn gaussian_fraction_mul(a: [u64; 3], b: [u64; 3]) -> [u64; 3] {
    let mut product = [0u64; 6];
    for (i, &ai) in a.iter().enumerate() {
        let mut carry = 0u128;
        for (j, &bj) in b.iter().enumerate() {
            let value = u128::from(ai) * u128::from(bj)
                + u128::from(product[i + j]) + carry;
            product[i + j] = value as u64;
            carry = value >> 64;
        }
        product[i + 3] = carry as u64;
    }
    [product[3], product[4], product[5]]
}

fn gaussian_fraction_lt(a: [u64; 3], b: [u64; 3]) -> bool {
    let mut borrow = false;
    for (&ai, &bi) in a.iter().zip(&b) {
        let (diff, first) = ai.overflowing_sub(bi);
        let (_, second) = diff.overflowing_sub(u64::from(borrow));
        borrow = first | second;
    }
    borrow
}

// Gaussian sampling by a uniform proposal and fixed-work Bernoulli rejection.
// Unlike indexed CDT lookup, this makes neither branches nor memory addresses
// depend on the accepted mask. Trial counts are independent of the final sample.
fn sample_gaussian_box(rng: &mut PartyPrivateRng, response: bool) -> [i16; RLWE_N] {
    let half = if response { RLWE_ZKPOK_Z_BOUND } else { RLWE_ZKPOK_Z_BOUND + 2 };
    core::array::from_fn(|_| loop {
        let mut coins = [0u8; 26];
        rng.fill_bytes(&mut coins);
        let proposal = u16::from_le_bytes([coins[0], coins[1]]) & 0x1fff;
        let valid = proposal < 2 * half as u16;
        let mask = 0u16.wrapping_sub(u16::from(valid));
        let x = (proposal & mask) as i16 - half;
        let exponent = (i64::from(x) * i64::from(x)) as u64;
        let random = core::array::from_fn(|i| u64::from_le_bytes(
            core::array::from_fn(|j| coins[2 + 8*i + j])));
        // Reject only when the cheap upper bound proves that the full 192-bit
        // comparison would reject. Every accepted proposal still takes the same
        // fixed-work exact path; discarded proposals are independent of it.
        let upper = gaussian_exp_upper_bound(exponent);
        if black_box(u128::from(random[2]) >= upper) {
            wipe_bytes(&mut coins);
            continue;
        }
        let probability = gaussian_exp_probability::<24>(exponent);
        let accept = gaussian_fraction_lt(random, probability) & valid;
        wipe_bytes(&mut coins);
        if black_box(accept) { break x; }
    })
}

// Ignore the low fourteen exponent bits for this bound only. This increases
// the ideal probability by at most exp(16383/980000) < 1.017, while needing
// only ten Q64 products. The actual decision below still uses all 192 bits.
// Relative to the Q192 computation with those exponent bits cleared, initial
// truncation loses <1 Q64 unit; each of ten factors and product truncations
// loses <1 more. Adding 21 therefore gives a strict upper bound. Keep the sum
// in u128 because it can exceed u64::MAX near probability one.
// No table index, loop bound or branch depends on the proposal.
fn gaussian_exp_upper_bound(exponent: u64) -> u128 {
    let mut probability = u64::MAX;
    for (bit, factor) in RLWE_GAUSSIAN_EXP_POWERS[14..24].iter().enumerate() {
        let multiplied = ((u128::from(probability) * u128::from(factor[2])) >> 64) as u64;
        let mask = 0u64.wrapping_sub((exponent >> (bit + 14)) & 1);
        probability ^= mask & (probability ^ multiplied);
    }
    u128::from(probability) + 21
}

fn gaussian_exp_probability<const BITS: usize>(exponent: u64) -> [u64; 3] {
    let mut probability = [u64::MAX; 3];
    for (bit, &factor) in RLWE_GAUSSIAN_EXP_POWERS[..BITS].iter().enumerate() {
        let multiplied = gaussian_fraction_mul(probability, factor);
        let mask = 0u64.wrapping_sub((exponent >> bit) & 1);
        for (p, m) in probability.iter_mut().zip(multiplied) {
            *p ^= mask & (*p ^ m);
        }
    }
    probability
}

// Ratio D(y+v)/(M D(y)). All arithmetic depending on the witness shift uses
// fixed loops and masked selection; only the final accept/reject bit is opened.
fn gaussian_accept(log_ratio: i64, rng: &mut PartyPrivateRng) -> bool {
    let exponent = log_ratio + RLWE_GAUSSIAN_LOG_M;
    let negative = (exponent >> 63) as u64;
    let clipped = (exponent as u64) & !negative;
    let mut probability = gaussian_exp_probability::<30>(clipped);
    let in_range = 0u64.wrapping_sub(u64::from(clipped < (1 << 30)));
    for limb in &mut probability { *limb &= in_range; }
    let random = core::array::from_fn(|_| rng.next_u64());
    gaussian_fraction_lt(random, probability) | (negative != 0)
}

// Generated at 120 decimal digits of precision. These are public bit-position
// factors, scanned in fixed order; there are no mask-indexed table accesses.
// floor(2^192 * exp(-2^i/980000)), i=0..29.
const RLWE_GAUSSIAN_EXP_POWERS: [[u64; 3]; 30] = [
    [0x1e0ee5c166ce3f45, 0x4596fdd04820cdf5, 0xffffeee161ee8ccb],
    [0xc4bd6a5137eea0f8, 0x4a2b8823ca1b4080, 0xffffddc2c5022e3e],
    [0x44427bc76a53ff98, 0x2a9c7998b671a801, 0xffffbb858e98aecd],
    [0xa0c9a58e0e64155f, 0x8111b86300311166, 0xffff770b2f82a469],
    [0x35a41e9244e165f3, 0x4c35e0bc42b0f5a8, 0xfffeee16a84a5076],
    [0x1d0613f7ebafa37a, 0xdf95f9d82b467952, 0xfffddc2e75a822ae],
    [0x1cc31b117b42ceb3, 0x692edb6ffd64b91e, 0xfffbb8617f996614],
    [0x29767ac0a297cf82, 0x4a27dce9e6d35099, 0xfff770d550301cb9],
    [0xadb8566b5ff3f42d, 0x31988b3d23e474e3, 0xffeee1f3e31bedf9],
    [0x6750e998b9b340e1, 0xf4f6785cfd460252, 0xffddc50cc75a8994],
    [0xd196fffa1ed986fd, 0xeeabfe39f8fd5b4e, 0xffbb8ead44e33bdc],
    [0x06cff414fc79dc4f, 0xdc50d69edfd2a160, 0xff772fa6efe402ed],
    [0xd0d009324a025ffe, 0x4b9e8aa4ca5654b6, 0xfeeea86be7f9fcc2],
    [0xaaf2184fd58065f9, 0x60409dd8686a08e8, 0xfdde74b3b7c53457],
    [0x965a565c6d111b08, 0xb4ec92392fe9aad0, 0xfbc173f9d621e030],
    [0x60aeffc51a982010, 0x3ca73c0a1d21b6eb, 0xf794eb9bfd25b6e8],
    [0x00bc34df6dfa8348, 0x655e44e2d45921a0, 0xef70b54847b33c5f],
    [0x647298b2cc3a9ced, 0xcf047b168746a1be, 0xdff3a41c157eb15a],
    [0x1e445c07efd41bd3, 0xefcffdd9e95adf36, 0xc3ea5fc9e3f7861f],
    [0x64853bde5727d2ff, 0x54f67e49ba147824, 0x95eee480d2374d3f],
    [0xb99bb3368bc0d7af, 0xc02dbeaedb0d80fa, 0x57cff4eba030f604],
    [0x77d66aade9197cc5, 0xe967d9885d913509, 0x1e1f0166264058a1],
    [0xd17313b79cc3aba7, 0x6b99ed77f4585a5e, 0x038b481547b64d6a],
    [0x36d997f1617c1bac, 0xf3a1a5781f3b6abe, 0x000c8f77db161fe3],
    [0x8102ba277dc54cf0, 0x1f1003bc1c646702, 0x0000009dc3a3a8f3],
    [0x29065424ef536df9, 0x8c3ff63710108879, 0x0000000000006139],
    [0x39e763f90442732a, 0x0000000024eca938, 0x0000000000000000],
    [0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    [0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    [0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
];
const RLWE_GAUSSIAN_LOG_M: i64 = 6113559;
const RLWE_WITNESS_ENERGY_BOUND: usize = 1376;

fn bounded_ternary_witness(s: &RlwePoly, e: &RlwePoly) -> bool {
    let (energy, ternary) = s.0.iter().chain(&e.0).fold((0usize, true), |(energy, valid), &c| {
        (energy + usize::from(c != 0), valid & ((c == 0) | (c == 1) | (c == RLWE_Q - 1)))
    });
    ternary & (energy <= RLWE_WITNESS_ENERGY_BOUND)
}


#[inline]
fn ct_select_i16_array(choice: bool, if_true: &[i16; RLWE_N], if_false: &[i16; RLWE_N]) -> [i16; RLWE_N] {
    let mask = 0u16.wrapping_sub(black_box(choice as u16));
    let mut out = [0i16; RLWE_N];
    for i in 0..RLWE_N {
        let a = if_true[i] as u16;
        let b = if_false[i] as u16;
        out[i] = (b ^ (mask & (a ^ b))) as i16;
    }
    out
}

#[expect(clippy::too_many_arguments, reason = "Preserve the explicit statement, role, witness and randomness bindings in this protocol API")]
fn hash_rlwe_zkpok_joint_challenges(
    crs_coin: &[u8; 32], session_id: &[u8; 32], sender_id: usize,
    receiver_id: usize, ot_idx: u32, pk0: &RlwePoly, t_crs: &RlwePoly,
    commitments: &[(RlwePoly, RlwePoly)],
) -> [u32; RLWE_ZKPOK_REPS] {
    let mut xof = Cshake256Xof::new(b"QSAG.OT.RLWE.ZKPOK/v2");
    xof.absorb(crs_coin);
    xof.absorb(session_id);
    xof.absorb(&(sender_id as u64).to_be_bytes());
    xof.absorb(&(receiver_id as u64).to_be_bytes());
    xof.absorb(&ot_idx.to_be_bytes());
    xof.absorb(&(RLWE_ZKPOK_REPS as u32).to_be_bytes());
    for p in core::iter::once(pk0).chain(core::iter::once(t_crs))
        .chain(commitments.iter().flat_map(|(a, b)| [a, b])) {
        for &c in &p.0 { xof.absorb(&c.to_le_bytes()); }
    }
    core::array::from_fn(|_| {
        let mut out = [0u8; 4];
        xof.squeeze(&mut out);
        u32::from_le_bytes(out) & 0xFFFFF
    })
}

impl RlweReceiverZkPok {
    #[expect(clippy::too_many_arguments, reason = "Preserve the explicit statement, role, witness and randomness bindings in this protocol API")]
    fn prove_ct(
        crs_coin: &[u8; 32],
        session_id: &[u8; 32],
        sender_id: usize,
        receiver_id: usize,
        ot_idx: u32,
        a_ntt: &RlwePolyNtt,
        t_crs: &RlwePoly,
        pk0: &RlwePoly,
        s_r: &RlwePoly,
        e1: &RlwePoly,
        choice_bit: bool,
        rng: &mut PartyPrivateRng,
    ) -> Self {
        let pk1 = pk0.add(t_crs);
        // When `choice_bit == false`, fake branch is `1` (`pk1`); when `true`, fake branch is `0` (`pk0`).
        let y_fake = RlwePoly::ct_select(choice_bit, pk0, &pk1);
        let mut y_fake_ntt = y_fake.to_ntt();
        let s_r_ntt = s_r.to_ntt();
        let e1_ntt = e1.to_ntt();

        let mut chal0 = [0u32; RLWE_ZKPOK_REPS];
        let mut chal1 = [0u32; RLWE_ZKPOK_REPS];
        let mut z_s0 = Box::new([[0i16; RLWE_N]; RLWE_ZKPOK_REPS]);
        let mut z_e0 = Box::new([[0i16; RLWE_N]; RLWE_ZKPOK_REPS]);
        let mut z_s1 = Box::new([[0i16; RLWE_N]; RLWE_ZKPOK_REPS]);
        let mut z_e1 = Box::new([[0i16; RLWE_N]; RLWE_ZKPOK_REPS]);

        // Reuse storage, but replace every transcript element on each attempt.
        let mut commitments = Vec::with_capacity(RLWE_ZKPOK_REPS);
        let mut masks = Vec::with_capacity(RLWE_ZKPOK_REPS);
        let mut fake = Vec::with_capacity(RLWE_ZKPOK_REPS);
        // Rejection restarts the entire joint transcript. Keeping an accepted
        // repetition while changing other commitments would bias its challenge.
        loop {
            commitments.clear();
            masks.clear();
            fake.clear();
            for _ in 0..RLWE_ZKPOK_REPS {
                let u_fake = (rng.next_u64() as u32) & 0xFFFFF;
                let zs_fake = sample_gaussian_box(rng, true);
                let ze_fake = sample_gaussian_box(rng, true);
                let w_fake = signed_box_to_rlwe_poly(&zs_fake).mul_ntt(a_ntt)
                    .add(&signed_box_to_rlwe_poly(&ze_fake))
                    .sub(&poly_from_chal20(u_fake).mul_ntt(&y_fake_ntt));
                let ys = sample_gaussian_box(rng, false);
                let ye = sample_gaussian_box(rng, false);
                let w_real = signed_box_to_rlwe_poly(&ys).mul_ntt(a_ntt)
                    .add(&signed_box_to_rlwe_poly(&ye));
                commitments.push((RlwePoly::ct_select(choice_bit, &w_fake, &w_real),
                    RlwePoly::ct_select(choice_bit, &w_real, &w_fake)));
                masks.push((ys, ye));
                fake.push((u_fake, zs_fake, ze_fake));
            }
            let challenges = hash_rlwe_zkpok_joint_challenges(crs_coin, session_id,
                sender_id, receiver_id, ot_idx, pk0, t_crs, &commitments);
            let mut in_bounds = 1u32;
            let mut log_ratio = 0i64;
            for rep in 0..RLWE_ZKPOK_REPS {
                let (u_fake, zs_fake, ze_fake) = &fake[rep];
                let u_real = challenges[rep] ^ u_fake;
                let d_ntt = poly_from_chal20(u_real).to_ntt();
                let mut ds_ntt = [0u16; RLWE_N];
                let mut de_ntt = [0u16; RLWE_N];
                for i in 0..RLWE_N {
                    ds_ntt[i] = rlwe_mul(d_ntt.0[i], s_r_ntt.0[i]);
                    de_ntt[i] = rlwe_mul(d_ntt.0[i], e1_ntt.0[i]);
                }
                let mut ds = center_small_mod_q(&RlwePolyNtt(ds_ntt).from_ntt());
                let mut de = center_small_mod_q(&RlwePolyNtt(de_ntt).from_ntt());
                wipe_u16s(&mut ds_ntt);
                wipe_u16s(&mut de_ntt);
                let (ys, ye) = &mut masks[rep];
                for i in 0..RLWE_N {
                    log_ratio += 2 * i64::from(ys[i]) * i64::from(ds[i]) + i64::from(ds[i]).pow(2);
                    log_ratio += 2 * i64::from(ye[i]) * i64::from(de[i]) + i64::from(de[i]).pow(2);
                    ys[i] += ds[i]; ye[i] += de[i];
                    in_bounds &= (((ys[i] as i32 + 3070) as u32) < 6140) as u32;
                    in_bounds &= (((ye[i] as i32 + 3070) as u32) < 6140) as u32;
                }
                let c_mask = 0u32.wrapping_sub(black_box(choice_bit as u32));
                chal0[rep] = u_real ^ (c_mask & (u_real ^ u_fake));
                chal1[rep] = u_fake ^ (c_mask & (u_fake ^ u_real));
                z_s0[rep] = ct_select_i16_array(choice_bit, zs_fake, ys);
                z_e0[rep] = ct_select_i16_array(choice_bit, ze_fake, ye);
                z_s1[rep] = ct_select_i16_array(choice_bit, ys, zs_fake);
                z_e1[rep] = ct_select_i16_array(choice_bit, ye, ze_fake);
                qsag_asm::volatile_fill(&mut ds, 0);
                qsag_asm::volatile_fill(&mut de, 0);
            }
            for (ys, ye) in &mut masks {
                qsag_asm::volatile_fill(ys, 0); qsag_asm::volatile_fill(ye, 0);
            }
            for (u, zs, ze) in &mut fake {
                qsag_asm::volatile_fill(core::slice::from_mut(u), 0);
                qsag_asm::volatile_fill(zs, 0); qsag_asm::volatile_fill(ze, 0);
            }
            let accept = gaussian_accept(log_ratio, rng);
            if black_box(in_bounds) == 1 && black_box(accept) { break; }
        }

        wipe_u16s(&mut y_fake_ntt.0);
        Self {
            chal0,
            chal1,
            z_s0,
            z_e0,
            z_s1,
            z_e1,
        }
    }

    #[expect(clippy::too_many_arguments, reason = "Preserve the explicit statement, role, witness and randomness bindings in this protocol API")]
    pub fn verify(
        &self,
        crs_coin: &[u8; 32],
        session_id: &[u8; 32],
        sender_id: usize,
        receiver_id: usize,
        ot_idx: u32,
        a_ntt: &RlwePolyNtt,
        t_crs: &RlwePoly,
        pk0: &RlwePoly,
    ) -> bool {
        let y0 = *pk0;
        let y1 = pk0.add(t_crs);
        let mut commitments = Vec::with_capacity(RLWE_ZKPOK_REPS);
        for rep in 0..RLWE_ZKPOK_REPS {
            if (self.chal0[rep] >> 20) != 0 || (self.chal1[rep] >> 20) != 0 {
                return false;
            }
            for arr in [&self.z_s0[rep], &self.z_e0[rep], &self.z_s1[rep], &self.z_e1[rep]] {
                for &v in arr {
                    if !(-RLWE_ZKPOK_Z_BOUND..RLWE_ZKPOK_Z_BOUND).contains(&v) {
                        return false;
                    }
                }
            }
            let zs0_p = signed_box_to_rlwe_poly(&self.z_s0[rep]);
            let ze0_p = signed_box_to_rlwe_poly(&self.z_e0[rep]);
            let zs1_p = signed_box_to_rlwe_poly(&self.z_s1[rep]);
            let ze1_p = signed_box_to_rlwe_poly(&self.z_e1[rep]);

            let w0 = zs0_p
                .mul_ntt(a_ntt)
                .add(&ze0_p)
                .sub(&mul_chal20_public(&y0, self.chal0[rep]));
            let w1 = zs1_p
                .mul_ntt(a_ntt)
                .add(&ze1_p)
                .sub(&mul_chal20_public(&y1, self.chal1[rep]));
            commitments.push((w0, w1));
        }
        let challenges = hash_rlwe_zkpok_joint_challenges(crs_coin, session_id,
            sender_id, receiver_id, ot_idx, pk0, t_crs, &commitments);
        for (rep, expected) in challenges.iter().enumerate() {
            if self.chal0[rep] ^ self.chal1[rep] != *expected { return false; }
        }
        true
    }
}

/// First message of active-checked Ring-LWE 1-out-of-2 OT (`Receiver -> Sender`), carrying `pk0`
/// and a constant-time OR-Sigma proof of short witness knowledge [`RlweReceiverZkPok`].
#[derive(Clone, Debug)]
pub struct RlweOtReceiverMsg {
    pub pk0: RlwePoly,
    pub pok: RlweReceiverZkPok,
}

/// Ephemeral receiver state for 1 FO-checked Ring-LWE base OT (`!Clone`, wiped on `Drop`).
pub struct RlweOtReceiverSecret {
    crs_coin: [u8; 32],
    session_id: [u8; 32],
    sender_id: usize,
    receiver_id: usize,
    ot_idx: u32,
    pk0: RlwePoly,
    s_r: RlwePoly,
    choice_bit: bool,
}

impl fmt::Debug for RlweOtReceiverSecret {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("RlweOtReceiverSecret([REDACTED])")
    }
}

impl Drop for RlweOtReceiverSecret {
    fn drop(&mut self) {
        wipe_u16s(&mut self.s_r.0);
        self.choice_bit = false;
        black_box(&mut self.choice_bit);
    }
}

/// Second message of active-checked Ring-LWE 1-out-of-2 OT (`Sender -> Receiver`).
#[derive(Clone, Debug)]
pub struct RlweOtSenderMsg {
    pub u0: RlwePoly,
    pub v0: RlwePoly,
    pub u1: RlwePoly,
    pub v1: RlwePoly,
}

#[inline]
fn encode_seed64_into_poly(seed: &[u8; 32], rho: &[u8; 32]) -> RlwePoly {
    let mut coeffs = [0u16; RLWE_N];
    for byte_idx in 0..32 {
        let b_s = black_box(seed[byte_idx]);
        let b_r = black_box(rho[byte_idx]);
        for bit in 0..8 {
            let bit_s = ((b_s >> bit) & 1) as u16;
            let bit_r = ((b_r >> bit) & 1) as u16;
            coeffs[8 * byte_idx + bit] = bit_s * RLWE_HALF_Q;
            coeffs[256 + 8 * byte_idx + bit] = bit_r * RLWE_HALF_Q;
        }
    }
    RlwePoly(coeffs)
}

#[inline]
fn decode_seed64_from_poly_ct(noisy: &RlwePoly) -> ([u8; 32], [u8; 32]) {
    let mut seed = [0u8; 32];
    let mut rho = [0u8; 32];
    for byte_idx in 0..32 {
        let mut acc_s = 0u8;
        let mut acc_r = 0u8;
        for bit in 0..8 {
            acc_s |= rlwe_decode_bit_ct(noisy.0[8 * byte_idx + bit]) << bit;
            acc_r |= rlwe_decode_bit_ct(noisy.0[256 + 8 * byte_idx + bit]) << bit;
        }
        seed[byte_idx] = acc_s;
        rho[byte_idx] = acc_r;
    }
    (seed, rho)
}

/// Deterministic Fujisaki–Okamoto branch encryptor: derives `(r_b, e2_b, e3_b)` from
/// `Cshake256("QSAG.OT.RLWE.FO/v1", crs_coin || session_id || sender || receiver || ot_idx || branch || seed || rho)`
/// and encrypts `(seed || rho)` (64 bytes = 512 bits <= 1024 coeffs).
#[expect(clippy::too_many_arguments, reason = "Preserve the explicit statement, role, witness and randomness bindings in this protocol API")]
fn rlwe_fo_encrypt_branch(
    crs_coin: &[u8; 32],
    session_id: &[u8; 32],
    sender_id: usize,
    receiver_id: usize,
    ot_idx: u32,
    branch: u8,
    a_ntt: &RlwePolyNtt,
    pk_branch: &RlwePoly,
    seed: &[u8; 32],
    rho: &[u8; 32],
) -> (RlwePoly, RlwePoly) {
    let mut label = [0u8; 120];
    label[0..32].copy_from_slice(crs_coin);
    label[32..64].copy_from_slice(session_id);
    label[64..72].copy_from_slice(&(sender_id as u64).to_be_bytes());
    label[72..80].copy_from_slice(&(receiver_id as u64).to_be_bytes());
    label[80..84].copy_from_slice(&ot_idx.to_be_bytes());
    label[84] = branch;
    label[88..120].copy_from_slice(seed);
    let fo_seed = cshake256_32(b"QSAG.OT.RLWE.FO/v2", &encode_multi_frame(&[&label, rho]));
    wipe_bytes(&mut label);

    let mut fo_rng = PartyPrivateRng::from_seed(fo_seed, b"QSAG.OT.RLWE.FO.STREAM/v2");
    let mut r_b = RlwePoly::sample_ternary_eta1(&mut fo_rng);
    let mut e2_b = RlwePoly::sample_ternary_eta1(&mut fo_rng);
    let mut e3_b = RlwePoly::sample_ternary_eta1(&mut fo_rng);
    let mut m_poly = encode_seed64_into_poly(seed, rho);

    let u_b = r_b.mul_ntt(a_ntt).add(&e2_b);
    let v_b = pk_branch.mul_negacyclic(&r_b).add(&e3_b).add(&m_poly);

    wipe_u16s(&mut r_b.0);
    wipe_u16s(&mut e2_b.0);
    wipe_u16s(&mut e3_b.0);
    wipe_u16s(&mut m_poly.0);
    (u_b, v_b)
}

#[expect(clippy::too_many_arguments, reason = "Preserve the explicit statement, role, witness and randomness bindings in this protocol API")]
fn rlwe_ot_choose_with_crs(
    crs_coin: &[u8; 32],
    session_id: &[u8; 32],
    sender_id: usize,
    receiver_id: usize,
    ot_idx: u32,
    a_ntt: &RlwePolyNtt,
    t_crs: &RlwePoly,
    choice_bit: bool,
    rng: &mut PartyPrivateRng,
) -> (RlweOtReceiverSecret, RlweOtReceiverMsg) {
    let (s_r, mut e1) = loop {
        let mut s = RlwePoly::sample_ternary_eta1(rng);
        let mut e = RlwePoly::sample_ternary_eta1(rng);
        if black_box(bounded_ternary_witness(&s, &e)) { break (s, e); }
        wipe_u16s(&mut s.0);
        wipe_u16s(&mut e.0);
    };
    let rlwe_sample = s_r.mul_ntt(a_ntt).add(&e1);
    let shifted = rlwe_sample.sub(t_crs);
    let pk0 = RlwePoly::ct_select(choice_bit, &shifted, &rlwe_sample);
    let pok = RlweReceiverZkPok::prove_ct(
        crs_coin,
        session_id,
        sender_id,
        receiver_id,
        ot_idx,
        a_ntt,
        t_crs,
        &pk0,
        &s_r,
        &e1,
        choice_bit,
        rng,
    );
    wipe_u16s(&mut e1.0);
    (
        RlweOtReceiverSecret {
            crs_coin: *crs_coin,
            session_id: *session_id,
            sender_id,
            receiver_id,
            ot_idx,
            pk0,
            s_r,
            choice_bit,
        },
        RlweOtReceiverMsg { pk0, pok },
    )
}

/// Transparent CRS for the standalone base-OT API, bound to its protocol and roles.
fn rlwe_session_crs(session_id: &[u8; 32], sender_id: usize, receiver_id: usize) -> [u8; 32] {
    cshake256_32(b"QSAG.OT.RLWE.CRS/v2", &encode_multi_frame(&[
        session_id, &(sender_id as u64).to_be_bytes(), &(receiver_id as u64).to_be_bytes(),
        &(RLWE_N as u64).to_be_bytes(), &RLWE_Q.to_be_bytes(),
        &(RLWE_ZKPOK_REPS as u64).to_be_bytes(),
    ]))
}

/// Receiver Round-1: encode secret `choice_bit` into `pk0 = (a * s_R + e_1) - choice_bit * t_crs`
/// and attach a constant-time OR-Sigma proof [`RlweReceiverZkPok`].
pub fn rlwe_ot_choose(
    session_id: &[u8; 32],
    sender_id: usize,
    receiver_id: usize,
    ot_idx: u32,
    choice_bit: bool,
    rng: &mut PartyPrivateRng,
) -> (RlweOtReceiverSecret, RlweOtReceiverMsg) {
    let zero_coin = rlwe_session_crs(session_id, sender_id, receiver_id);
    let a_ntt =
        RlwePoly::from_crs_xof_with_coin(&zero_coin, session_id, sender_id, receiver_id, 0, 0)
            .to_ntt();
    let t_crs =
        RlwePoly::from_crs_xof_with_coin(&zero_coin, session_id, sender_id, receiver_id, ot_idx, 1);
    rlwe_ot_choose_with_crs(
        &zero_coin,
        session_id,
        sender_id,
        receiver_id,
        ot_idx,
        &a_ntt,
        &t_crs,
        choice_bit,
        rng,
    )
}

#[expect(clippy::too_many_arguments, reason = "Preserve the explicit statement, role, witness and randomness bindings in this protocol API")]
fn try_rlwe_ot_transfer_with_crs(
    crs_coin: &[u8; 32],
    session_id: &[u8; 32],
    sender_id: usize,
    receiver_id: usize,
    ot_idx: u32,
    a_ntt: &RlwePolyNtt,
    t_crs: &RlwePoly,
    req: &RlweOtReceiverMsg,
    seed0: &[u8; 32],
    seed1: &[u8; 32],
    rng: &mut PartyPrivateRng,
) -> Result<RlweOtSenderMsg, PreprocessError> {
    if !req.pok.verify(
        crs_coin,
        session_id,
        sender_id,
        receiver_id,
        ot_idx,
        a_ntt,
        t_crs,
        &req.pk0,
    ) {
        return Err(PreprocessError::BaseOtReceiverProofFailed {
            sender_id,
            receiver_id,
        });
    }
    let pk0 = req.pk0;
    let pk1 = pk0.add(t_crs);
    let mut rho0 = rng.next_bytes32();
    let mut rho1 = rng.next_bytes32();
    let (u0, v0) = rlwe_fo_encrypt_branch(
        crs_coin,
        session_id,
        sender_id,
        receiver_id,
        ot_idx,
        0,
        a_ntt,
        &pk0,
        seed0,
        &rho0,
    );
    let (u1, v1) = rlwe_fo_encrypt_branch(
        crs_coin,
        session_id,
        sender_id,
        receiver_id,
        ot_idx,
        1,
        a_ntt,
        &pk1,
        seed1,
        &rho1,
    );
    wipe_bytes32(&mut rho0);
    wipe_bytes32(&mut rho1);
    Ok(RlweOtSenderMsg { u0, v0, u1, v1 })
}

/// Fallible Sender Round-2: verifies Receiver's OR-Sigma ZKPoK **before** encrypting `(seed0, seed1)`.
#[expect(clippy::too_many_arguments, reason = "Preserve the explicit statement, role, witness and randomness bindings in this protocol API")]
pub fn try_rlwe_ot_transfer(
    session_id: &[u8; 32],
    sender_id: usize,
    receiver_id: usize,
    ot_idx: u32,
    req: &RlweOtReceiverMsg,
    seed0: &[u8; 32],
    seed1: &[u8; 32],
    rng: &mut PartyPrivateRng,
) -> Result<RlweOtSenderMsg, PreprocessError> {
    let zero_coin = rlwe_session_crs(session_id, sender_id, receiver_id);
    let a_ntt =
        RlwePoly::from_crs_xof_with_coin(&zero_coin, session_id, sender_id, receiver_id, 0, 0)
            .to_ntt();
    let t_crs =
        RlwePoly::from_crs_xof_with_coin(&zero_coin, session_id, sender_id, receiver_id, ot_idx, 1);
    try_rlwe_ot_transfer_with_crs(
        &zero_coin,
        session_id,
        sender_id,
        receiver_id,
        ot_idx,
        &a_ntt,
        &t_crs,
        req,
        seed0,
        seed1,
        rng,
    )
}

/// Sender Round-2: verifies Receiver's OR-Sigma ZKPoK and Fujisaki–Okamoto encrypts 64-byte payloads
/// `(seed_b || rho_b)` under `(pk0, pk0 + t_crs)` with worst-case noise $\le 2049 < 3072$ (`0` decryption error).
#[expect(clippy::too_many_arguments, reason = "Preserve the explicit statement, role, witness and randomness bindings in this protocol API")]
pub fn rlwe_ot_transfer(
    session_id: &[u8; 32],
    sender_id: usize,
    receiver_id: usize,
    ot_idx: u32,
    req: &RlweOtReceiverMsg,
    seed0: &[u8; 32],
    seed1: &[u8; 32],
    rng: &mut PartyPrivateRng,
) -> RlweOtSenderMsg {
    match try_rlwe_ot_transfer(session_id, sender_id, receiver_id, ot_idx, req, seed0, seed1, rng) {
        Ok(message) => message,
        Err(error) => panic!("rlwe_ot_transfer simulation failed: {error}"),
    }
}

fn rlwe_ot_decrypt_with_crs(
    sec: &RlweOtReceiverSecret,
    a_ntt: &RlwePolyNtt,
    t_crs: &RlwePoly,
    resp: &RlweOtSenderMsg,
) -> Result<[u8; 32], PreprocessError> {
    let u_c = RlwePoly::ct_select(sec.choice_bit, &resp.u1, &resp.u0);
    let v_c = RlwePoly::ct_select(sec.choice_bit, &resp.v1, &resp.v0);
    let mut prod = u_c.mul_negacyclic(&sec.s_r);
    let mut diff = v_c.sub(&prod);
    let (mut seed_c, mut rho_c) = decode_seed64_from_poly_ct(&diff);
    wipe_u16s(&mut prod.0);
    wipe_u16s(&mut diff.0);

    let pk1 = sec.pk0.add(t_crs);
    let pk_c = RlwePoly::ct_select(sec.choice_bit, &pk1, &sec.pk0);
    let branch = black_box(sec.choice_bit as u8);
    let (u_exp, v_exp) = rlwe_fo_encrypt_branch(
        &sec.crs_coin,
        &sec.session_id,
        sec.sender_id,
        sec.receiver_id,
        sec.ot_idx,
        branch,
        a_ntt,
        &pk_c,
        &seed_c,
        &rho_c,
    );
    wipe_bytes32(&mut rho_c);
    if !(u_exp.ct_eq(&u_c) && v_exp.ct_eq(&v_c)) {
        wipe_bytes32(&mut seed_c);
        return Err(PreprocessError::BaseOtFoCheckFailed {
            sender_id: sec.sender_id,
            receiver_id: sec.receiver_id,
            ot_idx: sec.ot_idx,
        });
    }
    Ok(seed_c)
}

/// Receiver Round-3: branchlessly select `(u_c, v_c)`, recover `(seed_c, rho_c)`, and **actively
/// re-encrypt `(u_c, v_c)` from `rho_c`** (`Err(BaseOtFoCheckFailed)` if the Sender deviated!).
pub fn rlwe_ot_decrypt(
    sec: &RlweOtReceiverSecret,
    resp: &RlweOtSenderMsg,
) -> Result<[u8; 32], PreprocessError> {
    let a_ntt = RlwePoly::from_crs_xof_with_coin(
        &sec.crs_coin,
        &sec.session_id,
        sec.sender_id,
        sec.receiver_id,
        0,
        0,
    )
    .to_ntt();
    let t_crs = RlwePoly::from_crs_xof_with_coin(
        &sec.crs_coin,
        &sec.session_id,
        sec.sender_id,
        sec.receiver_id,
        sec.ot_idx,
        1,
    );
    rlwe_ot_decrypt_with_crs(sec, &a_ntt, &t_crs, resp)
}

// ============================================================================
// 2. Committed CRS + 4-Ciphertext `384 -> 128` Parity OT Combiner & Interactive 128-Col `KOS15`
// ============================================================================

/// Expand the 2-universal systematic Leftover-Hash matrix $E = [I_{128} \mid R_{128 \times 256}] \in \mathbb{F}_2^{128 \times 384}$
/// from the post-Base-OT public combiner coin. Every row `i` is `[u64; 6]` (`384` bits).
fn derive_extractor_matrix_128x384(
    session_id: &[u8; 32],
    ext_sender_id: usize,
    ext_receiver_id: usize,
    combiner_coin: &[u8; 32],
) -> [[u64; RLWE_BASE_OT_WORDS]; 128] {
    let mut xof = Cshake256Xof::new(b"QSAG.OT.COMBINER.EXT/v1");
    xof.absorb(session_id);
    xof.absorb(&(ext_sender_id as u64).to_be_bytes());
    xof.absorb(&(ext_receiver_id as u64).to_be_bytes());
    xof.absorb(combiner_coin);
    let mut raw = [0u8; 128 * 32];
    xof.squeeze(&mut raw);

    let mut mat = [[0u64; RLWE_BASE_OT_WORDS]; 128];
    for row in 0..128 {
        mat[row][row / 64] = 1u64 << (row % 64);
        let base = 32 * row;
        for w in 0..4 {
            let o = base + 8 * w;
            mat[row][2 + w] = u64::from_le_bytes([
                raw[o],
                raw[o + 1],
                raw[o + 2],
                raw[o + 3],
                raw[o + 4],
                raw[o + 5],
                raw[o + 6],
                raw[o + 7],
            ]);
        }
    }
    mat
}

/// Fast single-block `keccak_f1600` PRF (`0` heap allocations!) for the 4-ciphertext parity combiner.
#[inline]
fn combiner_step_hash32(
    session_id: &[u8; 32],
    row_idx: usize,
    step_idx: usize,
    beta: u8,
    gamma: u8,
    label_a: &[u8; 32],
    seed_b: &[u8; 32],
) -> [u8; 32] {
    let mut st = [0u64; 25];
    st[0] = u64::from_le_bytes(*b"QSAG.OT.");
    st[1] = u64::from_le_bytes(*b"PARCOMB1");
    for i in 0..4 {
        let o = 8 * i;
        st[2 + i] = u64::from_le_bytes(core::array::from_fn(|array_index| (session_id[o..o + 8])[array_index]));
        st[6 + i] = u64::from_le_bytes(core::array::from_fn(|array_index| (label_a[o..o + 8])[array_index]));
        st[10 + i] = u64::from_le_bytes(core::array::from_fn(|array_index| (seed_b[o..o + 8])[array_index]));
    }
    st[14] = ((row_idx as u64) << 32)
        | ((step_idx as u64) << 8)
        | ((beta as u64) << 1)
        | (gamma as u64);
    st[15] = 0x1f;
    st[16] = 0x8000_0000_0000_0000;
    keccak_f1600(&mut st);
    let mut out = [0u8; 32];
    for i in 0..4 {
        out[8 * i..8 * i + 8].copy_from_slice(&st[i].to_le_bytes());
    }
    wipe_u64s(&mut st);
    out
}

#[inline]
fn ct_select_bytes32_4(table: &[[u8; 32]; 4], secret_idx: u8) -> [u8; 32] {
    let mut out = [0u8; 32];
    for k in 0..4u8 {
        let diff = black_box(secret_idx ^ k);
        let is_zero = 1u8.wrapping_sub(((diff | diff.wrapping_neg()) >> 7) & 1);
        let mask = 0u8.wrapping_sub(is_zero);
        for b in 0..32 {
            out[b] |= table[k as usize][b] & mask;
        }
    }
    out
}

/// Wire message 0a (`OT-Ext Receiver -> OT-Ext Sender`): commitment to CRS coin share before CRS exists.
#[derive(Clone, Copy, Debug)]
pub struct BaseOtCrsCommitMsg {
    pub receiver_crs_commit: [u8; 32],
}

/// Wire message 0b (`OT-Ext Sender -> OT-Ext Receiver`): Sender's CRS coin share.
#[derive(Clone, Copy, Debug)]
pub struct BaseOtCrsShareMsg {
    pub sender_crs_share: [u8; 32],
}

/// Wire message 0c (`OT-Ext Receiver -> OT-Ext Sender`): opening of Receiver's committed CRS coin share.
#[derive(Clone, Copy, Debug)]
pub struct BaseOtCrsOpenMsg {
    pub receiver_crs_share: [u8; 32],
}

/// Isolated CRS Round-0 state for `OT-Ext Receiver` (`!Clone`, wiped on `Drop`).
pub struct BaseOtCrsReceiverRound0 {
    my_crs_share: [u8; 32],
}

impl Drop for BaseOtCrsReceiverRound0 {
    fn drop(&mut self) {
        wipe_bytes32(&mut self.my_crs_share);
    }
}

impl BaseOtCrsReceiverRound0 {
    pub fn commit(
        session_id: [u8; 32],
        ext_sender_id: usize,
        ext_receiver_id: usize,
        receiver_rng: &mut PartyPrivateRng,
    ) -> (Self, BaseOtCrsCommitMsg) {
        let my_crs_share = receiver_rng.next_bytes32();
        let receiver_crs_commit = commit_crs_coin_share(
            &session_id,
            ext_sender_id,
            ext_receiver_id,
            ext_receiver_id,
            &my_crs_share,
        );
        (
            Self { my_crs_share },
            BaseOtCrsCommitMsg {
                receiver_crs_commit,
            },
        )
    }

    pub fn open_and_derive_crs_coin(
        self,
        sender_msg: &BaseOtCrsShareMsg,
    ) -> ([u8; 32], BaseOtCrsOpenMsg) {
        let mut crs_coin = [0u8; 32];
        for (b, crs_coin_b_item) in crs_coin[..32].iter_mut().enumerate() {
            *crs_coin_b_item = self.my_crs_share[b] ^ sender_msg.sender_crs_share[b];
        }
        (
            crs_coin,
            BaseOtCrsOpenMsg {
                receiver_crs_share: self.my_crs_share,
            },
        )
    }
}

/// Isolated CRS Round-0 state for `OT-Ext Sender` (`!Clone`, wiped on `Drop`).
pub struct BaseOtCrsSenderRound0 {
    session_id: [u8; 32],
    ext_sender_id: usize,
    ext_receiver_id: usize,
    peer_crs_commit: [u8; 32],
    my_crs_share: [u8; 32],
}

impl Drop for BaseOtCrsSenderRound0 {
    fn drop(&mut self) {
        wipe_bytes32(&mut self.my_crs_share);
    }
}

impl BaseOtCrsSenderRound0 {
    pub fn respond(
        session_id: [u8; 32],
        ext_sender_id: usize,
        ext_receiver_id: usize,
        commit_msg: &BaseOtCrsCommitMsg,
        sender_rng: &mut PartyPrivateRng,
    ) -> (Self, BaseOtCrsShareMsg) {
        let my_crs_share = sender_rng.next_bytes32();
        (
            Self {
                session_id,
                ext_sender_id,
                ext_receiver_id,
                peer_crs_commit: commit_msg.receiver_crs_commit,
                my_crs_share,
            },
            BaseOtCrsShareMsg {
                sender_crs_share: my_crs_share,
            },
        )
    }

    pub fn verify_and_derive_crs_coin(
        self,
        open_msg: &BaseOtCrsOpenMsg,
    ) -> Result<[u8; 32], PreprocessError> {
        let exp = commit_crs_coin_share(
            &self.session_id,
            self.ext_sender_id,
            self.ext_receiver_id,
            self.ext_receiver_id,
            &open_msg.receiver_crs_share,
        );
        if !ct_eq_bytes32(&exp, &self.peer_crs_commit) {
            return Err(PreprocessError::CoinCommitMismatch {
                party_id: self.ext_receiver_id,
            });
        }
        let mut crs_coin = [0u8; 32];
        for (b, crs_coin_b_item) in crs_coin[..32].iter_mut().enumerate() {
            *crs_coin_b_item = open_msg.receiver_crs_share[b] ^ self.my_crs_share[b];
        }
        Ok(crs_coin)
    }
}

/// Wire message 1 of per-party OT-extension channel setup (`OT-Ext Sender -> OT-Ext Receiver`,
/// containing `384` random-choice Ring-LWE Base-OT requests + OR-Sigma ZKPoKs).
#[derive(Clone, Debug)]
pub struct BaseOtRound1Msg {
    pub reqs: Vec<RlweOtReceiverMsg>,
}

/// Wire message 2 of per-party OT-extension channel setup (`OT-Ext Receiver -> OT-Ext Sender`,
/// containing `384` FO-encrypted Ring-LWE Base-OT responses + combiner coin commitment).
#[derive(Clone, Debug)]
pub struct BaseOtRound2Msg {
    pub resps: Vec<RlweOtSenderMsg>,
    pub receiver_coin_commit: [u8; 32],
}

/// Wire message 3 (`OT-Ext Sender -> OT-Ext Receiver`: combiner coin share after FO check passes).
#[derive(Clone, Debug)]
pub struct BaseOtRound3Msg {
    pub sender_coin_share: [u8; 32],
}

/// Wire message 4 (`OT-Ext Receiver -> OT-Ext Sender`: opening of committed combiner coin share +
/// 4-ciphertext parity combiner tables folding `384` Base OTs into `128` active-secure Base OTs).
#[derive(Clone, Debug)]
pub struct BaseOtRound4Msg {
    pub receiver_coin_share: [u8; 32],
    pub parity_tables: Vec<Vec<[[u8; 32]; 4]>>,
}

/// Isolated single-party Round-1 state for the OT-Ext Sender (Base-OT Receiver).
pub struct BaseOtExtSenderRound1 {
    crs_coin: [u8; 32],
    session_id: [u8; 32],
    ext_sender_id: usize,
    ext_receiver_id: usize,
    c_tilde_words: [u64; RLWE_BASE_OT_WORDS],
    sec_states: Vec<RlweOtReceiverSecret>,
}

impl Drop for BaseOtExtSenderRound1 {
    fn drop(&mut self) {
        wipe_u64s(&mut self.c_tilde_words);
    }
}

/// Isolated single-party Round-2 state for the OT-Ext Receiver (Base-OT Sender).
pub struct BaseOtExtReceiverRound2 {
    session_id: [u8; 32],
    ext_sender_id: usize,
    ext_receiver_id: usize,
    base_seed_pairs: Vec<([u8; 32], [u8; 32])>,
    my_coin_share: [u8; 32],
    combiner_prf_seed: [u8; 32],
}

impl Drop for BaseOtExtReceiverRound2 {
    fn drop(&mut self) {
        for (s0, s1) in &mut self.base_seed_pairs {
            wipe_bytes32(s0);
            wipe_bytes32(s1);
        }
        wipe_bytes32(&mut self.my_coin_share);
        wipe_bytes32(&mut self.combiner_prf_seed);
    }
}

/// Isolated single-party Round-3 state for the OT-Ext Sender after all 384 FO checks pass.
pub struct BaseOtExtSenderRound3 {
    session_id: [u8; 32],
    ext_sender_id: usize,
    ext_receiver_id: usize,
    c_tilde_words: [u64; RLWE_BASE_OT_WORDS],
    base_seeds: Vec<[u8; 32]>,
    peer_coin_commit: [u8; 32],
    my_coin_share: [u8; 32],
}

impl Drop for BaseOtExtSenderRound3 {
    fn drop(&mut self) {
        wipe_u64s(&mut self.c_tilde_words);
        for s in &mut self.base_seeds {
            wipe_bytes32(s);
        }
        wipe_bytes32(&mut self.my_coin_share);
    }
}

fn commit_crs_coin_share(
    session_id: &[u8; 32],
    ext_sender_id: usize,
    ext_receiver_id: usize,
    party_id: usize,
    share: &[u8; 32],
) -> [u8; 32] {
    let s_be = (ext_sender_id as u64).to_be_bytes();
    let r_be = (ext_receiver_id as u64).to_be_bytes();
    let p_be = (party_id as u64).to_be_bytes();
    cshake256_32(
        b"QSAG.OT.CRS.COMMIT/v1",
        &encode_multi_frame(&[session_id, &s_be, &r_be, &p_be, share]),
    )
}

fn commit_combiner_coin_share(
    session_id: &[u8; 32],
    ext_sender_id: usize,
    ext_receiver_id: usize,
    party_id: usize,
    share: &[u8; 32],
) -> [u8; 32] {
    let s_be = (ext_sender_id as u64).to_be_bytes();
    let r_be = (ext_receiver_id as u64).to_be_bytes();
    let p_be = (party_id as u64).to_be_bytes();
    cshake256_32(
        b"QSAG.OT.COMBINER.COMMIT/v1",
        &encode_multi_frame(&[session_id, &s_be, &r_be, &p_be, share]),
    )
}

impl BaseOtExtSenderRound1 {
    /// Step 1 (`OT-Ext Sender` local) bound to a jointly committed CRS coin `crs_coin`.
    pub fn start_with_crs(
        crs_coin: [u8; 32],
        session_id: [u8; 32],
        ext_sender_id: usize,
        ext_receiver_id: usize,
        sender_rng: &mut PartyPrivateRng,
    ) -> (Self, BaseOtRound1Msg) {
        let mut c_tilde_words = [0u64; RLWE_BASE_OT_WORDS];
        for w in &mut c_tilde_words {
            *w = sender_rng.next_u64();
        }
        let a_ntt = RlwePoly::from_crs_xof_with_coin(
            &crs_coin,
            &session_id,
            ext_receiver_id,
            ext_sender_id,
            0,
            0,
        )
        .to_ntt();
        let mut sec_states = Vec::with_capacity(RLWE_BASE_OT_COUNT);
        let mut reqs = Vec::with_capacity(RLWE_BASE_OT_COUNT);
        for m in 0..RLWE_BASE_OT_COUNT {
            let bit = ((c_tilde_words[m / 64] >> (m % 64)) & 1) == 1;
            let t_crs = RlwePoly::from_crs_xof_with_coin(
                &crs_coin,
                &session_id,
                ext_receiver_id,
                ext_sender_id,
                m as u32,
                1,
            );
            let (sec, msg) = rlwe_ot_choose_with_crs(
                &crs_coin,
                &session_id,
                ext_receiver_id,
                ext_sender_id,
                m as u32,
                &a_ntt,
                &t_crs,
                bit,
                sender_rng,
            );
            sec_states.push(sec);
            reqs.push(msg);
        }
        (
            Self {
                crs_coin,
                session_id,
                ext_sender_id,
                ext_receiver_id,
                c_tilde_words,
                sec_states,
            },
            BaseOtRound1Msg { reqs },
        )
    }

    /// Step 1 (`OT-Ext Sender` local): sample 384 random Base-OT choice bits $\tilde{\mathbf{c}}$
    /// using ONLY `sender_rng` and emit `BaseOtRound1Msg` (including 384 OR-Sigma ZKPoKs).
    pub fn start(
        session_id: [u8; 32],
        ext_sender_id: usize,
        ext_receiver_id: usize,
        sender_rng: &mut PartyPrivateRng,
    ) -> (Self, BaseOtRound1Msg) {
        Self::start_with_crs([0u8; 32], session_id, ext_sender_id, ext_receiver_id, sender_rng)
    }

    /// Step 3 (`OT-Ext Sender` local): verify all 384 Fujisaki–Okamoto re-encryptions in **strict
    /// constant time across all 384 branches** (`0` early-abort index timing leak!) before sampling
    /// or revealing any combiner coin.
    pub fn verify_fo_and_respond_coin(
        mut self,
        msg2: &BaseOtRound2Msg,
        sender_rng: &mut PartyPrivateRng,
    ) -> Result<(BaseOtExtSenderRound3, BaseOtRound3Msg), PreprocessError> {
        if msg2.reqs_len_mismatch(RLWE_BASE_OT_COUNT) {
            return Err(PreprocessError::BaseOtFoCheckFailed {
                sender_id: self.ext_receiver_id,
                receiver_id: self.ext_sender_id,
                ot_idx: 0,
            });
        }
        let a_ntt = RlwePoly::from_crs_xof_with_coin(
            &self.crs_coin,
            &self.session_id,
            self.ext_receiver_id,
            self.ext_sender_id,
            0,
            0,
        )
        .to_ntt();
        let mut base_seeds = vec![[0u8; 32]; RLWE_BASE_OT_COUNT];
        let mut all_ok = 1u8;
        for (m, base_seeds_m_item) in base_seeds[..RLWE_BASE_OT_COUNT].iter_mut().enumerate() {
            let t_crs = RlwePoly::from_crs_xof_with_coin(
                &self.crs_coin,
                &self.session_id,
                self.ext_receiver_id,
                self.ext_sender_id,
                m as u32,
                1,
            );
            match rlwe_ot_decrypt_with_crs(&self.sec_states[m], &a_ntt, &t_crs, &msg2.resps[m]) {
                Ok(seed_m) => {
                    *base_seeds_m_item = seed_m;
                }
                Err(_) => {
                    all_ok = 0;
                }
            }
        }
        if black_box(all_ok) == 0 {
            for s in &mut base_seeds {
                wipe_bytes32(s);
            }
            return Err(PreprocessError::BaseOtFoCheckFailed {
                sender_id: self.ext_receiver_id,
                receiver_id: self.ext_sender_id,
                ot_idx: 0,
            });
        }
        let my_coin_share = sender_rng.next_bytes32();
        let c_tilde_words = self.c_tilde_words;
        wipe_u64s(&mut self.c_tilde_words);
        Ok((
            BaseOtExtSenderRound3 {
                session_id: self.session_id,
                ext_sender_id: self.ext_sender_id,
                ext_receiver_id: self.ext_receiver_id,
                c_tilde_words,
                base_seeds,
                peer_coin_commit: msg2.receiver_coin_commit,
                my_coin_share,
            },
            BaseOtRound3Msg {
                sender_coin_share: my_coin_share,
            },
        ))
    }

    /// Alias for [`Self::verify_fo_and_respond_coin`].
    #[inline]
    pub fn verify_fo_and_commit_coin(
        self,
        msg2: &BaseOtRound2Msg,
        sender_rng: &mut PartyPrivateRng,
    ) -> Result<(BaseOtExtSenderRound3, BaseOtRound3Msg), PreprocessError> {
        self.verify_fo_and_respond_coin(msg2, sender_rng)
    }
}

impl BaseOtRound2Msg {
    #[inline]
    fn reqs_len_mismatch(&self, expected: usize) -> bool {
        self.resps.len() != expected
    }
}

impl BaseOtExtReceiverRound2 {
    /// Step 2 (`OT-Ext Receiver` local) bound to jointly committed `crs_coin`: verifies all 384
    /// Receiver OR-Sigma ZKPoKs (`BaseOtReceiverProofFailed` on tamper!) before FO-encrypting seeds.
    pub fn respond_with_crs(
        crs_coin: [u8; 32],
        session_id: [u8; 32],
        ext_sender_id: usize,
        ext_receiver_id: usize,
        msg1: &BaseOtRound1Msg,
        receiver_rng: &mut PartyPrivateRng,
    ) -> Result<(Self, BaseOtRound2Msg), PreprocessError> {
        if msg1.reqs.len() != RLWE_BASE_OT_COUNT {
            return Err(PreprocessError::BaseOtFoCheckFailed {
                sender_id: ext_receiver_id,
                receiver_id: ext_sender_id,
                ot_idx: 0,
            });
        }
        let a_ntt = RlwePoly::from_crs_xof_with_coin(
            &crs_coin,
            &session_id,
            ext_receiver_id,
            ext_sender_id,
            0,
            0,
        )
        .to_ntt();
        let mut base_seed_pairs = Vec::with_capacity(RLWE_BASE_OT_COUNT);
        let mut resps = Vec::with_capacity(RLWE_BASE_OT_COUNT);
        for (m, req) in msg1.reqs.iter().enumerate() {
            let mut s0 = receiver_rng.next_bytes32();
            let mut s1 = receiver_rng.next_bytes32();
            let t_crs = RlwePoly::from_crs_xof_with_coin(
                &crs_coin,
                &session_id,
                ext_receiver_id,
                ext_sender_id,
                m as u32,
                1,
            );
            match try_rlwe_ot_transfer_with_crs(
                &crs_coin,
                &session_id,
                ext_receiver_id,
                ext_sender_id,
                m as u32,
                &a_ntt,
                &t_crs,
                req,
                &s0,
                &s1,
                receiver_rng,
            ) {
                Ok(resp) => {
                    base_seed_pairs.push((s0, s1));
                    resps.push(resp);
                }
                Err(e) => {
                    wipe_bytes32(&mut s0);
                    wipe_bytes32(&mut s1);
                    for (p0, p1) in &mut base_seed_pairs {
                        wipe_bytes32(p0);
                        wipe_bytes32(p1);
                    }
                    return Err(e);
                }
            }
        }
        let my_coin_share = receiver_rng.next_bytes32();
        let combiner_prf_seed = receiver_rng.next_bytes32();
        let receiver_coin_commit = commit_combiner_coin_share(
            &session_id,
            ext_sender_id,
            ext_receiver_id,
            ext_receiver_id,
            &my_coin_share,
        );
        Ok((
            Self {
                session_id,
                ext_sender_id,
                ext_receiver_id,
                base_seed_pairs,
                my_coin_share,
                combiner_prf_seed,
            },
            BaseOtRound2Msg {
                resps,
                receiver_coin_commit,
            },
        ))
    }

    /// Step 2 (`OT-Ext Receiver` local): verify 384 OR-Sigma ZKPoKs and FO-encrypt 384 seed pairs.
    pub fn respond(
        session_id: [u8; 32],
        ext_sender_id: usize,
        ext_receiver_id: usize,
        msg1: &BaseOtRound1Msg,
        receiver_rng: &mut PartyPrivateRng,
    ) -> Result<(Self, BaseOtRound2Msg), PreprocessError> {
        Self::respond_with_crs(
            [0u8; 32],
            session_id,
            ext_sender_id,
            ext_receiver_id,
            msg1,
            receiver_rng,
        )
    }

    /// Step 4 (`OT-Ext Receiver` local): receive Sender's coin share, open Receiver's committed coin
    /// share, fold the `384` Base OTs into `128` active-secure Base OTs via 4-ciphertext parity
    /// combiner tables, wipe all 384 raw Base-OT seeds, and build [`OtExtReceiverChannel`].
    pub fn finalize(mut self, msg3: &BaseOtRound3Msg) -> (OtExtReceiverChannel, BaseOtRound4Msg) {
        let mut combined_coin = [0u8; 32];
        for (b, combined_coin_b_item) in combined_coin[..32].iter_mut().enumerate() {
            *combined_coin_b_item = self.my_coin_share[b] ^ msg3.sender_coin_share[b];
        }
        let extractor = derive_extractor_matrix_128x384(
            &self.session_id,
            self.ext_sender_id,
            self.ext_receiver_id,
            &combined_coin,
        );
        let mut comb_rng =
            PartyPrivateRng::from_seed(self.combiner_prf_seed, b"QSAG.OT.PARCOMB.RNG/v1");
        wipe_bytes32(&mut self.combiner_prf_seed);

        let mut combined_seed_pairs = [([0u8; 32], [0u8; 32]); 128];
        let mut parity_tables = Vec::with_capacity(128);

        for row in 0..128 {
            let mut support = Vec::with_capacity(192);
            for m in 0..RLWE_BASE_OT_COUNT {
                if ((extractor[row][m / 64] >> (m % 64)) & 1) == 1 {
                    support.push(m);
                }
            }
            let m0 = support[0];
            let mut cur_l0 = combiner_step_hash32(
                &self.session_id,
                row,
                0,
                0,
                0,
                &[0u8; 32],
                &self.base_seed_pairs[m0].0,
            );
            let mut cur_l1 = combiner_step_hash32(
                &self.session_id,
                row,
                0,
                0,
                1,
                &[0u8; 32],
                &self.base_seed_pairs[m0].1,
            );

            let mut row_tables = Vec::with_capacity(support.len().saturating_sub(1));
            for (step_minus1, &mr) in support.iter().skip(1).enumerate() {
                let step = step_minus1 + 1;
                let next_l0 = comb_rng.next_bytes32();
                let next_l1 = comb_rng.next_bytes32();
                let mut tbl = [[0u8; 32]; 4];
                for beta in 0..2u8 {
                    let la = if beta == 0 { &cur_l0 } else { &cur_l1 };
                    for gamma in 0..2u8 {
                        let sb = if gamma == 0 {
                            &self.base_seed_pairs[mr].0
                        } else {
                            &self.base_seed_pairs[mr].1
                        };
                        let pad =
                            combiner_step_hash32(&self.session_id, row, step, beta, gamma, la, sb);
                        let target = if (beta ^ gamma) == 0 {
                            &next_l0
                        } else {
                            &next_l1
                        };
                        let slot = (2 * beta + gamma) as usize;
                        for b in 0..32 {
                            tbl[slot][b] = target[b] ^ pad[b];
                        }
                    }
                }
                wipe_bytes32(&mut cur_l0);
                wipe_bytes32(&mut cur_l1);
                cur_l0 = next_l0;
                cur_l1 = next_l1;
                row_tables.push(tbl);
            }
            combined_seed_pairs[row] = (cur_l0, cur_l1);
            parity_tables.push(row_tables);
        }

        for (s0, s1) in &mut self.base_seed_pairs {
            wipe_bytes32(s0);
            wipe_bytes32(s1);
        }
        let msg4 = BaseOtRound4Msg {
            receiver_coin_share: self.my_coin_share,
            parity_tables,
        };
        (
            OtExtReceiverChannel {
                session_id: self.session_id,
                sender_id: self.ext_sender_id,
                receiver_id: self.ext_receiver_id,
                combined_seed_pairs,
                batch_ctr: 0,
            },
            msg4,
        )
    }
}

impl BaseOtExtSenderRound3 {
    /// Step 5 (`OT-Ext Sender` local): verify Receiver's coin commitment, evaluate all 128 parity
    /// combiner chains in constant time to obtain `delta = E * c_tilde` and `combined_seeds[0..128]`,
    /// wipe `c_tilde_words` and `base_seeds`, and finalize [`OtExtSenderChannel`].
    pub fn finalize(
        mut self,
        msg4: &BaseOtRound4Msg,
    ) -> Result<OtExtSenderChannel, PreprocessError> {
        let expected_commit = commit_combiner_coin_share(
            &self.session_id,
            self.ext_sender_id,
            self.ext_receiver_id,
            self.ext_receiver_id,
            &msg4.receiver_coin_share,
        );
        if !ct_eq_bytes32(&expected_commit, &self.peer_coin_commit) {
            return Err(PreprocessError::CoinCommitMismatch {
                party_id: self.ext_receiver_id,
            });
        }
        if msg4.parity_tables.len() != 128 {
            return Err(PreprocessError::KosOtCheckFailed {
                sender_id: self.ext_sender_id,
                receiver_id: self.ext_receiver_id,
            });
        }
        let mut combined_coin = [0u8; 32];
        for (b, combined_coin_b_item) in combined_coin[..32].iter_mut().enumerate() {
            *combined_coin_b_item = msg4.receiver_coin_share[b] ^ self.my_coin_share[b];
        }
        let extractor = derive_extractor_matrix_128x384(
            &self.session_id,
            self.ext_sender_id,
            self.ext_receiver_id,
            &combined_coin,
        );
        let mut delta = 0u128;
        let mut combined_seeds = [[0u8; 32]; 128];

        for row in 0..128 {
            let mut support = Vec::with_capacity(192);
            for m in 0..RLWE_BASE_OT_COUNT {
                if ((extractor[row][m / 64] >> (m % 64)) & 1) == 1 {
                    support.push(m);
                }
            }
            if msg4.parity_tables[row].len() + 1 != support.len() {
                return Err(PreprocessError::KosOtCheckFailed {
                    sender_id: self.ext_sender_id,
                    receiver_id: self.ext_receiver_id,
                });
            }
            let m0 = support[0];
            let mut acc_bit = ((black_box(self.c_tilde_words[m0 / 64]) >> (m0 % 64)) & 1) as u8;
            let mut cur_label = combiner_step_hash32(
                &self.session_id,
                row,
                0,
                0,
                acc_bit,
                &[0u8; 32],
                &self.base_seeds[m0],
            );

            for (step_minus1, &mr) in support.iter().skip(1).enumerate() {
                let step = step_minus1 + 1;
                let gamma = ((black_box(self.c_tilde_words[mr / 64]) >> (mr % 64)) & 1) as u8;
                let slot = (acc_bit << 1) | gamma;
                let ct_entry = ct_select_bytes32_4(&msg4.parity_tables[row][step_minus1], slot);
                let pad = combiner_step_hash32(
                    &self.session_id,
                    row,
                    step,
                    acc_bit,
                    gamma,
                    &cur_label,
                    &self.base_seeds[mr],
                );
                for b in 0..32 {
                    cur_label[b] = ct_entry[b] ^ pad[b];
                }
                acc_bit ^= gamma;
            }
            delta |= (acc_bit as u128) << row;
            combined_seeds[row] = cur_label;
        }

        wipe_u64s(&mut self.c_tilde_words);
        for s in &mut self.base_seeds {
            wipe_bytes32(s);
        }
        Ok(OtExtSenderChannel {
            session_id: self.session_id,
            sender_id: self.ext_sender_id,
            receiver_id: self.ext_receiver_id,
            delta,
            combined_seeds,
            batch_ctr: 0,
            poisoned: false,
        })
    }
}

/// Established 128-column parity-combined Ring-LWE OT-Extension Sender channel (`!Clone`, wiped on
/// `Drop`, permanently poisoned and zeroed on first `KosOtCheckFailed`!).
pub struct OtExtSenderChannel {
    pub session_id: [u8; 32],
    pub sender_id: usize,
    pub receiver_id: usize,
    delta: u128,
    combined_seeds: [[u8; 32]; 128],
    batch_ctr: u64,
    poisoned: bool,
}

impl OtExtSenderChannel {
    fn poison_and_wipe(&mut self) {
        self.poisoned = true;
        self.delta = 0;
        black_box(&mut self.delta);
        for s in &mut self.combined_seeds {
            wipe_bytes32(s);
        }
    }
}

impl Drop for OtExtSenderChannel {
    fn drop(&mut self) {
        self.poison_and_wipe();
    }
}

/// Established 128-column parity-combined Ring-LWE OT-Extension Receiver channel (`!Clone`, wiped on `Drop`).
pub struct OtExtReceiverChannel {
    pub session_id: [u8; 32],
    pub sender_id: usize,
    pub receiver_id: usize,
    combined_seed_pairs: [([u8; 32], [u8; 32]); 128],
    batch_ctr: u64,
}

impl Drop for OtExtReceiverChannel {
    fn drop(&mut self) {
        for (s0, s1) in &mut self.combined_seed_pairs {
            wipe_bytes32(s0);
            wipe_bytes32(s1);
        }
    }
}

/// Execute the full committed-CRS + OR-Sigma ZKPoK + 384-branch FO + 4-ciphertext `384 -> 128`
/// parity combiner handshake over explicit per-party wire messages.
pub fn try_establish_rlwe_ot_ext_channel(
    session_id: [u8; 32],
    sender_id: usize,
    receiver_id: usize,
    sender_rng: &mut PartyPrivateRng,
    receiver_rng: &mut PartyPrivateRng,
) -> Result<(OtExtSenderChannel, OtExtReceiverChannel), PreprocessError> {
    let (crs_r0, crs_com) =
        BaseOtCrsReceiverRound0::commit(session_id, sender_id, receiver_id, receiver_rng);
    let (crs_s0, crs_sh) = BaseOtCrsSenderRound0::respond(
        session_id,
        sender_id,
        receiver_id,
        &crs_com,
        sender_rng,
    );
    let (r_crs_coin, crs_open) = crs_r0.open_and_derive_crs_coin(&crs_sh);
    let s_crs_coin = crs_s0.verify_and_derive_crs_coin(&crs_open)?;

    let (s_r1, msg1) = BaseOtExtSenderRound1::start_with_crs(
        s_crs_coin,
        session_id,
        sender_id,
        receiver_id,
        sender_rng,
    );
    let (r_r2, msg2) = BaseOtExtReceiverRound2::respond_with_crs(
        r_crs_coin,
        session_id,
        sender_id,
        receiver_id,
        &msg1,
        receiver_rng,
    )?;
    let (s_r3, msg3) = s_r1.verify_fo_and_respond_coin(&msg2, sender_rng)?;
    let (r_chan, msg4) = r_r2.finalize(&msg3);
    let s_chan = s_r3.finalize(&msg4)?;
    Ok((s_chan, r_chan))
}

/// Ideal base-OT functionality for unit tests of the OT extension and its
/// consumers. Production never compiles this constructor. Base proofs, FO,
/// committed CRS and KOS attacks have separate default regressions; the complete
/// 384-transfer bootstrap has an explicit integration soak test.
#[cfg(test)]
fn ideal_ot_ext_channel_for_test(
    session_id: [u8; 32], sender_id: usize, receiver_id: usize,
    sender_rng: &mut PartyPrivateRng, receiver_rng: &mut PartyPrivateRng,
) -> (OtExtSenderChannel, OtExtReceiverChannel) {
    let delta = u128::from(sender_rng.next_u64()) | (u128::from(sender_rng.next_u64()) << 64);
    let pairs: [([u8; 32], [u8; 32]); 128] = core::array::from_fn(|_| (
        receiver_rng.next_bytes32(), receiver_rng.next_bytes32()));
    let selected = core::array::from_fn(|i| if (delta >> i) & 1 == 0 { pairs[i].0 } else { pairs[i].1 });
    (OtExtSenderChannel { session_id, sender_id, receiver_id, delta,
        combined_seeds: selected, batch_ctr: 0, poisoned: false },
     OtExtReceiverChannel { session_id, sender_id, receiver_id,
        combined_seed_pairs: pairs, batch_ctr: 0 })
}

/// Honest-simulation wrapper around [`try_establish_rlwe_ot_ext_channel`].
/// Unit-test builds use ideal base-OT correlations; the full bootstrap is tested
/// separately through the fallible entrypoint.
pub fn establish_rlwe_ot_ext_channel(
    session_id: [u8; 32],
    sender_id: usize,
    receiver_id: usize,
    sender_rng: &mut PartyPrivateRng,
    receiver_rng: &mut PartyPrivateRng,
) -> (OtExtSenderChannel, OtExtReceiverChannel) {
    #[cfg(test)]
    return ideal_ot_ext_channel_for_test(session_id, sender_id, receiver_id, sender_rng, receiver_rng);
    #[cfg(not(test))]
    match try_establish_rlwe_ot_ext_channel(session_id, sender_id, receiver_id, sender_rng, receiver_rng) {
        Ok(channels) => channels,
        Err(error) => panic!("base-OT simulation failed: {error}"),
    }
}

/// Interactive KOS OT-Extension Message 1 (`OT Receiver -> OT Sender`: locks `128` parity-combined
/// `u_cols` BEFORE Sender samples `chi_seed`!).
#[derive(Clone, Debug)]
pub struct KosOtUColsMsg {
    /// `128` active-secure combined bit-columns of length `padded_words` (`payload_words + 4` sacrificial words = +256 OTs).
    pub u_cols: Vec<Vec<u64>>,
}

/// Interactive KOS OT-Extension Message 2 (`OT Sender -> OT Receiver`: fresh 256-bit random challenge seed!).
#[derive(Clone, Copy, Debug)]
pub struct KosOtChallengeMsg {
    pub chi_seed: [u8; 32],
}

/// Interactive KOS OT-Extension Message 3 (`OT Receiver -> OT Sender`: linear correlation proof `(x_kos, t_kos)`).
#[derive(Clone, Copy, Debug)]
pub struct KosOtProofMsg {
    pub x_kos: Tower128,
    pub t_kos: Tower128,
}

/// Ephemeral Receiver state awaiting `KosOtChallengeMsg` (`!Clone`, wiped on `Drop`).
pub struct KosOtReceiverPending {
    batch_ctr: u64,
    payload_words: usize,
    full_choices: Vec<u64>,
    t_rows: Vec<u128>,
    u_cols_digest: [u8; 32],
}

impl Drop for KosOtReceiverPending {
    fn drop(&mut self) {
        wipe_u64s(&mut self.full_choices);
        wipe_u128s(&mut self.t_rows);
    }
}

/// Ephemeral Sender state awaiting `KosOtProofMsg` (`!Clone`, wiped on `Drop`).
pub struct KosOtSenderPending {
    batch_ctr: u64,
    payload_words: usize,
    q_rows: Vec<u128>,
    u_cols_digest: [u8; 32],
    chi_seed: [u8; 32],
}

impl Drop for KosOtSenderPending {
    fn drop(&mut self) {
        wipe_u128s(&mut self.q_rows);
    }
}

#[inline]
fn expand_prg_column_u64s(
    session_id: &[u8; 32],
    batch_ctr: u64,
    col_idx: usize,
    seed: &[u8; 32],
    num_words: usize,
) -> Vec<u64> {
    let mut xof = Cshake256Xof::new(b"QSAG.OT.EXT.COL/v2");
    xof.absorb(session_id);
    xof.absorb(&batch_ctr.to_be_bytes());
    xof.absorb(&(col_idx as u64).to_be_bytes());
    xof.absorb(seed);
    let mut raw = vec![0u8; 8 * num_words];
    xof.squeeze(&mut raw);
    let mut words = Vec::with_capacity(num_words);
    #[expect(clippy::chunks_exact_to_as_chunks, reason = "Keep the workspace Rust 1.85 minimum; slice as_chunks requires a newer compiler")]
    for chunk in raw.chunks_exact(8) {
        words.push(u64::from_le_bytes([
            chunk[0], chunk[1], chunk[2], chunk[3], chunk[4], chunk[5], chunk[6], chunk[7],
        ]));
    }
    wipe_bytes(&mut raw);
    words
}

/// Transpose 128 bit-columns of `num_words` `u64`s into `64 * num_words` `u128` rows.
fn transpose_cols128_to_rows(cols: &[Vec<u64>], num_words: usize) -> Vec<u128> {
    debug_assert_eq!(cols.len(), 128);
    let total_rows = 64 * num_words;
    let mut rows = vec![0u128; total_rows];
    for w in 0..num_words {
        for half in 0..2 {
            let mut tile: [u64; 64] = core::array::from_fn(|i| cols[64 * half + i][w]);
            for stage in 0..6 {
                let shift = 1usize << stage;
                let mask = u64::MAX / ((1u64 << shift) + 1);
                for base in (0..64).step_by(2 * shift) {
                    for offset in 0..shift {
                        let a = base + offset;
                        let b = a + shift;
                        let delta = ((tile[a] >> shift) ^ tile[b]) & mask;
                        tile[a] ^= delta << shift;
                        tile[b] ^= delta;
                    }
                }
            }
            for i in 0..64 { rows[64 * w + i] |= (tile[i] as u128) << (64 * half); }
            wipe_u64s(&mut tile);
        }
    }
    rows
}

fn hash_kos_u_cols(
    session_id: &[u8; 32],
    sender_id: usize,
    receiver_id: usize,
    batch_ctr: u64,
    u_cols: &[Vec<u64>],
) -> [u8; 32] {
    let mut xof = Cshake256Xof::new(b"QSAG.OT.KOS.UCOLS/v2");
    xof.absorb(session_id);
    xof.absorb(&(sender_id as u64).to_be_bytes());
    xof.absorb(&(receiver_id as u64).to_be_bytes());
    xof.absorb(&batch_ctr.to_be_bytes());
    xof.absorb(&(u_cols.len() as u64).to_be_bytes());
    for col in u_cols {
        xof.absorb(&(col.len() as u64).to_be_bytes());
        for &w in col {
            xof.absorb(&w.to_le_bytes());
        }
    }
    let mut out = [0u8; 32];
    xof.squeeze(&mut out);
    out
}

fn compute_kos_transcript_bind(
    u_cols_digest: &[u8; 32],
    chi_seed: &[u8; 32],
    proof: &KosOtProofMsg,
) -> [u8; 32] {
    let x_bytes = proof.x_kos.0.to_le_bytes();
    let t_bytes = proof.t_kos.0.to_le_bytes();
    cshake256_32(
        b"QSAG.OT.KOS.BIND/v2",
        &encode_multi_frame(&[u_cols_digest, chi_seed, &x_bytes, &t_bytes]),
    )
}

/// Fast single-block `SHAKE256` transcript-bound correlation-robust hash
/// `H(session_id, transcript_bind, sender, receiver, batch, ell, row128) -> [u8; 48]`
/// (`128` bytes absorbed < `136` rate => `1` `keccak_f1600` call, `0` heap allocations!).
#[inline]
fn crh_ot_row_hash48(
    session_id: &[u8; 32],
    transcript_bind: &[u8; 32],
    sender_id: usize,
    receiver_id: usize,
    batch_ctr: u64,
    ell: u64,
    row: u128,
) -> [u8; 48] {
    let mut st = [0u64; 25];
    st[0] = u64::from_le_bytes(*b"QSAG.CRH");
    st[1] = u64::from_le_bytes(*b".OT.V002");
    for i in 0..4 {
        let o = 8 * i;
        st[2 + i] = u64::from_le_bytes(core::array::from_fn(|array_index| (session_id[o..o + 8])[array_index]));
        st[6 + i] = u64::from_le_bytes(core::array::from_fn(|array_index| (transcript_bind[o..o + 8])[array_index]));
    }
    st[10] = sender_id as u64;
    st[11] = receiver_id as u64;
    st[12] = batch_ctr;
    st[13] = ell;
    st[14] = row as u64;
    st[15] = (row >> 64) as u64;
    st[16] = 0x8000_0000_0000_001f;
    keccak_f1600(&mut st);
    let mut out = [0u8; 48];
    for i in 0..6 {
        out[8 * i..8 * i + 8].copy_from_slice(&st[i].to_le_bytes());
    }
    wipe_u64s(&mut st);
    out
}

fn derive_interactive_kos_challenges(
    session_id: &[u8; 32],
    sender_id: usize,
    receiver_id: usize,
    batch_ctr: u64,
    u_cols_digest: &[u8; 32],
    chi_seed: &[u8; 32],
    total_rows: usize,
) -> Vec<Tower128> {
    let mut xof = Cshake256Xof::new(b"QSAG.OT.KOS.ICHAL/v2");
    xof.absorb(session_id);
    xof.absorb(&(sender_id as u64).to_be_bytes());
    xof.absorb(&(receiver_id as u64).to_be_bytes());
    xof.absorb(&batch_ctr.to_be_bytes());
    xof.absorb(u_cols_digest);
    xof.absorb(chi_seed);
    let mut raw = vec![0u8; 16 * total_rows];
    xof.squeeze(&mut raw);
    #[expect(clippy::chunks_exact_to_as_chunks, reason = "Keep the workspace Rust 1.85 minimum; slice as_chunks requires a newer compiler")]
    raw.chunks_exact(16)
        .map(|c| {
            let mut b = [0u8; 16];
            b.copy_from_slice(c);
            Tower128(u128::from_le_bytes(b))
        })
        .collect()
}

// Pack consecutive products into the two existing assembly lanes. This is the
// same tower-field inner product as the scalar KOS equation, including tails.
fn kos_inner_product(rows: &[u128], challenges: &[Tower128]) -> Tower128 {
    assert_eq!(rows.len(), challenges.len());
    let mut total = Tower128::ZERO;
    for (values, weights) in rows.chunks(128).zip(challenges.chunks(128)) {
        let mut lhs = [[0u128; 2]; 64];
        let mut rhs = [[0u128; 2]; 64];
        for (i, (&value, weight)) in values.iter().zip(weights).enumerate() {
            lhs[i / 2][i % 2] = value;
            rhs[i / 2][i % 2] = weight.0;
        }
        let count = values.len().div_ceil(2);
        let mut folded = qsag_asm::tower128_bdoz_2lane_mac(&lhs[..count], &rhs[..count]);
        total = total.add(Tower128(folded[0] ^ folded[1]));
        crate::wipe::wipe_u128s(lhs.as_flattened_mut());
        crate::wipe::wipe_u128s(rhs.as_flattened_mut());
        crate::wipe::wipe_u128s(&mut folded);
    }
    total
}

impl OtExtReceiverChannel {
    /// Interactive KOS Step 1 (`OT Receiver -> OT Sender`): append 256 sacrificial random OTs,
    /// expand `128` parity-combined PRG columns, lock `KosOtUColsMsg` **before** seeing Sender's
    /// random `chi_seed`, and retain `KosOtReceiverPending`.
    pub fn round1_send_u_cols(
        &mut self,
        choice_words: &[u64],
        rng: &mut PartyPrivateRng,
    ) -> (KosOtReceiverPending, KosOtUColsMsg) {
        let payload_words = choice_words.len();
        let padded_words = payload_words + 4; // +256 sacrificial OTs masking x_kos & t_kos
        let batch_ctr = self.batch_ctr;
        self.batch_ctr = self.batch_ctr.wrapping_add(1);

        let mut full_choices = Vec::with_capacity(padded_words);
        full_choices.extend_from_slice(choice_words);
        for _ in 0..4 {
            full_choices.push(rng.next_u64());
        }

        let mut t0_cols = Vec::with_capacity(128);
        let mut u_cols = Vec::with_capacity(128);
        for i in 0..128 {
            let t0 = expand_prg_column_u64s(
                &self.session_id,
                batch_ctr,
                i,
                &self.combined_seed_pairs[i].0,
                padded_words,
            );
            let mut t1 = expand_prg_column_u64s(
                &self.session_id,
                batch_ctr,
                i,
                &self.combined_seed_pairs[i].1,
                padded_words,
            );
            let mut u = Vec::with_capacity(padded_words);
            for w in 0..padded_words {
                u.push(t0[w] ^ t1[w] ^ full_choices[w]);
            }
            wipe_u64s(&mut t1);
            t0_cols.push(t0);
            u_cols.push(u);
        }

        let t_rows = transpose_cols128_to_rows(&t0_cols, padded_words);
        for col in &mut t0_cols {
            wipe_u64s(col);
        }
        let u_cols_digest = hash_kos_u_cols(
            &self.session_id,
            self.sender_id,
            self.receiver_id,
            batch_ctr,
            &u_cols,
        );
        (
            KosOtReceiverPending {
                batch_ctr,
                payload_words,
                full_choices,
                t_rows,
                u_cols_digest,
            },
            KosOtUColsMsg { u_cols },
        )
    }

    /// Interactive KOS Step 3 (`OT Receiver -> OT Sender`): respond to `KosOtChallengeMsg` with
    /// `(x_kos, t_kos)` and derive transcript-bound receiver pads.
    pub fn round3_prove_and_finish(
        &self,
        mut pending: KosOtReceiverPending,
        chal: &KosOtChallengeMsg,
    ) -> (KosOtProofMsg, Vec<[u8; 48]>) {
        let total_rows = pending.t_rows.len();
        let chis = derive_interactive_kos_challenges(
            &self.session_id,
            self.sender_id,
            self.receiver_id,
            pending.batch_ctr,
            &pending.u_cols_digest,
            &chal.chi_seed,
            total_rows,
        );
        let mut x_kos = Tower128::ZERO;
        let t_kos = kos_inner_product(&pending.t_rows, &chis);
        for (ell, chis_ell_item) in chis[..total_rows].iter().enumerate() {
            let r_bit = ((pending.full_choices[ell / 64] >> (ell % 64)) & 1) as u128;
            let mask = 0u128.wrapping_sub(black_box(r_bit));
            x_kos = x_kos.add(Tower128(chis_ell_item.0 & mask));
        }
        wipe_u64s(&mut pending.full_choices);

        let proof = KosOtProofMsg { x_kos, t_kos };
        let bind = compute_kos_transcript_bind(&pending.u_cols_digest, &chal.chi_seed, &proof);
        let payload_rows = 64 * pending.payload_words;
        let mut pads = Vec::with_capacity(payload_rows);
        for ell in 0..payload_rows {
            pads.push(crh_ot_row_hash48(
                &self.session_id,
                &bind,
                self.sender_id,
                self.receiver_id,
                pending.batch_ctr,
                ell as u64,
                pending.t_rows[ell],
            ));
        }
        (proof, pads)
    }
}

impl OtExtSenderChannel {
    /// Interactive KOS Step 2 (`OT Sender -> OT Receiver`): validate 128-column `KosOtUColsMsg`,
    /// expand `q_rows`, and sample a **fresh** 256-bit `chi_seed` *after* `u_cols` is locked.
    pub fn round2_sample_challenge(
        &mut self,
        u_msg: &KosOtUColsMsg,
        sender_rng: &mut PartyPrivateRng,
    ) -> Result<(KosOtSenderPending, KosOtChallengeMsg), PreprocessError> {
        if self.poisoned {
            return Err(PreprocessError::ChannelPoisoned {
                sender_id: self.sender_id,
                receiver_id: self.receiver_id,
            });
        }
        if u_msg.u_cols.len() != 128 {
            self.poison_and_wipe();
            return Err(PreprocessError::KosOtCheckFailed {
                sender_id: self.sender_id,
                receiver_id: self.receiver_id,
            });
        }
        let padded_words = u_msg.u_cols[0].len();
        if padded_words < 4
            || validate_frame_count(padded_words, 128 * 8, MAX_FRAME_BUDGET).is_err()
            || u_msg.u_cols.iter().any(|c| c.len() != padded_words) {
            self.poison_and_wipe();
            return Err(PreprocessError::KosOtCheckFailed {
                sender_id: self.sender_id,
                receiver_id: self.receiver_id,
            });
        }
        let payload_words = padded_words - 4;
        let batch_ctr = self.batch_ctr;
        self.batch_ctr = self.batch_ctr.wrapping_add(1);

        let mut q_cols = Vec::with_capacity(128);
        for i in 0..128 {
            let mut ti = expand_prg_column_u64s(
                &self.session_id,
                batch_ctr,
                i,
                &self.combined_seeds[i],
                padded_words,
            );
            let di_bit = ((self.delta >> i) & 1) as u64;
            let di_mask = 0u64.wrapping_sub(black_box(di_bit));
            for (w, ti_w_item) in ti[..padded_words].iter_mut().enumerate() {
                *ti_w_item ^= di_mask & u_msg.u_cols[i][w];
            }
            q_cols.push(ti);
        }

        let q_rows = transpose_cols128_to_rows(&q_cols, padded_words);
        for col in &mut q_cols {
            wipe_u64s(col);
        }

        let u_cols_digest = hash_kos_u_cols(
            &self.session_id,
            self.sender_id,
            self.receiver_id,
            batch_ctr,
            &u_msg.u_cols,
        );
        let chi_seed = sender_rng.next_bytes32();
        Ok((
            KosOtSenderPending {
                batch_ctr,
                payload_words,
                q_rows,
                u_cols_digest,
                chi_seed,
            },
            KosOtChallengeMsg { chi_seed },
        ))
    }

    /// Interactive KOS Step 4 (`OT Sender` local): verify `q_kos == t_kos + x_kos * delta` against
    /// the post-`u_cols` random `chi_seed`. On mismatch, **permanently poisons and wipes** this
    /// channel (`0` multi-batch column probes!) before returning `Err(KosOtCheckFailed)`.
    pub fn round4_verify_and_finish(
        &mut self,
        pending: KosOtSenderPending,
        proof: &KosOtProofMsg,
    ) -> Result<Vec<OtPadPair>, PreprocessError> {
        if self.poisoned {
            return Err(PreprocessError::ChannelPoisoned {
                sender_id: self.sender_id,
                receiver_id: self.receiver_id,
            });
        }
        let total_rows = pending.q_rows.len();
        let chis = derive_interactive_kos_challenges(
            &self.session_id,
            self.sender_id,
            self.receiver_id,
            pending.batch_ctr,
            &pending.u_cols_digest,
            &pending.chi_seed,
            total_rows,
        );
        let q_kos = kos_inner_product(&pending.q_rows, &chis);
        let expected_q = proof.t_kos.add(proof.x_kos.mul(Tower128(self.delta)));
        if !q_kos.ct_eq(expected_q) {
            self.poison_and_wipe();
            return Err(PreprocessError::KosOtCheckFailed {
                sender_id: self.sender_id,
                receiver_id: self.receiver_id,
            });
        }

        let bind = compute_kos_transcript_bind(&pending.u_cols_digest, &pending.chi_seed, proof);
        let payload_rows = 64 * pending.payload_words;
        let mut pad_pairs = Vec::with_capacity(payload_rows);
        for ell in 0..payload_rows {
            let q = pending.q_rows[ell];
            let p0 = crh_ot_row_hash48(
                &self.session_id,
                &bind,
                self.sender_id,
                self.receiver_id,
                pending.batch_ctr,
                ell as u64,
                q,
            );
            let p1 = crh_ot_row_hash48(
                &self.session_id,
                &bind,
                self.sender_id,
                self.receiver_id,
                pending.batch_ctr,
                ell as u64,
                q ^ self.delta,
            );
            pad_pairs.push((p0, p1));
        }
        Ok(pad_pairs)
    }
}

/// Full $n$-party mesh of directional Ring-LWE OT-extension channels (`n * (n - 1)` channels).
