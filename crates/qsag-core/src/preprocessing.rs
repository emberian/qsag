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
use crate::sponge::keccak::{Cshake256Xof, cshake256_32, cshake256_32_multi_frame, keccak_f1600};
use crate::wipe::{
    SecretBuffer, ct_eq_bytes32, secret_vec_extend_from_slice, wipe_bytes, wipe_bytes32, wipe_u16s,
    wipe_u64s, wipe_u128s,
};

mod triple_f2;

// ============================================================================
// 0. Preprocessing Errors & Identifiable Cheater Attribution
// ============================================================================

/// Sender's two 384-bit correlation pads for one extended OT.
pub type OtPadPair = ([u8; 48], [u8; 48]);

/// Zeroizing sender OT pad batch (`!Clone`, volatile-wiped on normal and early-return `Drop`).
pub struct OtSendPads(pub(crate) Vec<OtPadPair>);

impl fmt::Debug for OtSendPads {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("OtSendPads")
            .field("len", &self.0.len())
            .finish_non_exhaustive()
    }
}

impl core::ops::Deref for OtSendPads {
    type Target = [OtPadPair];
    #[inline]
    fn deref(&self) -> &[OtPadPair] {
        &self.0
    }
}

impl core::ops::DerefMut for OtSendPads {
    #[inline]
    fn deref_mut(&mut self) -> &mut [OtPadPair] {
        &mut self.0
    }
}

impl Drop for OtSendPads {
    fn drop(&mut self) {
        for (p0, p1) in &mut self.0 {
            wipe_bytes(p0);
            wipe_bytes(p1);
        }
        black_box(&mut self.0);
    }
}

/// Zeroizing receiver OT pad batch (`!Clone`, volatile-wiped on normal and early-return `Drop`).
pub struct OtRecvPads(pub(crate) Vec<[u8; 48]>);

impl fmt::Debug for OtRecvPads {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("OtRecvPads")
            .field("len", &self.0.len())
            .finish_non_exhaustive()
    }
}

impl core::ops::Deref for OtRecvPads {
    type Target = [[u8; 48]];
    #[inline]
    fn deref(&self) -> &[[u8; 48]] {
        &self.0
    }
}

impl core::ops::DerefMut for OtRecvPads {
    #[inline]
    fn deref_mut(&mut self) -> &mut [[u8; 48]] {
        &mut self.0
    }
}

impl Drop for OtRecvPads {
    fn drop(&mut self) {
        for pad in &mut self.0 {
            wipe_bytes(pad);
        }
        black_box(&mut self.0);
    }
}

/// Pads for a complete correlated-OT batch, on both sides (`Drop`-wiped).
pub type OtBatchPads = (OtSendPads, OtRecvPads);
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
    PartyValues<Goldilocks>,
    PartyValues<Goldilocks>,
    PartyValues<Goldilocks>,
    PartyValues<GoldilocksExt2>,
    PartyValues<GoldilocksExt2>,
    PartyValues<GoldilocksExt2>,
);
#[cfg(test)]
type SpcotPunctureOutput = (Vec<[u128; 2]>, Vec<([u8; 16], [u8; 16])>);

/// Preprocessing abort with deterministic attribution when a party deviates during OT, coin-flip,
/// polynomial degree verification, BDOZ/SPDZ MAC check, Booleanity check, or companion sacrifice.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PreprocessError {
    InvalidThreshold {
        t: usize,
        n: usize,
    },
    DuplicateOrZeroEvalPoint,
    CoinCommitMismatch {
        party_id: usize,
    },
    ShareCommitMismatch {
        phase: &'static str,
        party_id: usize,
    },
    BaseOtReceiverProofFailed {
        sender_id: usize,
        receiver_id: usize,
    },
    BaseOtFoCheckFailed {
        sender_id: usize,
        receiver_id: usize,
        ot_idx: u32,
    },
    KosOtCheckFailed {
        sender_id: usize,
        receiver_id: usize,
    },
    ChannelPoisoned {
        sender_id: usize,
        receiver_id: usize,
    },
    DegreeCheckFailed {
        phase: &'static str,
    },
    MacCheckFailed {
        phase: &'static str,
        accused_party: Option<usize>,
    },
    SacrificeResidualNonZero {
        phase: &'static str,
    },
    NonBooleanBitDetected {
        phase: &'static str,
    },
    VaultExhausted {
        kind: &'static str,
    },
    VaultPoisoned {
        kind: &'static str,
    },
    PcgDepthOutOfRange {
        depth: usize,
    },
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
            Self::DuplicateOrZeroEvalPoint => {
                write!(f, "duplicate or zero Shamir evaluation point")
            }
            Self::CoinCommitMismatch { party_id } => {
                write!(f, "commit-and-open coin mismatch from party {}", party_id)
            }
            Self::ShareCommitMismatch { phase, party_id } => {
                write!(
                    f,
                    "share commitment opening mismatch in {} from party {}",
                    phase, party_id
                )
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
                write!(
                    f,
                    "preprocessed {} vault permanently poisoned after MAC abort",
                    kind
                )
            }
            Self::PcgDepthOutOfRange { depth } => {
                write!(
                    f,
                    "PCG GGM tree depth {} out of supported range 14..=16",
                    depth
                )
            }
            Self::ExperimentalSparsePcg => write!(
                f,
                "compact PCG is unavailable: use uniform vault preprocessing"
            ),
            Self::PcgInvalidWireSeed => write!(f, "malformed or tampered PCG wire seed"),
            Self::PcgObsoleteWireSeedFormat => write!(
                f,
                "PCG wire seed uses the obsolete QSAGDPC1 layout; re-run setup to obtain a QSAGDPC2 seed"
            ),
            Self::PcgSeedAlreadyBurned => {
                write!(
                    f,
                    "PCG seed was already expanded once; refusing to expand it again"
                )
            }
            Self::PcgSeedBurnNotRecorded => {
                write!(f, "PCG seed burn could not be recorded; refusing to expand")
            }
        }
    }
}

/// Maximum accepted preprocessing frame (16 MiB), including all declared elements.
pub const MAX_FRAME_BUDGET: usize = 16 * 1024 * 1024;
pub(crate) fn validate_frame_count(
    count: usize,
    elem_bytes: usize,
    remaining: usize,
) -> Result<(), PreprocessError> {
    match count.checked_mul(elem_bytes) {
        Some(size) if size <= remaining && size <= MAX_FRAME_BUDGET => Ok(()),
        _ => Err(PreprocessError::PcgInvalidWireSeed),
    }
}

/// Secret-keyed transcript hedge. A restored counter is safe for a new transcript;
/// identical seed, counter, entropy and transcript necessarily reproduce the same bytes.
pub struct HedgedTranscriptRng {
    seed: [u8; 32],
    counter: u64,
}
impl Drop for HedgedTranscriptRng {
    fn drop(&mut self) {
        wipe_bytes32(&mut self.seed);
    }
}
impl HedgedTranscriptRng {
    pub fn new(secret_hedge_seed: [u8; 32], monotonic_counter: u64) -> Self {
        Self {
            seed: secret_hedge_seed,
            counter: monotonic_counter,
        }
    }
    /// Fails before producing output on counter exhaustion. Variable inputs are length framed.
    pub fn fill_bytes(
        &mut self,
        caller_entropy: &[u8],
        session_and_msg_transcript: &[u8],
        out: &mut [u8],
    ) -> Result<(), PreprocessError> {
        let next = self
            .counter
            .checked_add(1)
            .ok_or(PreprocessError::PcgInvalidWireSeed)?;
        Self::derive(
            &self.seed,
            self.counter,
            caller_entropy,
            session_and_msg_transcript,
            out,
        );
        self.counter = next;
        Ok(())
    }
    pub(crate) fn derive(
        seed: &[u8; 32],
        counter: u64,
        caller_entropy: &[u8],
        session_and_msg_transcript: &[u8],
        out: &mut [u8],
    ) {
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
fn reserve_material(
    cursor: &mut usize,
    len: usize,
    count: usize,
    poisoned: bool,
    kind: &'static str,
) -> Result<core::ops::Range<usize>, PreprocessError> {
    if poisoned {
        return Err(PreprocessError::VaultPoisoned { kind });
    }
    let end = cursor
        .checked_add(count)
        .filter(|end| *end <= len)
        .ok_or(PreprocessError::VaultExhausted { kind })?;
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
        wipe_bytes(&mut self.buf);
    }
}

impl PartyPrivateRng {
    /// Seed from the operating system entropy source; failures are propagated.
    #[cfg(all(feature = "std", unix))]
    pub fn from_os_rng(domain_label: &[u8]) -> Result<Self, std::io::Error> {
        use std::io::Read;
        let mut seed = [0u8; 32];
        let result = std::fs::File::open("/dev/urandom").and_then(|mut f| f.read_exact(&mut seed));
        if let Err(error) = result {
            wipe_bytes32(&mut seed);
            return Err(error);
        }
        let rng = Self::from_seed(seed, domain_label);
        wipe_bytes32(&mut seed);
        Ok(rng)
    }

    pub fn from_seed(party_seed: [u8; 32], domain_label: &[u8]) -> Self {
        let mut seed_copy = party_seed;
        let derived =
            cshake256_32_multi_frame(b"QSAG.PARTY.RNG.INIT/v1", &[&seed_copy, domain_label]);
        wipe_bytes32(&mut seed_copy);
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
        assert!(
            self.counter <= u64::MAX - 4,
            "PartyPrivateRng counter exhausted"
        );
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
        qsag_asm::volatile_fill(&mut states, [0u64; 25]);
        self.off = 0;
    }

    #[inline(always)]
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
const fn rlwe_reduce_once(x: u32) -> u16 {
    let d = x.wrapping_sub(RLWE_Q as u32);
    (d.wrapping_add((RLWE_Q as u32) & 0u32.wrapping_sub(d >> 31))) as u16
}

#[inline]
const fn rlwe_add(a: u16, b: u16) -> u16 {
    rlwe_reduce_once((a as u32) + (b as u32))
}

#[inline]
const fn rlwe_sub(a: u16, b: u16) -> u16 {
    rlwe_reduce_once((a as u32) + (RLWE_Q as u32) - (b as u32))
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

const NTT_INVERSE_SCALES: [u16; RLWE_N] = {
    let mut arr = [0u16; RLWE_N];
    let mut cur = 1u16;
    let mut i = 0usize;
    while i < RLWE_N {
        arr[i] = rlwe_mul(cur, RLWE_N_INV);
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
        RlwePoly::ntt_inverse(&mut c);
        for i in 0..RLWE_N {
            c[i] = rlwe_mul(c[i], NTT_INVERSE_SCALES[i]);
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

    // Forward Gentleman–Sande DIF leaves evaluations in bit-reversed order.
    // Pointwise products retain that order; inverse Cooley–Tukey DIT consumes
    // it directly. All indices and loop bounds depend only on the public size.
    fn ntt_forward(a: &mut [u16; RLWE_N]) {
        let mut len = RLWE_N;
        while len >= 2 {
            let half = len / 2;
            let step = RLWE_N / len;
            for block in a.chunks_exact_mut(len) {
                let (left, right) = block.split_at_mut(half);
                for (j, (u, v)) in left.iter_mut().zip(right).enumerate() {
                    let sum = rlwe_add(*u, *v);
                    *v = rlwe_mul(rlwe_sub(*u, *v), OMEGA_POWS[j * step]);
                    *u = sum;
                }
            }
            len >>= 1;
        }
    }

    fn ntt_inverse(a: &mut [u16; RLWE_N]) {
        let mut len = 2;
        while len <= RLWE_N {
            let half = len / 2;
            let step = RLWE_N / len;
            for block in a.chunks_exact_mut(len) {
                let (left, right) = block.split_at_mut(half);
                for (j, (u, v)) in left.iter_mut().zip(right).enumerate() {
                    let product = rlwe_mul(*v, OMEGA_INV_POWS[j * step]);
                    *v = rlwe_sub(*u, product);
                    *u = rlwe_add(*u, product);
                }
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
        Self::ntt_forward(&mut a);
        RlwePolyNtt(a)
    }

    #[inline]
    pub fn mul_ntt(&self, lhs_ntt: &RlwePolyNtt) -> Self {
        let mut b = self.0;
        for i in 0..RLWE_N {
            b[i] = rlwe_mul(b[i], PSI_POWS[i]);
        }
        Self::ntt_forward(&mut b);
        let mut c = [0u16; RLWE_N];
        for i in 0..RLWE_N {
            c[i] = rlwe_mul(lhs_ntt.0[i], b[i]);
        }
        Self::ntt_inverse(&mut c);
        for i in 0..RLWE_N {
            c[i] = rlwe_mul(c[i], NTT_INVERSE_SCALES[i]);
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
            #[expect(
                clippy::chunks_exact_to_as_chunks,
                reason = "Keep the workspace Rust 1.85 minimum; slice as_chunks requires a newer compiler"
            )]
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
            cshake256_32_multi_frame(b"QSAG.OT.RLWE.CRS.COIN/v1", &[session_id, crs_coin])
        };
        Self::from_crs_xof(&mixed_sid, sender_id, receiver_id, ot_idx, role)
    }

    /// Check whether every coefficient lies in canonical `[0, RLWE_Q)`.
    #[inline]
    pub fn is_canonical(&self) -> bool {
        self.0.iter().all(|&c| c < RLWE_Q)
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

/// Number of parallel/sequential repetitions in [`RlweReceiverZkPok`] (`13 * 11 = 143` challenge bits over
/// pairwise-invertible signed monomials $\pm X^k$; matches `rlweOrSigmaParallelReps` in `RlweCyclotomicExtraction.lean`).
pub const RLWE_ZKPOK_REPS: usize = 13;
/// Bit-width of one single signed-monomial challenge `c in {0..2048}` (`deg = c & 0x3ff`, `sign = (c >> 10) & 1`),
/// matching `SignedMonomialChal.ofFinIndex` / `signedMonomial_challenge_set_pairwise_invertible` in Lean.
pub const RLWE_ZKPOK_CHAL_BITS: u32 = 11;
const RLWE_ZKPOK_CHAL_MASK: u32 = (1u32 << RLWE_ZKPOK_CHAL_BITS) - 1;
/// Joint Gaussian rejection parameters over the single signed-monomial challenge set
/// $\mathcal{C} = \{\pm X^k : 0 \le k < 1024\}$ (`2048` challenges per repetition, `100%` pairwise
/// invertible over $R_{12289}$ via $(c_1 - c_2) g(X) = 2$). Key generation conditions the two
/// $\mathrm{CBD}_1$ polynomials on total squared norm $\le 1376$ (Chernoff tail $< 2^{-178}$).
/// Because negacyclic multiplication by $\pm X^k$ is an exact $\ell_2$ and $\ell_\infty$ isometry,
/// every coordinate of the shift lies in $[-1, 1]$ and the 13-repetition response shift satisfies
/// $\|v\|_2^2 \le 13 \times 1376 = 17{,}888$.
///
/// Masks follow $\exp(-y^2 / (2 \cdot 700^2))$ on $[-3072, 3071]$. Accept $z = y + v$ only in
/// $[-3070, 3069]$, with probability $\min(1, \exp((\|y\|^2 - \|z\|^2)/980000) / M)$ where
/// $M = \exp(\lceil 980000 \ln(24) \rceil / 980000)$ (`RLWE_GAUSSIAN_LOG_M = 3_114_493`).
/// Every target response has preimages inside $[-3072, 3071]$ since $\|v\|_\infty \le 1$.
/// Exact discrete-Gaussian MGF domination over $\|v\|_2^2 \le 17{,}888, \|v\|_\infty \le 1$ bounds
/// the unclipped tail below $2^{-197.3}$; conditioning on acceptance and the response-box mass
/// ($> 0.73$) leaves statistical HVZK distance below $2^{-192}$ (`0` QROM claim).
///
/// Sampling uses uniform proposals and fixed-work, 192-bit Bernoulli rejection,
/// with no mask-indexed table access. Each exponential evaluation has absolute
/// error $< 64 / 2^{192}$. Expected acceptance is $\approx 0.735 / 24 \approx 1 / 32.6$,
/// and all rejections restart the entire joint real-branch transcript.
///
/// Bimodal rejection (Ducas–Durmus–Lepoint–Lyubashevsky, BLISS: `z = y + b v` with a secret
/// sign `b` and acceptance `1 / (M exp(-|v|^2 / 2 sigma^2) cosh(<z, v> / sigma^2))`) would give
/// `M = exp(17_888 / 980_000) < 1.02` here, but it does not apply to this statement. The sign
/// must cancel in the verification equation, which BLISS obtains from a homogeneous relation
/// `A S = q (mod 2q)`; for `Y = a s + e` that means proving `[2a | 2 | q - 2Y] (s, e, 1) = q
/// (mod 2q)` with a third response `z_3 = y_3 + b c`. Two accepting transcripts then agree only
/// modulo `q`-multiples of the challenge difference: the extractor learns
/// `a ds + de = Y dz_3 (mod q)` for a short `dz_3` with `dz_3 = c - c' (mod 2)` that the prover
/// chooses, not for `c - c'` itself. The exact extraction this proof relies on, where
/// `c - c'` is a difference of signed monomials dividing 2, is lost, and at `q = 12289` (fully
/// split, `|dz_3|_inf` up to `q / 2`) a relaxed witness with an arbitrary short denominator
/// carries no soundness for the receiver's key. `M = 24` is the cost of exact extraction at
/// this modulus.
const RLWE_ZKPOK_Z_BOUND: i16 = 3070;

/// Constant-time HVZK OR-Sigma proof of short Ring-LWE witness knowledge for [`RlweOtReceiverMsg`]:
/// proves knowledge of short `(s, e)` on EITHER `Y_0 = pk0` OR `Y_1 = pk0 + t_crs` under `a_crs`
/// over the 11-bit pairwise-invertible signed-monomial challenge set $\pm X^k$ (`13` repetitions).
#[derive(Clone, Debug)]
pub struct RlweReceiverZkPok {
    pub chal0: [u32; RLWE_ZKPOK_REPS],
    pub chal1: [u32; RLWE_ZKPOK_REPS],
    pub z_s0: Box<[[i16; RLWE_N]; RLWE_ZKPOK_REPS]>,
    pub z_e0: Box<[[i16; RLWE_N]; RLWE_ZKPOK_REPS]>,
    pub z_s1: Box<[[i16; RLWE_N]; RLWE_ZKPOK_REPS]>,
    pub z_e1: Box<[[i16; RLWE_N]; RLWE_ZKPOK_REPS]>,
}

/// Realize 11-bit signed-monomial challenge `u` (`deg = u & 0x3ff`, `sign = (u >> 10) & 1`) in $R_q$
/// in constant time (`false -> +X^deg`, `true -> -X^deg`, matching `SignedMonomialChal.ofFinIndex`).
#[inline]
fn poly_from_chal11(u: u32) -> RlwePoly {
    let deg = (u & 0x3FF) as usize;
    let sign = ((u >> 10) & 1) as u16;
    let mut coeffs = [0u16; RLWE_N];
    let value = 1 ^ (0u16.wrapping_sub(sign) & (1 ^ (RLWE_Q - 1)));
    for (i, coeff) in coeffs.iter_mut().enumerate() {
        *coeff = value & 0u16.wrapping_sub(black_box((i == deg) as u16));
    }
    RlwePoly(coeffs)
}

/// Multiply public `poly` by public signed monomial `(-1)^{sign} X^{deg}` in $R_q = \mathbb{Z}_q[X]/(X^{1024}+1)$
/// in $O(N)$ (`0` NTTs).
#[inline]
fn mul_chal11_public(poly: &RlwePoly, u: u32) -> RlwePoly {
    let deg = (u & 0x3FF) as usize;
    let is_neg = ((u >> 10) & 1) == 1;
    let mut out = [0u16; RLWE_N];
    for (dst, slot) in out.iter_mut().enumerate() {
        let (src, wrap_neg) = if dst >= deg {
            (dst - deg, is_neg)
        } else {
            (dst + RLWE_N - deg, !is_neg)
        };
        let coeff = poly.0[src];
        *slot = if wrap_neg && coeff != 0 {
            RLWE_Q - coeff
        } else {
            coeff
        };
    }
    RlwePoly(out)
}

/// Constant-time 10-stage barrel-rotator negacyclic product `(-1)^{sign} X^{deg} * poly` over
/// signed integer coefficients (`0` NTTs, fixed compile-time offsets, `0` secret/challenge branches).
#[inline]
fn mul_chal11_signed_ct(poly: &[i16; RLWE_N], u: u32) -> [i16; RLWE_N] {
    let u = black_box(u);
    let mut cur = *poly;
    let sign_mask = 0i16.wrapping_sub(((u >> 10) & 1) as i16);
    for x in &mut cur {
        *x = (*x ^ sign_mask).wrapping_sub(sign_mask);
    }
    for stage in 0..10u32 {
        let shift = 1usize << stage;
        let sel = 0i16.wrapping_sub(((u >> stage) & 1) as i16);
        let prev = cur;
        for (dst, slot) in cur.iter_mut().enumerate() {
            let shifted = if dst >= shift {
                prev[dst - shift]
            } else {
                prev[dst + RLWE_N - shift].wrapping_neg()
            };
            *slot = prev[dst] ^ (sel & (prev[dst] ^ shifted));
        }
    }
    cur
}

#[inline]
fn rlwe_ternary_to_i16_ct(poly: &RlwePoly) -> [i16; RLWE_N] {
    let mut out = [0i16; RLWE_N];
    for (dst, &c) in out.iter_mut().zip(&poly.0) {
        let is_one = (c == 1) as i16;
        let is_neg_one = (c == RLWE_Q - 1) as i16;
        *dst = is_one - is_neg_one;
    }
    out
}

#[inline]
fn signed_box_to_rlwe_poly(v: &[i16; RLWE_N]) -> RlwePoly {
    let mut out = [0u16; RLWE_N];
    for i in 0..RLWE_N {
        let x = i32::from(v[i]);
        let neg_mask = (x >> 31) & i32::from(RLWE_Q);
        out[i] = (x + neg_mask).rem_euclid(i32::from(RLWE_Q)) as u16;
    }
    RlwePoly(out)
}

// Fixed-point unsigned fractions in little-endian limbs, with denominator 2^192.
// The schoolbook product retains the high half, rounding toward zero.
#[inline(always)]
fn gaussian_fraction_mul(a: [u64; 3], b: [u64; 3]) -> [u64; 3] {
    let a0 = u128::from(a[0]);
    let a1 = u128::from(a[1]);
    let a2 = u128::from(a[2]);
    let b0 = u128::from(b[0]);
    let b1 = u128::from(b[1]);
    let b2 = u128::from(b[2]);

    let p00 = a0 * b0;
    let c0 = p00 >> 64;

    let s1_a = a0 * b1 + c0;
    let p1_a = s1_a as u64;
    let c1_a = s1_a >> 64;

    let s2_a = a0 * b2 + c1_a;
    let p2_a = s2_a as u64;
    let p3_a = (s2_a >> 64) as u64;

    let s1_b = a1 * b0 + u128::from(p1_a);
    let c1_b = s1_b >> 64;

    let s2_b = a1 * b1 + u128::from(p2_a) + c1_b;
    let p2_b = s2_b as u64;
    let c2_b = s2_b >> 64;

    let s3_b = a1 * b2 + u128::from(p3_a) + c2_b;
    let p3_b = s3_b as u64;
    let p4_b = (s3_b >> 64) as u64;

    let s2_c = a2 * b0 + u128::from(p2_b);
    let c2_c = s2_c >> 64;

    let s3_c = a2 * b1 + u128::from(p3_b) + c2_c;
    let p3 = s3_c as u64;
    let c3_c = s3_c >> 64;

    let s4_c = a2 * b2 + u128::from(p4_b) + c3_c;
    let p4 = s4_c as u64;
    let p5 = (s4_c >> 64) as u64;

    [p3, p4, p5]
}

#[inline(always)]
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
//
// The decision is `random < probability` on 192 bits. Two Q64 bounds settle it
// from the high limb alone in all but a sliver of cases: at or above the upper
// bound the proposal is rejected, below the lower bound it is accepted. Both
// outcomes equal what the full comparison returns, and every surviving
// proposal draws its low limbs first, so the sampler's outputs and its use of
// `rng` are those of the comparison without the bounds. The 192-bit path runs
// only for a high limb between the bounds: for an accepted proposal that has
// probability below 49 / (2^64 * probability), under 2^-44 even at the edge of
// the box, so the path taken is independent of the accepted value up to that.
fn sample_gaussian_box(rng: &mut PartyPrivateRng, response: bool) -> [i16; RLWE_N] {
    let half = if response {
        RLWE_ZKPOK_Z_BOUND
    } else {
        RLWE_ZKPOK_Z_BOUND + 2
    };
    let mut coins = [0u8; 26];
    let out = core::array::from_fn(|_| {
        loop {
            rng.fill_bytes(&mut coins[..10]);
            let proposal = u16::from_le_bytes([coins[0], coins[1]]) & 0x1fff;
            let valid = proposal < 2 * half as u16;
            let mask = 0u16.wrapping_sub(u16::from(valid));
            let x = (proposal & mask) as i16 - half;
            let exponent = (i64::from(x) * i64::from(x)) as u64;
            let high = u64::from_le_bytes(core::array::from_fn(|j| coins[2 + j]));
            // Reject only when the cheap upper bound proves that the full 192-bit
            // comparison would reject. Every accepted proposal still takes the same
            // fixed-work exact path; discarded proposals are independent of it.
            let upper = gaussian_exp_upper_bound(exponent);
            if black_box(u128::from(high) >= upper) {
                continue;
            }
            // The upper-bound rejection is decided by the high limb alone. Draw
            // the other two independent limbs only for surviving proposals. Rejected
            // proposals cannot affect the next sample.
            rng.fill_bytes(&mut coins[10..]);
            if black_box(high < gaussian_exp_lower_bound(exponent)) {
                if valid {
                    break x;
                }
                continue;
            }
            let random = [
                u64::from_le_bytes(core::array::from_fn(|j| coins[10 + j])),
                u64::from_le_bytes(core::array::from_fn(|j| coins[18 + j])),
                high,
            ];
            let probability = gaussian_exp_probability::<24>(exponent);
            let accept = gaussian_fraction_lt(random, probability) & valid;
            if black_box(accept) {
                break x;
            }
        }
    });
    wipe_bytes(&mut coins);
    out
}

// Ignore the low fourteen exponent bits for this bound only. This increases
// the ideal probability by at most exp(16383/980000) < 1.017, while needing
// only ten Q64 products. The actual decision below still uses all 192 bits.
// Relative to the Q192 computation with those exponent bits cleared, initial
// truncation loses <1 Q64 unit; each of ten factors and product truncations
// loses <1 more. Adding 21 therefore gives a strict upper bound. Keep the sum
// in u128 because it can exceed u64::MAX near probability one.
// No table index, loop bound or branch depends on the proposal.
#[inline(always)]
fn gaussian_exp_upper_bound(exponent: u64) -> u128 {
    let mut probability = u64::MAX;
    for (bit, factor) in RLWE_GAUSSIAN_EXP_POWERS[14..24].iter().enumerate() {
        let multiplied = ((u128::from(probability) * u128::from(factor[2])) >> 64) as u64;
        let mask = 0u64.wrapping_sub((exponent >> (bit + 14)) & 1);
        probability ^= mask & (probability ^ multiplied);
    }
    u128::from(probability) + 21
}

// Q64 chain over all 24 exponent bits, truncating at every step. It never
// exceeds the high limb of `gaussian_exp_probability::<24>`: if `v <= p >> 128`
// and `f_hi = f >> 128`, then `v * f_hi * 2^256 <= p * f`, hence
// `(v * f_hi) >> 64 <= ((p * f) >> 192) >> 128`, and the masked selection keeps
// the inequality. It falls short of that limb by fewer than 49 units (one per
// truncated product, one per truncated factor). Fixed work, no table index or
// branch on the proposal.
#[inline(always)]
fn gaussian_exp_lower_bound(exponent: u64) -> u64 {
    let mut probability = u64::MAX;
    for (bit, factor) in RLWE_GAUSSIAN_EXP_POWERS[..24].iter().enumerate() {
        let multiplied = ((u128::from(probability) * u128::from(factor[2])) >> 64) as u64;
        let mask = 0u64.wrapping_sub((exponent >> bit) & 1);
        probability ^= mask & (probability ^ multiplied);
    }
    probability
}

#[inline(always)]
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
    for limb in &mut probability {
        *limb &= in_range;
    }
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
/// `ceil(980_000 * ln(24)) = 3_114_493` (`M = 24` over single signed-monomial shifts `||v||_2^2 <= 17_888`).
const RLWE_GAUSSIAN_LOG_M: i64 = 3_114_493;
const RLWE_WITNESS_ENERGY_BOUND: usize = 1376;

fn bounded_ternary_witness(s: &RlwePoly, e: &RlwePoly) -> bool {
    let (energy, ternary) =
        s.0.iter()
            .chain(&e.0)
            .fold((0usize, true), |(energy, valid), &c| {
                (
                    energy + usize::from(c != 0),
                    valid & ((c == 0) | (c == 1) | (c == RLWE_Q - 1)),
                )
            });
    ternary & (energy <= RLWE_WITNESS_ENERGY_BOUND)
}

#[inline]
fn ct_select_i16_array(
    choice: bool,
    if_true: &[i16; RLWE_N],
    if_false: &[i16; RLWE_N],
) -> [i16; RLWE_N] {
    let mask = 0u16.wrapping_sub(black_box(choice as u16));
    let mut out = [0i16; RLWE_N];
    for i in 0..RLWE_N {
        let a = if_true[i] as u16;
        let b = if_false[i] as u16;
        out[i] = (b ^ (mask & (a ^ b))) as i16;
    }
    out
}

#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the explicit statement, role, witness and randomness bindings in this protocol API"
)]
fn hash_rlwe_zkpok_joint_challenges(
    crs_coin: &[u8; 32],
    session_id: &[u8; 32],
    sender_id: usize,
    receiver_id: usize,
    ot_idx: u32,
    pk0: &RlwePoly,
    t_crs: &RlwePoly,
    commitments: &[(RlwePoly, RlwePoly)],
) -> [u32; RLWE_ZKPOK_REPS] {
    let mut xof = Cshake256Xof::new(b"QSAG.OT.RLWE.ZKPOK/v3");
    xof.absorb(crs_coin);
    xof.absorb(session_id);
    xof.absorb(&(sender_id as u64).to_be_bytes());
    xof.absorb(&(receiver_id as u64).to_be_bytes());
    xof.absorb(&ot_idx.to_be_bytes());
    xof.absorb(&(RLWE_ZKPOK_REPS as u32).to_be_bytes());
    xof.absorb(&RLWE_ZKPOK_CHAL_BITS.to_be_bytes());
    for p in core::iter::once(pk0)
        .chain(core::iter::once(t_crs))
        .chain(commitments.iter().flat_map(|(a, b)| [a, b]))
    {
        for &c in &p.0 {
            xof.absorb(&c.to_le_bytes());
        }
    }
    core::array::from_fn(|_| {
        let mut out = [0u8; 4];
        xof.squeeze(&mut out);
        u32::from_le_bytes(out) & RLWE_ZKPOK_CHAL_MASK
    })
}

impl RlweReceiverZkPok {
    #[expect(
        clippy::too_many_arguments,
        reason = "Preserve the explicit statement, role, witness and randomness bindings in this protocol API"
    )]
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
        let mut y_fake = RlwePoly::ct_select(choice_bit, pk0, &pk1);
        let mut s_signed = rlwe_ternary_to_i16_ct(s_r);
        let mut e_signed = rlwe_ternary_to_i16_ct(e1);

        let mut chal0 = [0u32; RLWE_ZKPOK_REPS];
        let mut chal1 = [0u32; RLWE_ZKPOK_REPS];
        let mut z_s0 = Box::new([[0i16; RLWE_N]; RLWE_ZKPOK_REPS]);
        let mut z_e0 = Box::new([[0i16; RLWE_N]; RLWE_ZKPOK_REPS]);
        let mut z_s1 = Box::new([[0i16; RLWE_N]; RLWE_ZKPOK_REPS]);
        let mut z_e1 = Box::new([[0i16; RLWE_N]; RLWE_ZKPOK_REPS]);

        // Simulated branch `(u_fake, zs_fake, ze_fake, w_fake)` is witness-independent;
        // single-attempt real-branch acceptance probability is uniform across `u_real` up to `< 2^-197`.
        let mut u_fakes = [0u32; RLWE_ZKPOK_REPS];
        let mut zs_fakes = Box::new([[0i16; RLWE_N]; RLWE_ZKPOK_REPS]);
        let mut ze_fakes = Box::new([[0i16; RLWE_N]; RLWE_ZKPOK_REPS]);
        let mut w_fakes = [RlwePoly::ZERO; RLWE_ZKPOK_REPS];
        for rep in 0..RLWE_ZKPOK_REPS {
            let u_fake = (rng.next_u64() as u32) & RLWE_ZKPOK_CHAL_MASK;
            let zs_fake = sample_gaussian_box(rng, true);
            let ze_fake = sample_gaussian_box(rng, true);
            let d_poly = poly_from_chal11(u_fake);
            let w_fake = signed_box_to_rlwe_poly(&zs_fake)
                .mul_ntt(a_ntt)
                .add(&signed_box_to_rlwe_poly(&ze_fake))
                .sub(&y_fake.mul_negacyclic(&d_poly));
            u_fakes[rep] = u_fake;
            zs_fakes[rep] = zs_fake;
            ze_fakes[rep] = ze_fake;
            w_fakes[rep] = w_fake;
        }
        wipe_u16s(&mut y_fake.0);

        let mut commitments = vec![(RlwePoly::ZERO, RlwePoly::ZERO); RLWE_ZKPOK_REPS];
        let mut ys_masks = Box::new([[0i16; RLWE_N]; RLWE_ZKPOK_REPS]);
        let mut ye_masks = Box::new([[0i16; RLWE_N]; RLWE_ZKPOK_REPS]);
        let mut u_reals = [0u32; RLWE_ZKPOK_REPS];
        let mut ds = [0i16; RLWE_N];
        let mut de = [0i16; RLWE_N];

        // Rejection restarts the entire joint real-branch transcript.
        loop {
            for rep in 0..RLWE_ZKPOK_REPS {
                let ys = sample_gaussian_box(rng, false);
                let ye = sample_gaussian_box(rng, false);
                let w_real = signed_box_to_rlwe_poly(&ys)
                    .mul_ntt(a_ntt)
                    .add(&signed_box_to_rlwe_poly(&ye));
                commitments[rep] = (
                    RlwePoly::ct_select(choice_bit, &w_fakes[rep], &w_real),
                    RlwePoly::ct_select(choice_bit, &w_real, &w_fakes[rep]),
                );
                ys_masks[rep] = ys;
                ye_masks[rep] = ye;
            }
            let challenges = hash_rlwe_zkpok_joint_challenges(
                crs_coin,
                session_id,
                sender_id,
                receiver_id,
                ot_idx,
                pk0,
                t_crs,
                &commitments,
            );
            let mut in_bounds = 1u32;
            let mut log_ratio = 0i64;
            for rep in 0..RLWE_ZKPOK_REPS {
                let u_real = challenges[rep] ^ u_fakes[rep];
                u_reals[rep] = u_real;
                ds = mul_chal11_signed_ct(&s_signed, u_real);
                de = mul_chal11_signed_ct(&e_signed, u_real);
                let ys = &mut ys_masks[rep];
                let ye = &mut ye_masks[rep];
                for i in 0..RLWE_N {
                    let dsi = i64::from(ds[i]);
                    let dei = i64::from(de[i]);
                    log_ratio += 2 * i64::from(ys[i]) * dsi + dsi * dsi;
                    log_ratio += 2 * i64::from(ye[i]) * dei + dei * dei;
                    ys[i] += ds[i];
                    ye[i] += de[i];
                    in_bounds &= (((i32::from(ys[i]) + 3070) as u32) < 6140) as u32;
                    in_bounds &= (((i32::from(ye[i]) + 3070) as u32) < 6140) as u32;
                }
            }
            let accept = gaussian_accept(log_ratio, rng);
            if black_box(in_bounds) == 1 && black_box(accept) {
                break;
            }
        }

        let c_mask = 0u32.wrapping_sub(black_box(choice_bit as u32));
        for rep in 0..RLWE_ZKPOK_REPS {
            let u_real = u_reals[rep];
            let u_fake = u_fakes[rep];
            chal0[rep] = u_real ^ (c_mask & (u_real ^ u_fake));
            chal1[rep] = u_fake ^ (c_mask & (u_fake ^ u_real));
            z_s0[rep] = ct_select_i16_array(choice_bit, &zs_fakes[rep], &ys_masks[rep]);
            z_e0[rep] = ct_select_i16_array(choice_bit, &ze_fakes[rep], &ye_masks[rep]);
            z_s1[rep] = ct_select_i16_array(choice_bit, &ys_masks[rep], &zs_fakes[rep]);
            z_e1[rep] = ct_select_i16_array(choice_bit, &ye_masks[rep], &ze_fakes[rep]);
        }

        qsag_asm::volatile_fill(&mut s_signed, 0);
        qsag_asm::volatile_fill(&mut e_signed, 0);
        qsag_asm::volatile_fill(&mut ds, 0);
        qsag_asm::volatile_fill(&mut de, 0);
        qsag_asm::volatile_fill(&mut u_fakes, 0);
        qsag_asm::volatile_fill(&mut u_reals, 0);
        for rep in 0..RLWE_ZKPOK_REPS {
            qsag_asm::volatile_fill(&mut zs_fakes[rep], 0);
            qsag_asm::volatile_fill(&mut ze_fakes[rep], 0);
            qsag_asm::volatile_fill(&mut ys_masks[rep], 0);
            qsag_asm::volatile_fill(&mut ye_masks[rep], 0);
            wipe_u16s(&mut w_fakes[rep].0);
        }
        Self {
            chal0,
            chal1,
            z_s0,
            z_e0,
            z_s1,
            z_e1,
        }
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "Preserve the explicit statement, role, witness and randomness bindings in this protocol API"
    )]
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
        if !t_crs.is_canonical() || !pk0.is_canonical() {
            return false;
        }
        let y0 = *pk0;
        let y1 = pk0.add(t_crs);
        let mut commitments = Vec::with_capacity(RLWE_ZKPOK_REPS);
        for rep in 0..RLWE_ZKPOK_REPS {
            if (self.chal0[rep] >> RLWE_ZKPOK_CHAL_BITS) != 0
                || (self.chal1[rep] >> RLWE_ZKPOK_CHAL_BITS) != 0
            {
                return false;
            }
            for arr in [
                &self.z_s0[rep],
                &self.z_e0[rep],
                &self.z_s1[rep],
                &self.z_e1[rep],
            ] {
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
                .sub(&mul_chal11_public(&y0, self.chal0[rep]));
            let w1 = zs1_p
                .mul_ntt(a_ntt)
                .add(&ze1_p)
                .sub(&mul_chal11_public(&y1, self.chal1[rep]));
            commitments.push((w0, w1));
        }
        let challenges = hash_rlwe_zkpok_joint_challenges(
            crs_coin,
            session_id,
            sender_id,
            receiver_id,
            ot_idx,
            pk0,
            t_crs,
            &commitments,
        );
        for (rep, expected) in challenges.iter().enumerate() {
            if self.chal0[rep] ^ self.chal1[rep] != *expected {
                return false;
            }
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
#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the explicit statement, role, witness and randomness bindings in this protocol API"
)]
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
    let mut fo_seed = cshake256_32_multi_frame(b"QSAG.OT.RLWE.FO/v2", &[&label, rho]);
    wipe_bytes(&mut label);

    let mut fo_rng = PartyPrivateRng::from_seed(fo_seed, b"QSAG.OT.RLWE.FO.STREAM/v2");
    wipe_bytes32(&mut fo_seed);
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

#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the explicit statement, role, witness and randomness bindings in this protocol API"
)]
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
        if black_box(bounded_ternary_witness(&s, &e)) {
            break (s, e);
        }
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
    cshake256_32_multi_frame(
        b"QSAG.OT.RLWE.CRS/v2",
        &[
            session_id,
            &(sender_id as u64).to_be_bytes(),
            &(receiver_id as u64).to_be_bytes(),
            &(RLWE_N as u64).to_be_bytes(),
            &RLWE_Q.to_be_bytes(),
            &(RLWE_ZKPOK_REPS as u64).to_be_bytes(),
        ],
    )
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

#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the explicit statement, role, witness and randomness bindings in this protocol API"
)]
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
#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the explicit statement, role, witness and randomness bindings in this protocol API"
)]
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
#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the explicit statement, role, witness and randomness bindings in this protocol API"
)]
pub fn rlwe_ot_transfer(
    session_id: &[u8; 32],
    sender_id: usize,
    receiver_id: usize,
    ot_idx: u32,
    req: &RlweOtReceiverMsg,
    seed0: &[u8; 32],
    seed1: &[u8; 32],
    rng: &mut PartyPrivateRng,
) -> Result<RlweOtSenderMsg, PreprocessError> {
    try_rlwe_ot_transfer(
        session_id,
        sender_id,
        receiver_id,
        ot_idx,
        req,
        seed0,
        seed1,
        rng,
    )
}

fn rlwe_ot_decrypt_ct_mask(
    sec: &RlweOtReceiverSecret,
    a_ntt: &RlwePolyNtt,
    t_crs: &RlwePoly,
    resp: &RlweOtSenderMsg,
) -> Result<([u8; 32], u8), PreprocessError> {
    if !resp.u0.is_canonical()
        || !resp.v0.is_canonical()
        || !resp.u1.is_canonical()
        || !resp.v1.is_canonical()
    {
        return Err(PreprocessError::BaseOtFoCheckFailed {
            sender_id: sec.sender_id,
            receiver_id: sec.receiver_id,
            ot_idx: sec.ot_idx,
        });
    }
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
    let ok_u = u_exp.ct_eq(&u_c) as u8;
    let ok_v = v_exp.ct_eq(&v_c) as u8;
    let ok = black_box(ok_u & ok_v);
    let keep_mask = 0u8.wrapping_sub(ok);
    for b in &mut seed_c {
        *b &= keep_mask;
    }
    Ok((seed_c, ok))
}

fn rlwe_ot_decrypt_with_crs(
    sec: &RlweOtReceiverSecret,
    a_ntt: &RlwePolyNtt,
    t_crs: &RlwePoly,
    resp: &RlweOtSenderMsg,
) -> Result<[u8; 32], PreprocessError> {
    let (mut seed_c, ok) = rlwe_ot_decrypt_ct_mask(sec, a_ntt, t_crs, resp)?;
    if black_box(ok) == 0 {
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

/// Bulk two-lane BDOZ inner product in the protocol's tower basis.
/// Converts both inputs through the exact field isomorphism before dispatch;
/// backend failures propagate without accepting a partial check.
pub fn batch_bdoz_gf2128_dot(
    backend: &dyn qsag_accel::AcceleratorBackend,
    shares: &[[u128; 2]],
    weights: &[[u128; 2]],
) -> Result<[u128; 2], qsag_accel::AccelError> {
    if shares.len() != weights.len() {
        return Err(qsag_accel::AccelError::LengthMismatch {
            what: "BDOZ weights",
            expected: shares.len(),
            actual: weights.len(),
        });
    }
    let convert = |input: &[[u128; 2]]| {
        let mut converted = SecretBuffer(Vec::with_capacity(input.len()));
        for chunk in input.chunks(32) {
            let mut flat = SecretBuffer([0u128; 64]);
            flat[..chunk.len() * 2].copy_from_slice(chunk.as_flattened());
            qsag_asm::tower128_to_poly128_x64_ct(&mut flat);
            converted.extend((0..chunk.len()).map(|i| (flat[2 * i], flat[2 * i + 1])));
        }
        converted
    };
    let shares = convert(shares);
    let weights = convert(weights);
    let result = SecretBuffer(backend.bdoz_gf2_128_batch_dot(&shares, &weights)?);
    Ok([
        qsag_asm::poly128_to_tower128_ct(result.0.0),
        qsag_asm::poly128_to_tower128_ct(result.0.1),
    ])
}

/// Visit disjoint slots in deterministic index order within each worker.
fn parallel_slots<T: Send, F: Fn(usize, &mut T) + Sync>(slots: &mut [T], f: F) {
    #[cfg(feature = "std")]
    {
        let workers = std::thread::available_parallelism()
            .map_or(1, usize::from)
            .min(12);
        let chunk_len = slots.len().div_ceil(workers).max(1);
        std::thread::scope(|scope| {
            for (chunk, values) in slots.chunks_mut(chunk_len).enumerate() {
                let f = &f;
                scope.spawn(move || {
                    for (offset, value) in values.iter_mut().enumerate() {
                        f(chunk * chunk_len + offset, value);
                    }
                });
            }
        });
    }
    #[cfg(not(feature = "std"))]
    for (index, value) in slots.iter_mut().enumerate() {
        f(index, value);
    }
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
    let mut st = combiner_step_state(session_id, row_idx, step_idx, beta, gamma, label_a, seed_b);
    keccak_f1600(&mut st);
    let mut out = [0u8; 32];
    for i in 0..4 {
        out[8 * i..8 * i + 8].copy_from_slice(&st[i].to_le_bytes());
    }
    wipe_u64s(&mut st);
    out
}

fn combiner_step_state(
    session_id: &[u8; 32],
    row_idx: usize,
    step_idx: usize,
    beta: u8,
    gamma: u8,
    label_a: &[u8; 32],
    seed_b: &[u8; 32],
) -> [u64; 25] {
    let mut st = [0u64; 25];
    st[0] = u64::from_le_bytes(*b"QSAG.OT.");
    st[1] = u64::from_le_bytes(*b"PARCOMB1");
    for i in 0..4 {
        let o = 8 * i;
        st[2 + i] = u64::from_le_bytes(core::array::from_fn(|array_index| {
            (session_id[o..o + 8])[array_index]
        }));
        st[6 + i] = u64::from_le_bytes(core::array::from_fn(|array_index| {
            (label_a[o..o + 8])[array_index]
        }));
        st[10 + i] = u64::from_le_bytes(core::array::from_fn(|array_index| {
            (seed_b[o..o + 8])[array_index]
        }));
    }
    st[14] =
        ((row_idx as u64) << 32) | ((step_idx as u64) << 8) | ((beta as u64) << 1) | (gamma as u64);
    st[15] = 0x1f;
    st[16] = 0x8000_0000_0000_0000;
    st
}

fn combiner_step_hash32_x4(
    session_id: &[u8; 32],
    row: usize,
    step: usize,
    labels: &([u8; 32], [u8; 32]),
    seeds: &([u8; 32], [u8; 32]),
) -> [[u8; 32]; 4] {
    let mut states = SecretBuffer(core::array::from_fn::<_, 4, _>(|slot| {
        combiner_step_state(
            session_id,
            row,
            step,
            (slot / 2) as u8,
            (slot % 2) as u8,
            if slot / 2 == 0 { &labels.0 } else { &labels.1 },
            if slot % 2 == 0 { &seeds.0 } else { &seeds.1 },
        )
    }));
    qsag_asm::keccak_f1600_batch(&mut states[..]);
    core::array::from_fn(|slot| core::array::from_fn(|b| states[slot][b / 8].to_le_bytes()[b % 8]))
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
/// Number of 128-slot Multi-CRS Ring-LWE Base-OT blocks (`3 * 128 = 384` OTs, `3` OR-Sigma proofs).
pub const RLWE_BASE_OT_BLOCKS: usize = 3;
/// Number of independent CRS Ring-LWE OT slots packed per short Ring-LWE secret (`128`).
pub const RLWE_BASE_OT_SLOTS_PER_BLOCK: usize = RLWE_BASE_OT_COUNT / RLWE_BASE_OT_BLOCKS;

#[derive(Clone, Debug)]
pub struct BaseOtRound1Msg {
    /// `384` Ring-LWE receiver public keys `pk0[m] = a_m * s_{m / 128} + e_m - b_m * t_m`.
    pub pk0s: Vec<RlwePoly>,
    /// `3` constant-time 13-rep OR-Sigma ZKPoKs on block anchors `(a_{128*blk}, t_{128*blk}, pk0[128*blk])`.
    pub block_poks: Vec<RlweReceiverZkPok>,
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
    cshake256_32_multi_frame(
        b"QSAG.OT.CRS.COMMIT/v1",
        &[session_id, &s_be, &r_be, &p_be, share],
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
    cshake256_32_multi_frame(
        b"QSAG.OT.COMBINER.COMMIT/v1",
        &[session_id, &s_be, &r_be, &p_be, share],
    )
}

// Bound additional proof workers across concurrent mesh bootstraps.
#[cfg(any(test, feature = "std"))]
static BASE_PROOF_WORKERS: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);
#[cfg(any(test, feature = "std"))]
struct BaseProofWorkers {
    count: usize,
}
#[cfg(any(test, feature = "std"))]
impl BaseProofWorkers {
    fn acquire(requested: usize) -> Self {
        use core::sync::atomic::Ordering;
        let mut current = BASE_PROOF_WORKERS.load(Ordering::Relaxed);
        loop {
            let count = requested.min(32usize.saturating_sub(current)).max(1);
            match BASE_PROOF_WORKERS.compare_exchange_weak(
                current,
                current + count - 1,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                Ok(_) => return Self { count },
                Err(value) => current = value,
            }
        }
    }
}
#[cfg(any(test, feature = "std"))]
impl Drop for BaseProofWorkers {
    fn drop(&mut self) {
        BASE_PROOF_WORKERS.fetch_sub(self.count - 1, core::sync::atomic::Ordering::Relaxed);
    }
}

impl BaseOtExtSenderRound1 {
    fn build_packed_block(
        crs_coin: &[u8; 32],
        session_id: &[u8; 32],
        ext_sender_id: usize,
        ext_receiver_id: usize,
        blk: usize,
        c_tilde_words: &[u64; RLWE_BASE_OT_WORDS],
        rng: &mut PartyPrivateRng,
    ) -> (Vec<RlweOtReceiverSecret>, Vec<RlwePoly>, RlweReceiverZkPok) {
        let m0 = blk * RLWE_BASE_OT_SLOTS_PER_BLOCK;
        let (mut s_blk, mut e0) = loop {
            let mut s = RlwePoly::sample_ternary_eta1(rng);
            let mut e = RlwePoly::sample_ternary_eta1(rng);
            if black_box(bounded_ternary_witness(&s, &e)) {
                break (s, e);
            }
            wipe_u16s(&mut s.0);
            wipe_u16s(&mut e.0);
        };
        let mut s_blk_ntt = s_blk.to_ntt();
        let a0_ntt = RlwePoly::from_crs_xof_with_coin(
            crs_coin,
            session_id,
            ext_receiver_id,
            ext_sender_id,
            m0 as u32,
            0,
        )
        .to_ntt();
        let t0 = RlwePoly::from_crs_xof_with_coin(
            crs_coin,
            session_id,
            ext_receiver_id,
            ext_sender_id,
            m0 as u32,
            1,
        );
        let bit0 = ((c_tilde_words[m0 / 64] >> (m0 % 64)) & 1) == 1;
        let rlwe0 = s_blk.mul_ntt(&a0_ntt).add(&e0);
        let shifted0 = rlwe0.sub(&t0);
        let pk0_0 = RlwePoly::ct_select(bit0, &shifted0, &rlwe0);
        let pok = RlweReceiverZkPok::prove_ct(
            crs_coin,
            session_id,
            ext_receiver_id,
            ext_sender_id,
            m0 as u32,
            &a0_ntt,
            &t0,
            &pk0_0,
            &s_blk,
            &e0,
            bit0,
            rng,
        );
        wipe_u16s(&mut e0.0);

        let mut secs = Vec::with_capacity(RLWE_BASE_OT_SLOTS_PER_BLOCK);
        let mut pk0s = Vec::with_capacity(RLWE_BASE_OT_SLOTS_PER_BLOCK);
        secs.push(RlweOtReceiverSecret {
            crs_coin: *crs_coin,
            session_id: *session_id,
            sender_id: ext_receiver_id,
            receiver_id: ext_sender_id,
            ot_idx: m0 as u32,
            pk0: pk0_0,
            s_r: s_blk,
            choice_bit: bit0,
        });
        pk0s.push(pk0_0);

        for slot in 1..RLWE_BASE_OT_SLOTS_PER_BLOCK {
            let m = m0 + slot;
            let bit_m = ((c_tilde_words[m / 64] >> (m % 64)) & 1) == 1;
            let a_m = RlwePoly::from_crs_xof_with_coin(
                crs_coin,
                session_id,
                ext_receiver_id,
                ext_sender_id,
                m as u32,
                0,
            );
            let t_m = RlwePoly::from_crs_xof_with_coin(
                crs_coin,
                session_id,
                ext_receiver_id,
                ext_sender_id,
                m as u32,
                1,
            );
            let mut e_m = RlwePoly::sample_ternary_eta1(rng);
            let rlwe_m = a_m.mul_ntt(&s_blk_ntt).add(&e_m);
            wipe_u16s(&mut e_m.0);
            let shifted_m = rlwe_m.sub(&t_m);
            let pk0_m = RlwePoly::ct_select(bit_m, &shifted_m, &rlwe_m);
            secs.push(RlweOtReceiverSecret {
                crs_coin: *crs_coin,
                session_id: *session_id,
                sender_id: ext_receiver_id,
                receiver_id: ext_sender_id,
                ot_idx: m as u32,
                pk0: pk0_m,
                s_r: s_blk,
                choice_bit: bit_m,
            });
            pk0s.push(pk0_m);
        }
        wipe_u16s(&mut s_blk_ntt.0);
        wipe_u16s(&mut s_blk.0);
        (secs, pk0s, pok)
    }

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
        let mut sec_states = Vec::with_capacity(RLWE_BASE_OT_COUNT);
        let mut pk0s = Vec::with_capacity(RLWE_BASE_OT_COUNT);
        let mut block_poks = Vec::with_capacity(RLWE_BASE_OT_BLOCKS);

        #[cfg(any(test, feature = "std"))]
        {
            let mut jobs: Vec<_> = (0..RLWE_BASE_OT_BLOCKS)
                .map(|blk| {
                    (
                        blk,
                        PartyPrivateRng::from_seed(
                            sender_rng.next_bytes32(),
                            b"QSAG.BASE_OT.PROOF/v2",
                        ),
                    )
                })
                .collect();
            let requested = std::thread::available_parallelism()
                .map_or(1, usize::from)
                .min(RLWE_BASE_OT_BLOCKS);
            let budget = BaseProofWorkers::acquire(requested);
            let chunk_size = jobs.len().div_ceil(budget.count);
            let results = std::thread::scope(|scope| {
                let words = &c_tilde_words;
                let handles: Vec<_> = jobs
                    .chunks_mut(chunk_size)
                    .map(|chunk| {
                        scope.spawn(move || {
                            chunk
                                .iter_mut()
                                .map(|(blk, rng)| {
                                    Self::build_packed_block(
                                        &crs_coin,
                                        &session_id,
                                        ext_sender_id,
                                        ext_receiver_id,
                                        *blk,
                                        words,
                                        rng,
                                    )
                                })
                                .collect::<Vec<_>>()
                        })
                    })
                    .collect();
                handles
                    .into_iter()
                    .flat_map(|h| h.join().expect("base proof worker failed"))
                    .collect::<Vec<_>>()
            });
            for (secs, pks, pok) in results {
                sec_states.extend(secs);
                pk0s.extend(pks);
                block_poks.push(pok);
            }
        }
        #[cfg(not(any(test, feature = "std")))]
        for blk in 0..RLWE_BASE_OT_BLOCKS {
            let (secs, pks, pok) = Self::build_packed_block(
                &crs_coin,
                &session_id,
                ext_sender_id,
                ext_receiver_id,
                blk,
                &c_tilde_words,
                sender_rng,
            );
            sec_states.extend(secs);
            pk0s.extend(pks);
            block_poks.push(pok);
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
            BaseOtRound1Msg { pk0s, block_poks },
        )
    }

    /// Step 1 (`OT-Ext Sender` local): sample 384 random Base-OT choice bits $\tilde{\mathbf{c}}$
    /// using ONLY `sender_rng` and emit `BaseOtRound1Msg` (3 packed 128-slot blocks with OR-Sigma ZKPoKs).
    pub fn start(
        session_id: [u8; 32],
        ext_sender_id: usize,
        ext_receiver_id: usize,
        sender_rng: &mut PartyPrivateRng,
    ) -> (Self, BaseOtRound1Msg) {
        Self::start_with_crs(
            [0u8; 32],
            session_id,
            ext_sender_id,
            ext_receiver_id,
            sender_rng,
        )
    }

    /// Step 3 (`OT-Ext Sender` local): verify all 384 Fujisaki–Okamoto re-encryptions in **strict
    /// constant time across all 384 branches** (`0` early-abort index timing leak!) before sampling
    /// or revealing any combiner coin.
    pub fn verify_fo_and_respond_coin(
        mut self,
        msg2: &BaseOtRound2Msg,
        sender_rng: &mut PartyPrivateRng,
    ) -> Result<(BaseOtExtSenderRound3, BaseOtRound3Msg), PreprocessError> {
        if msg2.reqs_len_mismatch(RLWE_BASE_OT_COUNT)
            || msg2.resps.iter().any(|r| {
                !r.u0.is_canonical()
                    || !r.v0.is_canonical()
                    || !r.u1.is_canonical()
                    || !r.v1.is_canonical()
            })
        {
            return Err(PreprocessError::BaseOtFoCheckFailed {
                sender_id: self.ext_receiver_id,
                receiver_id: self.ext_sender_id,
                ot_idx: 0,
            });
        }
        let mut base_seeds = SecretBuffer(vec![[0u8; 32]; RLWE_BASE_OT_COUNT]);
        let mut results = (0..RLWE_BASE_OT_COUNT)
            .map(|_| (SecretBuffer([0u8; 32]), Ok(0u8)))
            .collect::<Vec<_>>();
        parallel_slots(&mut results, |m, result| {
            result.1 = (|| {
                let a_ntt = RlwePoly::from_crs_xof_with_coin(
                    &self.crs_coin,
                    &self.session_id,
                    self.ext_receiver_id,
                    self.ext_sender_id,
                    m as u32,
                    0,
                )
                .to_ntt();
                let t_crs = RlwePoly::from_crs_xof_with_coin(
                    &self.crs_coin,
                    &self.session_id,
                    self.ext_receiver_id,
                    self.ext_sender_id,
                    m as u32,
                    1,
                );
                let (seed_m, ok_m) =
                    rlwe_ot_decrypt_ct_mask(&self.sec_states[m], &a_ntt, &t_crs, &msg2.resps[m])?;
                *result.0 = seed_m;
                Ok::<_, PreprocessError>(ok_m)
            })();
        });
        let mut all_ok = 1u8;
        for (m, result) in results.into_iter().enumerate() {
            let (seed, ok) = result;
            base_seeds[m] = *seed;
            all_ok &= ok?;
        }
        if black_box(all_ok) == 0 {
            return Err(PreprocessError::BaseOtFoCheckFailed {
                sender_id: self.ext_receiver_id,
                receiver_id: self.ext_sender_id,
                ot_idx: 0,
            });
        }
        let my_coin_share = sender_rng.next_bytes32();
        let c_tilde_words = self.c_tilde_words;
        wipe_u64s(&mut self.c_tilde_words);
        let verified_base_seeds = core::mem::take(&mut base_seeds.0);
        Ok((
            BaseOtExtSenderRound3 {
                session_id: self.session_id,
                ext_sender_id: self.ext_sender_id,
                ext_receiver_id: self.ext_receiver_id,
                c_tilde_words,
                base_seeds: verified_base_seeds,
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
    /// Step 2 (`OT-Ext Receiver` local) bound to jointly committed `crs_coin`: verifies all 3
    /// block Receiver OR-Sigma ZKPoKs (`BaseOtReceiverProofFailed` on tamper!) before FO-encrypting
    /// all 384 seed pairs under per-slot `(a_m, t_m)` (`PVW08` lossy-branch security on every slot).
    pub fn respond_with_crs(
        crs_coin: [u8; 32],
        session_id: [u8; 32],
        ext_sender_id: usize,
        ext_receiver_id: usize,
        msg1: &BaseOtRound1Msg,
        receiver_rng: &mut PartyPrivateRng,
    ) -> Result<(Self, BaseOtRound2Msg), PreprocessError> {
        if msg1.pk0s.len() != RLWE_BASE_OT_COUNT || msg1.block_poks.len() != RLWE_BASE_OT_BLOCKS {
            return Err(PreprocessError::BaseOtFoCheckFailed {
                sender_id: ext_receiver_id,
                receiver_id: ext_sender_id,
                ot_idx: 0,
            });
        }
        if msg1.pk0s.iter().any(|p| !p.is_canonical()) {
            return Err(PreprocessError::BaseOtReceiverProofFailed {
                sender_id: ext_receiver_id,
                receiver_id: ext_sender_id,
            });
        }
        let mut proof_valid = [false; RLWE_BASE_OT_BLOCKS];
        parallel_slots(&mut proof_valid, |blk, valid| {
            let m0 = (blk * RLWE_BASE_OT_SLOTS_PER_BLOCK) as u32;
            let a0_ntt = RlwePoly::from_crs_xof_with_coin(
                &crs_coin,
                &session_id,
                ext_receiver_id,
                ext_sender_id,
                m0,
                0,
            )
            .to_ntt();
            let t0 = RlwePoly::from_crs_xof_with_coin(
                &crs_coin,
                &session_id,
                ext_receiver_id,
                ext_sender_id,
                m0,
                1,
            );
            *valid = msg1.block_poks[blk].verify(
                &crs_coin,
                &session_id,
                ext_receiver_id,
                ext_sender_id,
                m0,
                &a0_ntt,
                &t0,
                &msg1.pk0s[m0 as usize],
            );
        });
        if proof_valid.iter().any(|valid| !valid) {
            return Err(PreprocessError::BaseOtReceiverProofFailed {
                sender_id: ext_receiver_id,
                receiver_id: ext_sender_id,
            });
        }
        // Preserve the RNG schedule independently of worker scheduling.
        let mut seeds = SecretBuffer(
            (0..RLWE_BASE_OT_COUNT)
                .map(|_| {
                    [
                        receiver_rng.next_bytes32(),
                        receiver_rng.next_bytes32(),
                        receiver_rng.next_bytes32(),
                        receiver_rng.next_bytes32(),
                    ]
                })
                .collect::<Vec<_>>(),
        );
        let mut results = (0..RLWE_BASE_OT_COUNT).map(|_| None).collect::<Vec<_>>();
        parallel_slots(&mut results, |m, result| {
            let pk0 = &msg1.pk0s[m];
            let [mut s0, mut s1, mut rho0, mut rho1] = seeds[m];
            let a_ntt = RlwePoly::from_crs_xof_with_coin(
                &crs_coin,
                &session_id,
                ext_receiver_id,
                ext_sender_id,
                m as u32,
                0,
            )
            .to_ntt();
            let t_crs = RlwePoly::from_crs_xof_with_coin(
                &crs_coin,
                &session_id,
                ext_receiver_id,
                ext_sender_id,
                m as u32,
                1,
            );
            let pk1 = pk0.add(&t_crs);
            let (u0, v0) = rlwe_fo_encrypt_branch(
                &crs_coin,
                &session_id,
                ext_receiver_id,
                ext_sender_id,
                m as u32,
                0,
                &a_ntt,
                pk0,
                &s0,
                &rho0,
            );
            let (u1, v1) = rlwe_fo_encrypt_branch(
                &crs_coin,
                &session_id,
                ext_receiver_id,
                ext_sender_id,
                m as u32,
                1,
                &a_ntt,
                &pk1,
                &s1,
                &rho1,
            );
            wipe_bytes32(&mut rho0);
            wipe_bytes32(&mut rho1);
            wipe_bytes32(&mut s0);
            wipe_bytes32(&mut s1);
            *result = Some(RlweOtSenderMsg { u0, v0, u1, v1 });
        });
        let mut base_seed_pairs = Vec::with_capacity(RLWE_BASE_OT_COUNT);
        for seed in seeds.iter_mut() {
            base_seed_pairs.push((seed[0], seed[1]));
            for value in seed {
                wipe_bytes32(value);
            }
        }
        let resps = results
            .into_iter()
            .map(|r| r.expect("every slot is evaluated"))
            .collect();
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

        let supports: Vec<Vec<usize>> = extractor
            .iter()
            .map(|bits| {
                (0..RLWE_BASE_OT_COUNT)
                    .filter(|&m| ((bits[m / 64] >> (m % 64)) & 1) == 1)
                    .collect()
            })
            .collect();
        // Draw all masks in the original row/step order before scheduling work.
        let masks = SecretBuffer(
            supports
                .iter()
                .map(|support| {
                    (1..support.len())
                        .map(|_| (comb_rng.next_bytes32(), comb_rng.next_bytes32()))
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>(),
        );
        let mut rows = SecretBuffer(vec![(([0u8; 32], [0u8; 32]), Vec::new()); 128]);
        parallel_slots(&mut rows[..], |row, output| {
            let support = &supports[row];
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
                let (next_l0, next_l1) = masks[row][step_minus1];
                let mut tbl = [[0u8; 32]; 4];
                let pads = SecretBuffer(combiner_step_hash32_x4(
                    &self.session_id,
                    row,
                    step,
                    &(cur_l0, cur_l1),
                    &self.base_seed_pairs[mr],
                ));
                for slot in 0..4 {
                    let target = if (slot / 2) ^ (slot % 2) == 0 {
                        &next_l0
                    } else {
                        &next_l1
                    };
                    for b in 0..32 {
                        tbl[slot][b] = target[b] ^ pads[slot][b];
                    }
                }
                wipe_bytes32(&mut cur_l0);
                wipe_bytes32(&mut cur_l1);
                cur_l0 = next_l0;
                cur_l1 = next_l1;
                row_tables.push(tbl);
            }
            *output = ((cur_l0, cur_l1), row_tables);
        });
        let mut combined_seed_pairs = [([0u8; 32], [0u8; 32]); 128];
        let mut parity_tables = Vec::with_capacity(128);
        for (row, (mut pair, tables)) in core::mem::take(&mut rows.0).into_iter().enumerate() {
            combined_seed_pairs[row] = pair;
            wipe_bytes32(&mut pair.0);
            wipe_bytes32(&mut pair.1);
            parity_tables.push(tables);
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

        let supports: Vec<Vec<usize>> = extractor
            .iter()
            .map(|bits| {
                (0..RLWE_BASE_OT_COUNT)
                    .filter(|&m| ((bits[m / 64] >> (m % 64)) & 1) == 1)
                    .collect()
            })
            .collect();
        for (row, support) in supports.iter().enumerate() {
            if msg4.parity_tables[row].len() + 1 != support.len() {
                return Err(PreprocessError::KosOtCheckFailed {
                    sender_id: self.ext_sender_id,
                    receiver_id: self.ext_receiver_id,
                });
            }
        }
        let mut row_bits = [0u8; 128];
        let mut rows = SecretBuffer([([0u8; 32], 0u8); 128]);
        parallel_slots(&mut rows[..], |row, output| {
            let support = &supports[row];
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
            *output = (cur_label, acc_bit);
        });
        for row in 0..128 {
            combined_seeds[row] = rows[row].0;
            row_bits[row] = rows[row].1;
            delta |= (row_bits[row] as u128) << row;
        }
        wipe_bytes(&mut row_bits);

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
    let (crs_s0, crs_sh) =
        BaseOtCrsSenderRound0::respond(session_id, sender_id, receiver_id, &crs_com, sender_rng);
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
/// committed CRS and KOS attacks also have a real default end-to-end regression.
#[cfg(test)]
fn establish_ideal_ot_ext_channel_for_test(
    session_id: [u8; 32],
    sender_id: usize,
    receiver_id: usize,
    sender_rng: &mut PartyPrivateRng,
    receiver_rng: &mut PartyPrivateRng,
) -> (OtExtSenderChannel, OtExtReceiverChannel) {
    let delta = u128::from(sender_rng.next_u64()) | (u128::from(sender_rng.next_u64()) << 64);
    let pairs: [([u8; 32], [u8; 32]); 128] =
        core::array::from_fn(|_| (receiver_rng.next_bytes32(), receiver_rng.next_bytes32()));
    let selected = core::array::from_fn(|i| {
        if (delta >> i) & 1 == 0 {
            pairs[i].0
        } else {
            pairs[i].1
        }
    });
    (
        OtExtSenderChannel {
            session_id,
            sender_id,
            receiver_id,
            delta,
            combined_seeds: selected,
            batch_ctr: 0,
            poisoned: false,
        },
        OtExtReceiverChannel {
            session_id,
            sender_id,
            receiver_id,
            combined_seed_pairs: pairs,
            batch_ctr: 0,
        },
    )
}

/// Fallible full-protocol bootstrap; identical in production and test builds.
pub fn establish_rlwe_ot_ext_channel(
    session_id: [u8; 32],
    sender_id: usize,
    receiver_id: usize,
    sender_rng: &mut PartyPrivateRng,
    receiver_rng: &mut PartyPrivateRng,
) -> Result<(OtExtSenderChannel, OtExtReceiverChannel), PreprocessError> {
    try_establish_rlwe_ot_ext_channel(session_id, sender_id, receiver_id, sender_rng, receiver_rng)
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
    #[expect(
        clippy::chunks_exact_to_as_chunks,
        reason = "Keep the workspace Rust 1.85 minimum; slice as_chunks requires a newer compiler"
    )]
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
            for i in 0..64 {
                rows[64 * w + i] |= (tile[i] as u128) << (64 * half);
            }
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
    cshake256_32_multi_frame(
        b"QSAG.OT.KOS.BIND/v2",
        &[u_cols_digest, chi_seed, &x_bytes, &t_bytes],
    )
}

/// Fast 4-way SIMD (`keccak_f1600_x4`) single-block `SHAKE256` transcript-bound correlation-robust
/// hash batch for receiver rows `t_rows[0..payload_rows]`.
fn crh_ot_receiver_pads_batch(
    session_id: &[u8; 32],
    transcript_bind: &[u8; 32],
    sender_id: usize,
    receiver_id: usize,
    batch_ctr: u64,
    t_rows: &[u128],
) -> Vec<[u8; 48]> {
    let payload_rows = t_rows.len();
    let mut pads = vec![[0u8; 48]; payload_rows];
    if payload_rows == 0 {
        return pads;
    }
    let sid_words: [u64; 4] = core::array::from_fn(|i| {
        let o = 8 * i;
        u64::from_le_bytes(core::array::from_fn(|b| session_id[o + b]))
    });
    let bind_words: [u64; 4] = core::array::from_fn(|i| {
        let o = 8 * i;
        u64::from_le_bytes(core::array::from_fn(|b| transcript_bind[o + b]))
    });
    let backend = qsag_asm::detect_backend();

    let eval_range = |base_ell: usize, rows_slice: &[u128], out_slice: &mut [[u8; 48]]| {
        let w0 = [u64::from_le_bytes(*b"QSAG.CRH"); 4];
        let w1 = [u64::from_le_bytes(*b".OT.V002"); 4];
        let mut st = qsag_asm::KeccakState4x::default();
        for (chunk_idx, (r_chunk, o_chunk)) in rows_slice
            .chunks(4)
            .zip(out_slice.chunks_mut(4))
            .enumerate()
        {
            st.0 = [[0u64; 4]; 25];
            st.0[0] = w0;
            st.0[1] = w1;
            for i in 0..4 {
                st.0[2 + i] = [sid_words[i]; 4];
                st.0[6 + i] = [bind_words[i]; 4];
            }
            st.0[10] = [sender_id as u64; 4];
            st.0[11] = [receiver_id as u64; 4];
            st.0[12] = [batch_ctr; 4];
            for (slot, &row) in r_chunk.iter().enumerate() {
                st.0[13][slot] = (base_ell + 4 * chunk_idx + slot) as u64;
                st.0[14][slot] = row as u64;
                st.0[15][slot] = (row >> 64) as u64;
            }
            st.0[16] = [0x8000_0000_0000_001f; 4];
            qsag_asm::keccak_f1600_x4_with_backend(&mut st, backend);
            for (slot, dst) in o_chunk.iter_mut().enumerate() {
                for w in 0..6 {
                    dst[8 * w..8 * w + 8].copy_from_slice(&st.0[w][slot].to_le_bytes());
                }
            }
        }
        qsag_asm::volatile_fill(&mut st.0, [0u64; 4]);
    };

    #[cfg(any(test, feature = "std"))]
    if payload_rows >= 2048 {
        let workers = std::thread::available_parallelism()
            .map_or(1, usize::from)
            .min(16);
        let chunk_len = payload_rows.div_ceil(workers).max(64);
        std::thread::scope(|scope| {
            for (c_idx, (r_sub, o_sub)) in t_rows
                .chunks(chunk_len)
                .zip(pads.chunks_mut(chunk_len))
                .enumerate()
            {
                let base_ell = c_idx * chunk_len;
                scope.spawn(move || eval_range(base_ell, r_sub, o_sub));
            }
        });
        return pads;
    }
    eval_range(0, t_rows, &mut pads);
    pads
}

/// Fast 4-way SIMD (`keccak_f1600_x4`) single-block `SHAKE256` transcript-bound correlation-robust
/// hash batch for sender row pairs `(q_rows[ell], q_rows[ell] ^ delta)`.
fn crh_ot_sender_pad_pairs_batch(
    session_id: &[u8; 32],
    transcript_bind: &[u8; 32],
    sender_id: usize,
    receiver_id: usize,
    batch_ctr: u64,
    delta: u128,
    q_rows: &[u128],
) -> Vec<OtPadPair> {
    let payload_rows = q_rows.len();
    let mut pad_pairs = vec![([0u8; 48], [0u8; 48]); payload_rows];
    if payload_rows == 0 {
        return pad_pairs;
    }
    let sid_words: [u64; 4] = core::array::from_fn(|i| {
        let o = 8 * i;
        u64::from_le_bytes(core::array::from_fn(|b| session_id[o + b]))
    });
    let bind_words: [u64; 4] = core::array::from_fn(|i| {
        let o = 8 * i;
        u64::from_le_bytes(core::array::from_fn(|b| transcript_bind[o + b]))
    });
    let backend = qsag_asm::detect_backend();

    let eval_range = |base_ell: usize, rows_slice: &[u128], out_slice: &mut [OtPadPair]| {
        let w0 = [u64::from_le_bytes(*b"QSAG.CRH"); 4];
        let w1 = [u64::from_le_bytes(*b".OT.V002"); 4];
        let mut st = qsag_asm::KeccakState4x::default();
        // 2 rows (`(q0, q0^delta)` and `(q1, q1^delta)`) = 4 parallel Keccak states!
        for (pair_idx, (r_chunk, o_chunk)) in rows_slice
            .chunks(2)
            .zip(out_slice.chunks_mut(2))
            .enumerate()
        {
            st.0 = [[0u64; 4]; 25];
            st.0[0] = w0;
            st.0[1] = w1;
            for i in 0..4 {
                st.0[2 + i] = [sid_words[i]; 4];
                st.0[6 + i] = [bind_words[i]; 4];
            }
            st.0[10] = [sender_id as u64; 4];
            st.0[11] = [receiver_id as u64; 4];
            st.0[12] = [batch_ctr; 4];
            for (sub, &q) in r_chunk.iter().enumerate() {
                let ell = (base_ell + 2 * pair_idx + sub) as u64;
                let q1 = q ^ delta;
                st.0[13][2 * sub] = ell;
                st.0[14][2 * sub] = q as u64;
                st.0[15][2 * sub] = (q >> 64) as u64;
                st.0[13][2 * sub + 1] = ell;
                st.0[14][2 * sub + 1] = q1 as u64;
                st.0[15][2 * sub + 1] = (q1 >> 64) as u64;
            }
            st.0[16] = [0x8000_0000_0000_001f; 4];
            qsag_asm::keccak_f1600_x4_with_backend(&mut st, backend);
            for (sub, (p0, p1)) in o_chunk.iter_mut().enumerate() {
                for w in 0..6 {
                    p0[8 * w..8 * w + 8].copy_from_slice(&st.0[w][2 * sub].to_le_bytes());
                    p1[8 * w..8 * w + 8].copy_from_slice(&st.0[w][2 * sub + 1].to_le_bytes());
                }
            }
        }
        qsag_asm::volatile_fill(&mut st.0, [0u64; 4]);
    };

    #[cfg(any(test, feature = "std"))]
    if payload_rows >= 1024 {
        let workers = std::thread::available_parallelism()
            .map_or(1, usize::from)
            .min(16);
        let chunk_len = payload_rows.div_ceil(workers).max(64);
        std::thread::scope(|scope| {
            for (c_idx, (r_sub, o_sub)) in q_rows
                .chunks(chunk_len)
                .zip(pad_pairs.chunks_mut(chunk_len))
                .enumerate()
            {
                let base_ell = c_idx * chunk_len;
                scope.spawn(move || eval_range(base_ell, r_sub, o_sub));
            }
        });
        return pad_pairs;
    }
    eval_range(0, q_rows, &mut pad_pairs);
    pad_pairs
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
    #[expect(
        clippy::chunks_exact_to_as_chunks,
        reason = "Keep the workspace Rust 1.85 minimum; slice as_chunks requires a newer compiler"
    )]
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
        assert!(
            self.batch_ctr < u64::MAX,
            "OtExtReceiverChannel batch counter exhausted"
        );
        let payload_words = choice_words.len();
        let padded_words = payload_words + 4; // +256 sacrificial OTs masking x_kos & t_kos
        let batch_ctr = self.batch_ctr;
        self.batch_ctr += 1;

        let mut full_choices = Vec::with_capacity(padded_words);
        full_choices.extend_from_slice(choice_words);
        for _ in 0..4 {
            full_choices.push(rng.next_u64());
        }

        let mut t0_cols = vec![Vec::new(); 128];
        let mut u_cols = vec![Vec::new(); 128];
        #[cfg(any(test, feature = "std"))]
        if padded_words >= 64 {
            let sid = &self.session_id;
            let pairs = &self.combined_seed_pairs;
            let choices_ref = &full_choices;
            std::thread::scope(|scope| {
                for (c_idx, (t0_sub, u_sub)) in t0_cols
                    .chunks_mut(16)
                    .zip(u_cols.chunks_mut(16))
                    .enumerate()
                {
                    let base_i = 16 * c_idx;
                    scope.spawn(move || {
                        for (off, (t0_dst, u_dst)) in
                            t0_sub.iter_mut().zip(u_sub.iter_mut()).enumerate()
                        {
                            let i = base_i + off;
                            let t0 = expand_prg_column_u64s(
                                sid,
                                batch_ctr,
                                i,
                                &pairs[i].0,
                                padded_words,
                            );
                            let mut t1 = expand_prg_column_u64s(
                                sid,
                                batch_ctr,
                                i,
                                &pairs[i].1,
                                padded_words,
                            );
                            let mut u = Vec::with_capacity(padded_words);
                            for w in 0..padded_words {
                                u.push(t0[w] ^ t1[w] ^ choices_ref[w]);
                            }
                            wipe_u64s(&mut t1);
                            *t0_dst = t0;
                            *u_dst = u;
                        }
                    });
                }
            });
        } else {
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
                t0_cols[i] = t0;
                u_cols[i] = u;
            }
        }
        #[cfg(not(any(test, feature = "std")))]
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
            t0_cols[i] = t0;
            u_cols[i] = u;
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
        let pads = crh_ot_receiver_pads_batch(
            &self.session_id,
            &bind,
            self.sender_id,
            self.receiver_id,
            pending.batch_ctr,
            &pending.t_rows[..payload_rows],
        );
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
        if self.batch_ctr == u64::MAX {
            self.poison_and_wipe();
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
            || u_msg.u_cols.iter().any(|c| c.len() != padded_words)
        {
            self.poison_and_wipe();
            return Err(PreprocessError::KosOtCheckFailed {
                sender_id: self.sender_id,
                receiver_id: self.receiver_id,
            });
        }
        let payload_words = padded_words - 4;
        let batch_ctr = self.batch_ctr;
        self.batch_ctr += 1;

        let mut q_cols = vec![Vec::new(); 128];
        #[cfg(any(test, feature = "std"))]
        if padded_words >= 64 {
            let sid = &self.session_id;
            let seeds = &self.combined_seeds;
            let delta = self.delta;
            let u_cols_ref = &u_msg.u_cols;
            std::thread::scope(|scope| {
                for (c_idx, q_sub) in q_cols.chunks_mut(16).enumerate() {
                    let base_i = 16 * c_idx;
                    scope.spawn(move || {
                        for (off, q_dst) in q_sub.iter_mut().enumerate() {
                            let i = base_i + off;
                            let mut ti =
                                expand_prg_column_u64s(sid, batch_ctr, i, &seeds[i], padded_words);
                            let di_bit = ((delta >> i) & 1) as u64;
                            let di_mask = 0u64.wrapping_sub(black_box(di_bit));
                            for (w, ti_w_item) in ti[..padded_words].iter_mut().enumerate() {
                                *ti_w_item ^= di_mask & u_cols_ref[i][w];
                            }
                            *q_dst = ti;
                        }
                    });
                }
            });
        } else {
            for (i, q_col) in q_cols.iter_mut().enumerate() {
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
                *q_col = ti;
            }
        }
        #[cfg(not(any(test, feature = "std")))]
        for (i, q_col) in q_cols.iter_mut().enumerate() {
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
            *q_col = ti;
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
        let pad_pairs = crh_ot_sender_pad_pairs_batch(
            &self.session_id,
            &bind,
            self.sender_id,
            self.receiver_id,
            pending.batch_ctr,
            self.delta,
            &pending.q_rows[..payload_rows],
        );
        Ok(pad_pairs)
    }
}

/// Full $n$-party mesh of directional Ring-LWE OT-extension channels (`n * (n - 1)` channels).
pub struct OtMesh {
    pub n: usize,
    pub session_id: [u8; 32],
    senders: Vec<Vec<Option<OtExtSenderChannel>>>,
    receivers: Vec<Vec<Option<OtExtReceiverChannel>>>,
}

type OtChannelSetup = fn(
    [u8; 32],
    usize,
    usize,
    &mut PartyPrivateRng,
    &mut PartyPrivateRng,
) -> Result<(OtExtSenderChannel, OtExtReceiverChannel), PreprocessError>;

impl OtMesh {
    /// Run committed CRS + `384` OR-Sigma ZKPoK + FO-checked Ring-LWE Base OTs + 4-ciphertext
    /// `384 -> 128` parity combiner per ordered pair `(i, j)` (`i != j`).
    pub fn try_establish(
        session_id: [u8; 32],
        party_rngs: &mut [PartyPrivateRng],
    ) -> Result<Self, PreprocessError> {
        Self::try_establish_with(session_id, party_rngs, try_establish_rlwe_ot_ext_channel)
    }

    fn try_establish_with(
        session_id: [u8; 32],
        party_rngs: &mut [PartyPrivateRng],
        setup: OtChannelSetup,
    ) -> Result<Self, PreprocessError> {
        let n = party_rngs.len();
        if n < 2 {
            return Err(PreprocessError::InvalidThreshold { t: 2, n });
        }
        let mut senders: Vec<Vec<Option<OtExtSenderChannel>>> =
            (0..n).map(|_| (0..n).map(|_| None).collect()).collect();
        let mut receivers: Vec<Vec<Option<OtExtReceiverChannel>>> =
            (0..n).map(|_| (0..n).map(|_| None).collect()).collect();

        // Each pair gets fresh private substreams before workers start. No RNG
        // or transcript is shared between threads. Limit concurrency so large
        // committees do not allocate one full base-OT handshake per edge at once.
        #[cfg(any(test, feature = "std"))]
        {
            let mut jobs = Vec::new();
            for i in 0..n {
                for j in 0..n {
                    if i == j {
                        continue;
                    }
                    let sender = PartyPrivateRng::from_seed(
                        party_rngs[i].next_bytes32(),
                        b"QSAG.OT.MESH.SENDER/v1",
                    );
                    let receiver = PartyPrivateRng::from_seed(
                        party_rngs[j].next_bytes32(),
                        b"QSAG.OT.MESH.RECEIVER/v1",
                    );
                    jobs.push((i, j, sender, receiver));
                }
            }
            let workers = std::thread::available_parallelism()
                .map_or(1, usize::from)
                .min(12);
            for batch in jobs.chunks_mut(workers) {
                std::thread::scope(|scope| -> Result<(), PreprocessError> {
                    let handles: Vec<_> = batch
                        .iter_mut()
                        .map(|(i, j, sender, receiver)| {
                            let (i, j) = (*i, *j);
                            (
                                i,
                                j,
                                scope.spawn(move || setup(session_id, i, j, sender, receiver)),
                            )
                        })
                        .collect();
                    for (i, j, handle) in handles {
                        let (sender, receiver) = handle
                            .join()
                            .map_err(|_| PreprocessError::PcgInvalidWireSeed)??;
                        senders[i][j] = Some(sender);
                        receivers[j][i] = Some(receiver);
                    }
                    Ok(())
                })?;
            }
        }
        #[cfg(not(any(test, feature = "std")))]
        for i in 0..n {
            for j in 0..n {
                if i == j {
                    continue;
                }
                let (s_chan, r_chan) = if i < j {
                    let (left, right) = party_rngs.split_at_mut(j);
                    setup(session_id, i, j, &mut left[i], &mut right[0])?
                } else {
                    let (left, right) = party_rngs.split_at_mut(i);
                    setup(session_id, i, j, &mut right[0], &mut left[j])?
                };
                senders[i][j] = Some(s_chan);
                receivers[j][i] = Some(r_chan);
            }
        }
        Ok(Self {
            n,
            session_id,
            senders,
            receivers,
        })
    }

    /// Explicit ideal base OT for fast tests of downstream protocols.
    #[cfg(test)]
    pub(crate) fn establish_ideal_for_test(
        session_id: [u8; 32],
        party_rngs: &mut [PartyPrivateRng],
    ) -> Self {
        Self::try_establish_with(session_id, party_rngs, |sid, i, j, sender, receiver| {
            Ok(establish_ideal_ot_ext_channel_for_test(
                sid, i, j, sender, receiver,
            ))
        })
        .expect("ideal base-OT unit-test mesh")
    }

    /// Fallible real-protocol convenience constructor.
    pub fn establish(
        session_id: [u8; 32],
        party_rngs: &mut [PartyPrivateRng],
    ) -> Result<Self, PreprocessError> {
        Self::try_establish(session_id, party_rngs)
    }

    /// Execute an interactive 3-message KOS correlated OT batch from `sender_id` to `receiver_id`
    /// on `choice_words`, drawing `chi_seed` from `party_rngs[sender_id]` *after* `u_cols` is locked.
    pub fn run_correlated_ot_words(
        &mut self,
        sender_id: usize,
        receiver_id: usize,
        choice_words: &[u64],
        party_rngs: &mut [PartyPrivateRng],
    ) -> Result<OtBatchPads, PreprocessError> {
        if sender_id == receiver_id
            || sender_id >= self.n
            || receiver_id >= self.n
            || party_rngs.len() != self.n
        {
            return Err(PreprocessError::KosOtCheckFailed {
                sender_id,
                receiver_id,
            });
        }
        // Large local preprocessing jobs are split into independently challenged frames.
        // The peer-facing receiver keeps a strict budget even when a vault needs more OTs.
        const WORDS_PER_FRAME: usize = MAX_FRAME_BUDGET / (128 * 8) - 4;
        if choice_words.len() > WORDS_PER_FRAME {
            let (mut send, mut recv) = (OtSendPads(Vec::new()), OtRecvPads(Vec::new()));
            for choices in choice_words.chunks(WORDS_PER_FRAME) {
                let (s, r) =
                    self.run_correlated_ot_words(sender_id, receiver_id, choices, party_rngs)?;
                secret_vec_extend_from_slice(&mut send.0, &s.0);
                secret_vec_extend_from_slice(&mut recv.0, &r.0);
            }
            return Ok((send, recv));
        }
        let (sender_rng, receiver_rng) = if sender_id < receiver_id {
            let (left, right) = party_rngs.split_at_mut(receiver_id);
            (&mut left[sender_id], &mut right[0])
        } else {
            let (left, right) = party_rngs.split_at_mut(sender_id);
            (&mut right[0], &mut left[receiver_id])
        };

        let r_chan = self.receivers[receiver_id][sender_id]
            .as_mut()
            .ok_or(PreprocessError::PcgInvalidWireSeed)?;
        let s_chan = self.senders[sender_id][receiver_id]
            .as_mut()
            .ok_or(PreprocessError::PcgInvalidWireSeed)?;

        let (r_pending, u_msg) = r_chan.round1_send_u_cols(choice_words, receiver_rng);
        let (s_pending, chal_msg) = s_chan.round2_sample_challenge(&u_msg, sender_rng)?;
        let (proof_msg, recv_pads) = r_chan.round3_prove_and_finish(r_pending, &chal_msg);
        let recv_pads = OtRecvPads(recv_pads);
        let send_pads = OtSendPads(s_chan.round4_verify_and_finish(s_pending, &proof_msg)?);
        Ok((send_pads, recv_pads))
    }
}

// ============================================================================
// 3. Commit-and-Open Public Coin Flip (`Π_coin`, `0` Trusted Randomness)
// ============================================================================

/// Commit-and-open multi-party coin toss (`Π_coin`): every party commits `cSHAKE256` to a private
/// 32-byte share before seeing any peer share, then opens and verifies every peer commitment.
pub fn run_commit_and_open_coin(
    session_id: &[u8; 32],
    phase_label: &[u8],
    transcript_digest: &[u8; 32],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<[u8; 32], PreprocessError> {
    run_commit_and_open_coin_with_hook(
        session_id,
        phase_label,
        transcript_digest,
        party_rngs,
        |_, _| {},
    )
}

/// Same as [`run_commit_and_open_coin`], with an adversarial fault-injection hook on opened shares
/// for unit-testing `CoinCommitMismatch` detection.
pub fn run_commit_and_open_coin_with_hook<F>(
    session_id: &[u8; 32],
    phase_label: &[u8],
    transcript_digest: &[u8; 32],
    party_rngs: &mut [PartyPrivateRng],
    mut corrupt_opening: F,
) -> Result<[u8; 32], PreprocessError>
where
    F: FnMut(usize, &mut [u8; 32]),
{
    let n = party_rngs.len();
    let mut shares = Vec::with_capacity(n);
    let mut commits = Vec::with_capacity(n);
    for (p, rng) in party_rngs.iter_mut().enumerate() {
        let r_p = rng.next_bytes32();
        let pid = (p as u64).to_be_bytes();
        let com = cshake256_32_multi_frame(
            b"QSAG.COIN.COMMIT/v1",
            &[session_id, phase_label, transcript_digest, &pid, &r_p],
        );
        shares.push(r_p);
        commits.push(com);
    }

    // Broadcast openings (after all commitments are locked)
    let mut combined = [0u8; 32];
    for p in 0..n {
        let mut opened = shares[p];
        corrupt_opening(p, &mut opened);
        let pid = (p as u64).to_be_bytes();
        let recomputed = cshake256_32_multi_frame(
            b"QSAG.COIN.COMMIT/v1",
            &[session_id, phase_label, transcript_digest, &pid, &opened],
        );
        wipe_bytes32(&mut opened);
        if !ct_eq_bytes32(&recomputed, &commits[p]) {
            for s in &mut shares {
                wipe_bytes32(s);
            }
            wipe_bytes32(&mut combined);
            return Err(PreprocessError::CoinCommitMismatch { party_id: p });
        }
        for b in 0..32 {
            combined[b] ^= shares[p][b];
        }
    }
    for s in &mut shares {
        wipe_bytes32(s);
    }
    let out = cshake256_32_multi_frame(
        b"QSAG.COIN.DERIVE/v1",
        &[session_id, phase_label, transcript_digest, &combined],
    );
    wipe_bytes32(&mut combined);
    Ok(out)
}

// ============================================================================
// 4. Full-Vector `eval_points[0..n]` Degree Verifiers & Committed SPDZ `MacCheck`
// ============================================================================

/// Validate that ALL `n` evaluation points in `eval_points[0..n]` are non-zero and pairwise
/// distinct (`[P0-10]`: prevents `eval_points[m] == 0` for `m >= t` from leaking `f(0)`!).
pub fn validate_all_eval_points_gf256(eval_points: &[TowerGf256]) -> Result<(), PreprocessError> {
    for i in 0..eval_points.len() {
        if eval_points[i] == TowerGf256::ZERO {
            return Err(PreprocessError::DuplicateOrZeroEvalPoint);
        }
        for j in (i + 1)..eval_points.len() {
            if eval_points[i] == eval_points[j] {
                return Err(PreprocessError::DuplicateOrZeroEvalPoint);
            }
        }
    }
    Ok(())
}

/// Validate that ALL `n` `Goldilocks` evaluation points in `eval_points[0..n]` are canonical,
/// non-zero mod $p$, and pairwise distinct (`[P0-10]`).
pub fn validate_all_eval_points_goldilocks(
    eval_points: &[Goldilocks],
) -> Result<(), PreprocessError> {
    for i in 0..eval_points.len() {
        if eval_points[i].to_canonical_u64() == 0 {
            return Err(PreprocessError::DuplicateOrZeroEvalPoint);
        }
        for j in (i + 1)..eval_points.len() {
            if eval_points[i] == eval_points[j] {
                return Err(PreprocessError::DuplicateOrZeroEvalPoint);
            }
        }
    }
    Ok(())
}

/// Public interpolation tables for one ordered quorum and threshold.
/// Denominators use Montgomery batch inversion (one field inverse).
pub struct GoldilocksOpeningTables {
    t: usize,
    n: usize,
    zero: Vec<Goldilocks>,
    extra: Vec<Vec<Goldilocks>>,
}
impl GoldilocksOpeningTables {
    pub fn new(t: usize, points: &[Goldilocks]) -> Result<Self, PreprocessError> {
        let n = points.len();
        if t == 0 || t > n {
            return Err(PreprocessError::InvalidThreshold { t, n });
        }
        validate_all_eval_points_goldilocks(points)?;
        let mut denominators = vec![Goldilocks::ONE; t];
        let mut prefix = vec![Goldilocks::ONE; t];
        let mut product = Goldilocks::ONE;
        for i in 0..t {
            for j in 0..t {
                if i != j {
                    denominators[i] = denominators[i].const_mul(points[i].const_sub(points[j]));
                }
            }
            prefix[i] = product;
            product = product.const_mul(denominators[i]);
        }
        let mut inverse = product
            .checked_inv()
            .ok_or(PreprocessError::DuplicateOrZeroEvalPoint)?;
        for i in (0..t).rev() {
            let original = denominators[i];
            denominators[i] = inverse.const_mul(prefix[i]);
            inverse = inverse.const_mul(original);
        }
        let row = |x: Goldilocks| -> Vec<Goldilocks> {
            (0..t)
                .map(|i| {
                    let mut value = denominators[i];
                    for (j, point) in points[..t].iter().enumerate() {
                        if i != j {
                            value = value.const_mul(x.const_sub(*point));
                        }
                    }
                    value
                })
                .collect()
        };
        Ok(Self {
            t,
            n,
            zero: row(Goldilocks::ZERO),
            extra: points[t..].iter().map(|&x| row(x)).collect(),
        })
    }
    pub fn open(
        &self,
        shares: &[Goldilocks],
        phase: &'static str,
    ) -> Result<Goldilocks, PreprocessError> {
        if shares.len() != self.n {
            return Err(PreprocessError::DegreeCheckFailed { phase });
        }
        let dot = |row: &[Goldilocks]| {
            row.iter()
                .zip(&shares[..self.t])
                .fold(Goldilocks::ZERO, |acc, (&a, &b)| {
                    acc.const_add(a.const_mul(b))
                })
        };
        for (row, &actual) in self.extra.iter().zip(&shares[self.t..]) {
            if dot(row) != actual {
                return Err(PreprocessError::DegreeCheckFailed { phase });
            }
        }
        Ok(dot(&self.zero))
    }
}
pub struct Gf256OpeningTables {
    t: usize,
    n: usize,
    zero: Vec<TowerGf256>,
    extra: Vec<Vec<TowerGf256>>,
}
impl Gf256OpeningTables {
    pub fn new(t: usize, points: &[TowerGf256]) -> Result<Self, PreprocessError> {
        let n = points.len();
        if t == 0 || t > n {
            return Err(PreprocessError::InvalidThreshold { t, n });
        }
        validate_all_eval_points_gf256(points)?;
        let mut denominators = vec![TowerGf256::ONE; t];
        let mut prefix = vec![TowerGf256::ONE; t];
        let mut product = TowerGf256::ONE;
        for i in 0..t {
            for j in 0..t {
                if i != j {
                    denominators[i] = denominators[i].mul(points[i].add(points[j]));
                }
            }
            prefix[i] = product;
            product = product.mul(denominators[i]);
        }
        let mut inverse = product
            .inv()
            .ok_or(PreprocessError::DuplicateOrZeroEvalPoint)?;
        for i in (0..t).rev() {
            let original = denominators[i];
            denominators[i] = inverse.mul(prefix[i]);
            inverse = inverse.mul(original);
        }
        let row = |x: TowerGf256| -> Vec<TowerGf256> {
            (0..t)
                .map(|i| {
                    let mut value = denominators[i];
                    for (j, point) in points[..t].iter().enumerate() {
                        if i != j {
                            value = value.mul(x.add(*point));
                        }
                    }
                    value
                })
                .collect()
        };
        Ok(Self {
            t,
            n,
            zero: row(TowerGf256::ZERO),
            extra: points[t..].iter().map(|&x| row(x)).collect(),
        })
    }
    pub fn open(
        &self,
        shares: &[TowerGf256],
        phase: &'static str,
    ) -> Result<TowerGf256, PreprocessError> {
        if shares.len() != self.n {
            return Err(PreprocessError::DegreeCheckFailed { phase });
        }
        let dot = |row: &[TowerGf256]| {
            row.iter()
                .zip(&shares[..self.t])
                .fold(TowerGf256::ZERO, |acc, (&a, &b)| acc.add(a.mul(b)))
        };
        for (row, &actual) in self.extra.iter().zip(&shares[self.t..]) {
            if dot(row) != actual {
                return Err(PreprocessError::DegreeCheckFailed { phase });
            }
        }
        Ok(dot(&self.zero))
    }
}
impl Gf256OpeningTables {
    pub fn open_bitsliced(
        &self,
        shares: &[BitslicedGf256x64],
        phase: &'static str,
    ) -> Result<BitslicedGf256x64, PreprocessError> {
        if shares.len() != self.n {
            return Err(PreprocessError::DegreeCheckFailed { phase });
        }
        let dot = |row: &[TowerGf256]| {
            let mut out = [0; 8];
            for (&a, b) in row.iter().zip(&shares[..self.t]) {
                PublicGf256Matrix::from_public_scalar(a).scale_xor_into(&mut out, b);
            }
            out
        };
        for (row, actual) in self.extra.iter().zip(&shares[self.t..]) {
            if dot(row) != *actual {
                return Err(PreprocessError::DegreeCheckFailed { phase });
            }
        }
        Ok(dot(&self.zero))
    }
}

/// Interpolate the unique degree `< t` polynomial through `(pts[0..t], vals[0..t])` at `x = 0` AND
/// verify that ALL `eval_points[0..n]` are valid and `vals[t..n]` lie on that exact polynomial!
pub fn open_and_check_degree_gf256(
    t: usize,
    eval_points: &[TowerGf256],
    shares: &[TowerGf256],
    phase: &'static str,
) -> Result<TowerGf256, PreprocessError> {
    let n = eval_points.len();
    if t == 0 || t > n || shares.len() != n {
        return Err(PreprocessError::DegreeCheckFailed { phase });
    }
    validate_all_eval_points_gf256(eval_points)?;
    let lambdas_0 = lagrange_weights_zero_gf256(&eval_points[..t])
        .ok_or(PreprocessError::DuplicateOrZeroEvalPoint)?;
    let mut secret = TowerGf256::ZERO;
    for q in 0..t {
        secret = secret.add(lambdas_0[q].mul(shares[q]));
    }
    for m in t..n {
        let xm = eval_points[m];
        let mut expected = TowerGf256::ZERO;
        for i in 0..t {
            let mut num = TowerGf256::ONE;
            let mut den = TowerGf256::ONE;
            for j in 0..t {
                if i == j {
                    continue;
                }
                num = num.mul(xm.add(eval_points[j]));
                den = den.mul(eval_points[i].add(eval_points[j]));
            }
            let li = num.mul(den.inv().ok_or(PreprocessError::DuplicateOrZeroEvalPoint)?);
            expected = expected.add(li.mul(shares[i]));
        }
        if expected != shares[m] {
            return Err(PreprocessError::DegreeCheckFailed { phase });
        }
    }
    Ok(secret)
}

/// Bitsliced `64x` version of [`open_and_check_degree_gf256`] using [`PublicGf256Matrix`].
pub fn open_and_check_degree_bs_gf256(
    t: usize,
    eval_points: &[TowerGf256],
    shares: &[BitslicedGf256x64],
    phase: &'static str,
) -> Result<BitslicedGf256x64, PreprocessError> {
    let n = eval_points.len();
    if t == 0 || t > n || shares.len() != n {
        return Err(PreprocessError::DegreeCheckFailed { phase });
    }
    validate_all_eval_points_gf256(eval_points)?;
    let lambdas_0 = lagrange_weights_zero_gf256(&eval_points[..t])
        .ok_or(PreprocessError::DuplicateOrZeroEvalPoint)?;
    let mut secret = [0u64; 8];
    for q in 0..t {
        let mat = PublicGf256Matrix::from_public_scalar(lambdas_0[q]);
        mat.scale_xor_into(&mut secret, &shares[q]);
    }
    for m in t..n {
        let xm = eval_points[m];
        let mut expected = [0u64; 8];
        for i in 0..t {
            let mut num = TowerGf256::ONE;
            let mut den = TowerGf256::ONE;
            for j in 0..t {
                if i == j {
                    continue;
                }
                num = num.mul(xm.add(eval_points[j]));
                den = den.mul(eval_points[i].add(eval_points[j]));
            }
            let li = num.mul(den.inv().ok_or(PreprocessError::DuplicateOrZeroEvalPoint)?);
            let mat = PublicGf256Matrix::from_public_scalar(li);
            mat.scale_xor_into(&mut expected, &shares[i]);
        }
        if expected != shares[m] {
            return Err(PreprocessError::DegreeCheckFailed { phase });
        }
    }
    Ok(secret)
}

/// Interpolate degree `< t` polynomial over `Goldilocks` at `0` AND verify `eval_points[0..n]` + `shares[t..n]`.
pub fn open_and_check_degree_goldilocks(
    t: usize,
    eval_points: &[Goldilocks],
    shares: &[Goldilocks],
    phase: &'static str,
) -> Result<Goldilocks, PreprocessError> {
    let n = eval_points.len();
    if t == 0 || t > n || shares.len() != n {
        return Err(PreprocessError::DegreeCheckFailed { phase });
    }
    validate_all_eval_points_goldilocks(eval_points)?;
    let lambdas_0 = lagrange_weights_zero_goldilocks(&eval_points[..t])
        .ok_or(PreprocessError::DuplicateOrZeroEvalPoint)?;
    let mut secret = Goldilocks::ZERO;
    for q in 0..t {
        secret += lambdas_0[q] * shares[q];
    }
    for m in t..n {
        let xm = eval_points[m];
        let mut expected = Goldilocks::ZERO;
        for i in 0..t {
            let mut num = Goldilocks::ONE;
            let mut den = Goldilocks::ONE;
            for j in 0..t {
                if i == j {
                    continue;
                }
                num *= xm - eval_points[j];
                den *= eval_points[i] - eval_points[j];
            }
            let li = num
                * den
                    .checked_inv()
                    .ok_or(PreprocessError::DuplicateOrZeroEvalPoint)?;
            expected += li * shares[i];
        }
        if expected != shares[m] {
            return Err(PreprocessError::DegreeCheckFailed { phase });
        }
    }
    Ok(secret)
}

/// Interpolate degree `< t` polynomial over `GoldilocksExt2` at `0` AND verify `shares[t..n]`.
pub fn open_and_check_degree_ext2(
    t: usize,
    eval_points: &[Goldilocks],
    shares: &[GoldilocksExt2],
    phase: &'static str,
) -> Result<GoldilocksExt2, PreprocessError> {
    let c0_shares: Vec<Goldilocks> = shares.iter().map(|s| s.c0).collect();
    let c1_shares: Vec<Goldilocks> = shares.iter().map(|s| s.c1).collect();
    let s0 = open_and_check_degree_goldilocks(t, eval_points, &c0_shares, phase)?;
    let s1 = open_and_check_degree_goldilocks(t, eval_points, &c1_shares, phase)?;
    Ok(GoldilocksExt2::new(s0, s1))
}

/// Dishonest-majority commit-before-open + SPDZ 2-lane `Tower128` `MacCheck` over any quorum.
#[expect(
    clippy::too_many_arguments,
    reason = "Quorum, value shares, MAC shares and private randomness are separate protocol inputs"
)]
pub fn commit_and_open_spdz_gf256_quorum(
    session_id: &[u8; 32],
    phase: &'static str,
    t: usize,
    quorum_eval_points: &[TowerGf256],
    shares: &[TowerGf256],
    mac_shares: &[[Tower128; 2]],
    alpha_shares: &[[Tower128; 2]],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<TowerGf256, PreprocessError> {
    let m = quorum_eval_points.len();
    if t == 0
        || m < t
        || shares.len() != m
        || mac_shares.len() != m
        || alpha_shares.len() != m
        || party_rngs.len() != m
    {
        return Err(PreprocessError::InvalidThreshold { t, n: m });
    }
    let mut salts = Vec::with_capacity(m);
    let mut coms = Vec::with_capacity(m);
    for p in 0..m {
        let salt = party_rngs[p].next_bytes32();
        let pid = (p as u64).to_be_bytes();
        let val_b = [shares[p].0];
        let com = cshake256_32_multi_frame(
            b"QSAG.SPDZ.GF256.OPEN.COM/v1",
            &[session_id, phase.as_bytes(), &pid, &val_b, &salt],
        );
        salts.push(salt);
        coms.push(com);
    }
    for p in 0..m {
        let pid = (p as u64).to_be_bytes();
        let val_b = [shares[p].0];
        let exp = cshake256_32_multi_frame(
            b"QSAG.SPDZ.GF256.OPEN.COM/v1",
            &[session_id, phase.as_bytes(), &pid, &val_b, &salts[p]],
        );
        wipe_bytes32(&mut salts[p]);
        if !ct_eq_bytes32(&exp, &coms[p]) {
            return Err(PreprocessError::ShareCommitMismatch { phase, party_id: p });
        }
    }

    let x_cand = open_and_check_degree_gf256(t, quorum_eval_points, shares, phase)?;
    let lambdas_0 = lagrange_weights_zero_gf256(&quorum_eval_points[..t])
        .ok_or(PreprocessError::DuplicateOrZeroEvalPoint)?;

    let x_emb = Tower128::embed_gf256(x_cand);
    // Peer-to-peer additive zero-sharing across the `0..t` quorum: each member `r` deals uniform
    // additive shares of `0` privately to peers `0..t` (`0` central dealer, 100% ZK even at `t = 1`!).
    let mut z_masks = vec![[Tower128::ZERO; 2]; t];
    if t > 1 {
        for party_rngs_r_item in party_rngs[..t].iter_mut() {
            let mut sum0 = Tower128::ZERO;
            let mut sum1 = Tower128::ZERO;
            for z_masks_q_item in z_masks[..(t - 1)].iter_mut() {
                let u0 = (*party_rngs_r_item).next_tower128();
                let u1 = (*party_rngs_r_item).next_tower128();
                (*z_masks_q_item)[0] = (*z_masks_q_item)[0].add(u0);
                (*z_masks_q_item)[1] = (*z_masks_q_item)[1].add(u1);
                sum0 = sum0.add(u0);
                sum1 = sum1.add(u1);
            }
            z_masks[t - 1][0] = z_masks[t - 1][0].add(sum0);
            z_masks[t - 1][1] = z_masks[t - 1][1].add(sum1);
        }
    }

    let mut sigmas = Vec::with_capacity(t);
    let mut sig_salts = Vec::with_capacity(t);
    let mut sig_coms = Vec::with_capacity(t);
    for q in 0..t {
        let lam_emb = Tower128::embed_gf256(lambdas_0[q]);
        let s0 = lam_emb
            .mul(mac_shares[q][0].add(x_emb.mul(alpha_shares[q][0])))
            .add(z_masks[q][0]);
        let s1 = lam_emb
            .mul(mac_shares[q][1].add(x_emb.mul(alpha_shares[q][1])))
            .add(z_masks[q][1]);
        wipe_tower128(&mut z_masks[q]);
        let salt = party_rngs[q].next_bytes32();
        let q_be = (q as u64).to_be_bytes();
        let s0_b = s0.0.to_le_bytes();
        let s1_b = s1.0.to_le_bytes();
        let com = cshake256_32_multi_frame(
            b"QSAG.SPDZ.GF256.MAC.COM/v1",
            &[session_id, phase.as_bytes(), &q_be, &s0_b, &s1_b, &salt],
        );
        sigmas.push([s0, s1]);
        sig_salts.push(salt);
        sig_coms.push(com);
    }

    let mut sum0 = Tower128::ZERO;
    let mut sum1 = Tower128::ZERO;
    for q in 0..t {
        let q_be = (q as u64).to_be_bytes();
        let s0_b = sigmas[q][0].0.to_le_bytes();
        let s1_b = sigmas[q][1].0.to_le_bytes();
        let exp = cshake256_32_multi_frame(
            b"QSAG.SPDZ.GF256.MAC.COM/v1",
            &[
                session_id,
                phase.as_bytes(),
                &q_be,
                &s0_b,
                &s1_b,
                &sig_salts[q],
            ],
        );
        wipe_bytes32(&mut sig_salts[q]);
        if !ct_eq_bytes32(&exp, &sig_coms[q]) {
            return Err(PreprocessError::ShareCommitMismatch { phase, party_id: q });
        }
        sum0 = sum0.add(sigmas[q][0]);
        sum1 = sum1.add(sigmas[q][1]);
        wipe_tower128(&mut sigmas[q]);
    }
    if !(sum0.ct_eq(Tower128::ZERO) && sum1.ct_eq(Tower128::ZERO)) {
        return Err(PreprocessError::MacCheckFailed {
            phase,
            accused_party: None,
        });
    }
    Ok(x_cand)
}

/// Batch bitsliced `64x` SPDZ committed opening + 2-lane `Tower128` `MacCheck` (`2^{-256}` soundness).
#[expect(
    clippy::too_many_arguments,
    reason = "Quorum, value shares, MAC shares and private randomness are separate protocol inputs"
)]
pub fn commit_and_open_spdz_bs_gf256_quorum(
    session_id: &[u8; 32],
    phase: &'static str,
    t: usize,
    quorum_eval_points: &[TowerGf256],
    shares: &[BitslicedGf256x64],
    mac_shares: &[[[Tower128; 64]; 2]],
    alpha_shares: &[[Tower128; 2]],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<BitslicedGf256x64, PreprocessError> {
    let m = quorum_eval_points.len();
    if t == 0
        || m < t
        || shares.len() != m
        || mac_shares.len() != m
        || alpha_shares.len() != m
        || party_rngs.len() != m
    {
        return Err(PreprocessError::InvalidThreshold { t, n: m });
    }
    let mut salts = Vec::with_capacity(m);
    let mut coms = Vec::with_capacity(m);
    for p in 0..m {
        let salt = party_rngs[p].next_bytes32();
        let mut raw = [0u8; 64];
        for pl in 0..8 {
            raw[8 * pl..8 * pl + 8].copy_from_slice(&shares[p][pl].to_le_bytes());
        }
        let pid = (p as u64).to_be_bytes();
        let com = cshake256_32_multi_frame(
            b"QSAG.SPDZ.BS64.OPEN.COM/v1",
            &[session_id, phase.as_bytes(), &pid, &raw, &salt],
        );
        wipe_bytes(&mut raw);
        salts.push(salt);
        coms.push(com);
    }
    for p in 0..m {
        let mut raw = [0u8; 64];
        for pl in 0..8 {
            raw[8 * pl..8 * pl + 8].copy_from_slice(&shares[p][pl].to_le_bytes());
        }
        let pid = (p as u64).to_be_bytes();
        let exp = cshake256_32_multi_frame(
            b"QSAG.SPDZ.BS64.OPEN.COM/v1",
            &[session_id, phase.as_bytes(), &pid, &raw, &salts[p]],
        );
        wipe_bytes(&mut raw);
        wipe_bytes32(&mut salts[p]);
        if !ct_eq_bytes32(&exp, &coms[p]) {
            return Err(PreprocessError::ShareCommitMismatch { phase, party_id: p });
        }
    }

    let x_cand = open_and_check_degree_bs_gf256(t, quorum_eval_points, shares, phase)?;
    let mut open_raw = [0u8; 64];
    for pl in 0..8 {
        open_raw[8 * pl..8 * pl + 8].copy_from_slice(&x_cand[pl].to_le_bytes());
    }
    let open_digest = cshake256_32(b"QSAG.SPDZ.BS64.DIG/v1", &open_raw);
    let fold_coin =
        run_commit_and_open_coin(session_id, phase.as_bytes(), &open_digest, party_rngs)?;
    let mut xof = Cshake256Xof::new(b"QSAG.SPDZ.BS64.CHIS/v1");
    xof.absorb(&fold_coin);
    let mut chi_raw = [0u8; 2 * 64 * 16];
    xof.squeeze(&mut chi_raw);
    let chis: [[Tower128; 64]; 2] = core::array::from_fn(|lane| {
        core::array::from_fn(|bit| {
            let off = (2 * bit + lane) * 16;
            Tower128(u128::from_le_bytes(core::array::from_fn(|b| {
                chi_raw[off + b]
            })))
        })
    });
    wipe_bytes(&mut chi_raw);

    let lambdas_0 = lagrange_weights_zero_gf256(&quorum_eval_points[..t])
        .ok_or(PreprocessError::DuplicateOrZeroEvalPoint)?;
    let mut x_folded = [Tower128::ZERO; 2];
    for (bit, (&chi0, &chi1)) in chis[0].iter().zip(&chis[1]).enumerate() {
        let xb = bs_gf256_extract_lane(&x_cand, bit);
        x_folded[0] = x_folded[0].add(chi0.mul_gf256(xb));
        x_folded[1] = x_folded[1].add(chi1.mul_gf256(xb));
    }

    let mut z_masks = vec![[Tower128::ZERO; 2]; t];
    if t > 1 {
        for party_rngs_r_item in party_rngs[..t].iter_mut() {
            let mut sum0 = Tower128::ZERO;
            let mut sum1 = Tower128::ZERO;
            for z_masks_q_item in z_masks[..(t - 1)].iter_mut() {
                let u0 = (*party_rngs_r_item).next_tower128();
                let u1 = (*party_rngs_r_item).next_tower128();
                (*z_masks_q_item)[0] = (*z_masks_q_item)[0].add(u0);
                (*z_masks_q_item)[1] = (*z_masks_q_item)[1].add(u1);
                sum0 = sum0.add(u0);
                sum1 = sum1.add(u1);
            }
            z_masks[t - 1][0] = z_masks[t - 1][0].add(sum0);
            z_masks[t - 1][1] = z_masks[t - 1][1].add(sum1);
        }
    }

    let lhs: [[u128; 2]; 64] = core::array::from_fn(|bit| [chis[0][bit].0, chis[1][bit].0]);
    let mut sigmas = Vec::with_capacity(t);
    let mut sig_salts = Vec::with_capacity(t);
    let mut sig_coms = Vec::with_capacity(t);
    for q in 0..t {
        let lam_emb = Tower128::embed_gf256(lambdas_0[q]);
        let mut rhs: [[u128; 2]; 64] =
            core::array::from_fn(|bit| [mac_shares[q][0][bit].0, mac_shares[q][1][bit].0]);
        let mut fold = qsag_asm::tower128_bdoz_2lane_mac(&lhs, &rhs);
        let m0 = Tower128(fold[0]);
        let m1 = Tower128(fold[1]);
        wipe_u128s(rhs.as_flattened_mut());
        wipe_u128s(&mut fold);
        let s0 = lam_emb
            .mul(m0.add(x_folded[0].mul(alpha_shares[q][0])))
            .add(z_masks[q][0]);
        let s1 = lam_emb
            .mul(m1.add(x_folded[1].mul(alpha_shares[q][1])))
            .add(z_masks[q][1]);
        wipe_tower128(&mut z_masks[q]);
        let salt = party_rngs[q].next_bytes32();
        let q_be = (q as u64).to_be_bytes();
        let com = cshake256_32_multi_frame(
            b"QSAG.SPDZ.BS64.MAC.COM/v1",
            &[
                session_id,
                phase.as_bytes(),
                &q_be,
                &s0.0.to_le_bytes(),
                &s1.0.to_le_bytes(),
                &salt,
            ],
        );
        sigmas.push([s0, s1]);
        sig_salts.push(salt);
        sig_coms.push(com);
    }

    let mut sum0 = Tower128::ZERO;
    let mut sum1 = Tower128::ZERO;
    for q in 0..t {
        let q_be = (q as u64).to_be_bytes();
        let exp = cshake256_32_multi_frame(
            b"QSAG.SPDZ.BS64.MAC.COM/v1",
            &[
                session_id,
                phase.as_bytes(),
                &q_be,
                &sigmas[q][0].0.to_le_bytes(),
                &sigmas[q][1].0.to_le_bytes(),
                &sig_salts[q],
            ],
        );
        wipe_bytes32(&mut sig_salts[q]);
        if !ct_eq_bytes32(&exp, &sig_coms[q]) {
            return Err(PreprocessError::ShareCommitMismatch { phase, party_id: q });
        }
        sum0 = sum0.add(sigmas[q][0]);
        sum1 = sum1.add(sigmas[q][1]);
        wipe_tower128(&mut sigmas[q]);
    }
    if !(sum0.ct_eq(Tower128::ZERO) && sum1.ct_eq(Tower128::ZERO)) {
        return Err(PreprocessError::MacCheckFailed {
            phase,
            accused_party: None,
        });
    }
    Ok(x_cand)
}

/// Dishonest-majority commit-before-open + SPDZ `GoldilocksExt2` `MacCheck` over any quorum.
#[expect(
    clippy::too_many_arguments,
    reason = "Quorum, value shares, MAC shares and private randomness are separate protocol inputs"
)]
pub fn commit_and_open_spdz_goldilocks_quorum(
    session_id: &[u8; 32],
    phase: &'static str,
    t: usize,
    quorum_eval_points: &[Goldilocks],
    shares: &[Goldilocks],
    mac_shares: &[GoldilocksExt2],
    alpha_shares: &[GoldilocksExt2],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Goldilocks, PreprocessError> {
    let m = quorum_eval_points.len();
    if t == 0
        || m < t
        || shares.len() != m
        || mac_shares.len() != m
        || alpha_shares.len() != m
        || party_rngs.len() != m
    {
        return Err(PreprocessError::InvalidThreshold { t, n: m });
    }
    let mut salts = Vec::with_capacity(m);
    let mut coms = Vec::with_capacity(m);
    for p in 0..m {
        let salt = party_rngs[p].next_bytes32();
        let pid = (p as u64).to_be_bytes();
        let vb = shares[p].to_canonical_u64().to_le_bytes();
        let com = cshake256_32_multi_frame(
            b"QSAG.SPDZ.GL.OPEN.COM/v1",
            &[session_id, phase.as_bytes(), &pid, &vb, &salt],
        );
        salts.push(salt);
        coms.push(com);
    }
    for p in 0..m {
        let pid = (p as u64).to_be_bytes();
        let vb = shares[p].to_canonical_u64().to_le_bytes();
        let exp = cshake256_32_multi_frame(
            b"QSAG.SPDZ.GL.OPEN.COM/v1",
            &[session_id, phase.as_bytes(), &pid, &vb, &salts[p]],
        );
        wipe_bytes32(&mut salts[p]);
        if !ct_eq_bytes32(&exp, &coms[p]) {
            return Err(PreprocessError::ShareCommitMismatch { phase, party_id: p });
        }
    }

    let x_cand = open_and_check_degree_goldilocks(t, quorum_eval_points, shares, phase)?;
    let lambdas_0 = lagrange_weights_zero_goldilocks(&quorum_eval_points[..t])
        .ok_or(PreprocessError::DuplicateOrZeroEvalPoint)?;

    let mut z_masks = vec![GoldilocksExt2::ZERO; t];
    if t > 1 {
        for party_rngs_r_item in party_rngs[..t].iter_mut() {
            let mut acc = GoldilocksExt2::ZERO;
            for z_masks_q_item in z_masks[..(t - 1)].iter_mut() {
                let u = (*party_rngs_r_item).next_ext2();
                *z_masks_q_item += u;
                acc += u;
            }
            z_masks[t - 1] -= acc;
        }
    }

    let mut sigmas = Vec::with_capacity(t);
    let mut sig_salts = Vec::with_capacity(t);
    let mut sig_coms = Vec::with_capacity(t);
    for q in 0..t {
        let diff_q = mac_shares[q] - alpha_shares[q].mul_base(x_cand);
        let sig_q = diff_q.mul_base(lambdas_0[q]) + z_masks[q];
        let salt = party_rngs[q].next_bytes32();
        let q_be = (q as u64).to_be_bytes();
        let c0_b = sig_q.c0.to_canonical_u64().to_le_bytes();
        let c1_b = sig_q.c1.to_canonical_u64().to_le_bytes();
        let com = cshake256_32_multi_frame(
            b"QSAG.SPDZ.GL.MAC.COM/v1",
            &[session_id, phase.as_bytes(), &q_be, &c0_b, &c1_b, &salt],
        );
        sigmas.push(sig_q);
        sig_salts.push(salt);
        sig_coms.push(com);
    }
    wipe_ext2(&mut z_masks);

    let mut sum = GoldilocksExt2::ZERO;
    for q in 0..t {
        let q_be = (q as u64).to_be_bytes();
        let c0_b = sigmas[q].c0.to_canonical_u64().to_le_bytes();
        let c1_b = sigmas[q].c1.to_canonical_u64().to_le_bytes();
        let exp = cshake256_32_multi_frame(
            b"QSAG.SPDZ.GL.MAC.COM/v1",
            &[
                session_id,
                phase.as_bytes(),
                &q_be,
                &c0_b,
                &c1_b,
                &sig_salts[q],
            ],
        );
        wipe_bytes32(&mut sig_salts[q]);
        if !ct_eq_bytes32(&exp, &sig_coms[q]) {
            wipe_ext2(&mut sigmas);
            return Err(PreprocessError::ShareCommitMismatch { phase, party_id: q });
        }
        sum += sigmas[q];
    }
    wipe_ext2(&mut sigmas);
    if !sum.ct_eq(GoldilocksExt2::ZERO) {
        return Err(PreprocessError::MacCheckFailed {
            phase,
            accused_party: None,
        });
    }
    Ok(x_cand)
}

/// Dishonest-majority commit-before-open + SPDZ `GoldilocksExt2` `MacCheck` for an extension wire.
#[expect(
    clippy::too_many_arguments,
    reason = "Quorum, value shares, MAC shares and private randomness are separate protocol inputs"
)]
pub fn commit_and_open_spdz_ext2_quorum(
    session_id: &[u8; 32],
    phase: &'static str,
    t: usize,
    quorum_eval_points: &[Goldilocks],
    shares: &[GoldilocksExt2],
    mac_shares: &[GoldilocksExt2],
    alpha_shares: &[GoldilocksExt2],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<GoldilocksExt2, PreprocessError> {
    let m = quorum_eval_points.len();
    if t == 0
        || m < t
        || shares.len() != m
        || mac_shares.len() != m
        || alpha_shares.len() != m
        || party_rngs.len() != m
    {
        return Err(PreprocessError::InvalidThreshold { t, n: m });
    }
    let mut salts = Vec::with_capacity(m);
    let mut coms = Vec::with_capacity(m);
    for p in 0..m {
        let salt = party_rngs[p].next_bytes32();
        let pid = (p as u64).to_be_bytes();
        let c0_b = shares[p].c0.to_canonical_u64().to_le_bytes();
        let c1_b = shares[p].c1.to_canonical_u64().to_le_bytes();
        let com = cshake256_32_multi_frame(
            b"QSAG.SPDZ.EXT2.OPEN.COM/v1",
            &[session_id, phase.as_bytes(), &pid, &c0_b, &c1_b, &salt],
        );
        salts.push(salt);
        coms.push(com);
    }
    for p in 0..m {
        let pid = (p as u64).to_be_bytes();
        let c0_b = shares[p].c0.to_canonical_u64().to_le_bytes();
        let c1_b = shares[p].c1.to_canonical_u64().to_le_bytes();
        let exp = cshake256_32_multi_frame(
            b"QSAG.SPDZ.EXT2.OPEN.COM/v1",
            &[session_id, phase.as_bytes(), &pid, &c0_b, &c1_b, &salts[p]],
        );
        wipe_bytes32(&mut salts[p]);
        if !ct_eq_bytes32(&exp, &coms[p]) {
            return Err(PreprocessError::ShareCommitMismatch { phase, party_id: p });
        }
    }

    let x_cand = open_and_check_degree_ext2(t, quorum_eval_points, shares, phase)?;
    let lambdas_0 = lagrange_weights_zero_goldilocks(&quorum_eval_points[..t])
        .ok_or(PreprocessError::DuplicateOrZeroEvalPoint)?;

    let mut z_masks = vec![GoldilocksExt2::ZERO; t];
    if t > 1 {
        for party_rngs_r_item in party_rngs[..t].iter_mut() {
            let mut acc = GoldilocksExt2::ZERO;
            for z_masks_q_item in z_masks[..(t - 1)].iter_mut() {
                let u = (*party_rngs_r_item).next_ext2();
                *z_masks_q_item += u;
                acc += u;
            }
            z_masks[t - 1] -= acc;
        }
    }

    let mut sigmas = Vec::with_capacity(t);
    let mut sig_salts = Vec::with_capacity(t);
    let mut sig_coms = Vec::with_capacity(t);
    for q in 0..t {
        let diff_q = mac_shares[q] - (alpha_shares[q] * x_cand);
        let sig_q = diff_q.mul_base(lambdas_0[q]) + z_masks[q];
        let salt = party_rngs[q].next_bytes32();
        let q_be = (q as u64).to_be_bytes();
        let c0_b = sig_q.c0.to_canonical_u64().to_le_bytes();
        let c1_b = sig_q.c1.to_canonical_u64().to_le_bytes();
        let com = cshake256_32_multi_frame(
            b"QSAG.SPDZ.EXT2.MAC.COM/v1",
            &[session_id, phase.as_bytes(), &q_be, &c0_b, &c1_b, &salt],
        );
        sigmas.push(sig_q);
        sig_salts.push(salt);
        sig_coms.push(com);
    }
    wipe_ext2(&mut z_masks);

    let mut sum = GoldilocksExt2::ZERO;
    for q in 0..t {
        let q_be = (q as u64).to_be_bytes();
        let c0_b = sigmas[q].c0.to_canonical_u64().to_le_bytes();
        let c1_b = sigmas[q].c1.to_canonical_u64().to_le_bytes();
        let exp = cshake256_32_multi_frame(
            b"QSAG.SPDZ.EXT2.MAC.COM/v1",
            &[
                session_id,
                phase.as_bytes(),
                &q_be,
                &c0_b,
                &c1_b,
                &sig_salts[q],
            ],
        );
        wipe_bytes32(&mut sig_salts[q]);
        if !ct_eq_bytes32(&exp, &sig_coms[q]) {
            wipe_ext2(&mut sigmas);
            return Err(PreprocessError::ShareCommitMismatch { phase, party_id: q });
        }
        sum += sigmas[q];
    }
    wipe_ext2(&mut sigmas);
    if !sum.ct_eq(GoldilocksExt2::ZERO) {
        return Err(PreprocessError::MacCheckFailed {
            phase,
            accused_party: None,
        });
    }
    Ok(x_cand)
}

// ============================================================================
// 5. Dealerless `Π_triple_f2` (`PreprocessedKeccakVault` over `BinaryTower` + 2-Lane SPDZ `Tower128`)
// ============================================================================

/// One party's isolated 64-way bitsliced Boolean Beaver triple share `([a]_p, [b]_p, [c]_p)`
/// over $\mathcal{T}_3 = \mathbb{F}_{2^8}$ paired with full 2-lane `Tower128` SPDZ Shamir MAC shares
/// (`a_mac, b_mac, c_mac`), wiped on `Drop`.
pub struct KeccakBitTripleShare64 {
    pub a: BitslicedGf256x64,
    pub b: BitslicedGf256x64,
    pub c: BitslicedGf256x64,
    pub a_mac: [[Tower128; 64]; 2],
    pub b_mac: [[Tower128; 64]; 2],
    pub c_mac: [[Tower128; 64]; 2],
}

impl fmt::Debug for KeccakBitTripleShare64 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("KeccakBitTripleShare64([REDACTED])")
    }
}

impl Drop for KeccakBitTripleShare64 {
    fn drop(&mut self) {
        wipe_u64s(&mut self.a);
        wipe_u64s(&mut self.b);
        wipe_u64s(&mut self.c);
        for lane in 0..2 {
            wipe_tower128(&mut self.a_mac[lane]);
            wipe_tower128(&mut self.b_mac[lane]);
            wipe_tower128(&mut self.c_mac[lane]);
        }
    }
}

/// Per-party isolated vault of dealerless-preprocessed `Keccak-f[1600]` Boolean triples and
/// degree-$<t$ Shamir shares of the 2-lane `Tower128` SPDZ MAC keys (`!Clone`, wiped on `Drop`,
/// permanently poisoned and zeroized on any `MacCheck` abort `[P0-07]`).
pub struct PreprocessedKeccakPartyVault {
    pub party_id: usize,
    pub eval_point: TowerGf256,
    /// Degree-$<t$ Shamir share $[\alpha]_p \in \mathcal{T}_7^2$ of the global 2-lane SPDZ MAC key.
    pub mac_alpha_lanes: [Tower128; 2],
    pub(crate) triples: Vec<KeccakBitTripleShare64>,
    pub(crate) cursor: usize,
    pub poisoned: bool,
}

impl fmt::Debug for PreprocessedKeccakPartyVault {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "PreprocessedKeccakPartyVault(party={}, rem={}, poisoned={})",
            self.party_id,
            self.remaining(),
            self.poisoned
        )
    }
}

impl Drop for PreprocessedKeccakPartyVault {
    fn drop(&mut self) {
        self.poison_and_wipe();
    }
}

impl PreprocessedKeccakPartyVault {
    /// Immediately burn `mac_alpha_lanes` and purge all remaining triples on any `MacCheck` failure!
    pub fn poison_and_wipe(&mut self) {
        self.poisoned = true;
        wipe_tower128(&mut self.mac_alpha_lanes);
        self.triples.clear();
        self.cursor = 0;
    }

    #[inline]
    pub fn remaining(&self) -> usize {
        if self.poisoned {
            0
        } else {
            self.triples.len().saturating_sub(self.cursor)
        }
    }

    #[inline]
    pub fn triples_slice(&self) -> &[KeccakBitTripleShare64] {
        &self.triples
    }

    /// Monotonically burn a disjoint range before exposing its material. All quorums
    /// sharing this vault use the same cursor; abandoned reservations are never reclaimed.
    pub fn reserve_triples(
        &mut self,
        count: usize,
    ) -> Result<&[KeccakBitTripleShare64], PreprocessError> {
        let range = reserve_material(
            &mut self.cursor,
            self.triples.len(),
            count,
            self.poisoned,
            "Keccak triple",
        )?;
        Ok(&self.triples[range])
    }

    #[inline]
    pub fn pop_triple(&mut self) -> Result<&KeccakBitTripleShare64, PreprocessError> {
        Ok(&self.reserve_triples(1)?[0])
    }
}

/// Multiply XOR-shared Boolean words using the production KOS/MASCOT pool.
/// All masked openings carry two-lane GF(2^128) MACs; the pool performs batch
/// companion sacrifice before any triple is used. Full-field n-of-n Shamir
/// shares are converted back by the linear bit-zero projection only at the end.
pub(crate) fn checked_boolean_product(
    session_id: &[u8; 32],
    a: &[Vec<u64>],
    b: &[Vec<u64>],
    mesh: &mut OtMesh,
    rngs: &mut [PartyPrivateRng],
) -> Result<Vec<Vec<u64>>, PreprocessError> {
    checked_boolean_product_with_hook(session_id, a, b, mesh, rngs, |_| {})
}

fn checked_boolean_product_with_hook<F: FnMut(&mut [Vec<BitslicedGf256x64>])>(
    session_id: &[u8; 32],
    a: &[Vec<u64>],
    b: &[Vec<u64>],
    mesh: &mut OtMesh,
    rngs: &mut [PartyPrivateRng],
    mut fault: F,
) -> Result<Vec<Vec<u64>>, PreprocessError> {
    let n = a.len();
    if !(2..=255).contains(&n)
        || b.len() != n
        || rngs.len() != n
        || mesh.n != n
        || a.iter().chain(b).any(|v| v.len() != a[0].len())
    {
        return Err(PreprocessError::InvalidThreshold { t: n, n });
    }
    let points: Vec<_> = (1..=n).map(|p| TowerGf256(p as u8)).collect();
    let weights =
        lagrange_weights_zero_gf256(&points).ok_or(PreprocessError::DuplicateOrZeroEvalPoint)?;
    let projection: Vec<_> = weights
        .iter()
        .map(|&w| PublicGf256Matrix::from_public_scalar(w))
        .collect();
    let (mut contributions, mut alpha) = spdz_setup_alpha_gf256(session_id, n, &points, rngs)?;
    let result = (|| {
        let mut out = crate::wipe::SecretBuffer(vec![vec![0; a[0].len()]; n]);
        // One triple ceremony and one input authentication per chunk of words.
        const CHUNK_WORDS: usize = 512;
        for start in (0..a[0].len()).step_by(CHUNK_WORDS) {
            let count = (a[0].len() - start).min(CHUNK_WORDS);
            let sid = cshake256_32_multi_frame(
                b"QSAG.DPCG.ACTIVE.PRODUCT/v1",
                &[session_id, &(start as u64).to_be_bytes()],
            );
            let vaults = run_dealerless_pi_triple_f2_with_alpha(
                sid,
                n,
                &points,
                count,
                &contributions,
                &alpha,
                mesh,
                rngs,
            )?;
            let bits = crate::wipe::SecretBuffer(
                (0..n)
                    .map(|p| {
                        (start..start + count)
                            .flat_map(|k| [a[p][k], b[p][k]])
                            .collect::<Vec<u64>>()
                    })
                    .collect::<Vec<_>>(),
            );
            let (mut inputs, mut macs) = triple_f2::authenticate_xor_shared_words(
                &sid,
                n,
                &points,
                mesh,
                &contributions,
                &alpha,
                &bits,
                rngs,
            )?;
            drop(bits);
            let batch_result: Result<(), PreprocessError> = (|| {
                for p in 0..n {
                    for k in 0..count {
                        let triple = &vaults[p].triples[k];
                        bs_gf256_xor_assign(&mut inputs[p][2 * k], &triple.a);
                        bs_gf256_xor_assign(&mut inputs[p][2 * k + 1], &triple.b);
                        for (word, triple_mac) in macs[p][2 * k..2 * k + 2]
                            .iter_mut()
                            .zip([&triple.a_mac, &triple.b_mac])
                        {
                            for (lane, triple_lane) in word.iter_mut().zip(triple_mac) {
                                for (value, &mask) in lane.iter_mut().zip(triple_lane) {
                                    *value = value.add(mask);
                                }
                            }
                        }
                    }
                }
                fault(&mut inputs);
                let opening = commit_and_open_spdz_bs_gf256_batch_quorum(
                    &sid,
                    "dense_pcg_active_beaver_mask",
                    n,
                    &points,
                    &inputs,
                    &macs,
                    &alpha,
                    rngs,
                );
                for party in &mut macs {
                    for word in party {
                        for lane in word {
                            wipe_tower128(lane);
                        }
                    }
                }
                let opened = opening?;
                for p in 0..n {
                    for k in 0..count {
                        let triple = &vaults[p].triples[k];
                        let d = &opened[2 * k];
                        let e = &opened[2 * k + 1];
                        let mut c = bs_gf256_xor(&triple.c, &bs_gf256_mul_planes_ct(d, &triple.b));
                        bs_gf256_xor_assign(&mut c, &bs_gf256_mul_planes_ct(e, &triple.a));
                        bs_gf256_xor_assign(&mut c, &bs_gf256_mul_planes_ct(d, e));
                        out[p][start + k] = projection[p].scale_planes(&c)[0];
                        wipe_u64s(&mut c);
                    }
                }
                Ok(())
            })();
            for party in &mut inputs {
                for word in party {
                    wipe_u64s(word);
                }
            }
            batch_result?;
        }
        Ok(core::mem::take(&mut out.0))
    })();
    for v in &mut contributions {
        wipe_tower128(v);
    }
    for v in &mut alpha {
        wipe_tower128(v);
    }
    result
}

/// Evaluate a `Tower128` polynomial at `Tower128::embed_gf256(x)`.
#[inline]
fn eval_poly_tower128(coeffs: &[Tower128], x: TowerGf256) -> Tower128 {
    let mut acc = Tower128::ZERO;
    for &c in coeffs.iter().rev() {
        acc = acc.mul_gf256(x).add(c);
    }
    acc
}

/// Share a `Tower128` secret at degree `< t` across `eval_points[0..n]`.
#[inline]
fn shamir_share_tower128(
    t: usize,
    eval_points: &[TowerGf256],
    secret: Tower128,
    rng: &mut PartyPrivateRng,
) -> Vec<Tower128> {
    let mut coeffs = Vec::with_capacity(t);
    coeffs.push(secret);
    for _ in 1..t {
        coeffs.push(rng.next_tower128());
    }
    let out: Vec<Tower128> = eval_points
        .iter()
        .map(|&pt| eval_poly_tower128(&coeffs, pt))
        .collect();
    wipe_tower128(&mut coeffs);
    out
}

/// Commit-before-open + degree-`< t` interpolation of `Tower128` shares across `eval_points[0..n]`.
pub fn commit_and_open_degree_tower128(
    session_id: &[u8; 32],
    phase: &'static str,
    t: usize,
    eval_points: &[TowerGf256],
    shares: &[Tower128],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Tower128, PreprocessError> {
    let n = eval_points.len();
    if t == 0 || t > n || shares.len() != n || party_rngs.len() != n {
        return Err(PreprocessError::InvalidThreshold { t, n });
    }
    validate_all_eval_points_gf256(eval_points)?;
    let mut salts = Vec::with_capacity(n);
    let mut coms = Vec::with_capacity(n);
    for p in 0..n {
        let salt = party_rngs[p].next_bytes32();
        let pid = (p as u64).to_be_bytes();
        let vb = shares[p].0.to_le_bytes();
        let com = cshake256_32_multi_frame(
            b"QSAG.SPDZ.T128.OPEN.COM/v1",
            &[session_id, phase.as_bytes(), &pid, &vb, &salt],
        );
        salts.push(salt);
        coms.push(com);
    }
    for p in 0..n {
        let pid = (p as u64).to_be_bytes();
        let vb = shares[p].0.to_le_bytes();
        let exp = cshake256_32_multi_frame(
            b"QSAG.SPDZ.T128.OPEN.COM/v1",
            &[session_id, phase.as_bytes(), &pid, &vb, &salts[p]],
        );
        wipe_bytes32(&mut salts[p]);
        if !ct_eq_bytes32(&exp, &coms[p]) {
            return Err(PreprocessError::ShareCommitMismatch { phase, party_id: p });
        }
    }
    let lambdas_0 = lagrange_weights_zero_gf256(&eval_points[..t])
        .ok_or(PreprocessError::DuplicateOrZeroEvalPoint)?;
    let mut secret = Tower128::ZERO;
    for q in 0..t {
        secret = secret.add(shares[q].mul_gf256(lambdas_0[q]));
    }
    for m in t..n {
        let xm = eval_points[m];
        let mut expected = Tower128::ZERO;
        for i in 0..t {
            let mut num = TowerGf256::ONE;
            let mut den = TowerGf256::ONE;
            for j in 0..t {
                if i == j {
                    continue;
                }
                num = num.mul(xm.add(eval_points[j]));
                den = den.mul(eval_points[i].add(eval_points[j]));
            }
            let li = num.mul(den.inv().ok_or(PreprocessError::DuplicateOrZeroEvalPoint)?);
            expected = expected.add(shares[i].mul_gf256(li));
        }
        if !expected.ct_eq(shares[m]) {
            return Err(PreprocessError::DegreeCheckFailed { phase });
        }
    }
    Ok(secret)
}

/// Dealerless generation of consistent degree-`< t` Shamir shares of the global 2-lane `Tower128`
/// SPDZ MAC key $\alpha = \bigoplus_{i=0}^{n-1} \alpha^{(i)}$.
///
/// Returns `(alpha_contribs_per_sender, alpha_shamir_shares_per_party)` after verifying via a
/// random mask polynomial that every party dealt a consistent degree-`< t` polynomial across `0..n`.
pub fn spdz_setup_alpha_gf256(
    session_id: &[u8; 32],
    t: usize,
    eval_points: &[TowerGf256],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<(TowerAlphaShares, TowerAlphaShares), PreprocessError> {
    let n = eval_points.len();
    if t == 0 || t > n || party_rngs.len() != n {
        return Err(PreprocessError::InvalidThreshold { t, n });
    }
    validate_all_eval_points_gf256(eval_points)?;

    let mut alpha_contribs = vec![[Tower128::ZERO; 2]; n];
    let mut alpha_shamir = vec![[Tower128::ZERO; 2]; n];
    let mut beta_shamir = SecretBuffer(vec![[Tower128::ZERO; 2]; n]);

    for i in 0..n {
        for lane in 0..2 {
            let mut a_i = party_rngs[i].next_tower128();
            let mut b_i = party_rngs[i].next_tower128();
            alpha_contribs[i][lane] = a_i;
            let a_sh = SecretBuffer(shamir_share_tower128(
                t,
                eval_points,
                a_i,
                &mut party_rngs[i],
            ));
            let b_sh = SecretBuffer(shamir_share_tower128(
                t,
                eval_points,
                b_i,
                &mut party_rngs[i],
            ));
            wipe_u128s(core::slice::from_mut(&mut a_i.0));
            wipe_u128s(core::slice::from_mut(&mut b_i.0));
            for p in 0..n {
                alpha_shamir[p][lane] = alpha_shamir[p][lane].add(a_sh[p]);
                beta_shamir[p][lane] = beta_shamir[p][lane].add(b_sh[p]);
            }
        }
    }

    let coin =
        run_commit_and_open_coin(session_id, b"SPDZ_ALPHA_GF256_DEG", session_id, party_rngs)?;
    let etas = [
        Tower128(
            u128::from_le_bytes(core::array::from_fn(|array_index| {
                (coin[0..16])[array_index]
            })) | 1,
        ),
        Tower128(
            u128::from_le_bytes(core::array::from_fn(|array_index| {
                (coin[16..32])[array_index]
            })) | 1,
        ),
    ];
    for lane in 0..2 {
        let comb: SecretBuffer<Vec<Tower128>> = SecretBuffer(
            (0..n)
                .map(|p| beta_shamir[p][lane].add(etas[lane].mul(alpha_shamir[p][lane])))
                .collect(),
        );
        let _ = commit_and_open_degree_tower128(
            session_id,
            "spdz_setup_alpha_gf256",
            t,
            eval_points,
            &comb,
            party_rngs,
        )?;
    }
    Ok((alpha_contribs, alpha_shamir))
}

/// LHL-amplified (`[I | H]` with `32` disposable tail bytes = `256` bits, `< 2^{-129}` selective-failure
/// advantage) pairwise 2-lane `Tower128` BDOZ batch authentication of `count` `TowerGf256` share vectors.
///
/// Sender `i` inputs ONLY its private `alpha_per_party[i]`; Receiver `j` inputs uniform random OT
/// choice bytes and broadcasts derandomized differences after all OTs complete (`[P1-01]`).
pub fn authenticate_gf256_batch_two_lane(
    ot_mesh: &mut OtMesh,
    alpha_per_party: &[[Tower128; 2]],
    x_batch: &[Vec<TowerGf256>],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<(PairwiseTowerMacs, PairwiseTowerMacs), PreprocessError> {
    let n = ot_mesh.n;
    let count = x_batch.len();
    if n == 0 || alpha_per_party.len() != n || party_rngs.len() != n {
        return Err(PreprocessError::InvalidThreshold { t: 1, n });
    }
    for row in x_batch {
        if row.len() != n {
            return Err(PreprocessError::InvalidThreshold { t: 1, n });
        }
    }
    if count == 0 {
        return Ok((vec![vec![Vec::new(); n]; n], vec![vec![Vec::new(); n]; n]));
    }

    let m_raw = count + 32; // 32 extra random GF(256) bytes = 256 bits of LHL min-entropy buffer
    let num_u64 = m_raw.div_ceil(8);

    let mut r_bytes = vec![vec![0u8; m_raw]; n];
    let mut choice_words = vec![vec![0u64; num_u64]; n];
    for j in 0..n {
        party_rngs[j].fill_bytes(&mut r_bytes[j]);
        for s in 0..m_raw {
            choice_words[j][s / 8] |= (r_bytes[j][s] as u64) << (8 * (s % 8));
        }
    }

    let mut raw_macs = vec![vec![vec![[Tower128::ZERO; 2]; m_raw]; n]; n];
    let mut raw_keys = vec![vec![vec![[Tower128::ZERO; 2]; m_raw]; n]; n];

    for i in 0..n {
        for s in 0..m_raw {
            let ri_gf = TowerGf256(r_bytes[i][s]);
            for lane in 0..2 {
                let local_mask = party_rngs[i].next_tower128();
                raw_keys[i][i][s][lane] = local_mask;
                raw_macs[i][i][s][lane] = local_mask.add(alpha_per_party[i][lane].mul_gf256(ri_gf));
            }
        }
        for j in 0..n {
            if i == j {
                continue;
            }
            let (send_pads, recv_pads) =
                ot_mesh.run_correlated_ot_words(i, j, &choice_words[j], party_rngs)?;
            for s in 0..m_raw {
                let rj_byte = black_box(r_bytes[j][s]);
                for lane in 0..2 {
                    let alpha_il = alpha_per_party[i][lane];
                    let mut key_sum = Tower128::ZERO;
                    let mut mac_sum = Tower128::ZERO;
                    for bit in 0..8 {
                        let ot_idx = 8 * s + bit;
                        let (p0, p1) = &send_pads[ot_idx];
                        let pad0 =
                            Tower128(u128::from_le_bytes(core::array::from_fn(|array_index| {
                                (p0[16 * lane..16 * (lane + 1)])[array_index]
                            })));
                        let pad1 =
                            Tower128(u128::from_le_bytes(core::array::from_fn(|array_index| {
                                (p1[16 * lane..16 * (lane + 1)])[array_index]
                            })));
                        let mask_k = party_rngs[i].next_tower128();
                        key_sum = key_sum.add(mask_k);
                        let ct0 = mask_k.add(pad0);
                        let ct1 = mask_k
                            .add(alpha_il.mul_gf256(TowerGf256(1u8 << bit)))
                            .add(pad1);

                        let pad_c =
                            Tower128(u128::from_le_bytes(core::array::from_fn(|array_index| {
                                (recv_pads[ot_idx][16 * lane..16 * (lane + 1)])[array_index]
                            })));
                        let b_choice = ((rj_byte >> bit) & 1) == 1;
                        let c_mask = 0u128.wrapping_sub(black_box(b_choice as u128));
                        let ct_sel = Tower128(ct0.0 ^ (c_mask & (ct0.0 ^ ct1.0)));
                        mac_sum = mac_sum.add(ct_sel.add(pad_c));
                    }
                    raw_keys[i][j][s][lane] = key_sum;
                    raw_macs[i][j][s][lane] = mac_sum;
                }
            }
        }
    }

    // Post-OT systematic universal hash `[I | H]` (`count x (count + 32)`)
    let sid = ot_mesh.session_id;
    let lhl_coin = run_commit_and_open_coin(&sid, b"BDOZ_GF256_LHL_COMBINE", &sid, party_rngs)?;
    let mut h_xof = Cshake256Xof::new(b"QSAG.BDOZ.GF256.LHL_H/v1");
    h_xof.absorb(&lhl_coin);

    let mut h_rows = vec![[0u8; 32]; count];
    for row in &mut h_rows {
        h_xof.squeeze(row);
    }

    // Each party `j` broadcasts derandomized differences `diff[j][idx] = x_batch[idx][j] ^ u_comb[j][idx]`
    let mut diffs = vec![vec![TowerGf256::ZERO; count]; n];
    for j in 0..n {
        for idx in 0..count {
            let mut u_comb = TowerGf256(r_bytes[j][idx]);
            for tl in 0..32 {
                let g = TowerGf256(h_rows[idx][tl]);
                u_comb = u_comb.add(g.mul(TowerGf256(r_bytes[j][count + tl])));
            }
            diffs[j][idx] = x_batch[idx][j].add(u_comb);
        }
        wipe_bytes(&mut r_bytes[j]);
        wipe_u64s(&mut choice_words[j]);
    }

    let mut out_macs = vec![vec![vec![[Tower128::ZERO; 2]; count]; n]; n];
    let mut out_keys = vec![vec![vec![[Tower128::ZERO; 2]; count]; n]; n];
    for i in 0..n {
        for j in 0..n {
            for idx in 0..count {
                let d_gf = diffs[j][idx];
                for lane in 0..2 {
                    let mut m_acc = raw_macs[i][j][idx][lane];
                    let mut k_acc = raw_keys[i][j][idx][lane];
                    for tl in 0..32 {
                        let g_gf = TowerGf256(h_rows[idx][tl]);
                        m_acc = m_acc.add(raw_macs[i][j][count + tl][lane].mul_gf256(g_gf));
                        k_acc = k_acc.add(raw_keys[i][j][count + tl][lane].mul_gf256(g_gf));
                    }
                    k_acc = k_acc.add(alpha_per_party[i][lane].mul_gf256(d_gf));
                    out_macs[i][j][idx][lane] = m_acc;
                    out_keys[i][j][idx][lane] = k_acc;
                }
            }
            for s in 0..m_raw {
                wipe_tower128(&mut raw_macs[i][j][s]);
                wipe_tower128(&mut raw_keys[i][j][s]);
            }
        }
    }

    Ok((out_macs, out_keys))
}

/// Single-vector wrapper around `authenticate_gf256_batch_two_lane` inheriting full LHL `Combine`
/// selective-failure immunity (`< 2^{-129}`).
pub fn authenticate_gf256_shares_two_lane(
    ot_mesh: &mut OtMesh,
    alpha_per_party: &[[Tower128; 2]],
    x_shares: &[TowerGf256],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<TowerMacMatrices, PreprocessError> {
    let batch = alloc::vec![x_shares.to_vec()];
    let (b_macs, b_keys) =
        authenticate_gf256_batch_two_lane(ot_mesh, alpha_per_party, &batch, party_rngs)?;
    let n = ot_mesh.n;
    let mut macs = vec![vec![[Tower128::ZERO; 2]; n]; n];
    let mut keys = vec![vec![[Tower128::ZERO; 2]; n]; n];
    for i in 0..n {
        for j in 0..n {
            macs[i][j] = b_macs[i][j][0];
            keys[i][j] = b_keys[i][j][0];
        }
    }
    Ok((macs, keys))
}

/// Dealerless `Π_MAC` over `BitslicedGf256x64` words: computes degree-`< t` 2-lane `Tower128`
/// SPDZ Shamir MAC shares `macs[party][word_idx][lane][bit]` for every party `0..n` using
/// LHL-amplified OT (`< 2^{-129}` selective-failure advantage) AND verifies across ALL `0..n`
/// parties that both `words_per_party` and `macs` lie on consistent degree-`< t` polynomials with
/// $\gamma_{\text{lane}}(x) = \alpha_{\text{lane}} \cdot x$ ($2^{-256}$ soundness).
#[expect(
    clippy::too_many_arguments,
    reason = "Quorum, value shares, MAC shares and private randomness are separate protocol inputs"
)]
pub fn spdz_authenticate_bs_gf256_words(
    session_id: &[u8; 32],
    t: usize,
    eval_points: &[TowerGf256],
    ot_mesh: &mut OtMesh,
    alpha_contribs: &[[Tower128; 2]],
    alpha_shamir_shares: &[[Tower128; 2]],
    words_per_party: &[Vec<BitslicedGf256x64>],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<Vec<[[Tower128; 64]; 2]>>, PreprocessError> {
    let n = eval_points.len();
    if t == 0
        || t > n
        || ot_mesh.n != n
        || alpha_contribs.len() != n
        || alpha_shamir_shares.len() != n
        || words_per_party.len() != n
        || party_rngs.len() != n
    {
        return Err(PreprocessError::InvalidThreshold { t, n });
    }
    validate_all_eval_points_gf256(eval_points)?;
    let num_words = words_per_party[0].len();
    for words_per_party_p_item in words_per_party[..n].iter().skip(1) {
        if (*words_per_party_p_item).len() != num_words {
            return Err(PreprocessError::InvalidThreshold { t, n });
        }
    }
    if num_words == 0 {
        return Ok(vec![Vec::new(); n]);
    }

    let lambdas_t = lagrange_weights_zero_gf256(&eval_points[..t])
        .ok_or(PreprocessError::DuplicateOrZeroEvalPoint)?;
    let eval_mats: Vec<PublicGf256Matrix> = eval_points
        .iter()
        .map(|&pt| PublicGf256Matrix::from_public_scalar(pt))
        .collect();

    // Sample 1 disposable degree-`< t` random GF(256)^64 mask word `r_chk` (`512` bits of uniform entropy!)
    let mut r_chk_sh = vec![[0u64; 8]; n];
    for party_rngs_i_item in party_rngs[..n].iter_mut() {
        let mut coeffs = Vec::with_capacity(t);
        for _ in 0..t {
            let mut rp = [0u64; 8];
            for pl in &mut rp {
                *pl = (*party_rngs_i_item).next_u64();
            }
            coeffs.push(rp);
        }
        for (p, mat_pt) in eval_mats.iter().enumerate() {
            let mut acc = [0u64; 8];
            for c in coeffs.iter().rev() {
                acc = bs_gf256_xor(&mat_pt.scale_planes(&acc), c);
            }
            bs_gf256_xor_assign(&mut r_chk_sh[p], &acc);
        }
        for c in &mut coeffs {
            wipe_u64s(c);
        }
    }

    let total_w = num_words + 1;
    let total_elems = 64 * total_w;
    let m_raw = total_elems + 32; // +32 bytes = 256-bit LHL buffer
    let num_u64 = m_raw.div_ceil(8);

    let mut u_target = vec![vec![TowerGf256::ZERO; total_elems]; t];
    let mut r_bytes = vec![vec![0u8; m_raw]; t];
    let mut choice_words = vec![vec![0u64; num_u64]; t];
    for j in 0..t {
        let lj = lambdas_t[j];
        for k in 0..num_words {
            for bit in 0..64 {
                u_target[j][64 * k + bit] =
                    lj.mul(bs_gf256_extract_lane(&words_per_party[j][k], bit));
            }
        }
        for bit in 0..64 {
            u_target[j][64 * num_words + bit] = lj.mul(bs_gf256_extract_lane(&r_chk_sh[j], bit));
        }
        party_rngs[j].fill_bytes(&mut r_bytes[j]);
        for s in 0..m_raw {
            choice_words[j][s / 8] |= (r_bytes[j][s] as u64) << (8 * (s % 8));
        }
    }

    // Accumulate additive OT correlation shares directly into `sum_raw[party][slot]` (`O(n * m_raw)`
    // instead of `O(n * t * m_raw)` 4D matrices) before universal-hash `[I | H]` compression.
    let mut sum_raw = vec![vec![[Tower128::ZERO; 2]; m_raw]; n];

    for i in 0..n {
        if i < t {
            for s in 0..m_raw {
                let ri_emb = TowerGf256(r_bytes[i][s]);
                for lane in 0..2 {
                    let local_mask = party_rngs[i].next_tower128();
                    let local_mac = local_mask.add(alpha_contribs[i][lane].mul_gf256(ri_emb));
                    sum_raw[i][s][lane] = sum_raw[i][s][lane].add(local_mask).add(local_mac);
                }
            }
        }
        for j in 0..t {
            if i == j {
                continue;
            }
            let (send_pads, recv_pads) =
                ot_mesh.run_correlated_ot_words(i, j, &choice_words[j], party_rngs)?;
            for s in 0..m_raw {
                let rj_byte = black_box(r_bytes[j][s]);
                for lane in 0..2 {
                    let alpha_il = alpha_contribs[i][lane];
                    let mut key_sum = Tower128::ZERO;
                    let mut mac_sum = Tower128::ZERO;
                    for bit in 0..8 {
                        let ot_idx = 8 * s + bit;
                        let (p0, p1) = &send_pads[ot_idx];
                        let pad0 =
                            Tower128(u128::from_le_bytes(core::array::from_fn(|array_index| {
                                (p0[16 * lane..16 * (lane + 1)])[array_index]
                            })));
                        let pad1 =
                            Tower128(u128::from_le_bytes(core::array::from_fn(|array_index| {
                                (p1[16 * lane..16 * (lane + 1)])[array_index]
                            })));
                        let mask_k = party_rngs[i].next_tower128();
                        key_sum = key_sum.add(mask_k);
                        let ct0 = mask_k.add(pad0);
                        let ct1 = mask_k
                            .add(alpha_il.mul_gf256(TowerGf256(1u8 << bit)))
                            .add(pad1);

                        let pad_c =
                            Tower128(u128::from_le_bytes(core::array::from_fn(|array_index| {
                                (recv_pads[ot_idx][16 * lane..16 * (lane + 1)])[array_index]
                            })));
                        let b_choice = ((rj_byte >> bit) & 1) == 1;
                        let c_mask = 0u128.wrapping_sub(black_box(b_choice as u128));
                        let ct_sel = Tower128(ct0.0 ^ (c_mask & (ct0.0 ^ ct1.0)));
                        mac_sum = mac_sum.add(ct_sel.add(pad_c));
                    }
                    sum_raw[i][s][lane] = sum_raw[i][s][lane].add(key_sum);
                    sum_raw[j][s][lane] = sum_raw[j][s][lane].add(mac_sum);
                }
            }
        }
    }

    // Post-OT systematic Toeplitz 2-universal hash `[I | T]` (`256^{-total_elems}` collision bound!)
    let lhl_coin = run_commit_and_open_coin(
        session_id,
        b"SPDZ_BS64_LHL_COMBINE",
        &ot_mesh.session_id,
        party_rngs,
    )?;
    let mut h_xof = Cshake256Xof::new(b"QSAG.SPDZ.BS64.LHL_H/v1");
    h_xof.absorb(&lhl_coin);
    let mut toeplitz_h = vec![0u8; total_elems + 32];
    h_xof.squeeze(&mut toeplitz_h);

    let mut diff_sum = SecretBuffer(vec![TowerGf256::ZERO; total_elems]);
    for j in 0..t {
        let mut r_lut = [[0u8; 16]; 64];
        for tl in 0..32 {
            let rt = TowerGf256(r_bytes[j][total_elems + tl]);
            #[expect(
                clippy::needless_range_loop,
                reason = "Each public nibble updates two adjacent lookup rows"
            )]
            for nib in 0..16usize {
                r_lut[2 * tl][nib] = TowerGf256(nib as u8).mul(rt).0;
                r_lut[2 * tl + 1][nib] = TowerGf256((nib as u8) << 4).mul(rt).0;
            }
        }
        for idx in 0..total_elems {
            let mut u_comb = r_bytes[j][idx];
            for tl in 0..32 {
                let hb = toeplitz_h[idx + tl];
                u_comb ^=
                    r_lut[2 * tl][(hb & 0x0F) as usize] ^ r_lut[2 * tl + 1][(hb >> 4) as usize];
            }
            diff_sum[idx] = diff_sum[idx].add(u_target[j][idx].add(TowerGf256(u_comb)));
            u_target[j][idx] = TowerGf256::ZERO;
        }
        for row in &mut r_lut {
            wipe_bytes(row);
        }
        wipe_bytes(&mut r_bytes[j]);
        wipe_u64s(&mut choice_words[j]);
    }

    // Precompute Four-Russians nibble LUTs for `sum_raw[p][total_elems..+32][lane]` (indexed only by public `toeplitz_h`)
    let sum_luts: SecretBuffer<Vec<[[[u128; 16]; 64]; 2]>> = SecretBuffer(
        (0..n)
            .map(|p| {
                core::array::from_fn(|lane| {
                    core::array::from_fn(|slot| {
                        let tl = slot / 2;
                        let hi = (slot % 2) == 1;
                        let base = sum_raw[p][total_elems + tl][lane];
                        core::array::from_fn(|nib| {
                            let sc = if hi { (nib as u8) << 4 } else { nib as u8 };
                            base.mul_gf256(TowerGf256(sc)).0
                        })
                    })
                })
            })
            .collect(),
    );

    let party_work_seeds: SecretBuffer<Vec<[u8; 32]>> =
        SecretBuffer((0..n).map(|p| party_rngs[p].next_bytes32()).collect());

    // Sum additive shares `tau_p[idx][lane]` at each party `p in 0..n` and Shamir-share at degree `< t`
    let mut all_macs = vec![vec![[[Tower128::ZERO; 64]; 2]; total_w]; n];
    const SH_BLK_WORDS: usize = 256;
    let eval_sh_block = |blk_idx: usize, dst_per_party: &mut [&mut [[[Tower128; 64]; 2]]]| {
        let k_start = blk_idx * SH_BLK_WORDS;
        let blk_len = dst_per_party[0].len();
        let blk_le = (blk_idx as u64).to_le_bytes();
        for p in 0..n {
            let mut sub_rng = PartyPrivateRng::from_seed(party_work_seeds[p], &blk_le);
            for k_off in 0..blk_len {
                let k = k_start + k_off;
                for lane in 0..2 {
                    let ap = alpha_contribs[p][lane];
                    let lut = &sum_luts[p][lane];
                    let mut tau_word = [0u128; 64];
                    for (bit, tau_dst) in tau_word.iter_mut().enumerate() {
                        let idx = 64 * k + bit;
                        let mut acc = sum_raw[p][idx][lane].add(ap.mul_gf256(diff_sum[idx])).0;
                        for tl in 0..32 {
                            let hb = toeplitz_h[idx + tl];
                            acc ^= lut[2 * tl][(hb & 0x0F) as usize]
                                ^ lut[2 * tl + 1][(hb >> 4) as usize];
                        }
                        *tau_dst = acc;
                    }
                    let sh_blocks = SecretBuffer(shamir_share_tower128x64_mats(
                        t,
                        &eval_mats,
                        &tau_word,
                        &mut sub_rng,
                    ));
                    wipe_u128s(&mut tau_word);
                    for (q, dst_q) in dst_per_party.iter_mut().enumerate() {
                        let mut unpacked = unpack_bs_gf256x16_to_u128x64(&sh_blocks[q]);
                        for bit in 0..64 {
                            dst_q[k_off][lane][bit] =
                                dst_q[k_off][lane][bit].add(Tower128(unpacked[bit]));
                        }
                        wipe_u128s(&mut unpacked);
                    }
                }
            }
        }
    };

    #[cfg(any(test, feature = "std"))]
    if total_w > SH_BLK_WORDS {
        let mut party_iters: Vec<_> = all_macs
            .iter_mut()
            .map(|v| v.chunks_mut(SH_BLK_WORDS))
            .collect();
        let mut blk_groups: Vec<Vec<&mut [[[Tower128; 64]; 2]]>> = Vec::new();
        loop {
            let mut grp = Vec::with_capacity(n);
            for it in &mut party_iters {
                if let Some(sl) = it.next() {
                    grp.push(sl);
                }
            }
            if grp.is_empty() {
                break;
            }
            blk_groups.push(grp);
        }
        let workers = std::thread::available_parallelism()
            .map_or(1, usize::from)
            .min(16);
        let grp_per_worker = blk_groups.len().div_ceil(workers).max(1);
        std::thread::scope(|scope| {
            for (w_idx, worker_grps) in blk_groups.chunks_mut(grp_per_worker).enumerate() {
                let base_blk = w_idx * grp_per_worker;
                scope.spawn(move || {
                    for (off, grp) in worker_grps.iter_mut().enumerate() {
                        eval_sh_block(base_blk + off, grp.as_mut_slice());
                    }
                });
            }
        });
    } else {
        let mut party_iters: Vec<_> = all_macs
            .iter_mut()
            .map(|v| v.chunks_mut(SH_BLK_WORDS))
            .collect();
        let mut blk_idx = 0usize;
        loop {
            let mut grp = Vec::with_capacity(n);
            for it in &mut party_iters {
                if let Some(sl) = it.next() {
                    grp.push(sl);
                }
            }
            if grp.is_empty() {
                break;
            }
            eval_sh_block(blk_idx, grp.as_mut_slice());
            blk_idx += 1;
        }
    }
    #[cfg(not(any(test, feature = "std")))]
    {
        let mut party_iters: Vec<_> = all_macs
            .iter_mut()
            .map(|v| v.chunks_mut(SH_BLK_WORDS))
            .collect();
        let mut blk_idx = 0usize;
        loop {
            let mut grp = Vec::with_capacity(n);
            for it in &mut party_iters {
                if let Some(sl) = it.next() {
                    grp.push(sl);
                }
            }
            if grp.is_empty() {
                break;
            }
            eval_sh_block(blk_idx, grp.as_mut_slice());
            blk_idx += 1;
        }
    }

    for row in sum_raw.iter_mut() {
        for share in row {
            wipe_tower128(share);
        }
    }
    drop(sum_luts);
    drop(party_work_seeds);
    drop(diff_sum);

    spdz_pimac_check_bs_gf256_words(
        session_id,
        t,
        eval_points,
        alpha_shamir_shares,
        words_per_party,
        &all_macs,
        &mut r_chk_sh,
        &lhl_coin,
        party_rngs,
    )?;

    // Pop the disposable `r_chk` MAC slot and return the verified `num_words` SPDZ MAC shares
    for all_macs_p_item in all_macs[..n].iter_mut() {
        if let Some(mut chk_m) = (*all_macs_p_item).pop() {
            wipe_tower128(&mut chk_m[0]);
            wipe_tower128(&mut chk_m[1]);
        }
    }
    Ok(all_macs)
}

/// Batch `Π_MAC` consistency and full `0..n` degree check of Shamir value shares
/// `words_per_party[p][0..num_words]` against Shamir MAC shares `all_macs[p][0..=num_words]`.
///
/// Slot `num_words` of `all_macs` authenticates the disposable mask word whose value shares are
/// `r_chk_sh`. The check accepts only if both the value shares and the MAC shares lie on
/// degree-`< t` polynomials across all `n` parties and every MAC polynomial opens to
/// `alpha_lane * value` (`2^{-256}` soundness). `transcript` binds the check coin to everything
/// fixed before it; `r_chk_sh` is wiped.
#[expect(
    clippy::too_many_arguments,
    reason = "Quorum, value shares, MAC shares and private randomness are separate protocol inputs"
)]
pub(crate) fn spdz_pimac_check_bs_gf256_words(
    session_id: &[u8; 32],
    t: usize,
    eval_points: &[TowerGf256],
    alpha_shamir_shares: &[[Tower128; 2]],
    words_per_party: &[Vec<BitslicedGf256x64>],
    all_macs: &[Vec<[[Tower128; 64]; 2]>],
    r_chk_sh: &mut [BitslicedGf256x64],
    transcript: &[u8; 32],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<(), PreprocessError> {
    let n = eval_points.len();
    let num_words = words_per_party[0].len();
    const SH_BLK_WORDS: usize = 256;

    // 1) Check degree `< t` of `words_per_party` across `0..n` masked by `r_chk_sh` (`2^{-256}` soundness!)
    let chk_coin =
        run_commit_and_open_coin(session_id, b"SPDZ_BS64_PIMAC_CHK", transcript, party_rngs)?;
    let mut chk_xof = Cshake256Xof::new(b"QSAG.SPDZ.BS64.PIMAC_W/v1");
    chk_xof.absorb(&chk_coin);

    let mut deg_fold_sh = SecretBuffer(r_chk_sh.to_vec());
    #[expect(
        clippy::needless_range_loop,
        reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows"
    )]
    for k in 0..num_words {
        let mut s_byte = [0u8; 1];
        chk_xof.squeeze(&mut s_byte);
        let mat = PublicGf256Matrix::from_public_scalar(TowerGf256(s_byte[0] | 1));
        for p in 0..n {
            mat.scale_xor_into(&mut deg_fold_sh[p], &words_per_party[p][k]);
        }
    }
    // Check lanes `32..64` here while reserving lanes `0..16` and `16..32` strictly as two
    // independent 128-bit one-time pads `(R_0, R_1)` for `(Z_0, Z_1)` below (`0` pad reuse!).
    let mut deg_half_sh = vec![[0u64; 8]; n];
    for p in 0..n {
        for pl in 0..8 {
            deg_half_sh[p][pl] = deg_fold_sh[p][pl] & 0xFFFF_FFFF_0000_0000u64;
        }
    }
    drop(deg_fold_sh);
    let _ =
        open_and_check_degree_bs_gf256(t, eval_points, &deg_half_sh, "spdz_bs_gf256_words_deg")?;

    // 2) Independent 2-lane `Tower128` folding (`2^{-256}` soundness, zero pad reuse across lanes!):
    //    - `R_0` (lanes `0..16` of `r_chk_sh`) masks `Z_0` with identity basis `[I, *; 0, I]`;
    //    - `R_1` (lanes `16..32` of `r_chk_sh`) masks `Z_1` independently;
    //    - Lanes `32..64` of `r_chk_sh` and all `64 * num_words` wires use independent uniform
    //      `GF(2^128)` challenges `(chi_0, chi_1)` (no `| 1` bias!).
    let mut z_sh_lanes = SecretBuffer(vec![vec![Tower128::ZERO; n]; 2]);
    let mut z_mac = SecretBuffer(vec![[Tower128::ZERO; 2]; n]);
    for b_idx in 0..16 {
        let basis = Tower128(1u128 << (8 * b_idx));
        let mut cb0 = [0u8; 16];
        chk_xof.squeeze(&mut cb0);
        let chi0_hi = Tower128(u128::from_le_bytes(cb0));
        for p in 0..n {
            let r_lo = bs_gf256_extract_lane(&r_chk_sh[p], b_idx);
            let r_hi = bs_gf256_extract_lane(&r_chk_sh[p], 16 + b_idx);
            z_sh_lanes[0][p] = z_sh_lanes[0][p]
                .add(basis.mul_gf256(r_lo))
                .add(chi0_hi.mul_gf256(r_hi));
            z_sh_lanes[1][p] = z_sh_lanes[1][p].add(basis.mul_gf256(r_hi));
            z_mac[p][0] = z_mac[p][0]
                .add(basis.mul(all_macs[p][num_words][0][b_idx]))
                .add(chi0_hi.mul(all_macs[p][num_words][0][16 + b_idx]));
            z_mac[p][1] = z_mac[p][1].add(basis.mul(all_macs[p][num_words][1][16 + b_idx]));
        }
    }
    #[expect(
        clippy::needless_range_loop,
        reason = "Coordinate order binds the same lane across all party MAC matrices"
    )]
    for bit in 32..64 {
        let mut cb = [0u8; 32];
        chk_xof.squeeze(&mut cb);
        let chi0 = Tower128(u128::from_le_bytes(core::array::from_fn(|i| cb[i])));
        let chi1 = Tower128(u128::from_le_bytes(core::array::from_fn(|i| cb[16 + i])));
        for p in 0..n {
            let r_byte = bs_gf256_extract_lane(&r_chk_sh[p], bit);
            z_sh_lanes[0][p] = z_sh_lanes[0][p].add(chi0.mul_gf256(r_byte));
            z_sh_lanes[1][p] = z_sh_lanes[1][p].add(chi1.mul_gf256(r_byte));
            z_mac[p][0] = z_mac[p][0].add(chi0.mul(all_macs[p][num_words][0][bit]));
            z_mac[p][1] = z_mac[p][1].add(chi1.mul(all_macs[p][num_words][1][bit]));
        }
    }
    for r_chk_sh_p_item in r_chk_sh[..n].iter_mut() {
        wipe_u64s(&mut *r_chk_sh_p_item);
    }

    let fold_word_range = |blk_start: usize,
                           blk_count: usize|
     -> (Vec<[Tower128; 2]>, Vec<[Tower128; 2]>) {
        let mut local_zsh = vec![[Tower128::ZERO; 2]; n];
        let mut local_zmac = vec![[Tower128::ZERO; 2]; n];
        let mut chi_buf = [0u8; 64 * 32];
        for blk_idx in blk_start..(blk_start + blk_count) {
            let k_start = blk_idx * SH_BLK_WORDS;
            let k_end = (k_start + SH_BLK_WORDS).min(num_words);
            let mut blk_xof = Cshake256Xof::new(b"QSAG.SPDZ.BS64.PIMAC_W_BLK/v1");
            blk_xof.absorb(&chk_coin);
            blk_xof.absorb(&(blk_idx as u64).to_le_bytes());
            for k in k_start..k_end {
                blk_xof.squeeze(&mut chi_buf);
                let lhs: [[u128; 2]; 64] = core::array::from_fn(|bit| {
                    let off = 32 * bit;
                    [
                        u128::from_le_bytes(core::array::from_fn(|b| chi_buf[off + b])),
                        u128::from_le_bytes(core::array::from_fn(|b| chi_buf[off + 16 + b])),
                    ]
                });
                for p in 0..n {
                    for (bit, pair) in lhs.iter().enumerate() {
                        let x_byte = bs_gf256_extract_lane(&words_per_party[p][k], bit);
                        local_zsh[p][0] = local_zsh[p][0].add(Tower128(pair[0]).mul_gf256(x_byte));
                        local_zsh[p][1] = local_zsh[p][1].add(Tower128(pair[1]).mul_gf256(x_byte));
                    }
                    let mut rhs: [[u128; 2]; 64] = core::array::from_fn(|bit| {
                        [all_macs[p][k][0][bit].0, all_macs[p][k][1][bit].0]
                    });
                    let mut folded = qsag_asm::tower128_bdoz_2lane_mac(&lhs, &rhs);
                    local_zmac[p][0] = local_zmac[p][0].add(Tower128(folded[0]));
                    local_zmac[p][1] = local_zmac[p][1].add(Tower128(folded[1]));
                    wipe_u128s(rhs.as_flattened_mut());
                    wipe_u128s(&mut folded);
                }
            }
        }
        wipe_bytes(&mut chi_buf);
        (local_zsh, local_zmac)
    };

    let num_blks = num_words.div_ceil(SH_BLK_WORDS);
    #[cfg(any(test, feature = "std"))]
    if num_blks > 1 {
        let workers = std::thread::available_parallelism()
            .map_or(1, usize::from)
            .min(16);
        let blks_per_worker = num_blks.div_ceil(workers).max(1);
        let partials = std::thread::scope(|scope| {
            let mut handles = Vec::new();
            let mut b0 = 0usize;
            while b0 < num_blks {
                let cnt = (num_blks - b0).min(blks_per_worker);
                handles.push(scope.spawn(move || fold_word_range(b0, cnt)));
                b0 += cnt;
            }
            handles
                .into_iter()
                .map(|h| h.join().expect("spdz pimac fold worker"))
                .collect::<Vec<_>>()
        });
        for (mut l_zsh, mut l_zmac) in partials {
            for p in 0..n {
                z_sh_lanes[0][p] = z_sh_lanes[0][p].add(l_zsh[p][0]);
                z_sh_lanes[1][p] = z_sh_lanes[1][p].add(l_zsh[p][1]);
                z_mac[p][0] = z_mac[p][0].add(l_zmac[p][0]);
                z_mac[p][1] = z_mac[p][1].add(l_zmac[p][1]);
                wipe_tower128(&mut l_zsh[p]);
                wipe_tower128(&mut l_zmac[p]);
            }
        }
    } else if num_blks == 1 {
        let (mut l_zsh, mut l_zmac) = fold_word_range(0, 1);
        for p in 0..n {
            z_sh_lanes[0][p] = z_sh_lanes[0][p].add(l_zsh[p][0]);
            z_sh_lanes[1][p] = z_sh_lanes[1][p].add(l_zsh[p][1]);
            z_mac[p][0] = z_mac[p][0].add(l_zmac[p][0]);
            z_mac[p][1] = z_mac[p][1].add(l_zmac[p][1]);
            wipe_tower128(&mut l_zsh[p]);
            wipe_tower128(&mut l_zmac[p]);
        }
    }
    #[cfg(not(any(test, feature = "std")))]
    if num_blks > 0 {
        let (mut l_zsh, mut l_zmac) = fold_word_range(0, num_blks);
        for p in 0..n {
            z_sh_lanes[0][p] = z_sh_lanes[0][p].add(l_zsh[p][0]);
            z_sh_lanes[1][p] = z_sh_lanes[1][p].add(l_zsh[p][1]);
            z_mac[p][0] = z_mac[p][0].add(l_zmac[p][0]);
            z_mac[p][1] = z_mac[p][1].add(l_zmac[p][1]);
            wipe_tower128(&mut l_zsh[p]);
            wipe_tower128(&mut l_zmac[p]);
        }
    }

    let z_open = [
        commit_and_open_degree_tower128(
            session_id,
            "spdz_bs_gf256_pimac_z0",
            t,
            eval_points,
            &z_sh_lanes[0],
            party_rngs,
        )?,
        commit_and_open_degree_tower128(
            session_id,
            "spdz_bs_gf256_pimac_z1",
            t,
            eval_points,
            &z_sh_lanes[1],
            party_rngs,
        )?,
    ];
    drop(z_sh_lanes);

    // Open `D_lane(x_p) = [gamma_lane(Z_lane)]_p ^ (Z_lane * [alpha_lane]_p)` across ALL `0..n` parties!
    for (lane, &z_op_l) in z_open.iter().enumerate() {
        let d_sh: SecretBuffer<Vec<Tower128>> = SecretBuffer(
            (0..n)
                .map(|p| z_mac[p][lane].add(z_op_l.mul(alpha_shamir_shares[p][lane])))
                .collect(),
        );
        let d_zero = commit_and_open_degree_tower128(
            session_id,
            "spdz_bs_gf256_pimac_d",
            t,
            eval_points,
            &d_sh,
            party_rngs,
        )?;
        if !d_zero.ct_eq(Tower128::ZERO) {
            return Err(PreprocessError::MacCheckFailed {
                phase: "spdz_bs_gf256_pimac",
                accused_party: None,
            });
        }
    }
    drop(z_mac);
    Ok(())
}

/// Share a 64-bit Boolean word `word` across `eval_points` as a `BitslicedGf256x64` vector of
/// degree `< t` using `rng` and precomputed `PublicGf256Matrix` evaluation points.
#[inline]
fn shamir_share_bits64_gf256_mats(
    t: usize,
    eval_mats: &[PublicGf256Matrix],
    word: u64,
    rng: &mut PartyPrivateRng,
) -> Vec<BitslicedGf256x64> {
    let n = eval_mats.len();
    let mut coeffs: Vec<BitslicedGf256x64> = Vec::with_capacity(t);
    coeffs.push([word, 0, 0, 0, 0, 0, 0, 0]);
    for _ in 1..t {
        let mut rand_plane = [0u64; 8];
        for pl in &mut rand_plane {
            *pl = rng.next_u64();
        }
        coeffs.push(rand_plane);
    }

    let mut out = vec![[0u64; 8]; n];
    for (p, mat_pt) in eval_mats.iter().enumerate() {
        let mut acc = [0u64; 8];
        for c in coeffs.iter().rev() {
            acc = bs_gf256_xor(&mat_pt.scale_planes(&acc), c);
        }
        out[p] = acc;
    }
    for c in &mut coeffs {
        wipe_u64s(c);
    }
    out
}

#[cfg(test)]
fn shamir_share_bits64_gf256(
    t: usize,
    eval_points: &[TowerGf256],
    word: u64,
    rng: &mut PartyPrivateRng,
) -> Vec<BitslicedGf256x64> {
    let mats: Vec<PublicGf256Matrix> = eval_points
        .iter()
        .map(|&pt| PublicGf256Matrix::from_public_scalar(pt))
        .collect();
    shamir_share_bits64_gf256_mats(t, &mats, word, rng)
}

#[inline]
fn transpose_64x64_in_place(tile: &mut [u64; 64]) {
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
}

#[inline]
fn unpack_bs_gf256x16_to_u128x64(blocks: &[BitslicedGf256x64; 16]) -> [u128; 64] {
    let mut lo = [0u64; 64];
    let mut hi = [0u64; 64];
    for byte_idx in 0..8 {
        for pl in 0..8 {
            lo[8 * byte_idx + pl] = blocks[byte_idx][pl];
            hi[8 * byte_idx + pl] = blocks[8 + byte_idx][pl];
        }
    }
    transpose_64x64_in_place(&mut lo);
    transpose_64x64_in_place(&mut hi);
    let out: [u128; 64] = core::array::from_fn(|bit| (lo[bit] as u128) | ((hi[bit] as u128) << 64));
    wipe_u64s(&mut lo);
    wipe_u64s(&mut hi);
    out
}

/// Pack 64 `Tower128` elements (`[u128; 64]`) into 16 bitsliced `TowerGf256` byte blocks
/// (`[BitslicedGf256x64; 16]`) and Shamir-share at degree `< t` over `eval_mats`.
fn shamir_share_tower128x64_mats(
    t: usize,
    eval_mats: &[PublicGf256Matrix],
    vals: &[u128; 64],
    rng: &mut PartyPrivateRng,
) -> Vec<[BitslicedGf256x64; 16]> {
    let n = eval_mats.len();
    let mut lo: [u64; 64] = core::array::from_fn(|bit| vals[bit] as u64);
    let mut hi: [u64; 64] = core::array::from_fn(|bit| (vals[bit] >> 64) as u64);
    transpose_64x64_in_place(&mut lo);
    transpose_64x64_in_place(&mut hi);
    let mut const_blocks = [[0u64; 8]; 16];
    for byte_idx in 0..8 {
        for pl in 0..8 {
            const_blocks[byte_idx][pl] = lo[8 * byte_idx + pl];
            const_blocks[8 + byte_idx][pl] = hi[8 * byte_idx + pl];
        }
    }
    wipe_u64s(&mut lo);
    wipe_u64s(&mut hi);

    let mut out = vec![[[0u64; 8]; 16]; n];
    for byte_idx in 0..16 {
        let mut coeffs: Vec<BitslicedGf256x64> = Vec::with_capacity(t);
        coeffs.push(const_blocks[byte_idx]);
        for _ in 1..t {
            let mut rp = [0u64; 8];
            for pl in &mut rp {
                *pl = rng.next_u64();
            }
            coeffs.push(rp);
        }
        for (p, mat_pt) in eval_mats.iter().enumerate() {
            let mut acc = [0u64; 8];
            for c in coeffs.iter().rev() {
                acc = bs_gf256_xor(&mat_pt.scale_planes(&acc), c);
            }
            out[p][byte_idx] = acc;
        }
        for c in &mut coeffs {
            wipe_u64s(c);
        }
    }
    for blk in &mut const_blocks {
        wipe_u64s(blk);
    }
    out
}

/// Batch bitsliced `64x` SPDZ committed opening + 2-lane `Tower128` `MacCheck` (`2^{-256}` soundness)
/// across `batch_len` words in **2 constant rounds** (1 commitment hash per party + 1 folded `MacCheck`).
#[expect(
    clippy::too_many_arguments,
    reason = "Quorum, value shares, MAC shares and private randomness are separate protocol inputs"
)]
pub fn commit_and_open_spdz_bs_gf256_batch_quorum(
    session_id: &[u8; 32],
    phase: &'static str,
    t: usize,
    quorum_eval_points: &[TowerGf256],
    batch_shares: &[Vec<BitslicedGf256x64>],
    batch_macs: &[Vec<[[Tower128; 64]; 2]>],
    alpha_shares: &[[Tower128; 2]],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<BitslicedGf256x64>, PreprocessError> {
    let m = quorum_eval_points.len();
    if t == 0
        || m < t
        || batch_shares.len() != m
        || batch_macs.len() != m
        || alpha_shares.len() != m
        || party_rngs.len() != m
    {
        return Err(PreprocessError::InvalidThreshold { t, n: m });
    }
    let batch_len = batch_shares[0].len();
    for p in 0..m {
        if batch_shares[p].len() != batch_len || batch_macs[p].len() != batch_len {
            return Err(PreprocessError::InvalidThreshold { t, n: m });
        }
    }
    if batch_len == 0 {
        return Ok(Vec::new());
    }
    validate_all_eval_points_gf256(quorum_eval_points)?;

    // Round 1: Commit to all `batch_len` words per party before revealing any share
    let mut salts = Vec::with_capacity(m);
    let mut coms = Vec::with_capacity(m);
    for p in 0..m {
        let salt = party_rngs[p].next_bytes32();
        let mut xof = Cshake256Xof::new(b"QSAG.SPDZ.BS64.BATCH.OPEN.COM/v1");
        xof.absorb(session_id);
        xof.absorb(&(phase.len() as u64).to_be_bytes());
        xof.absorb(phase.as_bytes());
        xof.absorb(&(p as u64).to_be_bytes());
        xof.absorb(&salt);
        #[expect(
            clippy::needless_range_loop,
            reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows"
        )]
        for w in 0..batch_len {
            #[expect(
                clippy::needless_range_loop,
                reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows"
            )]
            for pl in 0..8 {
                xof.absorb(&batch_shares[p][w][pl].to_le_bytes());
            }
        }
        let mut com = [0u8; 32];
        xof.squeeze(&mut com);
        salts.push(salt);
        coms.push(com);
    }
    for p in 0..m {
        let mut xof = Cshake256Xof::new(b"QSAG.SPDZ.BS64.BATCH.OPEN.COM/v1");
        xof.absorb(session_id);
        xof.absorb(&(phase.len() as u64).to_be_bytes());
        xof.absorb(phase.as_bytes());
        xof.absorb(&(p as u64).to_be_bytes());
        xof.absorb(&salts[p]);
        #[expect(
            clippy::needless_range_loop,
            reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows"
        )]
        for w in 0..batch_len {
            #[expect(
                clippy::needless_range_loop,
                reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows"
            )]
            for pl in 0..8 {
                xof.absorb(&batch_shares[p][w][pl].to_le_bytes());
            }
        }
        let mut exp = [0u8; 32];
        xof.squeeze(&mut exp);
        wipe_bytes32(&mut salts[p]);
        if !ct_eq_bytes32(&exp, &coms[p]) {
            return Err(PreprocessError::ShareCommitMismatch { phase, party_id: p });
        }
    }

    let lambdas_0 = lagrange_weights_zero_gf256(&quorum_eval_points[..t])
        .ok_or(PreprocessError::DuplicateOrZeroEvalPoint)?;
    let lambda0_mats: Vec<PublicGf256Matrix> = lambdas_0
        .iter()
        .map(|&l| PublicGf256Matrix::from_public_scalar(l))
        .collect();
    let mut extrap_mats: Vec<Vec<PublicGf256Matrix>> = Vec::with_capacity(m - t);
    for r_idx in t..m {
        let xm = quorum_eval_points[r_idx];
        let mut row = Vec::with_capacity(t);
        for i in 0..t {
            let mut num = TowerGf256::ONE;
            let mut den = TowerGf256::ONE;
            for j in 0..t {
                if i == j {
                    continue;
                }
                num = num.mul(xm.add(quorum_eval_points[j]));
                den = den.mul(quorum_eval_points[i].add(quorum_eval_points[j]));
            }
            let li = num.mul(den.inv().ok_or(PreprocessError::DuplicateOrZeroEvalPoint)?);
            row.push(PublicGf256Matrix::from_public_scalar(li));
        }
        extrap_mats.push(row);
    }

    let mut opened = Vec::with_capacity(batch_len);
    let mut dig_xof = Cshake256Xof::new(b"QSAG.SPDZ.BS64.BATCH.DIG/v1");
    for (w, _) in batch_shares[0].iter().enumerate() {
        let mut sec = [0u64; 8];
        for q in 0..t {
            lambda0_mats[q].scale_xor_into(&mut sec, &batch_shares[q][w]);
        }
        for r_idx in t..m {
            let mut expected = [0u64; 8];
            for i in 0..t {
                extrap_mats[r_idx - t][i].scale_xor_into(&mut expected, &batch_shares[i][w]);
            }
            if expected != batch_shares[r_idx][w] {
                return Err(PreprocessError::DegreeCheckFailed { phase });
            }
        }
        #[expect(
            clippy::needless_range_loop,
            reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows"
        )]
        for pl in 0..8 {
            dig_xof.absorb(&sec[pl].to_le_bytes());
        }
        opened.push(sec);
    }
    let mut open_digest = [0u8; 32];
    dig_xof.squeeze(&mut open_digest);

    // Round 2: Public-coin random `Tower128` folding across all `64 * batch_len` opened lanes + ZK `MacCheck`
    let fold_coin =
        run_commit_and_open_coin(session_id, phase.as_bytes(), &open_digest, party_rngs)?;
    let mut chi_xof = Cshake256Xof::new(b"QSAG.SPDZ.BS64.BATCH.CHIS/v1");
    chi_xof.absorb(&fold_coin);

    let mut x_folded = [Tower128::ZERO; 2];
    let mut m_folded = SecretBuffer(vec![[Tower128::ZERO; 2]; t]);
    let mut chi_raw = [0u8; 2 * 64 * 16];
    for w in 0..batch_len {
        chi_xof.squeeze(&mut chi_raw);
        let lhs: [[u128; 2]; 64] = core::array::from_fn(|bit| {
            let off = 32 * bit;
            [
                u128::from_le_bytes(core::array::from_fn(|b| chi_raw[off + b])),
                u128::from_le_bytes(core::array::from_fn(|b| chi_raw[off + 16 + b])),
            ]
        });
        for (bit, pair) in lhs.iter().enumerate() {
            let xb = bs_gf256_extract_lane(&opened[w], bit);
            x_folded[0] = x_folded[0].add(Tower128(pair[0]).mul_gf256(xb));
            x_folded[1] = x_folded[1].add(Tower128(pair[1]).mul_gf256(xb));
        }
        for q in 0..t {
            let mut rhs: [[u128; 2]; 64] = core::array::from_fn(|bit| {
                [batch_macs[q][w][0][bit].0, batch_macs[q][w][1][bit].0]
            });
            let mut fold = qsag_asm::tower128_bdoz_2lane_mac(&lhs, &rhs);
            m_folded[q][0] = m_folded[q][0].add(Tower128(fold[0]));
            m_folded[q][1] = m_folded[q][1].add(Tower128(fold[1]));
            crate::wipe::wipe_u128s(rhs.as_flattened_mut());
            crate::wipe::wipe_u128s(&mut fold);
        }
    }
    wipe_bytes(&mut chi_raw);

    let mut z_masks = SecretBuffer(vec![[Tower128::ZERO; 2]; t]);
    if t > 1 {
        for party_rngs_r_item in party_rngs[..t].iter_mut() {
            let mut sum0 = Tower128::ZERO;
            let mut sum1 = Tower128::ZERO;
            for z_masks_q_item in z_masks[..(t - 1)].iter_mut() {
                let u0 = (*party_rngs_r_item).next_tower128();
                let u1 = (*party_rngs_r_item).next_tower128();
                (*z_masks_q_item)[0] = (*z_masks_q_item)[0].add(u0);
                (*z_masks_q_item)[1] = (*z_masks_q_item)[1].add(u1);
                sum0 = sum0.add(u0);
                sum1 = sum1.add(u1);
            }
            z_masks[t - 1][0] = z_masks[t - 1][0].add(sum0);
            z_masks[t - 1][1] = z_masks[t - 1][1].add(sum1);
        }
    }

    let mut sigmas = SecretBuffer(Vec::with_capacity(t));
    let mut sig_salts = SecretBuffer(Vec::with_capacity(t));
    let mut sig_coms = Vec::with_capacity(t);
    for q in 0..t {
        let lam_emb = Tower128::embed_gf256(lambdas_0[q]);
        let s0 = lam_emb
            .mul(m_folded[q][0].add(x_folded[0].mul(alpha_shares[q][0])))
            .add(z_masks[q][0]);
        let s1 = lam_emb
            .mul(m_folded[q][1].add(x_folded[1].mul(alpha_shares[q][1])))
            .add(z_masks[q][1]);
        wipe_tower128(&mut z_masks[q]);
        wipe_tower128(&mut m_folded[q]);
        let salt = party_rngs[q].next_bytes32();
        let q_be = (q as u64).to_be_bytes();
        let com = cshake256_32_multi_frame(
            b"QSAG.SPDZ.BS64.BATCH.MAC.COM/v1",
            &[
                session_id,
                phase.as_bytes(),
                &q_be,
                &s0.0.to_le_bytes(),
                &s1.0.to_le_bytes(),
                &salt,
            ],
        );
        sigmas.push([s0, s1]);
        sig_salts.push(salt);
        sig_coms.push(com);
    }

    let mut sum0 = Tower128::ZERO;
    let mut sum1 = Tower128::ZERO;
    for q in 0..t {
        let q_be = (q as u64).to_be_bytes();
        let exp = cshake256_32_multi_frame(
            b"QSAG.SPDZ.BS64.BATCH.MAC.COM/v1",
            &[
                session_id,
                phase.as_bytes(),
                &q_be,
                &sigmas[q][0].0.to_le_bytes(),
                &sigmas[q][1].0.to_le_bytes(),
                &sig_salts[q],
            ],
        );
        wipe_bytes32(&mut sig_salts[q]);
        if !ct_eq_bytes32(&exp, &sig_coms[q]) {
            return Err(PreprocessError::ShareCommitMismatch { phase, party_id: q });
        }
        sum0 = sum0.add(sigmas[q][0]);
        sum1 = sum1.add(sigmas[q][1]);
        wipe_tower128(&mut sigmas[q]);
    }
    if !(sum0.ct_eq(Tower128::ZERO) && sum1.ct_eq(Tower128::ZERO)) {
        return Err(PreprocessError::MacCheckFailed {
            phase,
            accused_party: None,
        });
    }
    Ok(opened)
}

/// Run the **100% dealerless `Π_triple_f2`** offline preprocessing protocol producing `num_triples`
/// SPDZ-MAC-authenticated, `3 -> 1` privacy-amplified 64-way bitsliced Boolean Beaver triples per party:
/// - Dealerless 2-lane `Tower128` Shamir SPDZ MAC setup (`spdz_setup_alpha_gf256`);
/// - Derandomized pairwise Ring-LWE + KOS OT Boolean AND + two uniform `Tower128` MASCOT companions;
/// - LHL-amplified `spdz_authenticate_bs_gf256_words` equipping every `a, b, c` wire AND every
///   companion share with stored 2-lane `Tower128` SPDZ MAC shares (`[P0-05]`, `[P0-07]`);
/// - Batched SPDZ-MAC-verified 2-lane `Tower128` MASCOT companion sacrifice ($2^{-256}$ soundness,
///   `0` unauthenticated openings even under $2t - 1 > n$ dishonest majority!);
/// - Exact $2^{-256}$ per-lane (`64 x 64` full binary matrix $\times$ `4` blocks) Frobenius
///   Booleanity check opened via `commit_and_open_spdz_bs_gf256_quorum` (`[P0-06]`);
/// - `3 -> 1` SPDZ-authenticated Beaver combiner amplifying privacy on both `a` and `b` (`[P1-05]`).
///   The three raw triples of each bucket are chosen by a public permutation drawn from a
///   commit-and-open coin after all raw shares are authenticated, so a party that deviates on a
///   raw triple cannot choose its bucket partners.
pub fn run_dealerless_pi_triple_f2(
    session_id: [u8; 32],
    t: usize,
    eval_points: &[TowerGf256],
    num_triples: usize,
    ot_mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<PreprocessedKeccakPartyVault>, PreprocessError> {
    run_dealerless_pi_triple_f2_with_fault(
        session_id,
        t,
        eval_points,
        num_triples,
        ot_mesh,
        party_rngs,
        |_, _, _| {},
    )
}

/// Fault-injectable entry point for adversarial unit tests of `Π_triple_f2`.
pub fn run_dealerless_pi_triple_f2_with_fault<F>(
    session_id: [u8; 32],
    t: usize,
    eval_points: &[TowerGf256],
    num_triples: usize,
    ot_mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
    fault_hook: F,
) -> Result<Vec<PreprocessedKeccakPartyVault>, PreprocessError>
where
    F: FnMut(usize, &mut [BitslicedGf256x64], &mut [BitslicedGf256x64]),
{
    let n = eval_points.len();
    if t == 0 || t > n || party_rngs.len() != n || ot_mesh.n != n {
        return Err(PreprocessError::InvalidThreshold { t, n });
    }
    validate_all_eval_points_gf256(eval_points)?;

    let (mut alpha_contribs, mut alpha_shamir) =
        spdz_setup_alpha_gf256(&session_id, t, eval_points, party_rngs)?;
    let res = run_dealerless_pi_triple_f2_with_alpha_and_fault(
        session_id,
        t,
        eval_points,
        num_triples,
        &alpha_contribs,
        &alpha_shamir,
        ot_mesh,
        party_rngs,
        fault_hook,
    )
    .map(|(vaults, _bucket_permutation)| vaults);
    for ac in &mut alpha_contribs {
        wipe_tower128(ac);
    }
    for ash in &mut alpha_shamir {
        wipe_tower128(ash);
    }
    res
}

/// Run dealerless `Π_triple_f2` bound to an existing session SPDZ MAC key `(alpha_contribs, alpha_shamir)`
/// (used when `SpdzAuthenticatedKeyShare` and `PreprocessedKeccakPartyVault` share a single global $\alpha$).
#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the public preprocessing API used by other protocol modules"
)]
pub fn run_dealerless_pi_triple_f2_with_alpha(
    session_id: [u8; 32],
    t: usize,
    eval_points: &[TowerGf256],
    num_triples: usize,
    alpha_contribs: &[[Tower128; 2]],
    alpha_shamir: &[[Tower128; 2]],
    ot_mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<PreprocessedKeccakPartyVault>, PreprocessError> {
    run_dealerless_pi_triple_f2_with_alpha_and_fault(
        session_id,
        t,
        eval_points,
        num_triples,
        alpha_contribs,
        alpha_shamir,
        ot_mesh,
        party_rngs,
        |_, _, _| {},
    )
    .map(|(vaults, _bucket_permutation)| vaults)
}

/// Unbiased Fisher–Yates permutation of `0..len`, expanded from the public coin `coin` under
/// `domain`.
///
/// Position `i` (from `len - 1` down to `1`) is swapped with an index drawn uniformly from
/// `0..=i`. Each draw takes 64 XOF bits, masks them to the smallest power of two above `i`
/// and is repeated until the value is at most `i`, so no residue class is favoured (a draw is
/// rejected with probability below 1/2).
pub(crate) fn derive_coin_permutation(coin: &[u8; 32], domain: &[u8], len: usize) -> Vec<u32> {
    assert!(
        len <= u32::MAX as usize,
        "permutation length exceeds u32 range"
    );
    let mut xof = Cshake256Xof::new(b"QSAG.COIN.PERMUTATION/v1");
    xof.absorb(&(domain.len() as u64).to_le_bytes());
    xof.absorb(domain);
    xof.absorb(&(len as u64).to_le_bytes());
    xof.absorb(coin);

    let mut perm: Vec<u32> = (0..len as u32).collect();
    for i in (1..len).rev() {
        let bound = i as u64;
        let mask = u64::MAX >> bound.leading_zeros();
        let j = loop {
            let mut buf = [0u8; 8];
            xof.squeeze(&mut buf);
            let draw = u64::from_le_bytes(buf) & mask;
            if draw <= bound {
                break draw as usize;
            }
        };
        perm.swap(i, j);
    }
    perm
}

/// Digest of the locked raw-triple material of `Π_triple_f2`, used to bind the bucket coin.
///
/// Every party commits (with a private 32-byte blinder) to its shares and SPDZ MAC shares of
/// all raw `(a, b, c)` words; the digest covers all commitments. The commitments are never
/// opened: what fixes the shares is their SPDZ authentication, and this digest ties the coin's
/// transcript to that fixed state.
#[expect(clippy::too_many_arguments, reason = "one slice per locked share kind")]
fn pi_triple_f2_lock_digest(
    session_id: &[u8; 32],
    raw_triples: usize,
    a_sh: &[Vec<BitslicedGf256x64>],
    b_sh: &[Vec<BitslicedGf256x64>],
    c_sh: &[Vec<BitslicedGf256x64>],
    a_mac: &[Vec<[[Tower128; 64]; 2]>],
    b_mac: &[Vec<[[Tower128; 64]; 2]>],
    c_mac: &[Vec<[[Tower128; 64]; 2]>],
    party_rngs: &mut [PartyPrivateRng],
) -> [u8; 32] {
    // Each party hashes only its own shares, so the commitments are computed side by side.
    let mut commitments: Vec<(usize, [u8; 32], [u8; 32])> = party_rngs
        .iter_mut()
        .enumerate()
        .map(|(p, rng)| (p, rng.next_bytes32(), [0u8; 32]))
        .collect();
    triple_f2::par_for_each(&mut commitments, |(p, blinder, commitment)| {
        let p = *p;
        let mut com = Cshake256Xof::new(b"QSAG.TRIPLE.F2.LOCK.COMMIT/v1");
        com.absorb(session_id);
        com.absorb(&(p as u64).to_le_bytes());
        com.absorb(blinder);
        wipe_bytes32(blinder);
        for k in 0..raw_triples {
            for (words, macs) in [
                (&a_sh[p][k], &a_mac[p][k]),
                (&b_sh[p][k], &b_mac[p][k]),
                (&c_sh[p][k], &c_mac[p][k]),
            ] {
                for plane in words {
                    com.absorb(&plane.to_le_bytes());
                }
                for lane in macs {
                    for tag in lane {
                        com.absorb(&tag.0.to_le_bytes());
                    }
                }
            }
        }
        com.squeeze(commitment);
    });
    let mut all = Cshake256Xof::new(b"QSAG.TRIPLE.F2.LOCK.DIGEST/v1");
    all.absorb(session_id);
    all.absorb(&(raw_triples as u64).to_le_bytes());
    all.absorb(&(commitments.len() as u64).to_le_bytes());
    for (_, _, commitment) in &commitments {
        all.absorb(commitment);
    }
    let mut digest = [0u8; 32];
    all.squeeze(&mut digest);
    digest
}

/// Runs `Π_triple_f2` and also returns the public bucket permutation it used: final triple `k`
/// is combined from raw triples `perm[k]`, `perm[num_triples + k]`, `perm[2 * num_triples + k]`.
#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the public preprocessing API used by other protocol modules"
)]
fn run_dealerless_pi_triple_f2_with_alpha_and_fault<F>(
    session_id: [u8; 32],
    t: usize,
    eval_points: &[TowerGf256],
    num_triples: usize,
    alpha_contribs: &[[Tower128; 2]],
    alpha_shamir: &[[Tower128; 2]],
    ot_mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
    mut fault_hook: F,
) -> Result<(Vec<PreprocessedKeccakPartyVault>, Vec<u32>), PreprocessError>
where
    F: FnMut(usize, &mut [BitslicedGf256x64], &mut [BitslicedGf256x64]),
{
    let n = eval_points.len();
    if t == 0
        || t > n
        || party_rngs.len() != n
        || ot_mesh.n != n
        || alpha_contribs.len() != n
        || alpha_shamir.len() != n
    {
        return Err(PreprocessError::InvalidThreshold { t, n });
    }
    validate_all_eval_points_gf256(eval_points)?;

    if num_triples == 0 {
        let mut vaults = Vec::with_capacity(n);
        for p in 0..n {
            vaults.push(PreprocessedKeccakPartyVault {
                party_id: p,
                eval_point: eval_points[p],
                mac_alpha_lanes: alpha_shamir[p],
                triples: Vec::new(),
                cursor: 0,
                poisoned: false,
            });
        }
        return Ok((vaults, Vec::new()));
    }
    triple_f2::run_pi_triple_f2(
        session_id,
        t,
        eval_points,
        num_triples,
        alpha_contribs,
        alpha_shamir,
        ot_mesh,
        party_rngs,
        &mut triple_f2::PiTripleF2Faults {
            shamir_shares: Some(&mut fault_hook),
            ..Default::default()
        },
    )
}

// ============================================================================
// 6. Dealerless `Π_pow7` & Canonical `< p` A2B Bit-Masks (`PreprocessedPoseidonVault`)
// ============================================================================

/// One party's isolated 1-round Binomial Power-7 tuple share `([r], [r^2], ..., [r^7])`
/// paired with full `GoldilocksExt2` SPDZ Shamir MAC shares `r_macs[0..7]` (`!Clone`, wiped on `Drop`).
pub struct AuthenticatedPower7Share {
    pub r_pows: [Goldilocks; 7],
    /// Full SPDZ Shamir MAC shares `([\alpha \cdot r], [\alpha \cdot r^2], ..., [\alpha \cdot r^7])`.
    pub r_macs: [GoldilocksExt2; 7],
    /// Convenience alias equal to `r_macs[0]` (`[\alpha \cdot r]`).
    pub r1_mac: GoldilocksExt2,
}

impl fmt::Debug for AuthenticatedPower7Share {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("AuthenticatedPower7Share([REDACTED])")
    }
}

impl Drop for AuthenticatedPower7Share {
    fn drop(&mut self) {
        wipe_goldilocks(&mut self.r_pows);
        wipe_ext2(&mut self.r_macs);
        wipe_ext2(core::slice::from_mut(&mut self.r1_mac));
    }
}

/// One party's isolated `Goldilocks` Beaver triple share `([a], [b], [c])` paired with
/// `GoldilocksExt2` SPDZ Shamir MAC shares (`a_mac, b_mac, c_mac`) (`!Clone`, wiped on `Drop`).
pub struct GoldilocksBeaverShare {
    pub a: Goldilocks,
    pub b: Goldilocks,
    pub c: Goldilocks,
    pub a_mac: GoldilocksExt2,
    pub b_mac: GoldilocksExt2,
    pub c_mac: GoldilocksExt2,
}

impl fmt::Debug for GoldilocksBeaverShare {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("GoldilocksBeaverShare([REDACTED])")
    }
}

impl Drop for GoldilocksBeaverShare {
    fn drop(&mut self) {
        wipe_goldilocks(core::slice::from_mut(&mut self.a));
        wipe_goldilocks(core::slice::from_mut(&mut self.b));
        wipe_goldilocks(core::slice::from_mut(&mut self.c));
        wipe_ext2(core::slice::from_mut(&mut self.a_mac));
        wipe_ext2(core::slice::from_mut(&mut self.b_mac));
        wipe_ext2(core::slice::from_mut(&mut self.c_mac));
    }
}

/// One party's isolated canonical `< p` 64-bit A2B bit-mask share `([b_0], ..., [b_63])`
/// verified in preprocessing via SPDZ `MacCheck` to satisfy $b_k \in \{0, 1\}$ AND
/// $\sum_{k=0}^{63} 2^k b_k < p$, paired with full `GoldilocksExt2` SPDZ MAC shares.
pub struct CanonicalBitMask64Share {
    pub bit_shares: [Goldilocks; 64],
    pub field_sum_share: Goldilocks,
    pub bit_macs: [GoldilocksExt2; 64],
    pub field_sum_mac: GoldilocksExt2,
}

impl fmt::Debug for CanonicalBitMask64Share {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("CanonicalBitMask64Share([REDACTED])")
    }
}

impl Drop for CanonicalBitMask64Share {
    fn drop(&mut self) {
        wipe_goldilocks(&mut self.bit_shares);
        wipe_goldilocks(core::slice::from_mut(&mut self.field_sum_share));
        wipe_ext2(&mut self.bit_macs);
        wipe_ext2(core::slice::from_mut(&mut self.field_sum_mac));
    }
}

/// Per-party isolated vault of dealerless-preprocessed `Poseidon2` `Π_pow7` tuples,
/// `Goldilocks` Beaver triples, and canonical `< p` 64-bit A2B masks (`!Clone`, wiped on `Drop`,
/// permanently poisoned and zeroized on any `MacCheck` abort `[P0-07]`).
pub struct PreprocessedPoseidonPartyVault {
    pub party_id: usize,
    pub eval_point: Goldilocks,
    /// Degree-`< t` Shamir share $[\alpha]_p \in \mathbb{F}_{p^2}$ of the global SPDZ MAC key.
    pub mac_alpha_share: GoldilocksExt2,
    pow7_tuples: Vec<AuthenticatedPower7Share>,
    pow7_cursor: usize,
    beaver_triples: Vec<GoldilocksBeaverShare>,
    beaver_cursor: usize,
    a2b_masks: Vec<CanonicalBitMask64Share>,
    a2b_cursor: usize,
    poisoned: bool,
}

impl fmt::Debug for PreprocessedPoseidonPartyVault {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "PreprocessedPoseidonPartyVault(party={}, pow7_rem={}, beaver_rem={}, a2b_rem={}, poisoned={})",
            self.party_id,
            self.remaining_pow7(),
            self.remaining_beaver(),
            self.remaining_a2b(),
            self.poisoned
        )
    }
}

impl Drop for PreprocessedPoseidonPartyVault {
    fn drop(&mut self) {
        wipe_ext2(core::slice::from_mut(&mut self.mac_alpha_share));
    }
}

impl PreprocessedPoseidonPartyVault {
    /// Trusted dealer fixture for large online-protocol tests only. Small production
    /// preprocessing tests separately exercise OT, sacrifice and canonicality checks.
    #[cfg(test)]
    pub(crate) fn fill_two_party_online_fixture(
        vaults: &mut [Self],
        budget: (usize, usize, usize),
        rng: &mut PartyPrivateRng,
    ) {
        assert_eq!(vaults.len(), 2);
        let pts = [vaults[0].eval_point, vaults[1].eval_point];
        let alpha = open_and_check_degree_ext2(
            2,
            &pts,
            &[vaults[0].mac_alpha_share, vaults[1].mac_alpha_share],
            "online fixture alpha",
        )
        .unwrap();
        let share = |value: Goldilocks, rng: &mut PartyPrivateRng| {
            let slope = rng.next_goldilocks();
            let mac_slope = rng.next_ext2();
            pts.map(|x| {
                (
                    value + slope * x,
                    alpha.mul_base(value) + mac_slope.mul_base(x),
                )
            })
        };
        for vault in vaults.iter_mut() {
            assert_eq!(
                (
                    vault.remaining_pow7(),
                    vault.remaining_beaver(),
                    vault.remaining_a2b()
                ),
                (0, 0, 0)
            );
            vault.pow7_tuples.reserve(budget.0);
            vault.beaver_triples.reserve(budget.1);
            vault.a2b_masks.reserve(budget.2);
        }
        for _ in 0..budget.0 {
            let r = rng.next_goldilocks();
            let mut power = Goldilocks::ONE;
            let shares: [[(Goldilocks, GoldilocksExt2); 2]; 7] = core::array::from_fn(|_| {
                power *= r;
                share(power, rng)
            });
            for (p, vault) in vaults.iter_mut().enumerate() {
                vault.pow7_tuples.push(AuthenticatedPower7Share {
                    r_pows: core::array::from_fn(|k| shares[k][p].0),
                    r_macs: core::array::from_fn(|k| shares[k][p].1),
                    r1_mac: shares[0][p].1,
                });
            }
        }
        for _ in 0..budget.1 {
            let a = rng.next_goldilocks();
            let b = rng.next_goldilocks();
            let shares = [a, b, a * b].map(|x| share(x, rng));
            for (p, vault) in vaults.iter_mut().enumerate() {
                vault.beaver_triples.push(GoldilocksBeaverShare {
                    a: shares[0][p].0,
                    b: shares[1][p].0,
                    c: shares[2][p].0,
                    a_mac: shares[0][p].1,
                    b_mac: shares[1][p].1,
                    c_mac: shares[2][p].1,
                });
            }
        }
        for _ in 0..budget.2 {
            let r = rng.next_goldilocks().to_canonical_u64();
            let shares: [[(Goldilocks, GoldilocksExt2); 2]; 64] = core::array::from_fn(|bit| {
                share(Goldilocks::from_u64_reduced((r >> bit) & 1), rng)
            });
            for (p, vault) in vaults.iter_mut().enumerate() {
                let bit_shares = core::array::from_fn(|k| shares[k][p].0);
                let bit_macs = core::array::from_fn(|k| shares[k][p].1);
                let mut sum = Goldilocks::ZERO;
                let mut mac = GoldilocksExt2::ZERO;
                for k in 0..64 {
                    let weight = Goldilocks::from_u64_reduced(1u64 << k);
                    sum += weight * bit_shares[k];
                    mac += bit_macs[k].mul_base(weight);
                }
                vault.a2b_masks.push(CanonicalBitMask64Share {
                    bit_shares,
                    bit_macs,
                    field_sum_share: sum,
                    field_sum_mac: mac,
                });
            }
        }
    }

    #[cfg(test)]
    pub(crate) fn empty_for_barrier_test(party_id: usize, eval_point: Goldilocks) -> Self {
        Self {
            party_id,
            eval_point,
            mac_alpha_share: GoldilocksExt2::ONE,
            pow7_tuples: Vec::new(),
            pow7_cursor: 0,
            beaver_triples: Vec::new(),
            beaver_cursor: 0,
            a2b_masks: Vec::new(),
            a2b_cursor: 0,
            poisoned: false,
        }
    }

    #[inline]
    pub fn is_poisoned(&self) -> bool {
        self.poisoned
    }

    /// Permanently burn the SPDZ MAC key share and wipe all remaining preprocessed material (`[P0-07]`).
    pub fn poison_and_wipe(&mut self) {
        self.poisoned = true;
        wipe_ext2(core::slice::from_mut(&mut self.mac_alpha_share));
        self.pow7_tuples.clear();
        self.pow7_cursor = 0;
        self.beaver_triples.clear();
        self.beaver_cursor = 0;
        self.a2b_masks.clear();
        self.a2b_cursor = 0;
    }

    #[inline]
    pub fn remaining_pow7(&self) -> usize {
        if self.poisoned {
            0
        } else {
            self.pow7_tuples.len().saturating_sub(self.pow7_cursor)
        }
    }

    #[inline]
    pub fn remaining_beaver(&self) -> usize {
        if self.poisoned {
            0
        } else {
            self.beaver_triples.len().saturating_sub(self.beaver_cursor)
        }
    }

    #[inline]
    pub fn remaining_a2b(&self) -> usize {
        if self.poisoned {
            0
        } else {
            self.a2b_masks.len().saturating_sub(self.a2b_cursor)
        }
    }

    /// Monotonically burn a disjoint range before exposing its material. All quorums
    /// sharing this vault use the same cursor; abandoned reservations are never reclaimed.
    pub fn reserve_pow7(
        &mut self,
        count: usize,
    ) -> Result<&[AuthenticatedPower7Share], PreprocessError> {
        let range = reserve_material(
            &mut self.pow7_cursor,
            self.pow7_tuples.len(),
            count,
            self.poisoned,
            "Poseidon2 pow7",
        )?;
        Ok(&self.pow7_tuples[range])
    }

    #[inline]
    pub fn pop_pow7(&mut self) -> Result<&AuthenticatedPower7Share, PreprocessError> {
        Ok(&self.reserve_pow7(1)?[0])
    }

    /// Monotonically burn a disjoint range before exposing its material. All quorums
    /// sharing this vault use the same cursor; abandoned reservations are never reclaimed.
    pub fn reserve_beaver(
        &mut self,
        count: usize,
    ) -> Result<&[GoldilocksBeaverShare], PreprocessError> {
        let range = reserve_material(
            &mut self.beaver_cursor,
            self.beaver_triples.len(),
            count,
            self.poisoned,
            "Goldilocks Beaver",
        )?;
        Ok(&self.beaver_triples[range])
    }

    #[inline]
    pub fn pop_beaver(&mut self) -> Result<&GoldilocksBeaverShare, PreprocessError> {
        Ok(&self.reserve_beaver(1)?[0])
    }

    /// Monotonically burn a disjoint range before exposing its material. All quorums
    /// sharing this vault use the same cursor; abandoned reservations are never reclaimed.
    pub fn reserve_a2b_masks(
        &mut self,
        count: usize,
    ) -> Result<&[CanonicalBitMask64Share], PreprocessError> {
        let range = reserve_material(
            &mut self.a2b_cursor,
            self.a2b_masks.len(),
            count,
            self.poisoned,
            "Poseidon2 A2B mask",
        )?;
        Ok(&self.a2b_masks[range])
    }

    #[inline]
    pub fn pop_a2b_mask(&mut self) -> Result<&CanonicalBitMask64Share, PreprocessError> {
        Ok(&self.reserve_a2b_masks(1)?[0])
    }
}

/// LHL-amplified (`320` random OT bits -> `64`-bit `Goldilocks` via post-OT 2-universal hash,
/// `< 2^{-129}` selective-failure advantage `[P1-01]`) + 24-byte unbiased pad (`< 2^{-192}` bias
/// `[P2-02]`) pairwise Gilboa OLE over `Goldilocks`:
/// computes $n$-party additive shares `w_i` such that $\sum_i w_i = (\sum_i u_i)(\sum_j v_j) \pmod p$
/// (`ole_pairwise_cross_sum_eq_mul`) with **zero** cleartext reconstruction and **zero** secret OT choice bits!
pub fn pairwise_gilboa_ole_goldilocks(
    ot_mesh: &mut OtMesh,
    u_per_party: &[Vec<Goldilocks>],
    v_per_party: &[Vec<Goldilocks>],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<Vec<Goldilocks>>, PreprocessError> {
    let n = ot_mesh.n;
    if n == 0 || u_per_party.len() != n || v_per_party.len() != n || party_rngs.len() != n {
        return Err(PreprocessError::InvalidThreshold { t: 1, n });
    }
    let count = u_per_party[0].len();
    for p in 0..n {
        if u_per_party[p].len() != count || v_per_party[p].len() != count {
            return Err(PreprocessError::InvalidThreshold { t: 1, n });
        }
    }
    if count == 0 {
        return Ok(vec![Vec::new(); n]);
    }

    let mut w_per_party: Vec<Vec<Goldilocks>> = (0..n)
        .map(|i| {
            (0..count)
                .map(|k| u_per_party[i][k] * v_per_party[i][k])
                .collect()
        })
        .collect();

    // 5 random `u64` words (`320` disposable bits = `64` target + `256` LHL min-entropy buffer) per item!
    const WORDS_PER_ITEM: usize = 5;
    let total_words = WORDS_PER_ITEM * count;
    let mut r_words = SecretBuffer(vec![vec![0u64; total_words]; n]);
    for i in 0..n {
        for w in 0..total_words {
            r_words[i][w] = party_rngs[i].next_u64();
        }
    }

    // `raw_sender_sh[j][i][k][s]` (held by Sender `j`) + `raw_recv_sh[j][i][k][s]` (held by Receiver `i`)
    // == `bit_s(r_words[i][5*k..5*k+5]) * v_per_party[j][k]`!
    let mut raw_sender_sh = SecretBuffer(vec![vec![vec![[Goldilocks::ZERO; 320]; count]; n]; n]);
    let mut raw_recv_sh = SecretBuffer(vec![vec![vec![[Goldilocks::ZERO; 320]; count]; n]; n]);

    for i in 0..n {
        for j in 0..n {
            if i == j {
                continue;
            }
            let (send_pads, recv_pads) =
                ot_mesh.run_correlated_ot_words(j, i, &r_words[i], party_rngs)?;
            for k in 0..count {
                let vj = v_per_party[j][k];
                for w_off in 0..WORDS_PER_ITEM {
                    let rw = black_box(r_words[i][WORDS_PER_ITEM * k + w_off]);
                    for bit in 0..64 {
                        let s_idx = 64 * w_off + bit;
                        let ot_idx = 320 * k + s_idx;
                        let (p0, p1) = &send_pads[ot_idx];
                        let pad0 = Goldilocks::from_bytes24_unbiased(&core::array::from_fn(
                            |array_index| (p0[0..24])[array_index],
                        ));
                        let pad1 = Goldilocks::from_bytes24_unbiased(&core::array::from_fn(
                            |array_index| (p1[0..24])[array_index],
                        ));
                        let m_mask = party_rngs[j].next_goldilocks();
                        raw_sender_sh[j][i][k][s_idx] = m_mask;

                        let ct0 = m_mask.const_neg() + pad0;
                        let ct1 = (vj - m_mask) + pad1;

                        let pad_c = Goldilocks::from_bytes24_unbiased(&core::array::from_fn(
                            |array_index| (recv_pads[ot_idx][0..24])[array_index],
                        ));
                        let choice = ((rw >> bit) & 1) == 1;
                        let mask64 = 0u64.wrapping_sub(black_box(choice as u64));
                        let sel_raw = ct0.to_canonical_u64()
                            ^ (mask64 & (ct0.to_canonical_u64() ^ ct1.to_canonical_u64()));
                        let sel = Goldilocks::from_u64_reduced(sel_raw);
                        raw_recv_sh[j][i][k][s_idx] = sel - pad_c;
                    }
                }
            }
        }
    }

    // Post-OT public-coin 2-universal LHL combiner `g[0..320] ∈ F_p^{320}` (`< 2^{-129}` selective-failure advantage!)
    let sid = ot_mesh.session_id;
    let lhl_coin = run_commit_and_open_coin(&sid, b"GILBOA_GL_LHL_COMBINE", &sid, party_rngs)?;
    let mut g_xof = Cshake256Xof::new(b"QSAG.GILBOA.GL.LHL_G/v1");
    g_xof.absorb(&lhl_coin);
    let mut g_weights = [Goldilocks::ZERO; 320];
    #[expect(
        clippy::needless_range_loop,
        reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows"
    )]
    for s in 0..320 {
        let mut b24 = [0u8; 24];
        g_xof.squeeze(&mut b24);
        g_weights[s] = Goldilocks::from_bytes24_unbiased(&b24);
    }

    let mut diffs = SecretBuffer(vec![vec![Goldilocks::ZERO; count]; n]);
    for i in 0..n {
        for k in 0..count {
            let mut u_comb = Goldilocks::ZERO;
            for w_off in 0..WORDS_PER_ITEM {
                let rw = black_box(r_words[i][WORDS_PER_ITEM * k + w_off]);
                for bit in 0..64 {
                    let b_mask = 0u64.wrapping_sub((rw >> bit) & 1);
                    let w_val = Goldilocks::from_u64_reduced(
                        b_mask & g_weights[64 * w_off + bit].to_canonical_u64(),
                    );
                    u_comb += w_val;
                }
            }
            diffs[i][k] = u_per_party[i][k] - u_comb;
        }
        wipe_u64s(&mut r_words[i]);
    }

    for i in 0..n {
        for j in 0..n {
            if i == j {
                continue;
            }
            for k in 0..count {
                let mut s_acc = diffs[i][k] * v_per_party[j][k];
                let mut r_acc = Goldilocks::ZERO;
                for s in 0..320 {
                    let gw = g_weights[s];
                    s_acc += gw * raw_sender_sh[j][i][k][s];
                    r_acc += gw * raw_recv_sh[j][i][k][s];
                }
                w_per_party[j][k] += s_acc;
                w_per_party[i][k] += r_acc;
                wipe_goldilocks(&mut raw_sender_sh[j][i][k]);
                wipe_goldilocks(&mut raw_recv_sh[j][i][k]);
            }
        }
    }
    Ok(w_per_party)
}

fn shamir_share_goldilocks(
    t: usize,
    eval_points: &[Goldilocks],
    secret: Goldilocks,
    rng: &mut PartyPrivateRng,
) -> Vec<Goldilocks> {
    let mut coeffs = Vec::with_capacity(t);
    coeffs.push(secret);
    for _ in 1..t {
        coeffs.push(rng.next_goldilocks());
    }
    let out = eval_points
        .iter()
        .map(|&pt| eval_poly_goldilocks(&coeffs, pt))
        .collect();
    wipe_goldilocks(&mut coeffs);
    out
}

fn shamir_share_ext2(
    t: usize,
    eval_points: &[Goldilocks],
    secret: GoldilocksExt2,
    rng: &mut PartyPrivateRng,
) -> Vec<GoldilocksExt2> {
    let mut coeffs = Vec::with_capacity(t);
    coeffs.push(secret);
    for _ in 1..t {
        coeffs.push(rng.next_ext2());
    }
    let out = eval_points
        .iter()
        .map(|&pt| eval_poly_ext2_at_base(&coeffs, pt))
        .collect();
    wipe_ext2(&mut coeffs);
    out
}

/// Commit-before-open + degree-`< t` interpolation of `GoldilocksExt2` shares across `eval_points[0..n]`.
pub fn commit_and_open_degree_ext2(
    session_id: &[u8; 32],
    phase: &'static str,
    t: usize,
    eval_points: &[Goldilocks],
    shares: &[GoldilocksExt2],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<GoldilocksExt2, PreprocessError> {
    let n = eval_points.len();
    if t == 0 || t > n || shares.len() != n || party_rngs.len() != n {
        return Err(PreprocessError::InvalidThreshold { t, n });
    }
    validate_all_eval_points_goldilocks(eval_points)?;
    let mut salts = SecretBuffer(Vec::with_capacity(n));
    let mut coms = Vec::with_capacity(n);
    for p in 0..n {
        let mut salt = party_rngs[p].next_bytes32();
        let mut pid = (p as u64).to_be_bytes();
        let mut c0_b = shares[p].c0.to_canonical_u64().to_le_bytes();
        let mut c1_b = shares[p].c1.to_canonical_u64().to_le_bytes();
        let com = cshake256_32_multi_frame(
            b"QSAG.SPDZ.EXT2.DEG.COM/v1",
            &[session_id, phase.as_bytes(), &pid, &c0_b, &c1_b, &salt],
        );
        wipe_bytes(&mut pid);
        wipe_bytes(&mut c0_b);
        wipe_bytes(&mut c1_b);
        salts.push(salt);
        wipe_bytes32(&mut salt);
        coms.push(com);
    }
    for p in 0..n {
        let mut pid = (p as u64).to_be_bytes();
        let mut c0_b = shares[p].c0.to_canonical_u64().to_le_bytes();
        let mut c1_b = shares[p].c1.to_canonical_u64().to_le_bytes();
        let exp = cshake256_32_multi_frame(
            b"QSAG.SPDZ.EXT2.DEG.COM/v1",
            &[session_id, phase.as_bytes(), &pid, &c0_b, &c1_b, &salts[p]],
        );
        wipe_bytes(&mut pid);
        wipe_bytes(&mut c0_b);
        wipe_bytes(&mut c1_b);
        wipe_bytes32(&mut salts[p]);
        if !ct_eq_bytes32(&exp, &coms[p]) {
            return Err(PreprocessError::ShareCommitMismatch { phase, party_id: p });
        }
    }
    open_and_check_degree_ext2(t, eval_points, shares, phase)
}

/// Dealerless generation of consistent degree-`< t` Shamir shares of the global `GoldilocksExt2`
/// SPDZ MAC key $\alpha = \sum_{i=0}^{n-1} \alpha^{(i)}$.
pub fn spdz_setup_alpha_goldilocks(
    session_id: &[u8; 32],
    t: usize,
    eval_points: &[Goldilocks],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<(Vec<GoldilocksExt2>, Vec<GoldilocksExt2>), PreprocessError> {
    let n = eval_points.len();
    if t == 0 || t > n || party_rngs.len() != n {
        return Err(PreprocessError::InvalidThreshold { t, n });
    }
    validate_all_eval_points_goldilocks(eval_points)?;

    let mut alpha_contribs = vec![GoldilocksExt2::ZERO; n];
    let mut alpha_shamir = vec![GoldilocksExt2::ZERO; n];
    let mut beta_shamir = SecretBuffer(vec![GoldilocksExt2::ZERO; n]);

    for i in 0..n {
        let a_i = party_rngs[i].next_ext2();
        let b_i = party_rngs[i].next_ext2();
        alpha_contribs[i] = a_i;
        let a_sh = SecretBuffer(shamir_share_ext2(t, eval_points, a_i, &mut party_rngs[i]));
        let b_sh = SecretBuffer(shamir_share_ext2(t, eval_points, b_i, &mut party_rngs[i]));
        for p in 0..n {
            alpha_shamir[p] += a_sh[p];
            beta_shamir[p] += b_sh[p];
        }
    }

    let coin = run_commit_and_open_coin(session_id, b"SPDZ_ALPHA_GL_DEG", session_id, party_rngs)?;
    let eta = GoldilocksExt2::new(
        Goldilocks::from_u128_reduced(
            u128::from_le_bytes(core::array::from_fn(|array_index| {
                (coin[0..16])[array_index]
            })) | 1,
        ),
        Goldilocks::from_u128_reduced(u128::from_le_bytes(core::array::from_fn(|array_index| {
            (coin[16..32])[array_index]
        }))),
    );
    let comb: SecretBuffer<Vec<GoldilocksExt2>> = SecretBuffer(
        (0..n)
            .map(|p| beta_shamir[p] + eta * alpha_shamir[p])
            .collect(),
    );
    let _ = commit_and_open_degree_ext2(
        session_id,
        "spdz_setup_alpha_goldilocks",
        t,
        eval_points,
        comb.as_slice(),
        party_rngs,
    )?;
    Ok((alpha_contribs, alpha_shamir))
}

/// Dealerless `Π_MAC` over `Goldilocks` Shamir shares: computes degree-`< t` `GoldilocksExt2` SPDZ
/// MAC shares `macs[party][k]` using LHL-amplified OT (full-vector 2-universal Toeplitz combiner
/// over `total_items + 4` `u64` words = `64 * total_items + 256` bits, exact $p^{-\text{total\_items}}$
/// collision probability across all $r \ne r' \in \{0, 1\}^{m\_\text{bits}}$, `< 2^{-129}` selective-failure
/// advantage; Sender `i` inputs ONLY private `alpha_contribs[i]`) AND verifies across ALL `0..n`
/// parties that `x_shares_per_party` and `macs` lie on consistent degree-`< t` polynomials with
/// $\gamma(x) = \alpha \cdot x$ (`< 2^{-127}` soundness).
#[expect(
    clippy::too_many_arguments,
    reason = "Quorum, value shares, MAC shares and private randomness are separate protocol inputs"
)]
pub fn spdz_authenticate_goldilocks_batch_ext2(
    session_id: &[u8; 32],
    t: usize,
    eval_points: &[Goldilocks],
    ot_mesh: &mut OtMesh,
    alpha_contribs: &[GoldilocksExt2],
    alpha_shamir_shares: &[GoldilocksExt2],
    x_shares_per_party: &[Vec<Goldilocks>],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<Vec<GoldilocksExt2>>, PreprocessError> {
    let n = eval_points.len();
    if t == 0
        || t > n
        || ot_mesh.n != n
        || alpha_contribs.len() != n
        || alpha_shamir_shares.len() != n
        || x_shares_per_party.len() != n
        || party_rngs.len() != n
    {
        return Err(PreprocessError::InvalidThreshold { t, n });
    }
    validate_all_eval_points_goldilocks(eval_points)?;
    let count = x_shares_per_party[0].len();
    for x_shares_per_party_p_item in x_shares_per_party[..n].iter().skip(1) {
        if (*x_shares_per_party_p_item).len() != count {
            return Err(PreprocessError::InvalidThreshold { t, n });
        }
    }
    if count == 0 {
        return Ok(vec![Vec::new(); n]);
    }

    let lambdas_t = lagrange_weights_zero_goldilocks(&eval_points[..t])
        .ok_or(PreprocessError::DuplicateOrZeroEvalPoint)?;

    // Sample 3 disposable degree-`< t` random Goldilocks wires:
    // - `r_deg`: one-time pad for full `0..n` degree check of `x_shares_per_party`
    // - `r_chk0, r_chk1`: `GoldilocksExt2` one-time pad for the `Π_MAC` linear check `Z`!
    let mut r_extra_sh = SecretBuffer(vec![[Goldilocks::ZERO; 3]; n]);
    for party_rngs_i_item in party_rngs[..n].iter_mut() {
        for slot in 0..3 {
            let ri = (*party_rngs_i_item).next_goldilocks();
            let s_ri = SecretBuffer(shamir_share_goldilocks(
                t,
                eval_points,
                ri,
                &mut *party_rngs_i_item,
            ));
            for p in 0..n {
                r_extra_sh[p][slot] += s_ri[p];
            }
        }
    }

    let total_items = count + 3;
    // Full-vector 2-universal Toeplitz LHL combiner over `total_items` `u64` words + `4` tail `u64` words (`256` bits)!
    let m_words = total_items + 4;
    let m_bits = 64 * m_words;

    let mut u_target = SecretBuffer(vec![vec![Goldilocks::ZERO; total_items]; t]);
    let mut r_words = SecretBuffer(vec![vec![0u64; m_words]; t]);
    for j in 0..t {
        let lj = lambdas_t[j];
        for k in 0..count {
            u_target[j][k] = lj * x_shares_per_party[j][k];
        }
        for slot in 0..3 {
            u_target[j][count + slot] = lj * r_extra_sh[j][slot];
        }
        for w in 0..m_words {
            r_words[j][w] = party_rngs[j].next_u64();
        }
    }

    // Sender `i in 0..n` inputs ONLY private `alpha_contribs[i]`; Receiver `j in 0..t` inputs random `r_words[j]`
    let mut raw_keys = SecretBuffer(vec![vec![vec![GoldilocksExt2::ZERO; m_bits]; t]; n]);
    let mut raw_macs = SecretBuffer(vec![vec![vec![GoldilocksExt2::ZERO; m_bits]; t]; n]);

    for i in 0..n {
        if i < t {
            let ai = alpha_contribs[i];
            for s in 0..m_bits {
                let bit_val = (r_words[i][s / 64] >> (s % 64)) & 1;
                let mask = party_rngs[i].next_ext2();
                raw_keys[i][i][s] = mask;
                raw_macs[i][i][s] = ai.mul_base(Goldilocks::from_u64_reduced(bit_val)) - mask;
            }
        }
        for j in 0..t {
            if i == j {
                continue;
            }
            let ai = alpha_contribs[i];
            let (send_pads, recv_pads) =
                ot_mesh.run_correlated_ot_words(i, j, &r_words[j], party_rngs)?;
            #[inline]
            fn expand_ot_pad48_to_ext2(pad: &[u8; 48]) -> GoldilocksExt2 {
                GoldilocksExt2::new(
                    Goldilocks::from_bytes24_unbiased(&core::array::from_fn(|array_index| {
                        (pad[0..24])[array_index]
                    })),
                    Goldilocks::from_bytes24_unbiased(&core::array::from_fn(|array_index| {
                        (pad[24..48])[array_index]
                    })),
                )
            }

            for s in 0..m_bits {
                let (p0, p1) = &send_pads[s];
                let pad0 = expand_ot_pad48_to_ext2(p0);
                let pad1 = expand_ot_pad48_to_ext2(p1);

                let mask = party_rngs[i].next_ext2();
                raw_keys[i][j][s] = mask;
                let ct0 = pad0 - mask;
                let ct1 = (ai - mask) + pad1;

                let pad_c = expand_ot_pad48_to_ext2(&recv_pads[s]);

                let rj_w = black_box(r_words[j][s / 64]);
                let choice = ((rj_w >> (s % 64)) & 1) == 1;
                let cmask = 0u64.wrapping_sub(black_box(choice as u64));
                let sel_c0 = Goldilocks::from_u64_reduced(
                    ct0.c0.to_canonical_u64()
                        ^ (cmask & (ct0.c0.to_canonical_u64() ^ ct1.c0.to_canonical_u64())),
                );
                let sel_c1 = Goldilocks::from_u64_reduced(
                    ct0.c1.to_canonical_u64()
                        ^ (cmask & (ct0.c1.to_canonical_u64() ^ ct1.c1.to_canonical_u64())),
                );
                raw_macs[i][j][s] = GoldilocksExt2::new(sel_c0, sel_c1) - pad_c;
            }
        }
    }

    // Post-OT full-vector 2-universal Toeplitz combiner `H[idx, s] = toeplitz_all[idx + s]`
    // over ALL `idx in 0..total_items` and ALL `s in 0..m_bits`:
    // For ANY non-zero bit difference `\Delta r = r - r' \in \{-1, 0, 1\}^{m_bits} \setminus \{0\}`,
    // let `s* = max { s : \Delta r_s != 0 }`. Conditioned on `toeplitz_all[0 .. idx + s*]`,
    // `(H \cdot \Delta r)[idx]` adds `\pm toeplitz_all[idx + s*]`, which is freshly uniform in `F_p`.
    // By the chain rule across `idx = 0 .. total_items - 1`, `Pr_H[H r == H r'] == p^{-total_items}`
    // unconditionally across the entire `m_bits`-bit input vector (`0` block-diagonal blind spots).
    let lhl_coin = run_commit_and_open_coin(
        session_id,
        b"SPDZ_GL_PIMAC_LHL",
        &ot_mesh.session_id,
        party_rngs,
    )?;
    let mut h_xof = Cshake256Xof::new(b"QSAG.SPDZ.GL.LHL_H/v2");
    h_xof.absorb(&lhl_coin);

    let mut toeplitz_u64 = vec![0u64; total_items + m_bits];
    for slot in &mut toeplitz_u64 {
        let mut b24 = [0u8; 24];
        h_xof.squeeze(&mut b24);
        *slot = Goldilocks::from_bytes24_unbiased(&b24).to_canonical_u64();
    }

    let mut diff_sum = SecretBuffer(vec![Goldilocks::ZERO; total_items]);
    for j in 0..t {
        for idx in 0..total_items {
            let h_row = &toeplitz_u64[idx..idx + m_bits];
            let mut acc_u128 = 0u128;
            for w in 0..m_words {
                let rw = black_box(r_words[j][w]);
                let h_word = &h_row[64 * w..64 * (w + 1)];
                for (b, &h) in h_word.iter().enumerate() {
                    let m = 0u64.wrapping_sub((rw >> b) & 1);
                    acc_u128 += (m & h) as u128;
                }
            }
            let u_comb = Goldilocks::reduce128(acc_u128);
            diff_sum[idx] += u_target[j][idx] - u_comb;
        }
        wipe_goldilocks(&mut u_target[j]);
        wipe_u64s(&mut r_words[j]);
    }
    drop((u_target, r_words));

    // Pre-sum additive OT shares across `j in 0..t` and `i in 0..n` BEFORE `toeplitz_u64` multiplies!
    let mut sum_raw_c0 = SecretBuffer(vec![vec![0u64; m_bits]; n]);
    let mut sum_raw_c1 = SecretBuffer(vec![vec![0u64; m_bits]; n]);
    for p in 0..n {
        for s in 0..m_bits {
            let mut acc = GoldilocksExt2::ZERO;
            for j in 0..t {
                acc += raw_keys[p][j][s];
            }
            if p < t {
                for raw_macs_i_item in raw_macs[..n].iter() {
                    acc += (*raw_macs_i_item)[p][s];
                }
            }
            sum_raw_c0[p][s] = acc.c0.to_canonical_u64();
            sum_raw_c1[p][s] = acc.c1.to_canonical_u64();
        }
    }
    drop((raw_keys, raw_macs));

    // `2^64 == 2^32 - 1 (mod p)` => `2^128 == (2^32 - 1)^2 (mod p)`.
    let two_pow_64_mod_p = Goldilocks::from_u64_reduced((1u64 << 32) - 1);
    let two_pow_128_mod_p = two_pow_64_mod_p * two_pow_64_mod_p;

    let compute_party_taus = |p: usize| -> Vec<GoldilocksExt2> {
        let ap = alpha_contribs[p];
        let sr0 = &sum_raw_c0[p];
        let sr1 = &sum_raw_c1[p];
        let mut taus_p = vec![GoldilocksExt2::ZERO; total_items];
        for idx in 0..total_items {
            let h_row = &toeplitz_u64[idx..idx + m_bits];
            let mut acc0_lo = 0u128;
            let mut acc0_hi = 0u64;
            let mut acc1_lo = 0u128;
            let mut acc1_hi = 0u64;
            for s in 0..m_bits {
                let h = h_row[s] as u128;
                let (n0, ov0) = acc0_lo.overflowing_add((sr0[s] as u128) * h);
                acc0_lo = n0;
                acc0_hi += ov0 as u64;
                let (n1, ov1) = acc1_lo.overflowing_add((sr1[s] as u128) * h);
                acc1_lo = n1;
                acc1_hi += ov1 as u64;
            }
            let comb_c0 = Goldilocks::reduce128(acc0_lo)
                + Goldilocks::from_u64_reduced(acc0_hi) * two_pow_128_mod_p;
            let comb_c1 = Goldilocks::reduce128(acc1_lo)
                + Goldilocks::from_u64_reduced(acc1_hi) * two_pow_128_mod_p;
            taus_p[idx] = ap.mul_base(diff_sum[idx]) + GoldilocksExt2::new(comb_c0, comb_c1);
        }
        taus_p
    };

    #[cfg(feature = "std")]
    let taus_per_party: SecretBuffer<Vec<Vec<GoldilocksExt2>>> = if total_items >= 64 {
        SecretBuffer(std::thread::scope(|s| {
            let handles: Vec<_> = (0..n)
                .map(|p| s.spawn(move || compute_party_taus(p)))
                .collect();
            handles
                .into_iter()
                .map(|h| h.join().unwrap_or_default())
                .collect()
        }))
    } else {
        SecretBuffer((0..n).map(compute_party_taus).collect())
    };
    #[cfg(not(feature = "std"))]
    let taus_per_party: SecretBuffer<Vec<Vec<GoldilocksExt2>>> =
        SecretBuffer((0..n).map(compute_party_taus).collect());

    drop((sum_raw_c0, sum_raw_c1, diff_sum));

    let mut all_macs = SecretBuffer(vec![vec![GoldilocksExt2::ZERO; total_items]; n]);
    for p in 0..n {
        for idx in 0..total_items {
            let sh = SecretBuffer(shamir_share_ext2(
                t,
                eval_points,
                taus_per_party[p][idx],
                &mut party_rngs[p],
            ));
            for q in 0..n {
                all_macs[q][idx] += sh[q];
            }
        }
    }
    drop(taus_per_party);

    // Batch `Π_MAC` consistency + full `0..n` degree check:
    let chk_coin =
        run_commit_and_open_coin(session_id, b"SPDZ_GL_PIMAC_CHK", &lhl_coin, party_rngs)?;
    let mut chk_xof = Cshake256Xof::new(b"QSAG.SPDZ.GL.PIMAC_W/v1");
    chk_xof.absorb(&chk_coin);

    // 1) Degree `< t` check on `x_shares_per_party` across `0..n` masked by `r_extra_sh[..][0]`
    let mut deg_sh: SecretBuffer<Vec<Goldilocks>> =
        SecretBuffer((0..n).map(|p| r_extra_sh[p][0]).collect());
    #[expect(
        clippy::needless_range_loop,
        reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows"
    )]
    for k in 0..count {
        let mut b24 = [0u8; 24];
        chk_xof.squeeze(&mut b24);
        let w = Goldilocks::from_bytes24_unbiased(&b24);
        for p in 0..n {
            deg_sh[p] += w * x_shares_per_party[p][k];
        }
    }
    let _ =
        open_and_check_degree_goldilocks(t, eval_points, deg_sh.as_slice(), "spdz_gl_words_deg")?;
    drop(deg_sh);

    // 2) Fold all wires (`0..count` + `r_extra_sh[0]`) with random `GoldilocksExt2` weights, masked
    //    over `F_{p^2}` by `R_pad = (r_extra_sh[1], r_extra_sh[2])` (`0` bits leaked!)
    let mut z_sh = SecretBuffer(vec![GoldilocksExt2::ZERO; n]);
    let mut z_mac = SecretBuffer(vec![GoldilocksExt2::ZERO; n]);
    let ext_u = GoldilocksExt2::new(Goldilocks::ZERO, Goldilocks::ONE);
    for p in 0..n {
        z_sh[p] = GoldilocksExt2::new(r_extra_sh[p][1], r_extra_sh[p][2]);
        z_mac[p] = all_macs[p][count + 1] + ext_u * all_macs[p][count + 2];
    }
    {
        let mut b48 = [0u8; 48];
        chk_xof.squeeze(&mut b48);
        let chi0 = GoldilocksExt2::new(
            Goldilocks::from_bytes24_unbiased(&core::array::from_fn(|array_index| {
                (b48[0..24])[array_index]
            })),
            Goldilocks::from_bytes24_unbiased(&core::array::from_fn(|array_index| {
                (b48[24..48])[array_index]
            })),
        );
        for p in 0..n {
            z_sh[p] += chi0.mul_base(r_extra_sh[p][0]);
            z_mac[p] += chi0 * all_macs[p][count];
            wipe_goldilocks(&mut r_extra_sh[p]);
        }
    }
    drop(r_extra_sh);
    for k in 0..count {
        let mut b48 = [0u8; 48];
        chk_xof.squeeze(&mut b48);
        let chi = GoldilocksExt2::new(
            Goldilocks::from_bytes24_unbiased(&core::array::from_fn(|array_index| {
                (b48[0..24])[array_index]
            })),
            Goldilocks::from_bytes24_unbiased(&core::array::from_fn(|array_index| {
                (b48[24..48])[array_index]
            })),
        );
        for p in 0..n {
            z_sh[p] += chi.mul_base(x_shares_per_party[p][k]);
            z_mac[p] += chi * all_macs[p][k];
        }
    }

    let z_open = commit_and_open_degree_ext2(
        session_id,
        "spdz_gl_pimac_z",
        t,
        eval_points,
        z_sh.as_slice(),
        party_rngs,
    )?;
    drop(z_sh);

    let d_sh: SecretBuffer<Vec<GoldilocksExt2>> = SecretBuffer(
        (0..n)
            .map(|p| z_mac[p] - z_open * alpha_shamir_shares[p])
            .collect(),
    );
    drop(z_mac);
    let d_zero = commit_and_open_degree_ext2(
        session_id,
        "spdz_gl_pimac_d",
        t,
        eval_points,
        d_sh.as_slice(),
        party_rngs,
    )?;
    drop(d_sh);
    if !d_zero.ct_eq(GoldilocksExt2::ZERO) {
        return Err(PreprocessError::MacCheckFailed {
            phase: "spdz_gl_pimac",
            accused_party: None,
        });
    }

    let mut out_macs = Vec::with_capacity(n);
    for p in 0..n {
        let mut v = Vec::with_capacity(count);
        v.extend_from_slice(&all_macs[p][..count]);
        out_macs.push(v);
    }
    Ok(out_macs)
}

/// Batched dishonest-majority commit-before-open + SPDZ `GoldilocksExt2` `MacCheck` over any quorum.
#[expect(
    clippy::too_many_arguments,
    reason = "Quorum, value shares, MAC shares and private randomness are separate protocol inputs"
)]
pub fn commit_and_open_spdz_goldilocks_batch_quorum(
    session_id: &[u8; 32],
    phase: &'static str,
    t: usize,
    quorum_eval_points: &[Goldilocks],
    batch_shares: &[Vec<Goldilocks>],
    batch_macs: &[Vec<GoldilocksExt2>],
    alpha_shares: &[GoldilocksExt2],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<Goldilocks>, PreprocessError> {
    let m = quorum_eval_points.len();
    if t == 0
        || m < t
        || batch_shares.len() != m
        || batch_macs.len() != m
        || alpha_shares.len() != m
        || party_rngs.len() != m
    {
        return Err(PreprocessError::InvalidThreshold { t, n: m });
    }
    let batch_len = batch_shares[0].len();
    for p in 0..m {
        if batch_shares[p].len() != batch_len || batch_macs[p].len() != batch_len {
            return Err(PreprocessError::InvalidThreshold { t, n: m });
        }
    }
    if batch_len == 0 {
        return Ok(Vec::new());
    }
    validate_all_eval_points_goldilocks(quorum_eval_points)?;

    let mut salts = SecretBuffer(Vec::with_capacity(m));
    let mut coms = Vec::with_capacity(m);
    for p in 0..m {
        let mut salt = party_rngs[p].next_bytes32();
        let mut xof = Cshake256Xof::new(b"QSAG.SPDZ.GL.BATCH.OPEN.COM/v1");
        xof.absorb(session_id);
        xof.absorb(&(phase.len() as u64).to_be_bytes());
        xof.absorb(phase.as_bytes());
        xof.absorb(&(p as u64).to_be_bytes());
        xof.absorb(&salt);
        #[expect(
            clippy::needless_range_loop,
            reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows"
        )]
        for w in 0..batch_len {
            let mut b8 = batch_shares[p][w].to_canonical_u64().to_le_bytes();
            xof.absorb(&b8);
            wipe_bytes(&mut b8);
        }
        let mut com = [0u8; 32];
        xof.squeeze(&mut com);
        salts.push(salt);
        wipe_bytes32(&mut salt);
        coms.push(com);
    }
    for p in 0..m {
        let mut xof = Cshake256Xof::new(b"QSAG.SPDZ.GL.BATCH.OPEN.COM/v1");
        xof.absorb(session_id);
        xof.absorb(&(phase.len() as u64).to_be_bytes());
        xof.absorb(phase.as_bytes());
        xof.absorb(&(p as u64).to_be_bytes());
        xof.absorb(&salts[p]);
        #[expect(
            clippy::needless_range_loop,
            reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows"
        )]
        for w in 0..batch_len {
            let mut b8 = batch_shares[p][w].to_canonical_u64().to_le_bytes();
            xof.absorb(&b8);
            wipe_bytes(&mut b8);
        }
        let mut exp = [0u8; 32];
        xof.squeeze(&mut exp);
        wipe_bytes32(&mut salts[p]);
        if !ct_eq_bytes32(&exp, &coms[p]) {
            return Err(PreprocessError::ShareCommitMismatch { phase, party_id: p });
        }
    }
    drop(salts);

    let mut opened = Vec::with_capacity(batch_len);
    let mut dig_xof = Cshake256Xof::new(b"QSAG.SPDZ.GL.BATCH.DIG/v1");
    let mut single_sh = SecretBuffer(vec![Goldilocks::ZERO; m]);
    let opening_tables = GoldilocksOpeningTables::new(t, quorum_eval_points)?;
    #[expect(
        clippy::needless_range_loop,
        reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows"
    )]
    for w in 0..batch_len {
        for p in 0..m {
            single_sh[p] = batch_shares[p][w];
        }
        let sec = opening_tables.open(single_sh.as_slice(), phase)?;
        dig_xof.absorb(&sec.to_canonical_u64().to_le_bytes());
        opened.push(sec);
    }
    drop(single_sh);
    let mut open_digest = [0u8; 32];
    dig_xof.squeeze(&mut open_digest);

    let fold_coin =
        run_commit_and_open_coin(session_id, phase.as_bytes(), &open_digest, party_rngs)?;
    let mut chi_xof = Cshake256Xof::new(b"QSAG.SPDZ.GL.BATCH.CHIS/v1");
    chi_xof.absorb(&fold_coin);

    let mut x_folded = GoldilocksExt2::ZERO;
    let mut m_folded = SecretBuffer(vec![GoldilocksExt2::ZERO; t]);
    for w in 0..batch_len {
        let mut b48 = [0u8; 48];
        chi_xof.squeeze(&mut b48);
        let chi = GoldilocksExt2::new(
            Goldilocks::from_bytes24_unbiased(&core::array::from_fn(|array_index| {
                (b48[0..24])[array_index]
            })),
            Goldilocks::from_bytes24_unbiased(&core::array::from_fn(|array_index| {
                (b48[24..48])[array_index]
            })),
        );
        x_folded += chi.mul_base(opened[w]);
        for q in 0..t {
            m_folded[q] += chi * batch_macs[q][w];
        }
    }

    let lambdas_0 = lagrange_weights_zero_goldilocks(&quorum_eval_points[..t])
        .ok_or(PreprocessError::DuplicateOrZeroEvalPoint)?;
    let mut z_masks = SecretBuffer(vec![GoldilocksExt2::ZERO; t]);
    if t > 1 {
        for party_rngs_r_item in party_rngs[..t].iter_mut() {
            let mut acc = GoldilocksExt2::ZERO;
            for z_masks_q_item in z_masks[..(t - 1)].iter_mut() {
                let u = (*party_rngs_r_item).next_ext2();
                *z_masks_q_item += u;
                acc += u;
            }
            z_masks[t - 1] -= acc;
        }
    }

    let mut sigmas = SecretBuffer(Vec::with_capacity(t));
    let mut sig_salts = SecretBuffer(Vec::with_capacity(t));
    let mut sig_coms = Vec::with_capacity(t);
    for q in 0..t {
        let diff_q = m_folded[q] - (alpha_shares[q] * x_folded);
        let sig_q = diff_q.mul_base(lambdas_0[q]) + z_masks[q];
        let mut salt = party_rngs[q].next_bytes32();
        let mut q_be = (q as u64).to_be_bytes();
        let mut c0_b = sig_q.c0.to_canonical_u64().to_le_bytes();
        let mut c1_b = sig_q.c1.to_canonical_u64().to_le_bytes();
        let com = cshake256_32_multi_frame(
            b"QSAG.SPDZ.GL.BATCH.MAC.COM/v1",
            &[session_id, phase.as_bytes(), &q_be, &c0_b, &c1_b, &salt],
        );
        wipe_bytes(&mut q_be);
        wipe_bytes(&mut c0_b);
        wipe_bytes(&mut c1_b);
        sigmas.push(sig_q);
        sig_salts.push(salt);
        wipe_bytes32(&mut salt);
        sig_coms.push(com);
    }
    drop((z_masks, m_folded));

    let mut sum = GoldilocksExt2::ZERO;
    for q in 0..t {
        let mut q_be = (q as u64).to_be_bytes();
        let mut c0_b = sigmas[q].c0.to_canonical_u64().to_le_bytes();
        let mut c1_b = sigmas[q].c1.to_canonical_u64().to_le_bytes();
        let exp = cshake256_32_multi_frame(
            b"QSAG.SPDZ.GL.BATCH.MAC.COM/v1",
            &[
                session_id,
                phase.as_bytes(),
                &q_be,
                &c0_b,
                &c1_b,
                &sig_salts[q],
            ],
        );
        wipe_bytes(&mut q_be);
        wipe_bytes(&mut c0_b);
        wipe_bytes(&mut c1_b);
        wipe_bytes32(&mut sig_salts[q]);
        if !ct_eq_bytes32(&exp, &sig_coms[q]) {
            return Err(PreprocessError::ShareCommitMismatch { phase, party_id: q });
        }
        sum += sigmas[q];
    }
    drop((sigmas, sig_salts));
    if !sum.ct_eq(GoldilocksExt2::ZERO) {
        return Err(PreprocessError::MacCheckFailed {
            phase,
            accused_party: None,
        });
    }
    Ok(opened)
}

/// Evaluate 1 batch of parallel SPDZ-authenticated Shamir Beaver multiplications `[x_k * y_k]`,
/// opening `(delta_k, eps_k)` via `commit_and_open_spdz_goldilocks_batch_quorum` AND propagating
/// exact `GoldilocksExt2` SPDZ MAC shares `(out_shares, out_macs)`!
#[allow(clippy::too_many_arguments)]
fn eval_spdz_shamir_beaver_batch_goldilocks(
    session_id: &[u8; 32],
    t: usize,
    eval_points: &[Goldilocks],
    alpha_shamir: &[GoldilocksExt2],
    xs: &[Vec<Goldilocks>],
    xs_mac: &[Vec<GoldilocksExt2>],
    ys: &[Vec<Goldilocks>],
    ys_mac: &[Vec<GoldilocksExt2>],
    ta: &[Vec<Goldilocks>],
    ta_mac: &[Vec<GoldilocksExt2>],
    tb: &[Vec<Goldilocks>],
    tb_mac: &[Vec<GoldilocksExt2>],
    tc: &[Vec<Goldilocks>],
    tc_mac: &[Vec<GoldilocksExt2>],
    phase: &'static str,
    party_rngs: &mut [PartyPrivateRng],
) -> Result<(PartyValues<Goldilocks>, PartyValues<GoldilocksExt2>), PreprocessError> {
    let n = eval_points.len();
    let count = xs[0].len();
    if count == 0 {
        return Ok((vec![Vec::new(); n], vec![Vec::new(); n]));
    }
    let mut de_sh = vec![Vec::with_capacity(2 * count); n];
    let mut de_mac = vec![Vec::with_capacity(2 * count); n];
    for p in 0..n {
        for k in 0..count {
            de_sh[p].push(xs[p][k] - ta[p][k]);
            de_mac[p].push(xs_mac[p][k] - ta_mac[p][k]);
            de_sh[p].push(ys[p][k] - tb[p][k]);
            de_mac[p].push(ys_mac[p][k] - tb_mac[p][k]);
        }
    }
    let opened = commit_and_open_spdz_goldilocks_batch_quorum(
        session_id,
        phase,
        t,
        eval_points,
        &de_sh,
        &de_mac,
        alpha_shamir,
        party_rngs,
    )?;

    let mut out = vec![vec![Goldilocks::ZERO; count]; n];
    let mut out_mac = vec![vec![GoldilocksExt2::ZERO; count]; n];
    for k in 0..count {
        let delta = opened[2 * k];
        let eps = opened[2 * k + 1];
        let de = delta * eps;
        for p in 0..n {
            out[p][k] = tc[p][k] + delta * tb[p][k] + eps * ta[p][k] + de;
            out_mac[p][k] = tc_mac[p][k]
                + tb_mac[p][k].mul_base(delta)
                + ta_mac[p][k].mul_base(eps)
                + alpha_shamir[p].mul_base(de);
        }
    }
    Ok((out, out_mac))
}

/// Generate a pool of SPDZ-MAC-authenticated `Goldilocks` Beaver triples verified via
/// SPDZ-MAC-authenticated `GoldilocksExt2` companion sacrifice (`< 2^{-127}` soundness, `0`
/// unauthenticated openings even under dishonest majority!).
#[expect(
    clippy::too_many_arguments,
    reason = "Quorum, value shares, MAC shares and private randomness are separate protocol inputs"
)]
fn generate_verified_spdz_beaver_pool_goldilocks<F>(
    session_id: &[u8; 32],
    t: usize,
    eval_points: &[Goldilocks],
    ot_mesh: &mut OtMesh,
    alpha_contribs: &[GoldilocksExt2],
    alpha_shamir: &[GoldilocksExt2],
    count: usize,
    party_rngs: &mut [PartyPrivateRng],
    fault_hook: &mut F,
) -> Result<GoldilocksBeaverMaterial, PreprocessError>
where
    F: FnMut(usize, &mut [Goldilocks]),
{
    let n = eval_points.len();
    if count == 0 {
        return Ok((
            vec![Vec::new(); n],
            vec![Vec::new(); n],
            vec![Vec::new(); n],
            vec![Vec::new(); n],
            vec![Vec::new(); n],
            vec![Vec::new(); n],
        ));
    }

    let ole_pairs = 3 * count;
    let mut u_vec = vec![vec![Goldilocks::ZERO; ole_pairs]; n];
    let mut v_vec = vec![vec![Goldilocks::ZERO; ole_pairs]; n];
    for i in 0..n {
        for k in 0..count {
            let ai = party_rngs[i].next_goldilocks();
            let bi = party_rngs[i].next_goldilocks();
            let at0 = party_rngs[i].next_goldilocks();
            let at1 = party_rngs[i].next_goldilocks();
            u_vec[i][3 * k] = ai;
            v_vec[i][3 * k] = bi;
            u_vec[i][3 * k + 1] = at0;
            v_vec[i][3 * k + 1] = bi;
            u_vec[i][3 * k + 2] = at1;
            v_vec[i][3 * k + 2] = bi;
        }
    }
    let mut w_vec = pairwise_gilboa_ole_goldilocks(ot_mesh, &u_vec, &v_vec, party_rngs)?;

    let mut a_sh = vec![vec![Goldilocks::ZERO; count]; n];
    let mut b_sh = vec![vec![Goldilocks::ZERO; count]; n];
    let mut c_sh = vec![vec![Goldilocks::ZERO; count]; n];
    let mut at0_sh = vec![vec![Goldilocks::ZERO; count]; n];
    let mut at1_sh = vec![vec![Goldilocks::ZERO; count]; n];
    let mut ct0_sh = vec![vec![Goldilocks::ZERO; count]; n];
    let mut ct1_sh = vec![vec![Goldilocks::ZERO; count]; n];

    for i in 0..n {
        for k in 0..count {
            let sa = shamir_share_goldilocks(t, eval_points, u_vec[i][3 * k], &mut party_rngs[i]);
            let sb = shamir_share_goldilocks(t, eval_points, v_vec[i][3 * k], &mut party_rngs[i]);
            let sc = shamir_share_goldilocks(t, eval_points, w_vec[i][3 * k], &mut party_rngs[i]);
            let sat0 =
                shamir_share_goldilocks(t, eval_points, u_vec[i][3 * k + 1], &mut party_rngs[i]);
            let sat1 =
                shamir_share_goldilocks(t, eval_points, u_vec[i][3 * k + 2], &mut party_rngs[i]);
            let sct0 =
                shamir_share_goldilocks(t, eval_points, w_vec[i][3 * k + 1], &mut party_rngs[i]);
            let sct1 =
                shamir_share_goldilocks(t, eval_points, w_vec[i][3 * k + 2], &mut party_rngs[i]);
            for p in 0..n {
                a_sh[p][k] += sa[p];
                b_sh[p][k] += sb[p];
                c_sh[p][k] += sc[p];
                at0_sh[p][k] += sat0[p];
                at1_sh[p][k] += sat1[p];
                ct0_sh[p][k] += sct0[p];
                ct1_sh[p][k] += sct1[p];
            }
        }
        wipe_goldilocks(&mut u_vec[i]);
        wipe_goldilocks(&mut v_vec[i]);
        wipe_goldilocks(&mut w_vec[i]);
    }

    for (p, c_sh_p_item) in c_sh[..n].iter_mut().enumerate() {
        fault_hook(p, &mut *c_sh_p_item);
    }

    // Authenticate all `7 * count` wires under the global SPDZ MAC BEFORE sacrifice!
    let packed: Vec<Vec<Goldilocks>> = (0..n)
        .map(|p| {
            let mut v = Vec::with_capacity(7 * count);
            v.extend_from_slice(&a_sh[p]);
            v.extend_from_slice(&b_sh[p]);
            v.extend_from_slice(&c_sh[p]);
            v.extend_from_slice(&at0_sh[p]);
            v.extend_from_slice(&at1_sh[p]);
            v.extend_from_slice(&ct0_sh[p]);
            v.extend_from_slice(&ct1_sh[p]);
            v
        })
        .collect();
    let all_macs = spdz_authenticate_goldilocks_batch_ext2(
        session_id,
        t,
        eval_points,
        ot_mesh,
        alpha_contribs,
        alpha_shamir,
        &packed,
        party_rngs,
    )?;

    let mut a_mac = vec![vec![GoldilocksExt2::ZERO; count]; n];
    let mut b_mac = vec![vec![GoldilocksExt2::ZERO; count]; n];
    let mut c_mac = vec![vec![GoldilocksExt2::ZERO; count]; n];
    let mut at0_mac = vec![vec![GoldilocksExt2::ZERO; count]; n];
    let mut at1_mac = vec![vec![GoldilocksExt2::ZERO; count]; n];
    let mut ct0_mac = vec![vec![GoldilocksExt2::ZERO; count]; n];
    let mut ct1_mac = vec![vec![GoldilocksExt2::ZERO; count]; n];
    for p in 0..n {
        a_mac[p].copy_from_slice(&all_macs[p][0..count]);
        b_mac[p].copy_from_slice(&all_macs[p][count..2 * count]);
        c_mac[p].copy_from_slice(&all_macs[p][2 * count..3 * count]);
        at0_mac[p].copy_from_slice(&all_macs[p][3 * count..4 * count]);
        at1_mac[p].copy_from_slice(&all_macs[p][4 * count..5 * count]);
        ct0_mac[p].copy_from_slice(&all_macs[p][5 * count..6 * count]);
        ct1_mac[p].copy_from_slice(&all_macs[p][6 * count..7 * count]);
    }

    // SPDZ-MAC-authenticated `GoldilocksExt2` companion sacrifice (`< 2^{-127}`, `0` unauthenticated openings!)
    let coin = run_commit_and_open_coin(session_id, b"PI_POW7_SACRIFICE", session_id, party_rngs)?;
    let rho = GoldilocksExt2::new(
        Goldilocks::from_bytes24_unbiased(&core::array::from_fn(|array_index| {
            (coin[0..24])[array_index]
        })),
        Goldilocks::from_u128_reduced(
            u128::from_le_bytes(core::array::from_fn(|array_index| {
                (coin[16..32])[array_index]
            })) | 1,
        ),
    );

    let mut u_coords_sh = vec![Vec::with_capacity(2 * count); n];
    let mut u_coords_mac = vec![Vec::with_capacity(2 * count); n];
    for p in 0..n {
        for k in 0..count {
            // `u = rho * a_k - (at0_k + u * at1_k)`
            u_coords_sh[p].push(rho.c0 * a_sh[p][k] - at0_sh[p][k]);
            u_coords_mac[p].push(a_mac[p][k].mul_base(rho.c0) - at0_mac[p][k]);
            u_coords_sh[p].push(rho.c1 * a_sh[p][k] - at1_sh[p][k]);
            u_coords_mac[p].push(a_mac[p][k].mul_base(rho.c1) - at1_mac[p][k]);
        }
    }
    let u_opened = commit_and_open_spdz_goldilocks_batch_quorum(
        session_id,
        "pi_pow7_sac_u",
        t,
        eval_points,
        &u_coords_sh,
        &u_coords_mac,
        alpha_shamir,
        party_rngs,
    )?;

    let mut res_coords_sh = vec![Vec::with_capacity(2 * count); n];
    let mut res_coords_mac = vec![Vec::with_capacity(2 * count); n];
    for p in 0..n {
        for k in 0..count {
            let u_op = GoldilocksExt2::new(u_opened[2 * k], u_opened[2 * k + 1]);
            res_coords_sh[p].push((rho.c0 * c_sh[p][k] - ct0_sh[p][k]) - u_op.c0 * b_sh[p][k]);
            res_coords_mac[p].push(
                (c_mac[p][k].mul_base(rho.c0) - ct0_mac[p][k]) - b_mac[p][k].mul_base(u_op.c0),
            );
            res_coords_sh[p].push((rho.c1 * c_sh[p][k] - ct1_sh[p][k]) - u_op.c1 * b_sh[p][k]);
            res_coords_mac[p].push(
                (c_mac[p][k].mul_base(rho.c1) - ct1_mac[p][k]) - b_mac[p][k].mul_base(u_op.c1),
            );
        }
        wipe_goldilocks(&mut at0_sh[p]);
        wipe_goldilocks(&mut at1_sh[p]);
        wipe_goldilocks(&mut ct0_sh[p]);
        wipe_goldilocks(&mut ct1_sh[p]);
        wipe_ext2(&mut at0_mac[p]);
        wipe_ext2(&mut at1_mac[p]);
        wipe_ext2(&mut ct0_mac[p]);
        wipe_ext2(&mut ct1_mac[p]);
    }
    let res_opened = commit_and_open_spdz_goldilocks_batch_quorum(
        session_id,
        "pi_pow7_sac_res",
        t,
        eval_points,
        &res_coords_sh,
        &res_coords_mac,
        alpha_shamir,
        party_rngs,
    )?;
    for &rv in &res_opened {
        if rv != Goldilocks::ZERO {
            return Err(PreprocessError::SacrificeResidualNonZero { phase: "pi_pow7" });
        }
    }

    Ok((a_sh, b_sh, c_sh, a_mac, b_mac, c_mac))
}

/// Run the **100% dealerless `Π_pow7` + Canonical `< p` A2B** offline preprocessing protocol:
/// - Dealerless `GoldilocksExt2` Shamir SPDZ MAC setup (`spdz_setup_alpha_goldilocks`);
/// - LHL-amplified Gilboa OLE (`< 2^{-129}` selective-failure immunity, `< 2^{-192}` unbiased pads);
/// - SPDZ-MAC-authenticated `GoldilocksExt2` companion sacrifice (`< 2^{-127}` soundness, `0`
///   unauthenticated openings even under dishonest majority!);
/// - 3-round SPDZ-MAC-propagating Beaver power-tree (`evalPow7BeaverTree`) producing all 7
///   authenticated powers `r_pows[0..7]` + `r_macs[0..7]`;
/// - Exact `while` loop (`[P2-03]`) producing `num_a2b_masks` canonical `< p` 64-bit A2B bit-masks
///   verified via $b_k^2 - b_k = 0$ and `is_ge_p == 0` under SPDZ `MacCheck`.
#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the public preprocessing API used by other protocol modules"
)]
pub fn run_dealerless_pi_pow7(
    session_id: [u8; 32],
    t: usize,
    eval_points: &[Goldilocks],
    num_pow7: usize,
    num_extra_beaver: usize,
    num_a2b_masks: usize,
    ot_mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<PreprocessedPoseidonPartyVault>, PreprocessError> {
    run_dealerless_pi_pow7_with_fault(
        session_id,
        t,
        eval_points,
        num_pow7,
        num_extra_beaver,
        num_a2b_masks,
        ot_mesh,
        party_rngs,
        |_, _| {},
    )
}

/// Fault-injectable entry point for adversarial unit tests of `Π_pow7`.
#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the public preprocessing API used by other protocol modules"
)]
pub fn run_dealerless_pi_pow7_with_fault<F>(
    session_id: [u8; 32],
    t: usize,
    eval_points: &[Goldilocks],
    num_pow7: usize,
    num_extra_beaver: usize,
    num_a2b_masks: usize,
    ot_mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
    fault_hook: F,
) -> Result<Vec<PreprocessedPoseidonPartyVault>, PreprocessError>
where
    F: FnMut(usize, &mut [Goldilocks]),
{
    let n = eval_points.len();
    if t == 0 || t > n || party_rngs.len() != n || ot_mesh.n != n {
        return Err(PreprocessError::InvalidThreshold { t, n });
    }
    validate_all_eval_points_goldilocks(eval_points)?;

    let (mut alpha_contribs, mut alpha_shamir) =
        spdz_setup_alpha_goldilocks(&session_id, t, eval_points, party_rngs)?;
    let res = run_dealerless_pi_pow7_with_alpha_and_fault(
        session_id,
        t,
        eval_points,
        num_pow7,
        num_extra_beaver,
        num_a2b_masks,
        &alpha_contribs,
        &alpha_shamir,
        ot_mesh,
        party_rngs,
        fault_hook,
    );
    wipe_ext2(&mut alpha_contribs);
    wipe_ext2(&mut alpha_shamir);
    res
}

/// Run dealerless `Π_pow7` + Canonical `< p` A2B bound to an existing session SPDZ MAC key
/// `(alpha_contribs, alpha_shamir)` (used when Poseidon2 key shares and `PreprocessedPoseidonPartyVault`
/// share a single global `GoldilocksExt2` MAC key $\alpha$).
#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the public preprocessing API used by other protocol modules"
)]
pub fn run_dealerless_pi_pow7_with_alpha(
    session_id: [u8; 32],
    t: usize,
    eval_points: &[Goldilocks],
    num_pow7: usize,
    num_extra_beaver: usize,
    num_a2b_masks: usize,
    alpha_contribs: &[GoldilocksExt2],
    alpha_shamir: &[GoldilocksExt2],
    ot_mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<PreprocessedPoseidonPartyVault>, PreprocessError> {
    run_dealerless_pi_pow7_with_alpha_and_fault(
        session_id,
        t,
        eval_points,
        num_pow7,
        num_extra_beaver,
        num_a2b_masks,
        alpha_contribs,
        alpha_shamir,
        ot_mesh,
        party_rngs,
        |_, _| {},
    )
}

#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the public preprocessing API used by other protocol modules"
)]
fn run_dealerless_pi_pow7_with_alpha_and_fault<F>(
    session_id: [u8; 32],
    t: usize,
    eval_points: &[Goldilocks],
    num_pow7: usize,
    num_extra_beaver: usize,
    num_a2b_masks: usize,
    alpha_contribs: &[GoldilocksExt2],
    alpha_shamir: &[GoldilocksExt2],
    ot_mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
    mut fault_hook: F,
) -> Result<Vec<PreprocessedPoseidonPartyVault>, PreprocessError>
where
    F: FnMut(usize, &mut [Goldilocks]),
{
    let n = eval_points.len();
    if t == 0
        || t > n
        || party_rngs.len() != n
        || ot_mesh.n != n
        || alpha_contribs.len() != n
        || alpha_shamir.len() != n
    {
        return Err(PreprocessError::InvalidThreshold { t, n });
    }
    validate_all_eval_points_goldilocks(eval_points)?;

    let base_triples = 6 * num_pow7 + num_extra_beaver;
    let (mut a_sh, mut b_sh, mut c_sh, mut a_mac, mut b_mac, mut c_mac) =
        generate_verified_spdz_beaver_pool_goldilocks(
            &session_id,
            t,
            eval_points,
            ot_mesh,
            alpha_contribs,
            alpha_shamir,
            base_triples,
            party_rngs,
            &mut fault_hook,
        )?;

    // Joint `Π_rand` + SPDZ `Π_MAC` + 3-Round Parallel Beaver Power-Tree (`evalPow7BeaverTree`)
    let mut r1_sh = vec![vec![Goldilocks::ZERO; num_pow7]; n];
    for party_rngs_i_item in party_rngs[..n].iter_mut() {
        #[expect(
            clippy::needless_range_loop,
            reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows"
        )]
        for k in 0..num_pow7 {
            let ri = (*party_rngs_i_item).next_goldilocks();
            let s_ri = shamir_share_goldilocks(t, eval_points, ri, &mut *party_rngs_i_item);
            for p in 0..n {
                r1_sh[p][k] += s_ri[p];
            }
        }
    }
    let r1_mac = spdz_authenticate_goldilocks_batch_ext2(
        &session_id,
        t,
        eval_points,
        ot_mesh,
        alpha_contribs,
        alpha_shamir,
        &r1_sh,
        party_rngs,
    )?;

    let slice_spdz_triples = |a: &[Vec<Goldilocks>],
                              b: &[Vec<Goldilocks>],
                              c: &[Vec<Goldilocks>],
                              am: &[Vec<GoldilocksExt2>],
                              bm: &[Vec<GoldilocksExt2>],
                              cm: &[Vec<GoldilocksExt2>],
                              start: usize,
                              len: usize| {
        let ta: Vec<Vec<Goldilocks>> = (0..n).map(|p| a[p][start..start + len].to_vec()).collect();
        let tb: Vec<Vec<Goldilocks>> = (0..n).map(|p| b[p][start..start + len].to_vec()).collect();
        let tc: Vec<Vec<Goldilocks>> = (0..n).map(|p| c[p][start..start + len].to_vec()).collect();
        let tam: Vec<Vec<GoldilocksExt2>> =
            (0..n).map(|p| am[p][start..start + len].to_vec()).collect();
        let tbm: Vec<Vec<GoldilocksExt2>> =
            (0..n).map(|p| bm[p][start..start + len].to_vec()).collect();
        let tcm: Vec<Vec<GoldilocksExt2>> =
            (0..n).map(|p| cm[p][start..start + len].to_vec()).collect();
        (ta, tb, tc, tam, tbm, tcm)
    };

    let (
        (mut r2_sh, mut r2_mac),
        (mut r3_sh, mut r3_mac),
        (mut r4_sh, mut r4_mac),
        (mut r5_sh, mut r5_mac),
        (mut r6_sh, mut r6_mac),
        (mut r7_sh, mut r7_mac),
    ) = if num_pow7 > 0 {
        let (t2a, t2b, t2c, t2am, t2bm, t2cm) =
            slice_spdz_triples(&a_sh, &b_sh, &c_sh, &a_mac, &b_mac, &c_mac, 0, num_pow7);
        let (t3a, t3b, t3c, t3am, t3bm, t3cm) = slice_spdz_triples(
            &a_sh, &b_sh, &c_sh, &a_mac, &b_mac, &c_mac, num_pow7, num_pow7,
        );
        let (t4a, t4b, t4c, t4am, t4bm, t4cm) = slice_spdz_triples(
            &a_sh,
            &b_sh,
            &c_sh,
            &a_mac,
            &b_mac,
            &c_mac,
            2 * num_pow7,
            num_pow7,
        );
        let (t5a, t5b, t5c, t5am, t5bm, t5cm) = slice_spdz_triples(
            &a_sh,
            &b_sh,
            &c_sh,
            &a_mac,
            &b_mac,
            &c_mac,
            3 * num_pow7,
            num_pow7,
        );
        let (t6a, t6b, t6c, t6am, t6bm, t6cm) = slice_spdz_triples(
            &a_sh,
            &b_sh,
            &c_sh,
            &a_mac,
            &b_mac,
            &c_mac,
            4 * num_pow7,
            num_pow7,
        );
        let (t7a, t7b, t7c, t7am, t7bm, t7cm) = slice_spdz_triples(
            &a_sh,
            &b_sh,
            &c_sh,
            &a_mac,
            &b_mac,
            &c_mac,
            5 * num_pow7,
            num_pow7,
        );

        let (r2, r2m) = eval_spdz_shamir_beaver_batch_goldilocks(
            &session_id,
            t,
            eval_points,
            alpha_shamir,
            &r1_sh,
            &r1_mac,
            &r1_sh,
            &r1_mac,
            &t2a,
            &t2am,
            &t2b,
            &t2bm,
            &t2c,
            &t2cm,
            "pow7_r2",
            party_rngs,
        )?;
        let (r3, r3m) = eval_spdz_shamir_beaver_batch_goldilocks(
            &session_id,
            t,
            eval_points,
            alpha_shamir,
            &r2,
            &r2m,
            &r1_sh,
            &r1_mac,
            &t3a,
            &t3am,
            &t3b,
            &t3bm,
            &t3c,
            &t3cm,
            "pow7_r3",
            party_rngs,
        )?;
        let (r4, r4m) = eval_spdz_shamir_beaver_batch_goldilocks(
            &session_id,
            t,
            eval_points,
            alpha_shamir,
            &r2,
            &r2m,
            &r2,
            &r2m,
            &t4a,
            &t4am,
            &t4b,
            &t4bm,
            &t4c,
            &t4cm,
            "pow7_r4",
            party_rngs,
        )?;
        let (r5, r5m) = eval_spdz_shamir_beaver_batch_goldilocks(
            &session_id,
            t,
            eval_points,
            alpha_shamir,
            &r4,
            &r4m,
            &r1_sh,
            &r1_mac,
            &t5a,
            &t5am,
            &t5b,
            &t5bm,
            &t5c,
            &t5cm,
            "pow7_r5",
            party_rngs,
        )?;
        let (r6, r6m) = eval_spdz_shamir_beaver_batch_goldilocks(
            &session_id,
            t,
            eval_points,
            alpha_shamir,
            &r4,
            &r4m,
            &r2,
            &r2m,
            &t6a,
            &t6am,
            &t6b,
            &t6bm,
            &t6c,
            &t6cm,
            "pow7_r6",
            party_rngs,
        )?;
        let (r7, r7m) = eval_spdz_shamir_beaver_batch_goldilocks(
            &session_id,
            t,
            eval_points,
            alpha_shamir,
            &r4,
            &r4m,
            &r3,
            &r3m,
            &t7a,
            &t7am,
            &t7b,
            &t7bm,
            &t7c,
            &t7cm,
            "pow7_r7",
            party_rngs,
        )?;
        (
            (r2, r2m),
            (r3, r3m),
            (r4, r4m),
            (r5, r5m),
            (r6, r6m),
            (r7, r7m),
        )
    } else {
        (
            (vec![Vec::new(); n], vec![Vec::new(); n]),
            (vec![Vec::new(); n], vec![Vec::new(); n]),
            (vec![Vec::new(); n], vec![Vec::new(); n]),
            (vec![Vec::new(); n], vec![Vec::new(); n]),
            (vec![Vec::new(); n], vec![Vec::new(); n]),
            (vec![Vec::new(); n], vec![Vec::new(); n]),
        )
    };

    // Dealerless Canonical `< p` 64-Bit A2B Masks (`while` loop guarantees exact `num_a2b_masks` `[P2-03]`!)
    let mut a2b_masks_per_party: Vec<Vec<CanonicalBitMask64Share>> =
        (0..n).map(|_| Vec::with_capacity(num_a2b_masks)).collect();

    while a2b_masks_per_party[0].len() < num_a2b_masks {
        let need = num_a2b_masks - a2b_masks_per_party[0].len();
        let batch_cands = need + 1;
        let total_bits = 64 * batch_cands;

        // Fold each party's private random bits via LHL-amplified `pairwise_gilboa_ole_goldilocks`
        // (`B ^ c_i = B + c_i - 2 * B * c_i` — `0` un-combined OT choice bits!)
        let mut cur_shares = vec![vec![Goldilocks::ZERO; total_bits]; n];
        #[expect(
            clippy::needless_range_loop,
            reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows"
        )]
        for m in 0..total_bits {
            let b0 = party_rngs[0].next_u64() & 1;
            cur_shares[0][m] = Goldilocks::from_u64_reduced(b0);
        }
        for i in 1..n {
            let mut u_party = vec![vec![Goldilocks::ZERO; total_bits]; n];
            let mut v_party = vec![vec![Goldilocks::ZERO; total_bits]; n];
            for m in 0..total_bits {
                let ci = party_rngs[i].next_u64() & 1;
                u_party[i][m] = Goldilocks::from_u64_reduced(ci);
                for p in 0..n {
                    v_party[p][m] = cur_shares[p][m];
                }
            }
            let mut prod = pairwise_gilboa_ole_goldilocks(ot_mesh, &u_party, &v_party, party_rngs)?;
            for m in 0..total_bits {
                cur_shares[i][m] += u_party[i][m];
                for p in 0..n {
                    let two_prod = prod[p][m] + prod[p][m];
                    cur_shares[p][m] -= two_prod;
                }
            }
            for p in 0..n {
                wipe_goldilocks(&mut u_party[p]);
                wipe_goldilocks(&mut v_party[p]);
                wipe_goldilocks(&mut prod[p]);
            }
        }

        let mut b_shamir = vec![vec![Goldilocks::ZERO; total_bits]; n];
        for i in 0..n {
            for m in 0..total_bits {
                let sb =
                    shamir_share_goldilocks(t, eval_points, cur_shares[i][m], &mut party_rngs[i]);
                for p in 0..n {
                    b_shamir[p][m] += sb[p];
                }
            }
            wipe_goldilocks(&mut cur_shares[i]);
        }

        let b_mac = spdz_authenticate_goldilocks_batch_ext2(
            &session_id,
            t,
            eval_points,
            ot_mesh,
            alpha_contribs,
            alpha_shamir,
            &b_shamir,
            party_rngs,
        )?;

        // Generate `127 * batch_cands` verified SPDZ Beaver triples:
        // - `64 * batch_cands` to prove `b_m^2 - b_m == 0` under SPDZ `MacCheck`
        // - `63 * batch_cands` to evaluate exact `is_ge_p == 0` under SPDZ `MacCheck`
        let mut no_fault = |_: usize, _: &mut [Goldilocks]| {};
        let (ba, bb, bc, bam, bbm, bcm) = generate_verified_spdz_beaver_pool_goldilocks(
            &session_id,
            t,
            eval_points,
            ot_mesh,
            alpha_contribs,
            alpha_shamir,
            127 * batch_cands,
            party_rngs,
            &mut no_fault,
        )?;

        let (sq_a, sq_b, sq_c, sq_am, sq_bm, sq_cm) =
            slice_spdz_triples(&ba, &bb, &bc, &bam, &bbm, &bcm, 0, total_bits);
        let (bsq_sh, bsq_mac) = eval_spdz_shamir_beaver_batch_goldilocks(
            &session_id,
            t,
            eval_points,
            alpha_shamir,
            &b_shamir,
            &b_mac,
            &b_shamir,
            &b_mac,
            &sq_a,
            &sq_am,
            &sq_b,
            &sq_bm,
            &sq_c,
            &sq_cm,
            "a2b_bit_sq",
            party_rngs,
        )?;
        let diff_sh: Vec<Vec<Goldilocks>> = (0..n)
            .map(|p| {
                (0..total_bits)
                    .map(|m| bsq_sh[p][m] - b_shamir[p][m])
                    .collect()
            })
            .collect();
        let diff_mac: Vec<Vec<GoldilocksExt2>> = (0..n)
            .map(|p| {
                (0..total_bits)
                    .map(|m| bsq_mac[p][m] - b_mac[p][m])
                    .collect()
            })
            .collect();
        let diffs_opened = commit_and_open_spdz_goldilocks_batch_quorum(
            &session_id,
            "a2b_bool_diff",
            t,
            eval_points,
            &diff_sh,
            &diff_mac,
            alpha_shamir,
            party_rngs,
        )?;
        for &dv in &diffs_opened {
            if dv != Goldilocks::ZERO {
                return Err(PreprocessError::NonBooleanBitDetected { phase: "a2b_bits" });
            }
        }

        let mut t_off = total_bits;
        for cand in 0..batch_cands {
            if a2b_masks_per_party[0].len() == num_a2b_masks {
                break;
            }
            let mut cur_nodes: Vec<Vec<Goldilocks>> = (0..n)
                .map(|p| {
                    let mut v = Vec::with_capacity(64);
                    for k in 0..32 {
                        v.push(Goldilocks::ONE - b_shamir[p][64 * cand + k]);
                    }
                    for k in 32..64 {
                        v.push(b_shamir[p][64 * cand + k]);
                    }
                    v
                })
                .collect();
            let mut cur_macs: Vec<Vec<GoldilocksExt2>> = (0..n)
                .map(|p| {
                    let mut v = Vec::with_capacity(64);
                    for k in 0..32 {
                        v.push(alpha_shamir[p] - b_mac[p][64 * cand + k]);
                    }
                    for k in 32..64 {
                        v.push(b_mac[p][64 * cand + k]);
                    }
                    v
                })
                .collect();

            for _ in 0..5 {
                let pairs = cur_nodes[0].len() / 2;
                let lhs: Vec<Vec<Goldilocks>> = (0..n)
                    .map(|p| (0..pairs).map(|j| cur_nodes[p][2 * j]).collect())
                    .collect();
                let lhs_m: Vec<Vec<GoldilocksExt2>> = (0..n)
                    .map(|p| (0..pairs).map(|j| cur_macs[p][2 * j]).collect())
                    .collect();
                let rhs: Vec<Vec<Goldilocks>> = (0..n)
                    .map(|p| (0..pairs).map(|j| cur_nodes[p][2 * j + 1]).collect())
                    .collect();
                let rhs_m: Vec<Vec<GoldilocksExt2>> = (0..n)
                    .map(|p| (0..pairs).map(|j| cur_macs[p][2 * j + 1]).collect())
                    .collect();
                let (ta, tb, tc, tam, tbm, tcm) =
                    slice_spdz_triples(&ba, &bb, &bc, &bam, &bbm, &bcm, t_off, pairs);
                t_off += pairs;
                let (next_n, next_m) = eval_spdz_shamir_beaver_batch_goldilocks(
                    &session_id,
                    t,
                    eval_points,
                    alpha_shamir,
                    &lhs,
                    &lhs_m,
                    &rhs,
                    &rhs_m,
                    &ta,
                    &tam,
                    &tb,
                    &tbm,
                    &tc,
                    &tcm,
                    "a2b_ge_p_tree",
                    party_rngs,
                )?;
                cur_nodes = next_n;
                cur_macs = next_m;
            }

            let lhs: Vec<Vec<Goldilocks>> = (0..n).map(|p| alloc::vec![cur_nodes[p][1]]).collect();
            let lhs_m: Vec<Vec<GoldilocksExt2>> =
                (0..n).map(|p| alloc::vec![cur_macs[p][1]]).collect();
            let rhs: Vec<Vec<Goldilocks>> = (0..n)
                .map(|p| alloc::vec![Goldilocks::ONE - cur_nodes[p][0]])
                .collect();
            let rhs_m: Vec<Vec<GoldilocksExt2>> = (0..n)
                .map(|p| alloc::vec![alpha_shamir[p] - cur_macs[p][0]])
                .collect();
            let (ta, tb, tc, tam, tbm, tcm) =
                slice_spdz_triples(&ba, &bb, &bc, &bam, &bbm, &bcm, t_off, 1);
            t_off += 1;
            let (ge_p_vec, ge_p_mvec) = eval_spdz_shamir_beaver_batch_goldilocks(
                &session_id,
                t,
                eval_points,
                alpha_shamir,
                &lhs,
                &lhs_m,
                &rhs,
                &rhs_m,
                &ta,
                &tam,
                &tb,
                &tbm,
                &tc,
                &tcm,
                "a2b_ge_p_final",
                party_rngs,
            )?;
            let ge_p_sh: Vec<Goldilocks> = (0..n).map(|p| ge_p_vec[p][0]).collect();
            let ge_p_mac: Vec<GoldilocksExt2> = (0..n).map(|p| ge_p_mvec[p][0]).collect();
            let is_ge_p = commit_and_open_spdz_goldilocks_quorum(
                &session_id,
                "a2b_ge_p_open",
                t,
                eval_points,
                &ge_p_sh,
                &ge_p_mac,
                alpha_shamir,
                party_rngs,
            )?;
            if is_ge_p == Goldilocks::ZERO {
                for p in 0..n {
                    let mut bit_shares = [Goldilocks::ZERO; 64];
                    let mut bit_macs = [GoldilocksExt2::ZERO; 64];
                    let mut sum_sh = Goldilocks::ZERO;
                    let mut sum_mac = GoldilocksExt2::ZERO;
                    for k in 0..64 {
                        let bk = b_shamir[p][64 * cand + k];
                        let bmk = b_mac[p][64 * cand + k];
                        let pow2 = Goldilocks::from_u64_reduced(1u64 << k);
                        bit_shares[k] = bk;
                        bit_macs[k] = bmk;
                        sum_sh += pow2 * bk;
                        sum_mac += bmk.mul_base(pow2);
                    }
                    a2b_masks_per_party[p].push(CanonicalBitMask64Share {
                        bit_shares,
                        field_sum_share: sum_sh,
                        bit_macs,
                        field_sum_mac: sum_mac,
                    });
                }
            }
        }
        for b_shamir_p_item in b_shamir[..n].iter_mut() {
            wipe_goldilocks(&mut *b_shamir_p_item);
        }
    }

    // Package isolated per-party vaults and wipe all temporary vectors
    let extra_start = 6 * num_pow7;
    let mut vaults = Vec::with_capacity(n);
    for p in 0..n {
        let mut pow7_tuples = Vec::with_capacity(num_pow7);
        for k in 0..num_pow7 {
            let r1_m = r1_mac[p][k];
            pow7_tuples.push(AuthenticatedPower7Share {
                r_pows: [
                    r1_sh[p][k],
                    r2_sh[p][k],
                    r3_sh[p][k],
                    r4_sh[p][k],
                    r5_sh[p][k],
                    r6_sh[p][k],
                    r7_sh[p][k],
                ],
                r_macs: [
                    r1_m,
                    r2_mac[p][k],
                    r3_mac[p][k],
                    r4_mac[p][k],
                    r5_mac[p][k],
                    r6_mac[p][k],
                    r7_mac[p][k],
                ],
                r1_mac: r1_m,
            });
        }
        wipe_goldilocks(&mut r1_sh[p]);
        wipe_goldilocks(&mut r2_sh[p]);
        wipe_goldilocks(&mut r3_sh[p]);
        wipe_goldilocks(&mut r4_sh[p]);
        wipe_goldilocks(&mut r5_sh[p]);
        wipe_goldilocks(&mut r6_sh[p]);
        wipe_goldilocks(&mut r7_sh[p]);
        wipe_ext2(&mut r2_mac[p]);
        wipe_ext2(&mut r3_mac[p]);
        wipe_ext2(&mut r4_mac[p]);
        wipe_ext2(&mut r5_mac[p]);
        wipe_ext2(&mut r6_mac[p]);
        wipe_ext2(&mut r7_mac[p]);

        let mut beaver_triples = Vec::with_capacity(num_extra_beaver);
        for k in 0..num_extra_beaver {
            let idx = extra_start + k;
            beaver_triples.push(GoldilocksBeaverShare {
                a: a_sh[p][idx],
                b: b_sh[p][idx],
                c: c_sh[p][idx],
                a_mac: a_mac[p][idx],
                b_mac: b_mac[p][idx],
                c_mac: c_mac[p][idx],
            });
        }
        wipe_goldilocks(&mut a_sh[p]);
        wipe_goldilocks(&mut b_sh[p]);
        wipe_goldilocks(&mut c_sh[p]);
        wipe_ext2(&mut a_mac[p]);
        wipe_ext2(&mut b_mac[p]);
        wipe_ext2(&mut c_mac[p]);

        let alpha = alpha_shamir[p];
        vaults.push(PreprocessedPoseidonPartyVault {
            party_id: p,
            eval_point: eval_points[p],
            mac_alpha_share: alpha,
            pow7_tuples,
            pow7_cursor: 0,
            beaver_triples,
            beaver_cursor: 0,
            a2b_masks: core::mem::take(&mut a2b_masks_per_party[p]),
            a2b_cursor: 0,
            poisoned: false,
        });
    }
    Ok(vaults)
}

// ============================================================================
// 7. Sublinear Silent-OT / SHAKE256 GGM Puncturable-PRF + LPN PCG (`PcgSeedExpansion`)
// ============================================================================

/// Validated tree depth for the experimental compact correlation format.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PcgTreeDepth {
    Depth14,
    Depth15,
    Depth16,
}
impl TryFrom<usize> for PcgTreeDepth {
    type Error = PreprocessError;
    fn try_from(depth: usize) -> Result<Self, Self::Error> {
        match depth {
            14 => Ok(Self::Depth14),
            15 => Ok(Self::Depth15),
            16 => Ok(Self::Depth16),
            _ => Err(PreprocessError::PcgDepthOutOfRange { depth }),
        }
    }
}

/// Minimum supported `SHAKE256` GGM puncturable-PRF tree depth (`2^14 = 16,384` leaves/tree).
pub const PCG_MIN_TREE_DEPTH: usize = 14;
/// Default `SHAKE256` GGM puncturable-PRF tree depth (`2^15 = 32,768` leaves/tree).
pub const PCG_DEFAULT_TREE_DEPTH: usize = 15;
/// Maximum supported `SHAKE256` GGM puncturable-PRF tree depth (`2^16 = 65,536` leaves/tree).
pub const PCG_MAX_TREE_DEPTH: usize = 16;

/// Number of packed 64-bit Boolean Beaver triple batches expanded per PCG seed (`1,025 * 64 = 65,600 > 65,536`).
pub const PCG_NUM_WORDS: usize = 1025;
/// Total authenticated Boolean Beaver triples expanded locally from one `< 24 KB` PCG seed (`65,600`).
pub const PCG_NUM_BOOL_TRIPLES: usize = PCG_NUM_WORDS * 64;
/// Number of full 128-bit `Tower128` Beaver triples bundled alongside the `65,600` Boolean triples.
pub const PCG_NUM_TOWER_TRIPLES: usize = 8;
/// Regular LPN noise weight (number of independent punctured GGM trees per primal/dual LPN bundle).
pub const PCG_TREES_PER_BUNDLE: usize = 4;
/// Number of Quasi-Cyclic LPN parity taps per tree block (`4 * 3 = 12`-regular LPN code).
pub const PCG_TAPS_PER_TREE: usize = 3;
/// Hard ceiling on serialized `PcgPartySeed` wire size (`24,576` bytes = `24 KB`).
pub const PCG_MAX_SEED_WIRE_BYTES: usize = 24 * 1024;

// Historical sparse construction is retained only as a regression fixture.
#[cfg(test)]
mod legacy_sparse_pcg {
    use super::*;
    use crate::sponge::keccak::Shake256Xof;

    type BooleanMascotProducts = (
        PartyValues<u64>,
        PartyValues<[u128; 64]>,
        PartyValues<[u128; 64]>,
    );

    /// Pairwise correlated-OT pass of the sparse fixture: Boolean AND shares plus two `Tower128`
    /// companion products per bit. Receiver `j` uses fresh choice bits `c_rand` and publishes
    /// `diff = v_words[j] ^ c_rand`.
    fn pairwise_boolean_and_mascot_companions(
        ot_mesh: &mut OtMesh,
        u_words_per_party: &[Vec<u64>],
        v_words_per_party: &[Vec<u64>],
        at0_per_party: &[Vec<[u128; 64]>],
        at1_per_party: &[Vec<[u128; 64]>],
        party_rngs: &mut [PartyPrivateRng],
    ) -> Result<BooleanMascotProducts, PreprocessError> {
        let n = ot_mesh.n;
        let num_words = u_words_per_party[0].len();
        let mut w_bool: Vec<Vec<u64>> = (0..n)
            .map(|i| {
                (0..num_words)
                    .map(|k| u_words_per_party[i][k] & v_words_per_party[i][k])
                    .collect()
            })
            .collect();
        let mut ct0: Vec<Vec<[u128; 64]>> = (0..n)
            .map(|i| {
                (0..num_words)
                    .map(|k| {
                        let mut arr = [0u128; 64];
                        let vi = v_words_per_party[i][k];
                        for bit in 0..64 {
                            let mask = 0u128.wrapping_sub(((vi >> bit) & 1) as u128);
                            arr[bit] = at0_per_party[i][k][bit] & mask;
                        }
                        arr
                    })
                    .collect()
            })
            .collect();
        let mut ct1: Vec<Vec<[u128; 64]>> = (0..n)
            .map(|i| {
                (0..num_words)
                    .map(|k| {
                        let mut arr = [0u128; 64];
                        let vi = v_words_per_party[i][k];
                        for bit in 0..64 {
                            let mask = 0u128.wrapping_sub(((vi >> bit) & 1) as u128);
                            arr[bit] = at1_per_party[i][k][bit] & mask;
                        }
                        arr
                    })
                    .collect()
            })
            .collect();
        if num_words == 0 {
            return Ok((w_bool, ct0, ct1));
        }

        for i in 0..n {
            for j in 0..n {
                if i == j {
                    continue;
                }
                let mut c_rand = vec![0u64; num_words];
                for w in &mut c_rand {
                    *w = party_rngs[j].next_u64();
                }
                let (send_pads, recv_pads) =
                    ot_mesh.run_correlated_ot_words(i, j, &c_rand, party_rngs)?;
                for k in 0..num_words {
                    let ui = u_words_per_party[i][k];
                    let cr = black_box(c_rand[k]);
                    let dw = v_words_per_party[j][k] ^ cr;
                    let mut s_ij_bool = 0u64;
                    let mut enc_one_bool = 0u64;
                    let mut c1_lane0 = [0u128; 64];
                    let mut c1_lane1 = [0u128; 64];

                    for bit in 0..64 {
                        let (p0, p1) = &send_pads[64 * k + bit];
                        let d_bit = (dw >> bit) & 1;
                        let mask_bit = (p0[32] & 1) as u64;
                        let ui_bit = (ui >> bit) & 1;
                        let c1_b = (mask_bit ^ ui_bit) ^ ((p1[32] & 1) as u64);
                        s_ij_bool |= (mask_bit ^ (ui_bit & d_bit)) << bit;
                        enc_one_bool |= c1_b << bit;

                        let d_mask128 = 0u128.wrapping_sub(d_bit as u128);
                        let p0_l0 = u128::from_le_bytes(core::array::from_fn(|array_index| {
                            (p0[0..16])[array_index]
                        }));
                        let p1_l0 = u128::from_le_bytes(core::array::from_fn(|array_index| {
                            (p1[0..16])[array_index]
                        }));
                        ct0[i][k][bit] ^= p0_l0 ^ (at0_per_party[i][k][bit] & d_mask128);
                        c1_lane0[bit] = p0_l0 ^ at0_per_party[i][k][bit] ^ p1_l0;

                        let p0_l1 = u128::from_le_bytes(core::array::from_fn(|array_index| {
                            (p0[16..32])[array_index]
                        }));
                        let p1_l1 = u128::from_le_bytes(core::array::from_fn(|array_index| {
                            (p1[16..32])[array_index]
                        }));
                        ct1[i][k][bit] ^= p0_l1 ^ (at1_per_party[i][k][bit] & d_mask128);
                        c1_lane1[bit] = p0_l1 ^ at1_per_party[i][k][bit] ^ p1_l1;
                    }
                    w_bool[i][k] ^= s_ij_bool;

                    let mut s_ji_bool = 0u64;
                    for bit in 0..64 {
                        let rpad = &recv_pads[64 * k + bit];
                        let cr_bit = (cr >> bit) & 1;
                        let pb = (rpad[32] & 1) as u64;
                        let corr = cr_bit & ((enc_one_bool >> bit) & 1);
                        s_ji_bool |= (pb ^ corr) << bit;

                        let cmask128 = 0u128.wrapping_sub(cr_bit as u128);
                        let rp_l0 = u128::from_le_bytes(core::array::from_fn(|array_index| {
                            (rpad[0..16])[array_index]
                        }));
                        let rp_l1 = u128::from_le_bytes(core::array::from_fn(|array_index| {
                            (rpad[16..32])[array_index]
                        }));
                        ct0[j][k][bit] ^= rp_l0 ^ (cmask128 & c1_lane0[bit]);
                        ct1[j][k][bit] ^= rp_l1 ^ (cmask128 & c1_lane1[bit]);
                    }
                    w_bool[j][k] ^= s_ji_bool;
                }
                wipe_u64s(&mut c_rand);
            }
        }
        Ok((w_bool, ct0, ct1))
    }

    pub(super) const PCG_WIRE_MAGIC: &[u8; 8] = b"QSAGPCG1";

    /// Sender-side compact seed (`16 B`) for one `SHAKE256` GGM puncturable-PRF tree.
    #[derive(Clone)]
    pub struct GgmSenderTreeSeed {
        pub root_seed: [u8; 16],
    }

    impl fmt::Debug for GgmSenderTreeSeed {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("GgmSenderTreeSeed([REDACTED])")
        }
    }

    impl Drop for GgmSenderTreeSeed {
        fn drop(&mut self) {
            wipe_bytes(&mut self.root_seed);
        }
    }

    /// Receiver-side punctured `SHAKE256` GGM tree seed for Binary Subfield-VOLE (`depth * 16 + 34` bytes).
    #[derive(Clone)]
    pub struct GgmReceiverBinaryTreeSeed {
        pub punctured_idx: u16,
        pub copath: Vec<[u8; 16]>,
        /// Masked punctured-leaf 2-lane `Tower128` correlation `(\bigoplus_u key_S[u]) \oplus \Delta`.
        pub punctured_mac_corr: [Tower128; 2],
    }

    impl fmt::Debug for GgmReceiverBinaryTreeSeed {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("GgmReceiverBinaryTreeSeed([REDACTED])")
        }
    }

    impl Drop for GgmReceiverBinaryTreeSeed {
        fn drop(&mut self) {
            self.punctured_idx = 0;
            for node in &mut self.copath {
                wipe_bytes(node);
            }
            wipe_u128s(core::slice::from_mut(&mut self.punctured_mac_corr[0].0));
            wipe_u128s(core::slice::from_mut(&mut self.punctured_mac_corr[1].0));
        }
    }

    /// Receiver-side punctured `SHAKE256` GGM tree seed for `Tower128` VOLE (`depth * 16 + 50` bytes).
    #[derive(Clone)]
    pub struct GgmReceiverTowerTreeSeed {
        pub punctured_idx: u16,
        pub punctured_beta: Tower128,
        pub copath: Vec<[u8; 16]>,
        /// Masked punctured-leaf 2-lane `Tower128` correlation `key_S[p^*] \oplus (\beta \cdot \Delta)`.
        pub punctured_mac_val: [Tower128; 2],
    }

    impl fmt::Debug for GgmReceiverTowerTreeSeed {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("GgmReceiverTowerTreeSeed([REDACTED])")
        }
    }

    impl Drop for GgmReceiverTowerTreeSeed {
        fn drop(&mut self) {
            self.punctured_idx = 0;
            wipe_u128s(core::slice::from_mut(&mut self.punctured_beta.0));
            for node in &mut self.copath {
                wipe_bytes(node);
            }
            wipe_u128s(core::slice::from_mut(&mut self.punctured_mac_val[0].0));
            wipe_u128s(core::slice::from_mut(&mut self.punctured_mac_val[1].0));
        }
    }

    /// Directional GGM seed material held by `party_id` for a single peer `peer_id != party_id`.
    #[derive(Clone)]
    pub struct PcgPeerSeedMaterial {
        pub peer_id: u16,
        /// `3 * 4 = 12` binary GGM sender roots (`X`, `Y`, `Z` bundles where `party_id` is MAC verifier).
        pub bin_sender_trees: Vec<GgmSenderTreeSeed>,
        /// `3 * 4 = 12` binary GGM punctured receiver trees (`X`, `Y`, `Z` bundles where `party_id` holds sparse noise).
        pub bin_receiver_trees: Vec<GgmReceiverBinaryTreeSeed>,
        /// `2 * 4 = 8` `Tower128` GGM sender roots (`A0`, `A1` sacrifice companion bundles, fixed `depth = 14`).
        pub tower_sender_trees: Vec<GgmSenderTreeSeed>,
        /// `2 * 4 = 8` `Tower128` GGM punctured receiver trees (`A0`, `A1` companion bundles, fixed `depth = 14`).
        pub tower_receiver_trees: Vec<GgmReceiverTowerTreeSeed>,
    }

    impl fmt::Debug for PcgPeerSeedMaterial {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.debug_struct("PcgPeerSeedMaterial")
                .field("peer_id", &self.peer_id)
                .finish_non_exhaustive()
        }
    }

    /// Additive 2-lane `Tower128` BDOZ-authenticated scalar share `[x]_p \in \mathcal{T}_7`.
    ///
    /// Global invariant across parties $p \in \{0, \dots, n-1\}$:
    /// `macs_for_me[q][lane] \oplus Peer(q).keys_from_me[p][lane] == Peer(q).alpha[lane] * value` (`q != p`),
    /// and for `q == p`, `macs_for_me[p][lane] \oplus keys_from_me[p][lane] == alpha[lane] * value`.
    #[derive(PartialEq, Eq)]
    pub struct PcgAuthTower128Share {
        pub value: Tower128,
        /// `macs[verifier_q][lane]` authenticating `self.value` under party `q`'s MAC key.
        pub macs: Vec<[Tower128; 2]>,
        /// `keys[holder_q][lane]` authenticating party `q`'s share under `self.alpha`.
        pub keys: Vec<[Tower128; 2]>,
    }

    impl fmt::Debug for PcgAuthTower128Share {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("PcgAuthTower128Share([REDACTED])")
        }
    }

    impl Drop for PcgAuthTower128Share {
        fn drop(&mut self) {
            wipe_u128s(core::slice::from_mut(&mut self.value.0));
            for row in &mut self.macs {
                wipe_tower128(row);
            }
            for row in &mut self.keys {
                wipe_tower128(row);
            }
        }
    }

    impl PcgAuthTower128Share {
        pub fn zero(n: usize) -> Self {
            Self {
                value: Tower128::ZERO,
                macs: vec![[Tower128::ZERO; 2]; n],
                keys: vec![[Tower128::ZERO; 2]; n],
            }
        }

        #[inline]
        pub fn xor_assign(&mut self, rhs: &Self) {
            self.value = self.value.add(rhs.value);
            for q in 0..self.macs.len() {
                for lane in 0..2 {
                    self.macs[q][lane] = self.macs[q][lane].add(rhs.macs[q][lane]);
                    self.keys[q][lane] = self.keys[q][lane].add(rhs.keys[q][lane]);
                }
            }
        }

        #[inline]
        pub fn scale(&self, rho: Tower128) -> Self {
            let n = self.macs.len();
            let mut macs = vec![[Tower128::ZERO; 2]; n];
            let mut keys = vec![[Tower128::ZERO; 2]; n];
            for q in 0..n {
                for lane in 0..2 {
                    macs[q][lane] = self.macs[q][lane].mul(rho);
                    keys[q][lane] = self.keys[q][lane].mul(rho);
                }
            }
            Self {
                value: self.value.mul(rho),
                macs,
                keys,
            }
        }
    }

    /// Authenticated 128-bit `Tower128` Beaver triple `([a], [b], [c])` with `c = a * b` in $\mathcal{T}_7$.
    #[derive(PartialEq, Eq)]
    pub struct PcgAuthTower128TripleShare {
        pub a: PcgAuthTower128Share,
        pub b: PcgAuthTower128Share,
        pub c: PcgAuthTower128Share,
    }

    impl fmt::Debug for PcgAuthTower128TripleShare {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("PcgAuthTower128TripleShare([REDACTED])")
        }
    }

    /// Packed 64-bit batch of authenticated Boolean Beaver triples `([a], [b], [c])` (`c = a & b`)
    /// with exact per-bit 2-lane `Tower128` BDOZ MACs and keys.
    pub struct PcgAuthBoolTripleWord64 {
        pub a_word: u64,
        pub b_word: u64,
        pub c_word: u64,
        /// `[bit][verifier_q][lane]` authenticating `a_word / b_word / c_word` bits.
        pub a_macs: Vec<[[Tower128; 2]; 64]>,
        pub a_keys: Vec<[[Tower128; 2]; 64]>,
        pub b_macs: Vec<[[Tower128; 2]; 64]>,
        pub b_keys: Vec<[[Tower128; 2]; 64]>,
        pub c_macs: Vec<[[Tower128; 2]; 64]>,
        pub c_keys: Vec<[[Tower128; 2]; 64]>,
    }

    impl fmt::Debug for PcgAuthBoolTripleWord64 {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("PcgAuthBoolTripleWord64([REDACTED])")
        }
    }

    impl Drop for PcgAuthBoolTripleWord64 {
        fn drop(&mut self) {
            wipe_u64s(core::slice::from_mut(&mut self.a_word));
            wipe_u64s(core::slice::from_mut(&mut self.b_word));
            wipe_u64s(core::slice::from_mut(&mut self.c_word));
            for v in &mut self.a_macs {
                for pair in v {
                    wipe_tower128(pair);
                }
            }
            for v in &mut self.a_keys {
                for pair in v {
                    wipe_tower128(pair);
                }
            }
            for v in &mut self.b_macs {
                for pair in v {
                    wipe_tower128(pair);
                }
            }
            for v in &mut self.b_keys {
                for pair in v {
                    wipe_tower128(pair);
                }
            }
            for v in &mut self.c_macs {
                for pair in v {
                    wipe_tower128(pair);
                }
            }
            for v in &mut self.c_keys {
                for pair in v {
                    wipe_tower128(pair);
                }
            }
        }
    }

    /// Experimental sparse correlation format, not suitable for online masks.
    /// Production vault APIs use uniform KOS/MASCOT preprocessing.
    /// Compact `< 24 KB` sublinear Silent-OT / `SHAKE256` GGM + QC-LPN Pseudorandom Correlation
    /// Generator (`PCG`) seed held by one party.
    ///
    /// Calling [`PcgPartySeed::expand_local`] expands this `< 24 KB` seed **locally with ZERO network I/O**
    /// into `65,600` (`> 65,536`) 2-lane `Tower128` BDOZ-authenticated Boolean Beaver triples +
    /// `8` authenticated 128-bit `Tower128` Beaver triples + sacrifice companion masks.
    pub struct PcgPartySeed {
        session_id: [u8; 32],
        party_id: usize,
        num_parties: usize,
        tree_depth: usize,
        mac_alpha: [Tower128; 2],
        /// Local PRG seed generating diagonal self-MAC masks `keys[p][p]` (`0` wire bloat).
        diag_mask_seed: [u8; 32],
        peers: Vec<PcgPeerSeedMaterial>,
        /// Public 1-bit `Ferret`-style correlation syndrome `\delta_\ell = z_\ell \oplus (x_\ell \wedge y_\ell)` (`8,200 B`).
        delta_words: Vec<u64>,
        /// Pre-authenticated unweighted companion sums `[\bigoplus_\ell \tilde{A}_{L,\ell} \cdot y_\ell]` (`L = 0, 1`).
        tilde_c_sums: [PcgAuthTower128Share; 2],
        /// `8` authenticated 128-bit `Tower128` Beaver triples.
        tower_triples: Vec<PcgAuthTower128TripleShare>,
    }

    impl fmt::Debug for PcgPartySeed {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.debug_struct("PcgPartySeed")
                .field("party_id", &self.party_id)
                .field("num_parties", &self.num_parties)
                .field("tree_depth", &self.tree_depth)
                .finish_non_exhaustive()
        }
    }

    impl Drop for PcgPartySeed {
        fn drop(&mut self) {
            wipe_u128s(core::slice::from_mut(&mut self.mac_alpha[0].0));
            wipe_u128s(core::slice::from_mut(&mut self.mac_alpha[1].0));
            wipe_bytes(&mut self.diag_mask_seed);
        }
    }

    /// Locally expanded PCG correlation vault (`65,600` Boolean triples + `8` `Tower128` triples +
    /// sacrifice companion masks), produced by [`PcgPartySeed::expand_local`] with **zero** network I/O.
    pub struct PcgExpandedPartyVault {
        pub session_id: [u8; 32],
        pub party_id: usize,
        pub num_parties: usize,
        pub mac_alpha: [Tower128; 2],
        pub bool_triple_words: Vec<PcgAuthBoolTripleWord64>,
        pub tower_triples: Vec<PcgAuthTower128TripleShare>,
        /// Sacrifice companion masks `[\tilde{A}_{lane, \ell}] \in \mathcal{T}_7` (`lane = 0, 1`, `\ell = 0..65,600`).
        pub companion_a: [Vec<PcgAuthTower128Share>; 2],
        pub companion_c_sums: [PcgAuthTower128Share; 2],
    }

    impl fmt::Debug for PcgExpandedPartyVault {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.debug_struct("PcgExpandedPartyVault")
                .field("party_id", &self.party_id)
                .field("num_parties", &self.num_parties)
                .finish_non_exhaustive()
        }
    }

    impl Drop for PcgExpandedPartyVault {
        fn drop(&mut self) {
            wipe_tower128(&mut self.mac_alpha);
        }
    }

    impl PcgExpandedPartyVault {
        /// Total number of authenticated Boolean Beaver triples in this expanded vault (`65,600`).
        #[inline]
        pub fn num_boolean_triples(&self) -> usize {
            self.bool_triple_words.len() * 64
        }
    }

    /// Single-block `SHAKE256` (`Keccak-f[1600]`) GGM internal node expansion:
    /// expands `node_seed: [u8; 16]` at `(domain_tag, tree_id, level)` into `(left: [u8; 16], right: [u8; 16])`.
    #[inline]
    fn ggm_expand_node_shake256(
        session_id: &[u8; 32],
        tree_tag: u8,
        level: u8,
        node_seed: &[u8; 16],
    ) -> ([u8; 16], [u8; 16]) {
        let mut state = [0u64; 25];
        let mut blk = [0u8; 72];
        blk[0..16].copy_from_slice(b"QSAG.PCG.GGM.ND1");
        blk[16..48].copy_from_slice(session_id);
        blk[48] = tree_tag;
        blk[49] = level;
        blk[50..66].copy_from_slice(node_seed);
        blk[66] = 0x1F; // SHAKE256 pad start (`rate = 136` bytes = `17` u64 lanes)
        for w in 0..9 {
            state[w] = u64::from_le_bytes(core::array::from_fn(|array_index| {
                (blk[8 * w..8 * (w + 1)])[array_index]
            }));
        }
        state[16] ^= 0x80u64 << 56;
        keccak_f1600(&mut state);

        let mut left = [0u8; 16];
        let mut right = [0u8; 16];
        left[0..8].copy_from_slice(&state[0].to_le_bytes());
        left[8..16].copy_from_slice(&state[1].to_le_bytes());
        right[0..8].copy_from_slice(&state[2].to_le_bytes());
        right[8..16].copy_from_slice(&state[3].to_le_bytes());
        wipe_bytes(&mut blk);
        wipe_u64s(&mut state);
        (left, right)
    }

    /// Single-block `SHAKE256` (`Keccak-f[1600]`) GGM leaf expansion:
    /// expands `leaf_seed: [u8; 16]` into two 128-bit `Tower128` MAC/key tags `(lane0, lane1)`.
    #[inline]
    fn ggm_expand_leaf_tags_shake256(
        session_id: &[u8; 32],
        tree_tag: u8,
        leaf_idx: u32,
        leaf_seed: &[u8; 16],
    ) -> [u128; 2] {
        let mut state = [0u64; 25];
        let mut blk = [0u8; 72];
        blk[0..16].copy_from_slice(b"QSAG.PCG.GGM.LF1");
        blk[16..48].copy_from_slice(session_id);
        blk[48] = tree_tag;
        blk[49..53].copy_from_slice(&leaf_idx.to_le_bytes());
        blk[53..69].copy_from_slice(leaf_seed);
        blk[69] = 0x1F;
        for w in 0..9 {
            state[w] = u64::from_le_bytes(core::array::from_fn(|array_index| {
                (blk[8 * w..8 * (w + 1)])[array_index]
            }));
        }
        state[16] ^= 0x80u64 << 56;
        keccak_f1600(&mut state);

        let lane0 = (state[0] as u128) | ((state[1] as u128) << 64);
        let lane1 = (state[2] as u128) | ((state[3] as u128) << 64);
        wipe_bytes(&mut blk);
        wipe_u64s(&mut state);
        [lane0, lane1]
    }

    /// Sender full-tree `SHAKE256` GGM evaluation: returns `(leaf_tags: Vec<[u128; 2]>, level_lr_xors: Vec<([u8; 16], [u8; 16])>)`.
    fn ggm_eval_sender_full(
        session_id: &[u8; 32],
        tree_tag: u8,
        depth: usize,
        root_seed: &[u8; 16],
    ) -> SpcotPunctureOutput {
        let mut cur_level = Vec::with_capacity(1);
        cur_level.push(*root_seed);
        let mut level_lr_xors = Vec::with_capacity(depth);

        for lvl in 0..depth {
            let mut next_level = Vec::with_capacity(cur_level.len() * 2);
            let mut l_xor = [0u8; 16];
            let mut r_xor = [0u8; 16];
            for nodes in cur_level.chunks(4) {
                let mut states = [[0u64; 25]; 4];
                for (i, node) in nodes.iter().enumerate() {
                    let mut block = [0u8; 72];
                    block[..16].copy_from_slice(b"QSAG.PCG.GGM.ND1");
                    block[16..48].copy_from_slice(session_id);
                    block[48] = tree_tag;
                    block[49] = lvl as u8;
                    block[50..66].copy_from_slice(node);
                    block[66] = 0x1f;
                    #[expect(
                        clippy::chunks_exact_to_as_chunks,
                        reason = "Keep the workspace Rust 1.85 minimum; slice as_chunks requires a newer compiler"
                    )]
                    for (word, bytes) in states[i].iter_mut().zip(block.chunks_exact(8)) {
                        *word = u64::from_le_bytes(core::array::from_fn(|array_index| {
                            (bytes)[array_index]
                        }));
                    }
                    states[i][16] = 0x80u64 << 56;
                    wipe_bytes(&mut block);
                }
                qsag_asm::keccak_f1600_batch(&mut states[..nodes.len()]);
                for state in &mut states[..nodes.len()] {
                    let mut left = [0u8; 16];
                    let mut right = [0u8; 16];
                    left[..8].copy_from_slice(&state[0].to_le_bytes());
                    left[8..].copy_from_slice(&state[1].to_le_bytes());
                    right[..8].copy_from_slice(&state[2].to_le_bytes());
                    right[8..].copy_from_slice(&state[3].to_le_bytes());
                    for b in 0..16 {
                        l_xor[b] ^= left[b];
                        r_xor[b] ^= right[b];
                    }
                    next_level.push(left);
                    next_level.push(right);
                    wipe_bytes(&mut left);
                    wipe_bytes(&mut right);
                    wipe_u64s(state);
                }
            }
            for node in &mut cur_level {
                wipe_bytes(node);
            }
            cur_level = next_level;
            level_lr_xors.push((l_xor, r_xor));
        }

        let num_leaves = 1usize << depth;
        let mut leaf_tags = Vec::with_capacity(num_leaves);
        for (u, cur_level_u_item) in cur_level[..num_leaves].iter_mut().enumerate() {
            leaf_tags.push(ggm_expand_leaf_tags_shake256(
                session_id,
                tree_tag,
                u as u32,
                &*cur_level_u_item,
            ));
            wipe_bytes(&mut *cur_level_u_item);
        }
        (leaf_tags, level_lr_xors)
    }

    /// Receiver punctured-tree `SHAKE256` GGM evaluation from a compressed `depth * 16 B` copath:
    /// reconstructs exact leaf tags at every `u != punctured_idx`, and fills `punctured_idx` from the
    /// masked correlation so `mac_R[u] ^ key_S[u] == (u == p^*) * target_delta`.
    fn ggm_eval_receiver_punctured(
        session_id: &[u8; 32],
        tree_tag: u8,
        depth: usize,
        punctured_idx: usize,
        copath: &[[u8; 16]],
        punctured_mode_sum_or_direct: ([u128; 2], bool),
    ) -> Vec<[u128; 2]> {
        let mut cur_level = vec![[0u8; 16]; 1];
        let mut missing_prefix = 0usize;

        for (lvl, copath_lvl_item) in copath[..depth].iter().enumerate() {
            let bit = (punctured_idx >> (depth - 1 - lvl)) & 1;
            let mut next_level = vec![[0u8; 16]; cur_level.len() * 2];
            let mut known_xor = [0u8; 16];

            for (idx, node) in cur_level.iter().enumerate() {
                if idx == missing_prefix {
                    continue;
                }
                let (left, right) = ggm_expand_node_shake256(session_id, tree_tag, lvl as u8, node);
                if bit == 0 {
                    for b in 0..16 {
                        known_xor[b] ^= right[b];
                    }
                } else {
                    for b in 0..16 {
                        known_xor[b] ^= left[b];
                    }
                }
                next_level[2 * idx] = left;
                next_level[2 * idx + 1] = right;
            }

            let mut recovered_sibling = [0u8; 16];
            for b in 0..16 {
                recovered_sibling[b] = (*copath_lvl_item)[b] ^ known_xor[b];
            }
            let sibling_pos = (missing_prefix << 1) | (bit ^ 1);
            next_level[sibling_pos] = recovered_sibling;
            missing_prefix = (missing_prefix << 1) | bit;

            for node in &mut cur_level {
                wipe_bytes(node);
            }
            cur_level = next_level;
        }

        let num_leaves = 1usize << depth;
        let mut leaf_tags = vec![[0u128; 2]; num_leaves];
        let mut partial_xor = [0u128; 2];
        for u in 0..num_leaves {
            if u == punctured_idx {
                continue;
            }
            let tags = ggm_expand_leaf_tags_shake256(session_id, tree_tag, u as u32, &cur_level[u]);
            leaf_tags[u] = tags;
            partial_xor[0] ^= tags[0];
            partial_xor[1] ^= tags[1];
            wipe_bytes(&mut cur_level[u]);
        }

        let (corr, xor_with_partial) = punctured_mode_sum_or_direct;
        if xor_with_partial {
            leaf_tags[punctured_idx] = [corr[0] ^ partial_xor[0], corr[1] ^ partial_xor[1]];
        } else {
            leaf_tags[punctured_idx] = corr;
        }
        leaf_tags
    }

    /// Deterministic Quasi-Cyclic LPN parity-check / generator schedule (`base`, odd `stride`) derived
    /// via `SHAKE256` from `(session_id, bundle_tag)` for `num_words` 64-bit blocks across `4` trees.
    struct QcLpnParitySchedule {
        /// Flattened `[word * 12 + tree * 3 + tap] -> (base, odd_stride)` masked to `(1 << depth) - 1`.
        base_and_stride: Vec<(u32, u32)>,
        leaf_mask: usize,
    }

    impl QcLpnParitySchedule {
        fn derive(
            session_id: &[u8; 32],
            bundle_tag: &[u8],
            depth: usize,
            num_words: usize,
        ) -> Self {
            let leaf_mask = (1usize << depth) - 1;
            let entries = num_words * PCG_TREES_PER_BUNDLE * PCG_TAPS_PER_TREE;
            let mut xof = Shake256Xof::new_shake256();
            xof.absorb(b"QSAG.PCG.QCLPN.SCHED/v1");
            xof.absorb(session_id);
            xof.absorb(bundle_tag);
            xof.absorb(&(depth as u32).to_le_bytes());
            let mut raw = vec![0u8; entries * 4];
            xof.squeeze(&mut raw);

            let mut base_and_stride = Vec::with_capacity(entries);
            for e in 0..entries {
                let b = (u16::from_le_bytes([raw[4 * e], raw[4 * e + 1]]) as usize) & leaf_mask;
                let s = ((u16::from_le_bytes([raw[4 * e + 2], raw[4 * e + 3]]) as usize) | 1)
                    & leaf_mask;
                base_and_stride.push((b as u32, s as u32));
            }
            Self {
                base_and_stride,
                leaf_mask,
            }
        }

        /// Compress `4` GGM leaf-tag vectors (`[tree][0..2^depth]`) into `num_words * 64` LPN output
        /// tags AND compute the sparse noise bit-words `H * e` for `punctured_indices: Option<[usize; 4]>`.
        fn compress_binary_bundle(
            &self,
            num_words: usize,
            tree_leaf_tags: &[Vec<[u128; 2]>],
            punctured_indices: Option<[usize; 4]>,
        ) -> (Vec<u64>, Vec<[[u128; 2]; 64]>) {
            let mut bit_words = vec![0u64; num_words];
            let mut out_tags = vec![[[0u128; 2]; 64]; num_words];
            let mask = self.leaf_mask;

            for k in 0..num_words {
                let mut w_bits = 0u64;
                let row_tags = &mut out_tags[k];
                for tree in 0..PCG_TREES_PER_BUNDLE {
                    let leaves = &tree_leaf_tags[tree];
                    let p_star = punctured_indices.map(|arr| arr[tree]).unwrap_or(usize::MAX);
                    for tap in 0..PCG_TAPS_PER_TREE {
                        let (base, stride) = self.base_and_stride
                            [(k * PCG_TREES_PER_BUNDLE + tree) * PCG_TAPS_PER_TREE + tap];
                        let mut col = base as usize;
                        let step = stride as usize;
                        for (bit, row_tags_bit_item) in row_tags[..64].iter_mut().enumerate() {
                            let t = leaves[col];
                            (*row_tags_bit_item)[0] ^= t[0];
                            (*row_tags_bit_item)[1] ^= t[1];
                            if col == p_star {
                                w_bits ^= 1u64 << bit;
                            }
                            col = (col + step) & mask;
                        }
                    }
                }
                bit_words[k] = w_bits;
            }
            (bit_words, out_tags)
        }

        /// Compress `4` `Tower128` VOLE GGM trees into `num_words * 64` values + 2-lane tags.
        fn compress_tower_bundle(
            &self,
            num_words: usize,
            tree_leaf_tags: &[Vec<[u128; 2]>],
            punctured: Option<[(usize, Tower128); 4]>,
        ) -> (Vec<Tower128>, Vec<[u128; 2]>) {
            let total = num_words * 64;
            let mut vals = vec![Tower128::ZERO; total];
            let mut tags = vec![[0u128; 2]; total];
            let mask = self.leaf_mask;

            for k in 0..num_words {
                for tree in 0..PCG_TREES_PER_BUNDLE {
                    let leaves = &tree_leaf_tags[tree];
                    let (p_star, beta) = punctured
                        .map(|arr| arr[tree])
                        .unwrap_or((usize::MAX, Tower128::ZERO));
                    for tap in 0..PCG_TAPS_PER_TREE {
                        let (base, stride) = self.base_and_stride
                            [(k * PCG_TREES_PER_BUNDLE + tree) * PCG_TAPS_PER_TREE + tap];
                        let mut col = base as usize;
                        let step = stride as usize;
                        for bit in 0..64 {
                            let idx = 64 * k + bit;
                            let t = leaves[col];
                            tags[idx][0] ^= t[0];
                            tags[idx][1] ^= t[1];
                            if col == p_star {
                                vals[idx] = vals[idx].add(beta);
                            }
                            col = (col + step) & mask;
                        }
                    }
                }
            }
            (vals, tags)
        }
    }

    /// LHL-amplified (`4` uniform `Tower128` OT masks = `512` bits per element -> `< 2^{-192}`
    /// selective-failure advantage) pairwise 128-bit `Tower128` MASCOT OLE on `OtMesh`:
    /// computes additive shares `w[i][k]` of `(\bigoplus_i u[i][k]) * (\bigoplus_j v[j][k])` in $\mathcal{T}_7$
    /// with **zero** cleartext reconstruction of `u` or `v` and **zero** raw secret OT choice bits.
    fn pairwise_ole_tower128(
        session_id: &[u8; 32],
        ot_mesh: &mut OtMesh,
        u_per_party: &[Vec<Tower128>],
        v_per_party: &[Vec<Tower128>],
        party_rngs: &mut [PartyPrivateRng],
    ) -> Result<Vec<Vec<Tower128>>, PreprocessError> {
        let n = ot_mesh.n;
        let count = u_per_party[0].len();
        let mut w_per_party: Vec<Vec<Tower128>> = (0..n)
            .map(|i| {
                (0..count)
                    .map(|k| u_per_party[i][k].mul(v_per_party[i][k]))
                    .collect()
            })
            .collect();
        if count == 0 {
            return Ok(w_per_party);
        }

        // Each party `i` samples `4 * count` uniform `Tower128` OT masks (`8 * count` u64 choice words)
        let mut r_masks = vec![vec![[Tower128::ZERO; 4]; count]; n];
        let mut choice_words = vec![Vec::with_capacity(8 * count); n];
        for i in 0..n {
            #[expect(
                clippy::needless_range_loop,
                reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows"
            )]
            for k in 0..count {
                #[expect(
                    clippy::needless_range_loop,
                    reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows"
                )]
                for m in 0..4 {
                    let r = party_rngs[i].next_tower128();
                    r_masks[i][k][m] = r;
                    choice_words[i].push(r.0 as u64);
                    choice_words[i].push((r.0 >> 64) as u64);
                }
            }
        }

        let mut raw_s = vec![vec![vec![[Tower128::ZERO; 4]; count]; n]; n];
        let mut raw_r = vec![vec![vec![[Tower128::ZERO; 4]; count]; n]; n];
        for i in 0..n {
            for j in 0..n {
                if i == j {
                    continue;
                }
                // Sender `j` inputs `u_j[k]`; Receiver `i` inputs uniform random `r_masks[i][k][0..4]`
                let (send_pads, recv_pads) =
                    ot_mesh.run_correlated_ot_words(j, i, &choice_words[i], party_rngs)?;
                for k in 0..count {
                    let uj = u_per_party[j][k];
                    for m in 0..4 {
                        let rm_raw = black_box(r_masks[i][k][m].0);
                        let mut s_sum = Tower128::ZERO;
                        let mut r_sum = Tower128::ZERO;
                        let base_off = (4 * k + m) * 128;
                        for bit in 0..128 {
                            let (p0, p1) = &send_pads[base_off + bit];
                            let pad0 = Tower128(u128::from_le_bytes(core::array::from_fn(
                                |array_index| (p0[0..16])[array_index],
                            )));
                            let pad1 = Tower128(u128::from_le_bytes(core::array::from_fn(
                                |array_index| (p1[0..16])[array_index],
                            )));
                            let mask = party_rngs[j].next_tower128();
                            s_sum = s_sum.add(mask);
                            let basis = Tower128(1u128 << bit);
                            let ct0 = mask.add(pad0);
                            let ct1 = mask.add(uj.mul(basis)).add(pad1);

                            let pad_c = Tower128(u128::from_le_bytes(core::array::from_fn(
                                |array_index| (recv_pads[base_off + bit][0..16])[array_index],
                            )));
                            let choice = ((rm_raw >> bit) & 1) == 1;
                            let cmask = 0u128.wrapping_sub(black_box(choice as u128));
                            let sel = Tower128(ct0.0 ^ (cmask & (ct0.0 ^ ct1.0)));
                            r_sum = r_sum.add(sel.add(pad_c));
                        }
                        raw_s[j][i][k][m] = s_sum;
                        raw_r[j][i][k][m] = r_sum;
                    }
                }
            }
        }

        // Post-OT `Π_coin` 2-universal LHL combiner (`512 -> 128` bits) + MASCOT input derandomization
        let coin =
            run_commit_and_open_coin(session_id, b"PCG_OLE_T128_LHL", session_id, party_rngs)?;
        let mut xof = Cshake256Xof::new(b"QSAG.PCG.OLE.T128.LHL/v1");
        xof.absorb(&coin);
        let mut g_weights = vec![[Tower128::ONE; 4]; count];
        for g_weights_k_item in g_weights[..count].iter_mut() {
            for m in 1..4 {
                let mut gb = [0u8; 16];
                xof.squeeze(&mut gb);
                (*g_weights_k_item)[m] = Tower128(u128::from_le_bytes(gb) | 1);
            }
        }

        let mut diffs = vec![vec![Tower128::ZERO; count]; n];
        for i in 0..n {
            for k in 0..count {
                let mut r_comb = r_masks[i][k][0];
                for m in 1..4 {
                    r_comb = r_comb.add(g_weights[k][m].mul(r_masks[i][k][m]));
                }
                diffs[i][k] = v_per_party[i][k].add(r_comb);
                wipe_tower128(&mut r_masks[i][k]);
            }
            wipe_u64s(&mut choice_words[i]);
        }

        for i in 0..n {
            for j in 0..n {
                if i == j {
                    continue;
                }
                for k in 0..count {
                    let mut s_comb = raw_s[j][i][k][0];
                    let mut r_comb = raw_r[j][i][k][0];
                    for m in 1..4 {
                        let g = g_weights[k][m];
                        s_comb = s_comb.add(g.mul(raw_s[j][i][k][m]));
                        r_comb = r_comb.add(g.mul(raw_r[j][i][k][m]));
                    }
                    // `s_comb + r_comb == u_j * r_comb_i`; add `u_j * (v_i + r_comb_i)` to Sender `j`!
                    s_comb = s_comb.add(u_per_party[j][k].mul(diffs[i][k]));
                    w_per_party[j][k] = w_per_party[j][k].add(s_comb);
                    w_per_party[i][k] = w_per_party[i][k].add(r_comb);
                    wipe_tower128(&mut raw_s[j][i][k]);
                    wipe_tower128(&mut raw_r[j][i][k]);
                }
            }
        }
        Ok(w_per_party)
    }

    /// LHL-amplified (`4` uniform `Tower128` OT masks = `512` bits per element -> `< 2^{-192}`
    /// selective-failure advantage) 2-lane BDOZ authentication of `vals_per_party[party][k]` via `OtMesh`.
    fn authenticate_tower128_batch(
        session_id: &[u8; 32],
        ot_mesh: &mut OtMesh,
        alphas: &[[Tower128; 2]],
        vals_per_party: &[Vec<Tower128>],
        party_rngs: &mut [PartyPrivateRng],
    ) -> Result<Vec<Vec<PcgAuthTower128Share>>, PreprocessError> {
        let n = ot_mesh.n;
        let count = vals_per_party[0].len();
        let mut out: Vec<Vec<PcgAuthTower128Share>> = (0..n)
            .map(|p| {
                (0..count)
                    .map(|k| {
                        let mut sh = PcgAuthTower128Share::zero(n);
                        sh.value = vals_per_party[p][k];
                        sh
                    })
                    .collect()
            })
            .collect();
        if count == 0 {
            return Ok(out);
        }

        let mut r_masks = vec![vec![[Tower128::ZERO; 4]; count]; n];
        let mut choice_words = vec![Vec::with_capacity(8 * count); n];
        for j in 0..n {
            #[expect(
                clippy::needless_range_loop,
                reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows"
            )]
            for k in 0..count {
                #[expect(
                    clippy::needless_range_loop,
                    reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows"
                )]
                for m in 0..4 {
                    let r = party_rngs[j].next_tower128();
                    r_masks[j][k][m] = r;
                    choice_words[j].push(r.0 as u64);
                    choice_words[j].push((r.0 >> 64) as u64);
                }
            }
        }

        let mut raw_k = vec![vec![vec![[[Tower128::ZERO; 4]; 2]; count]; n]; n];
        let mut raw_m = vec![vec![vec![[[Tower128::ZERO; 4]; 2]; count]; n]; n];

        for i in 0..n {
            for k in 0..count {
                for (lane, alpha) in alphas[i].iter().enumerate() {
                    let m = party_rngs[i].next_tower128();
                    out[i][k].keys[i][lane] = m;
                    out[i][k].macs[i][lane] = m.add(alpha.mul(vals_per_party[i][k]));
                }
            }
            for j in 0..n {
                if i == j {
                    continue;
                }
                let (send_pads, recv_pads) =
                    ot_mesh.run_correlated_ot_words(i, j, &choice_words[j], party_rngs)?;
                for k in 0..count {
                    for m in 0..4 {
                        let rj_raw = black_box(r_masks[j][k][m].0);
                        let base_off = (4 * k + m) * 128;
                        for lane in 0..2 {
                            let alpha_il = alphas[i][lane];
                            let mut k_sum = Tower128::ZERO;
                            let mut m_sum = Tower128::ZERO;
                            for bit in 0..128 {
                                let (p0, p1) = &send_pads[base_off + bit];
                                let pad0 = Tower128(u128::from_le_bytes(core::array::from_fn(
                                    |array_index| (p0[16 * lane..16 * (lane + 1)])[array_index],
                                )));
                                let pad1 = Tower128(u128::from_le_bytes(core::array::from_fn(
                                    |array_index| (p1[16 * lane..16 * (lane + 1)])[array_index],
                                )));
                                let mk = party_rngs[i].next_tower128();
                                k_sum = k_sum.add(mk);
                                let basis = Tower128(1u128 << bit);
                                let ct0 = mk.add(pad0);
                                let ct1 = mk.add(alpha_il.mul(basis)).add(pad1);

                                let pad_c = Tower128(u128::from_le_bytes(core::array::from_fn(
                                    |array_index| {
                                        (recv_pads[base_off + bit][16 * lane..16 * (lane + 1)])
                                            [array_index]
                                    },
                                )));
                                let choice = ((rj_raw >> bit) & 1) == 1;
                                let cmask = 0u128.wrapping_sub(black_box(choice as u128));
                                let sel = Tower128(ct0.0 ^ (cmask & (ct0.0 ^ ct1.0)));
                                m_sum = m_sum.add(sel.add(pad_c));
                            }
                            raw_k[i][j][k][lane][m] = k_sum;
                            raw_m[i][j][k][lane][m] = m_sum;
                        }
                    }
                }
            }
        }

        let coin =
            run_commit_and_open_coin(session_id, b"PCG_AUTH_T128_LHL", session_id, party_rngs)?;
        let mut xof = Cshake256Xof::new(b"QSAG.PCG.AUTH.T128.LHL/v1");
        xof.absorb(&coin);
        let mut g_weights = vec![[Tower128::ONE; 4]; count];
        for g_weights_k_item in g_weights[..count].iter_mut() {
            for m in 1..4 {
                let mut gb = [0u8; 16];
                xof.squeeze(&mut gb);
                (*g_weights_k_item)[m] = Tower128(u128::from_le_bytes(gb) | 1);
            }
        }

        let mut diffs = vec![vec![Tower128::ZERO; count]; n];
        for j in 0..n {
            for k in 0..count {
                let mut r_comb = r_masks[j][k][0];
                for m in 1..4 {
                    r_comb = r_comb.add(g_weights[k][m].mul(r_masks[j][k][m]));
                }
                diffs[j][k] = vals_per_party[j][k].add(r_comb);
                wipe_tower128(&mut r_masks[j][k]);
            }
            wipe_u64s(&mut choice_words[j]);
        }

        for i in 0..n {
            for j in 0..n {
                if i == j {
                    continue;
                }
                for k in 0..count {
                    let d = diffs[j][k];
                    for lane in 0..2 {
                        let mut k_comb = raw_k[i][j][k][lane][0];
                        let mut m_comb = raw_m[i][j][k][lane][0];
                        for m in 1..4 {
                            let g = g_weights[k][m];
                            k_comb = k_comb.add(g.mul(raw_k[i][j][k][lane][m]));
                            m_comb = m_comb.add(g.mul(raw_m[i][j][k][lane][m]));
                        }
                        k_comb = k_comb.add(alphas[i][lane].mul(d));
                        out[i][k].keys[j][lane] = k_comb;
                        out[j][k].macs[i][lane] = m_comb;
                        wipe_tower128(&mut raw_k[i][j][k][lane]);
                        wipe_tower128(&mut raw_m[i][j][k][lane]);
                    }
                }
            }
        }
        Ok(out)
    }

    /// Transfer `depth` compressed 16-byte GGM copath siblings from Sender `s` to Receiver `r` via `OtMesh`.
    fn transfer_ggm_copath_via_ot(
        ot_mesh: &mut OtMesh,
        s: usize,
        r: usize,
        depth: usize,
        punctured_idx: usize,
        level_lr_xors: &[([u8; 16], [u8; 16])],
        party_rngs: &mut [PartyPrivateRng],
    ) -> Result<Vec<[u8; 16]>, PreprocessError> {
        let mut choice_word = 0u64;
        for lvl in 0..depth {
            let path_bit = (punctured_idx >> (depth - 1 - lvl)) & 1;
            // When `path_bit == 0` (puncture left), Receiver needs `R_xor` (`choice = 1`);
            // when `path_bit == 1` (puncture right), Receiver needs `L_xor` (`choice = 0`).
            let sib_choice = (path_bit ^ 1) as u64;
            choice_word |= sib_choice << lvl;
        }
        let (send_pads, recv_pads) =
            ot_mesh.run_correlated_ot_words(s, r, &[choice_word], party_rngs)?;
        let mut copath = Vec::with_capacity(depth);
        for lvl in 0..depth {
            let (p0, p1) = &send_pads[lvl];
            let mut ct0 = [0u8; 16];
            let mut ct1 = [0u8; 16];
            for b in 0..16 {
                ct0[b] = level_lr_xors[lvl].0[b] ^ p0[b];
                ct1[b] = level_lr_xors[lvl].1[b] ^ p1[b];
            }
            let sib_choice = ((choice_word >> lvl) & 1) == 1;
            let cmask = 0u8.wrapping_sub(black_box(sib_choice as u8));
            let mut out = [0u8; 16];
            for b in 0..16 {
                let sel = ct0[b] ^ (cmask & (ct0[b] ^ ct1[b]));
                out[b] = sel ^ recv_pads[lvl][b];
            }
            copath.push(out);
        }
        wipe_u64s(core::slice::from_mut(&mut choice_word));
        Ok(copath)
    }

    /// Namespace for sublinear Silent-OT / `SHAKE256` GGM Puncturable-PRF + QC-LPN `PCG` seed setup,
    /// zero-I/O local expansion, and 2-lane `Tower128` BDOZ batch MAC sacrifice (`2^{-256}` soundness).
    pub struct PcgSeedExpansion;

    impl PcgSeedExpansion {
        /// Interactive base-correlation setup generating compact `< 24 KB` [`PcgPartySeed`]s for
        /// `n = party_rngs.len()` parties (`tree_depth \in 14..=16`).
        pub fn setup_seeds(
            session_id: [u8; 32],
            tree_depth: usize,
            ot_mesh: &mut OtMesh,
            party_rngs: &mut [PartyPrivateRng],
        ) -> Result<Vec<PcgPartySeed>, PreprocessError> {
            Self::setup_seeds_with_fault(session_id, tree_depth, ot_mesh, party_rngs, |_, _| {})
        }

        /// Fault-injectable PCG seed setup for adversarial sacrifice unit testing.
        pub fn setup_seeds_with_fault<F>(
            session_id: [u8; 32],
            tree_depth: usize,
            ot_mesh: &mut OtMesh,
            party_rngs: &mut [PartyPrivateRng],
            mut fault_hook: F,
        ) -> Result<Vec<PcgPartySeed>, PreprocessError>
        where
            F: FnMut(usize, &mut Vec<u64>),
        {
            if !cfg!(test) {
                return Err(PreprocessError::ExperimentalSparsePcg);
            }
            if !(PCG_MIN_TREE_DEPTH..=PCG_MAX_TREE_DEPTH).contains(&tree_depth) {
                return Err(PreprocessError::PcgDepthOutOfRange { depth: tree_depth });
            }
            let n = party_rngs.len();
            if n < 2 || ot_mesh.n != n {
                return Err(PreprocessError::InvalidThreshold { t: 2, n });
            }

            let leaf_mask = (1usize << tree_depth) - 1;
            let tower_depth = PCG_MIN_TREE_DEPTH;
            let tower_leaf_mask = (1usize << tower_depth) - 1;

            let mut alphas = vec![[Tower128::ZERO; 2]; n];
            let mut diag_seeds = vec![[0u8; 32]; n];
            for i in 0..n {
                alphas[i] = [party_rngs[i].next_tower128(), party_rngs[i].next_tower128()];
                diag_seeds[i] = party_rngs[i].next_bytes32();
            }

            // Each party `r` chooses ONE sparse noise vector per bundle (`X, Y, Z` = 12 indices; `A0, A1` = 8 `(idx, beta)` pairs)
            let mut bin_p_stars = vec![[0usize; 3 * PCG_TREES_PER_BUNDLE]; n];
            let mut tow_p_stars = vec![[(0usize, Tower128::ZERO); 2 * PCG_TREES_PER_BUNDLE]; n];
            for r in 0..n {
                #[expect(
                    clippy::needless_range_loop,
                    reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows"
                )]
                for t_idx in 0..(3 * PCG_TREES_PER_BUNDLE) {
                    bin_p_stars[r][t_idx] = (party_rngs[r].next_u64() as usize) & leaf_mask;
                }
                #[expect(
                    clippy::needless_range_loop,
                    reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows"
                )]
                for t_idx in 0..(2 * PCG_TREES_PER_BUNDLE) {
                    let p_idx = (party_rngs[r].next_u64() as usize) & tower_leaf_mask;
                    let mut beta = party_rngs[r].next_tower128();
                    if beta.0 == 0 {
                        beta = Tower128::ONE;
                    }
                    tow_p_stars[r][t_idx] = (p_idx, beta);
                }
            }

            // Pre-authenticate `tow_p_stars[r][0..8].1` (`beta`) across all peers via LHL-amplified
            // `authenticate_tower128_batch` (`< 2^{-192}` selective-failure immunity; `beta` never enters raw OT!)
            let beta_vecs: Vec<Vec<Tower128>> = (0..n)
                .map(|r| {
                    (0..(2 * PCG_TREES_PER_BUNDLE))
                        .map(|t_idx| tow_p_stars[r][t_idx].1)
                        .collect()
                })
                .collect();
            let auth_betas =
                authenticate_tower128_batch(&session_id, ot_mesh, &alphas, &beta_vecs, party_rngs)?;

            let mut bin_send_trees: Vec<Vec<Vec<GgmSenderTreeSeed>>> = (0..n)
                .map(|_| (0..n).map(|_| Vec::new()).collect())
                .collect();
            let mut bin_recv_trees: Vec<Vec<Vec<GgmReceiverBinaryTreeSeed>>> = (0..n)
                .map(|_| (0..n).map(|_| Vec::new()).collect())
                .collect();
            let mut tow_send_trees: Vec<Vec<Vec<GgmSenderTreeSeed>>> = (0..n)
                .map(|_| (0..n).map(|_| Vec::new()).collect())
                .collect();
            let mut tow_recv_trees: Vec<Vec<Vec<GgmReceiverTowerTreeSeed>>> = (0..n)
                .map(|_| (0..n).map(|_| Vec::new()).collect())
                .collect();

            // Setup GGM copaths across all ordered pairs `(s, r)` (`s != r`)
            for s in 0..n {
                for r in 0..n {
                    if s == r {
                        continue;
                    }
                    // 12 Binary Subfield-VOLE GGM trees
                    let mut s_btrees = Vec::with_capacity(3 * PCG_TREES_PER_BUNDLE);
                    let mut r_btrees = Vec::with_capacity(3 * PCG_TREES_PER_BUNDLE);
                    #[expect(
                        clippy::needless_range_loop,
                        reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows"
                    )]
                    for t_idx in 0..(3 * PCG_TREES_PER_BUNDLE) {
                        let mut root = [0u8; 16];
                        party_rngs[s].fill_bytes(&mut root);
                        let tree_tag = ((s * 16 + r) as u8)
                            .wrapping_mul(31)
                            .wrapping_add(t_idx as u8);
                        let (leaf_tags, lr_xors) =
                            ggm_eval_sender_full(&session_id, tree_tag, tree_depth, &root);
                        let mut sum_s = [0u128; 2];
                        for lt in &leaf_tags {
                            sum_s[0] ^= lt[0];
                            sum_s[1] ^= lt[1];
                        }
                        let p_star = bin_p_stars[r][t_idx];
                        let copath = transfer_ggm_copath_via_ot(
                            ot_mesh, s, r, tree_depth, p_star, &lr_xors, party_rngs,
                        )?;
                        let corr = [
                            Tower128(sum_s[0] ^ alphas[s][0].0),
                            Tower128(sum_s[1] ^ alphas[s][1].0),
                        ];
                        s_btrees.push(GgmSenderTreeSeed { root_seed: root });
                        r_btrees.push(GgmReceiverBinaryTreeSeed {
                            punctured_idx: p_star as u16,
                            copath,
                            punctured_mac_corr: corr,
                        });
                    }
                    bin_send_trees[s][r] = s_btrees;
                    bin_recv_trees[r][s] = r_btrees;

                    // 8 Tower128 VOLE GGM trees (`depth = 14`): consume LHL-amplified `auth_betas` correlations
                    let mut s_ttrees = Vec::with_capacity(2 * PCG_TREES_PER_BUNDLE);
                    let mut r_ttrees = Vec::with_capacity(2 * PCG_TREES_PER_BUNDLE);

                    for t_idx in 0..(2 * PCG_TREES_PER_BUNDLE) {
                        let mut root = [0u8; 16];
                        party_rngs[s].fill_bytes(&mut root);
                        let tree_tag = 0x80u8
                            .wrapping_add(((s * 16 + r) as u8).wrapping_mul(17))
                            .wrapping_add(t_idx as u8);
                        let (leaf_tags, lr_xors) =
                            ggm_eval_sender_full(&session_id, tree_tag, tower_depth, &root);
                        let (p_star, beta) = tow_p_stars[r][t_idx];
                        let copath = transfer_ggm_copath_via_ot(
                            ot_mesh,
                            s,
                            r,
                            tower_depth,
                            p_star,
                            &lr_xors,
                            party_rngs,
                        )?;

                        // From `auth_betas`: `k_ole[lane] ^ m_ole[lane] == alphas[s][lane] * beta`
                        let k_ole = [
                            auth_betas[s][t_idx].keys[r][0].0,
                            auth_betas[s][t_idx].keys[r][1].0,
                        ];
                        let m_ole = [
                            auth_betas[r][t_idx].macs[s][0].0,
                            auth_betas[r][t_idx].macs[s][1].0,
                        ];

                        // The full sender tree already contains the punctured leaf.
                        let p_mac = [
                            Tower128(leaf_tags[p_star][0] ^ k_ole[0] ^ m_ole[0]),
                            Tower128(leaf_tags[p_star][1] ^ k_ole[1] ^ m_ole[1]),
                        ];

                        s_ttrees.push(GgmSenderTreeSeed { root_seed: root });
                        r_ttrees.push(GgmReceiverTowerTreeSeed {
                            punctured_idx: p_star as u16,
                            punctured_beta: beta,
                            copath,
                            punctured_mac_val: p_mac,
                        });
                    }
                    tow_send_trees[s][r] = s_ttrees;
                    tow_recv_trees[r][s] = r_ttrees;
                }
            }

            // Compute each party's local LPN noise vectors `(x_i, y_i, z_i)` & companion `(at0_i, at1_i)`
            // strictly from its own punctured indices `(bin_p_stars[i], tow_p_stars[i])` (`0` cross-party read!)
            let sched_x =
                QcLpnParitySchedule::derive(&session_id, b"BIN_X", tree_depth, PCG_NUM_WORDS);
            let sched_y =
                QcLpnParitySchedule::derive(&session_id, b"BIN_Y", tree_depth, PCG_NUM_WORDS);
            let sched_z =
                QcLpnParitySchedule::derive(&session_id, b"BIN_Z", tree_depth, PCG_NUM_WORDS);
            let sched_a0 =
                QcLpnParitySchedule::derive(&session_id, b"TOW_A0", tower_depth, PCG_NUM_WORDS);
            let sched_a1 =
                QcLpnParitySchedule::derive(&session_id, b"TOW_A1", tower_depth, PCG_NUM_WORDS);

            let zero_bin_leaves = vec![vec![[0u128; 2]; 1 << tree_depth]; PCG_TREES_PER_BUNDLE];
            let zero_tow_leaves = vec![vec![[0u128; 2]; 1 << tower_depth]; PCG_TREES_PER_BUNDLE];

            let mut x_per_party = Vec::with_capacity(n);
            let mut y_per_party = Vec::with_capacity(n);
            let mut z_per_party = Vec::with_capacity(n);
            let mut at0_words = Vec::with_capacity(n);
            let mut at1_words = Vec::with_capacity(n);

            for i in 0..n {
                let px: [usize; 4] =
                    core::array::from_fn(|array_index| (bin_p_stars[i][0..4])[array_index]);
                let py: [usize; 4] =
                    core::array::from_fn(|array_index| (bin_p_stars[i][4..8])[array_index]);
                let pz: [usize; 4] =
                    core::array::from_fn(|array_index| (bin_p_stars[i][8..12])[array_index]);
                let (xi, _) =
                    sched_x.compress_binary_bundle(PCG_NUM_WORDS, &zero_bin_leaves, Some(px));
                let (yi, _) =
                    sched_y.compress_binary_bundle(PCG_NUM_WORDS, &zero_bin_leaves, Some(py));
                let (zi, _) =
                    sched_z.compress_binary_bundle(PCG_NUM_WORDS, &zero_bin_leaves, Some(pz));
                x_per_party.push(xi);
                y_per_party.push(yi);
                z_per_party.push(zi);

                let pa0: [(usize, Tower128); 4] =
                    core::array::from_fn(|array_index| (tow_p_stars[i][0..4])[array_index]);
                let pa1: [(usize, Tower128); 4] =
                    core::array::from_fn(|array_index| (tow_p_stars[i][4..8])[array_index]);
                let (va0, _) =
                    sched_a0.compress_tower_bundle(PCG_NUM_WORDS, &zero_tow_leaves, Some(pa0));
                let (va1, _) =
                    sched_a1.compress_tower_bundle(PCG_NUM_WORDS, &zero_tow_leaves, Some(pa1));
                let mut w0 = vec![[0u128; 64]; PCG_NUM_WORDS];
                let mut w1 = vec![[0u128; 64]; PCG_NUM_WORDS];
                for k in 0..PCG_NUM_WORDS {
                    for bit in 0..64 {
                        w0[k][bit] = va0[64 * k + bit].0;
                        w1[k][bit] = va1[64 * k + bit].0;
                    }
                }
                at0_words.push(w0);
                at1_words.push(w1);
            }

            // Dealerless pairwise OT computes:
            // (1) `w_bool[i]` additive shares of `x & y` -> open `delta_words = \bigoplus_i (z_i ^ w_bool_i)` (`8,200 B`)
            // (2) `ct0[i], ct1[i]` additive shares of `\tilde{A}_{L,\ell} * y_\ell` -> sum over `\ell` and authenticate (`2` scalars!)
            let (mut w_bool, mut ct0, mut ct1) = pairwise_boolean_and_mascot_companions(
                ot_mesh,
                &x_per_party,
                &y_per_party,
                &at0_words,
                &at1_words,
                party_rngs,
            )?;
            let mut delta_words = vec![0u64; PCG_NUM_WORDS];
            let mut csum_vals_per_party = vec![vec![Tower128::ZERO; 2]; n];
            for i in 0..n {
                let mut d_i: Vec<u64> = (0..PCG_NUM_WORDS)
                    .map(|k| z_per_party[i][k] ^ w_bool[i][k])
                    .collect();
                fault_hook(i, &mut d_i);
                for k in 0..PCG_NUM_WORDS {
                    delta_words[k] ^= d_i[k];
                    for bit in 0..64 {
                        csum_vals_per_party[i][0].0 ^= ct0[i][k][bit];
                        csum_vals_per_party[i][1].0 ^= ct1[i][k][bit];
                    }
                }
                wipe_u64s(&mut d_i);
                wipe_u64s(&mut w_bool[i]);
                wipe_u64s(&mut x_per_party[i]);
                wipe_u64s(&mut y_per_party[i]);
                wipe_u64s(&mut z_per_party[i]);
                ct0[i].clear();
                ct1[i].clear();
            }
            let mut auth_csums = authenticate_tower128_batch(
                &session_id,
                ot_mesh,
                &alphas,
                &csum_vals_per_party,
                party_rngs,
            )?;

            // Also generate `PCG_NUM_TOWER_TRIPLES` (`8`) + `PCG_NUM_TOWER_TRIPLES` (`8` sacrifice companions)
            // 128-bit `Tower128` Beaver triples via LHL-amplified dealerless `pairwise_ole_tower128` + sacrifice!
            let tow_batch = PCG_NUM_TOWER_TRIPLES;
            let mut ta_raw = vec![vec![Tower128::ZERO; 2 * tow_batch]; n];
            let mut tb_raw = vec![vec![Tower128::ZERO; tow_batch]; n];
            for i in 0..n {
                #[expect(
                    clippy::needless_range_loop,
                    reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows"
                )]
                for k in 0..(2 * tow_batch) {
                    ta_raw[i][k] = party_rngs[i].next_tower128();
                }
                #[expect(
                    clippy::needless_range_loop,
                    reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows"
                )]
                for k in 0..tow_batch {
                    tb_raw[i][k] = party_rngs[i].next_tower128();
                }
            }
            let mut tb_dup = Vec::with_capacity(n);
            for tb_raw_i_item in tb_raw[..n].iter() {
                let mut v = Vec::with_capacity(2 * tow_batch);
                v.extend_from_slice(tb_raw_i_item);
                v.extend_from_slice(tb_raw_i_item);
                tb_dup.push(v);
            }
            let tc_raw = pairwise_ole_tower128(&session_id, ot_mesh, &ta_raw, &tb_dup, party_rngs)?;
            let mut auth_ta =
                authenticate_tower128_batch(&session_id, ot_mesh, &alphas, &ta_raw, party_rngs)?;
            let mut auth_tb =
                authenticate_tower128_batch(&session_id, ot_mesh, &alphas, &tb_raw, party_rngs)?;
            let mut auth_tc =
                authenticate_tower128_batch(&session_id, ot_mesh, &alphas, &tc_raw, party_rngs)?;

            // Immediate committed sacrifice of the 8 companion `Tower128` triples `[tow_batch .. 2*tow_batch]`
            let coin = run_commit_and_open_coin(
                &session_id,
                b"PCG_TOW_TRIPLE_SAC",
                &[0x5A; 32],
                party_rngs,
            )?;
            let rho_tow = Tower128(
                u128::from_le_bytes(core::array::from_fn(|array_index| {
                    (coin[0..16])[array_index]
                })) | 1,
            );
            for k in 0..tow_batch {
                let u_shares: Vec<PcgAuthTower128Share> = (0..n)
                    .map(|p| {
                        let mut s = auth_ta[p][k].scale(rho_tow);
                        s.xor_assign(&auth_ta[p][tow_batch + k]);
                        s
                    })
                    .collect();
                let u_open = open_and_verify_pcg_tower128(
                    &session_id,
                    &alphas,
                    &u_shares,
                    "pcg_tow_u",
                    party_rngs,
                )?;
                let w_shares: Vec<PcgAuthTower128Share> = (0..n)
                    .map(|p| {
                        let mut s = auth_tc[p][k].scale(rho_tow);
                        s.xor_assign(&auth_tc[p][tow_batch + k]);
                        s.xor_assign(&auth_tb[p][k].scale(u_open));
                        s
                    })
                    .collect();
                let w_open = open_and_verify_pcg_tower128(
                    &session_id,
                    &alphas,
                    &w_shares,
                    "pcg_tow_w",
                    party_rngs,
                )?;
                if !w_open.ct_eq(Tower128::ZERO) {
                    return Err(PreprocessError::SacrificeResidualNonZero {
                        phase: "pcg_tower_triples",
                    });
                }
            }

            // Package `< 24 KB` `PcgPartySeed` per party and assert wire budget
            let mut seeds = Vec::with_capacity(n);
            for i in 0..n {
                let mut peers = Vec::with_capacity(n - 1);
                for j in 0..n {
                    if i == j {
                        continue;
                    }
                    peers.push(PcgPeerSeedMaterial {
                        peer_id: j as u16,
                        bin_sender_trees: core::mem::take(&mut bin_send_trees[i][j]),
                        bin_receiver_trees: core::mem::take(&mut bin_recv_trees[i][j]),
                        tower_sender_trees: core::mem::take(&mut tow_send_trees[i][j]),
                        tower_receiver_trees: core::mem::take(&mut tow_recv_trees[i][j]),
                    });
                }
                let tower_triples: Vec<PcgAuthTower128TripleShare> = auth_ta[i]
                    .drain(..)
                    .zip(auth_tb[i].drain(..))
                    .zip(auth_tc[i].drain(..))
                    .map(|((a, b), c)| PcgAuthTower128TripleShare { a, b, c })
                    .collect();
                let seed = PcgPartySeed {
                    session_id,
                    party_id: i,
                    num_parties: n,
                    tree_depth,
                    mac_alpha: alphas[i],
                    diag_mask_seed: diag_seeds[i],
                    peers,
                    delta_words: delta_words.clone(),
                    tilde_c_sums: core::array::from_fn(|_| auth_csums[i].remove(0)),
                    tower_triples,
                };
                seeds.push(seed);
            }
            Ok(seeds)
        }

        /// End-to-end committed 2-lane `Tower128` BDOZ batch MAC sacrifice (`2^{-256}` soundness) verifying
        /// ALL `65,600` locally expanded Boolean Beaver triples + `8` `Tower128` triples with **zero**
        /// leakage of surviving `(a_\ell, b_\ell, c_\ell)` triples!
        pub fn verify_2lane_bdoz_sacrifice(
            vaults: &[PcgExpandedPartyVault],
            party_rngs: &mut [PartyPrivateRng],
        ) -> Result<(), PreprocessError> {
            let n = vaults.len();
            if n < 2 || party_rngs.len() != n {
                return Err(PreprocessError::InvalidThreshold { t: 2, n });
            }
            let session_id = vaults[0].session_id;
            let alphas: Vec<[Tower128; 2]> = vaults.iter().map(|v| v.mac_alpha).collect();

            // Joint commit-and-open public coin AFTER `PcgPartySeed` expansion
            let coin = run_commit_and_open_coin(
                &session_id,
                b"PCG_BOOL_2LANE_SAC",
                &[0xA5; 32],
                party_rngs,
            )?;
            let mut xof = Shake256Xof::new_shake256();
            xof.absorb(b"QSAG.PCG.SAC.RHOS/v1");
            xof.absorb(&session_id);
            xof.absorb(&coin);
            let num_triples = vaults[0].num_boolean_triples();
            let mut rho_bytes = vec![0u8; num_triples * 32];
            xof.squeeze(&mut rho_bytes);

            // Two independent sacrifice passes (`sac_lane = 0, 1`), each over `Tower128` (`2^{-128 * 2} = 2^{-256}`!)
            for sac_lane in 0..2 {
                // Step 1: Commit-before-open ALL `65,600` masked openings `U_{sac_lane, \ell}` per party,
                // then verify BDOZ MACs on every individual `U_\ell` via committed random linear combination!
                let mut u_shares_per_party = vec![vec![Tower128::ZERO; num_triples]; n];
                let mut u_salts = Vec::with_capacity(n);
                let mut u_coms = Vec::with_capacity(n);
                for p in 0..n {
                    let mut u_hasher = Cshake256Xof::new(b"QSAG.PCG.SAC.U.OPEN.COM/v1");
                    u_hasher.absorb(&session_id);
                    u_hasher.absorb(&[sac_lane as u8]);
                    u_hasher.absorb(&(p as u64).to_be_bytes());
                    for k in 0..vaults[0].bool_triple_words.len() {
                        let bw = &vaults[p].bool_triple_words[k];
                        for bit in 0..64 {
                            let ell = 64 * k + bit;
                            let off = (ell * 2 + sac_lane) * 16;
                            let mut rho = Tower128(u128::from_le_bytes(core::array::from_fn(
                                |array_index| (rho_bytes[off..off + 16])[array_index],
                            )));
                            if rho.0 == 0 {
                                rho = Tower128::ONE;
                            }
                            let a_bit = ((bw.a_word >> bit) & 1) == 1;
                            let a_val = if a_bit { rho } else { Tower128::ZERO };
                            let u_p_val = a_val.add(vaults[p].companion_a[sac_lane][ell].value);
                            u_shares_per_party[p][ell] = u_p_val;
                            u_hasher.absorb(&u_p_val.0.to_le_bytes());
                        }
                    }
                    let salt = party_rngs[p].next_bytes32();
                    u_hasher.absorb(&salt);
                    let mut com = [0u8; 32];
                    u_hasher.squeeze(&mut com);
                    u_salts.push(salt);
                    u_coms.push(com);
                }

                // Verify commitments on `u_shares_per_party` before opening & sampling `chi`!
                let mut u_trans_xof = Cshake256Xof::new(b"QSAG.PCG.SAC.U.TRANS/v1");
                for p in 0..n {
                    let mut u_hasher = Cshake256Xof::new(b"QSAG.PCG.SAC.U.OPEN.COM/v1");
                    u_hasher.absorb(&session_id);
                    u_hasher.absorb(&[sac_lane as u8]);
                    u_hasher.absorb(&(p as u64).to_be_bytes());
                    #[expect(
                        clippy::needless_range_loop,
                        reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows"
                    )]
                    for ell in 0..num_triples {
                        let b16 = u_shares_per_party[p][ell].0.to_le_bytes();
                        u_hasher.absorb(&b16);
                        u_trans_xof.absorb(&b16);
                    }
                    u_hasher.absorb(&u_salts[p]);
                    wipe_bytes32(&mut u_salts[p]);
                    let mut exp = [0u8; 32];
                    u_hasher.squeeze(&mut exp);
                    if !ct_eq_bytes32(&exp, &u_coms[p]) {
                        return Err(PreprocessError::ShareCommitMismatch {
                            phase: "pcg_bool_sac_u",
                            party_id: p,
                        });
                    }
                }
                let mut u_trans_digest = [0u8; 32];
                u_trans_xof.squeeze(&mut u_trans_digest);

                // Sample `chi` via `Π_coin` *after* all `u_shares_per_party` are committed & opened!
                let chi_coin = run_commit_and_open_coin(
                    &session_id,
                    b"PCG_SAC_CHI_COIN",
                    &u_trans_digest,
                    party_rngs,
                )?;
                let mut chi_xof = Shake256Xof::new_shake256();
                chi_xof.absorb(b"QSAG.PCG.SAC.MAC_BATCH/v1");
                chi_xof.absorb(&chi_coin);
                chi_xof.absorb(&[sac_lane as u8]);
                let mut chi_bytes = vec![0u8; num_triples * 16];
                chi_xof.squeeze(&mut chi_bytes);

                let mut u_opened = vec![Tower128::ZERO; num_triples];
                let mut mac_batch_sh: Vec<PcgAuthTower128Share> =
                    (0..n).map(|_| PcgAuthTower128Share::zero(n)).collect();

                for k in 0..vaults[0].bool_triple_words.len() {
                    for bit in 0..64 {
                        let ell = 64 * k + bit;
                        let off = (ell * 2 + sac_lane) * 16;
                        let mut rho =
                            Tower128(u128::from_le_bytes(core::array::from_fn(|array_index| {
                                (rho_bytes[off..off + 16])[array_index]
                            })));
                        if rho.0 == 0 {
                            rho = Tower128::ONE;
                        }
                        let chi = Tower128(
                            u128::from_le_bytes(core::array::from_fn(|array_index| {
                                (chi_bytes[16 * ell..16 * (ell + 1)])[array_index]
                            })) | 1,
                        );

                        let mut u_sum = Tower128::ZERO;
                        for p in 0..n {
                            let bw = &vaults[p].bool_triple_words[k];
                            let comp = &vaults[p].companion_a[sac_lane][ell];
                            let u_p_val = u_shares_per_party[p][ell];
                            u_sum = u_sum.add(u_p_val);

                            mac_batch_sh[p].value = mac_batch_sh[p].value.add(u_p_val.mul(chi));
                            let scale_rho_chi = rho.mul(chi);
                            for q in 0..n {
                                for m_lane in 0..2 {
                                    let um = bw.a_macs[q][bit][m_lane]
                                        .mul(scale_rho_chi)
                                        .add(comp.macs[q][m_lane].mul(chi));
                                    let uk = bw.a_keys[q][bit][m_lane]
                                        .mul(scale_rho_chi)
                                        .add(comp.keys[q][m_lane].mul(chi));
                                    mac_batch_sh[p].macs[q][m_lane] =
                                        mac_batch_sh[p].macs[q][m_lane].add(um);
                                    mac_batch_sh[p].keys[q][m_lane] =
                                        mac_batch_sh[p].keys[q][m_lane].add(uk);
                                }
                            }
                        }
                        u_opened[ell] = u_sum;
                    }
                }

                // Verify 2-lane BDOZ MACs on the entire `U_{sac_lane, 0..65600}` vector before checking `W`
                let u_batch_check = open_and_verify_pcg_tower128(
                    &session_id,
                    &alphas,
                    &mac_batch_sh,
                    "pcg_bool_sac_u",
                    party_rngs,
                )?;
                let mut expected_u_batch = Tower128::ZERO;
                for ell in 0..num_triples {
                    let chi = Tower128(
                        u128::from_le_bytes(core::array::from_fn(|array_index| {
                            (chi_bytes[16 * ell..16 * (ell + 1)])[array_index]
                        })) | 1,
                    );
                    expected_u_batch = expected_u_batch.add(u_opened[ell].mul(chi));
                }
                if !u_batch_check.ct_eq(expected_u_batch) {
                    return Err(PreprocessError::MacCheckFailed {
                        phase: "pcg_bool_sac_u",
                        accused_party: None,
                    });
                }

                // Step 2: Form authenticated zero-check share
                // `[W_{sac_lane}] = \bigoplus_\ell \rho_{sac_lane,\ell} [c_\ell] \oplus [\tilde{C}_{sac_lane,sum}] \oplus \bigoplus_\ell U_{sac_lane,\ell} [b_\ell]`
                // Commit-before-open `[W_{sac_lane}]` with full 2-lane BDOZ MAC verification and assert `W_{sac_lane} == 0`!
                let mut w_shares: Vec<PcgAuthTower128Share> = (0..n)
                    .map(|p| vaults[p].companion_c_sums[sac_lane].scale(Tower128::ONE))
                    .collect();
                for (k, _) in vaults[0].bool_triple_words.iter().enumerate() {
                    for bit in 0..64 {
                        let ell = 64 * k + bit;
                        let off = (ell * 2 + sac_lane) * 16;
                        let mut rho =
                            Tower128(u128::from_le_bytes(core::array::from_fn(|array_index| {
                                (rho_bytes[off..off + 16])[array_index]
                            })));
                        if rho.0 == 0 {
                            rho = Tower128::ONE;
                        }
                        let u_ell = u_opened[ell];
                        for p in 0..n {
                            let bw = &vaults[p].bool_triple_words[k];
                            let c_bit = ((bw.c_word >> bit) & 1) == 1;
                            let b_bit = ((bw.b_word >> bit) & 1) == 1;
                            let term = (if c_bit { rho } else { Tower128::ZERO }).add(if b_bit {
                                u_ell
                            } else {
                                Tower128::ZERO
                            });
                            w_shares[p].value = w_shares[p].value.add(term);
                            for q in 0..n {
                                for m_lane in 0..2 {
                                    let wm = bw.c_macs[q][bit][m_lane]
                                        .mul(rho)
                                        .add(bw.b_macs[q][bit][m_lane].mul(u_ell));
                                    let wk = bw.c_keys[q][bit][m_lane]
                                        .mul(rho)
                                        .add(bw.b_keys[q][bit][m_lane].mul(u_ell));
                                    w_shares[p].macs[q][m_lane] =
                                        w_shares[p].macs[q][m_lane].add(wm);
                                    w_shares[p].keys[q][m_lane] =
                                        w_shares[p].keys[q][m_lane].add(wk);
                                }
                            }
                        }
                    }
                }

                let w_open = open_and_verify_pcg_tower128(
                    &session_id,
                    &alphas,
                    &w_shares,
                    "pcg_bool_sac_w",
                    party_rngs,
                )?;
                if !w_open.ct_eq(Tower128::ZERO) {
                    return Err(PreprocessError::SacrificeResidualNonZero {
                        phase: "pcg_boolean_triples",
                    });
                }
            }
            Ok(())
        }
    }

    /// Commit-before-open a 2-lane `Tower128` BDOZ-authenticated share across `n` parties and verify
    /// EVERY pairwise MAC tag (`macs[q][lane] ^ keys[p][lane] == alphas[q][lane] * shares[p].value`).
    fn open_and_verify_pcg_tower128(
        session_id: &[u8; 32],
        alphas: &[[Tower128; 2]],
        shares: &[PcgAuthTower128Share],
        phase: &'static str,
        party_rngs: &mut [PartyPrivateRng],
    ) -> Result<Tower128, PreprocessError> {
        let n = shares.len();
        if party_rngs.len() != n || alphas.len() != n {
            return Err(PreprocessError::InvalidThreshold { t: 2, n });
        }
        // Round 1: Commit to `(value, macs[0..n])` before opening (`0` rushing cancellation!)
        let mut salts = Vec::with_capacity(n);
        let mut coms = Vec::with_capacity(n);
        for p in 0..n {
            let salt = party_rngs[p].next_bytes32();
            let mut xof = Cshake256Xof::new(b"QSAG.PCG.T128.OPEN.COM/v1");
            xof.absorb(session_id);
            xof.absorb(phase.as_bytes());
            xof.absorb(&(p as u64).to_be_bytes());
            xof.absorb(&shares[p].value.0.to_le_bytes());
            for mac in shares[p].macs.iter().take(n) {
                xof.absorb(&mac[0].0.to_le_bytes());
                xof.absorb(&mac[1].0.to_le_bytes());
            }
            xof.absorb(&salt);
            let mut com = [0u8; 32];
            xof.squeeze(&mut com);
            salts.push(salt);
            coms.push(com);
        }
        // Round 2: Verify commitments, then verify every pairwise 2-lane BDOZ MAC
        for p in 0..n {
            let mut xof = Cshake256Xof::new(b"QSAG.PCG.T128.OPEN.COM/v1");
            xof.absorb(session_id);
            xof.absorb(phase.as_bytes());
            xof.absorb(&(p as u64).to_be_bytes());
            xof.absorb(&shares[p].value.0.to_le_bytes());
            for mac in shares[p].macs.iter().take(n) {
                xof.absorb(&mac[0].0.to_le_bytes());
                xof.absorb(&mac[1].0.to_le_bytes());
            }
            xof.absorb(&salts[p]);
            wipe_bytes32(&mut salts[p]);
            let mut exp = [0u8; 32];
            xof.squeeze(&mut exp);
            if !ct_eq_bytes32(&exp, &coms[p]) {
                return Err(PreprocessError::ShareCommitMismatch { phase, party_id: p });
            }
        }

        let mut sum = Tower128::ZERO;
        for p in 0..n {
            sum = sum.add(shares[p].value);
            for verifier_q in 0..n {
                for (lane, alpha) in alphas[verifier_q].iter().enumerate() {
                    let lhs =
                        shares[p].macs[verifier_q][lane].add(shares[verifier_q].keys[p][lane]);
                    let rhs = alpha.mul(shares[p].value);
                    if !lhs.ct_eq(rhs) {
                        return Err(PreprocessError::MacCheckFailed {
                            phase,
                            accused_party: Some(p),
                        });
                    }
                }
            }
        }
        Ok(sum)
    }

    fn write_auth_tower128_share(out: &mut Vec<u8>, sh: &PcgAuthTower128Share) {
        out.extend_from_slice(&sh.value.0.to_le_bytes());
        let n = sh.macs.len();
        out.extend_from_slice(&(n as u16).to_le_bytes());
        for q in 0..n {
            out.extend_from_slice(&sh.macs[q][0].0.to_le_bytes());
            out.extend_from_slice(&sh.macs[q][1].0.to_le_bytes());
            out.extend_from_slice(&sh.keys[q][0].0.to_le_bytes());
            out.extend_from_slice(&sh.keys[q][1].0.to_le_bytes());
        }
    }

    fn read_auth_tower128_share(
        bytes: &[u8],
        cur: &mut usize,
    ) -> Result<PcgAuthTower128Share, PreprocessError> {
        if *cur + 18 > bytes.len() {
            return Err(PreprocessError::PcgInvalidWireSeed);
        }
        let value = Tower128(u128::from_le_bytes(core::array::from_fn(|array_index| {
            (bytes[*cur..*cur + 16])[array_index]
        })));
        *cur += 16;
        let n = u16::from_le_bytes([bytes[*cur], bytes[*cur + 1]]) as usize;
        *cur += 2;
        validate_frame_count(n, 64, bytes.len() - *cur)?;
        let mut macs = vec![[Tower128::ZERO; 2]; n];
        let mut keys = vec![[Tower128::ZERO; 2]; n];
        for q in 0..n {
            macs[q][0] = Tower128(u128::from_le_bytes(core::array::from_fn(|array_index| {
                (bytes[*cur..*cur + 16])[array_index]
            })));
            *cur += 16;
            macs[q][1] = Tower128(u128::from_le_bytes(core::array::from_fn(|array_index| {
                (bytes[*cur..*cur + 16])[array_index]
            })));
            *cur += 16;
            keys[q][0] = Tower128(u128::from_le_bytes(core::array::from_fn(|array_index| {
                (bytes[*cur..*cur + 16])[array_index]
            })));
            *cur += 16;
            keys[q][1] = Tower128(u128::from_le_bytes(core::array::from_fn(|array_index| {
                (bytes[*cur..*cur + 16])[array_index]
            })));
            *cur += 16;
        }
        Ok(PcgAuthTower128Share { value, macs, keys })
    }

    impl PcgPartySeed {
        /// Serialize this compact PCG seed to canonical wire bytes (`< 24 KB` for 2–3 parties).
        pub fn to_wire_bytes(&self) -> Vec<u8> {
            let mut out = Vec::with_capacity(16 * 1024);
            out.extend_from_slice(PCG_WIRE_MAGIC);
            out.extend_from_slice(&self.session_id);
            out.extend_from_slice(&(self.party_id as u16).to_le_bytes());
            out.extend_from_slice(&(self.num_parties as u16).to_le_bytes());
            out.push(self.tree_depth as u8);
            out.extend_from_slice(&self.mac_alpha[0].0.to_le_bytes());
            out.extend_from_slice(&self.mac_alpha[1].0.to_le_bytes());
            out.extend_from_slice(&self.diag_mask_seed);

            out.extend_from_slice(&(self.peers.len() as u16).to_le_bytes());
            for peer in &self.peers {
                out.extend_from_slice(&peer.peer_id.to_le_bytes());
                for st in &peer.bin_sender_trees {
                    out.extend_from_slice(&st.root_seed);
                }
                for rt in &peer.bin_receiver_trees {
                    out.extend_from_slice(&rt.punctured_idx.to_le_bytes());
                    out.extend_from_slice(&rt.punctured_mac_corr[0].0.to_le_bytes());
                    out.extend_from_slice(&rt.punctured_mac_corr[1].0.to_le_bytes());
                    for node in &rt.copath {
                        out.extend_from_slice(node);
                    }
                }
                for st in &peer.tower_sender_trees {
                    out.extend_from_slice(&st.root_seed);
                }
                for rt in &peer.tower_receiver_trees {
                    out.extend_from_slice(&rt.punctured_idx.to_le_bytes());
                    out.extend_from_slice(&rt.punctured_beta.0.to_le_bytes());
                    out.extend_from_slice(&rt.punctured_mac_val[0].0.to_le_bytes());
                    out.extend_from_slice(&rt.punctured_mac_val[1].0.to_le_bytes());
                    for node in &rt.copath {
                        out.extend_from_slice(node);
                    }
                }
            }

            out.extend_from_slice(&(self.delta_words.len() as u32).to_le_bytes());
            for &dw in &self.delta_words {
                out.extend_from_slice(&dw.to_le_bytes());
            }
            write_auth_tower128_share(&mut out, &self.tilde_c_sums[0]);
            write_auth_tower128_share(&mut out, &self.tilde_c_sums[1]);
            out.extend_from_slice(&(self.tower_triples.len() as u16).to_le_bytes());
            for tr in &self.tower_triples {
                write_auth_tower128_share(&mut out, &tr.a);
                write_auth_tower128_share(&mut out, &tr.b);
                write_auth_tower128_share(&mut out, &tr.c);
            }
            out
        }

        /// Deserialize a [`PcgPartySeed`] from canonical wire bytes.
        pub fn from_wire_bytes(bytes: &[u8]) -> Result<Self, PreprocessError> {
            if !cfg!(test) {
                return Err(PreprocessError::ExperimentalSparsePcg);
            }
            if bytes.len() > MAX_FRAME_BUDGET || bytes.len() < 111 || &bytes[0..8] != PCG_WIRE_MAGIC
            {
                return Err(PreprocessError::PcgInvalidWireSeed);
            }
            let mut session_id = [0u8; 32];
            session_id.copy_from_slice(&bytes[8..40]);
            let party_id = u16::from_le_bytes([bytes[40], bytes[41]]) as usize;
            let num_parties = u16::from_le_bytes([bytes[42], bytes[43]]) as usize;
            let tree_depth = bytes[44] as usize;
            if !(PCG_MIN_TREE_DEPTH..=PCG_MAX_TREE_DEPTH).contains(&tree_depth)
                || party_id >= num_parties
                || num_parties < 2
            {
                return Err(PreprocessError::PcgInvalidWireSeed);
            }
            let alpha0 = Tower128(u128::from_le_bytes(core::array::from_fn(|array_index| {
                (bytes[45..61])[array_index]
            })));
            let alpha1 = Tower128(u128::from_le_bytes(core::array::from_fn(|array_index| {
                (bytes[61..77])[array_index]
            })));
            let mut diag_mask_seed = [0u8; 32];
            diag_mask_seed.copy_from_slice(&bytes[77..109]);
            let num_peers = u16::from_le_bytes([bytes[109], bytes[110]]) as usize;
            if num_peers != num_parties - 1 {
                return Err(PreprocessError::PcgInvalidWireSeed);
            }
            let mut cur = 111usize;
            let tower_depth = PCG_MIN_TREE_DEPTH;

            let peer_bytes = 2
                + 3 * PCG_TREES_PER_BUNDLE * (16 + 2 + 32 + 16 * tree_depth)
                + 2 * PCG_TREES_PER_BUNDLE * (16 + 2 + 16 + 32 + 16 * tower_depth);
            validate_frame_count(num_peers, peer_bytes, bytes.len() - cur)?;
            let mut peers = Vec::with_capacity(num_peers);
            for _ in 0..num_peers {
                if cur + 2 > bytes.len() {
                    return Err(PreprocessError::PcgInvalidWireSeed);
                }
                let peer_id = u16::from_le_bytes([bytes[cur], bytes[cur + 1]]);
                cur += 2;

                let mut bin_sender_trees = Vec::with_capacity(3 * PCG_TREES_PER_BUNDLE);
                for _ in 0..(3 * PCG_TREES_PER_BUNDLE) {
                    if cur + 16 > bytes.len() {
                        return Err(PreprocessError::PcgInvalidWireSeed);
                    }
                    let mut root_seed = [0u8; 16];
                    root_seed.copy_from_slice(&bytes[cur..cur + 16]);
                    cur += 16;
                    bin_sender_trees.push(GgmSenderTreeSeed { root_seed });
                }

                let mut bin_receiver_trees = Vec::with_capacity(3 * PCG_TREES_PER_BUNDLE);
                for _ in 0..(3 * PCG_TREES_PER_BUNDLE) {
                    let need = 2 + 32 + 16 * tree_depth;
                    if cur + need > bytes.len() {
                        return Err(PreprocessError::PcgInvalidWireSeed);
                    }
                    let punctured_idx = u16::from_le_bytes([bytes[cur], bytes[cur + 1]]);
                    cur += 2;
                    let c0 = Tower128(u128::from_le_bytes(core::array::from_fn(|array_index| {
                        (bytes[cur..cur + 16])[array_index]
                    })));
                    cur += 16;
                    let c1 = Tower128(u128::from_le_bytes(core::array::from_fn(|array_index| {
                        (bytes[cur..cur + 16])[array_index]
                    })));
                    cur += 16;
                    let mut copath = Vec::with_capacity(tree_depth);
                    for _ in 0..tree_depth {
                        let mut node = [0u8; 16];
                        node.copy_from_slice(&bytes[cur..cur + 16]);
                        cur += 16;
                        copath.push(node);
                    }
                    bin_receiver_trees.push(GgmReceiverBinaryTreeSeed {
                        punctured_idx,
                        copath,
                        punctured_mac_corr: [c0, c1],
                    });
                }

                let mut tower_sender_trees = Vec::with_capacity(2 * PCG_TREES_PER_BUNDLE);
                for _ in 0..(2 * PCG_TREES_PER_BUNDLE) {
                    if cur + 16 > bytes.len() {
                        return Err(PreprocessError::PcgInvalidWireSeed);
                    }
                    let mut root_seed = [0u8; 16];
                    root_seed.copy_from_slice(&bytes[cur..cur + 16]);
                    cur += 16;
                    tower_sender_trees.push(GgmSenderTreeSeed { root_seed });
                }

                let mut tower_receiver_trees = Vec::with_capacity(2 * PCG_TREES_PER_BUNDLE);
                for _ in 0..(2 * PCG_TREES_PER_BUNDLE) {
                    let need = 2 + 16 + 32 + 16 * tower_depth;
                    if cur + need > bytes.len() {
                        return Err(PreprocessError::PcgInvalidWireSeed);
                    }
                    let punctured_idx = u16::from_le_bytes([bytes[cur], bytes[cur + 1]]);
                    cur += 2;
                    let punctured_beta =
                        Tower128(u128::from_le_bytes(core::array::from_fn(|array_index| {
                            (bytes[cur..cur + 16])[array_index]
                        })));
                    cur += 16;
                    let m0 = Tower128(u128::from_le_bytes(core::array::from_fn(|array_index| {
                        (bytes[cur..cur + 16])[array_index]
                    })));
                    cur += 16;
                    let m1 = Tower128(u128::from_le_bytes(core::array::from_fn(|array_index| {
                        (bytes[cur..cur + 16])[array_index]
                    })));
                    cur += 16;
                    let mut copath = Vec::with_capacity(tower_depth);
                    for _ in 0..tower_depth {
                        let mut node = [0u8; 16];
                        node.copy_from_slice(&bytes[cur..cur + 16]);
                        cur += 16;
                        copath.push(node);
                    }
                    tower_receiver_trees.push(GgmReceiverTowerTreeSeed {
                        punctured_idx,
                        punctured_beta,
                        copath,
                        punctured_mac_val: [m0, m1],
                    });
                }

                peers.push(PcgPeerSeedMaterial {
                    peer_id,
                    bin_sender_trees,
                    bin_receiver_trees,
                    tower_sender_trees,
                    tower_receiver_trees,
                });
            }

            if cur + 4 > bytes.len() {
                return Err(PreprocessError::PcgInvalidWireSeed);
            }
            let d_len = u32::from_le_bytes(core::array::from_fn(|array_index| {
                (bytes[cur..cur + 4])[array_index]
            })) as usize;
            cur += 4;
            if d_len != PCG_NUM_WORDS || cur + d_len * 8 > bytes.len() {
                return Err(PreprocessError::PcgInvalidWireSeed);
            }
            let mut delta_words = Vec::with_capacity(d_len);
            for _ in 0..d_len {
                delta_words.push(u64::from_le_bytes(core::array::from_fn(|array_index| {
                    (bytes[cur..cur + 8])[array_index]
                })));
                cur += 8;
            }
            let csum0 = read_auth_tower128_share(bytes, &mut cur)?;
            let csum1 = read_auth_tower128_share(bytes, &mut cur)?;
            if cur + 2 > bytes.len() {
                return Err(PreprocessError::PcgInvalidWireSeed);
            }
            let num_tow = u16::from_le_bytes([bytes[cur], bytes[cur + 1]]) as usize;
            cur += 2;
            validate_frame_count(num_tow, 3 * 18, bytes.len() - cur)?;
            let mut tower_triples = Vec::with_capacity(num_tow);
            for _ in 0..num_tow {
                let a = read_auth_tower128_share(bytes, &mut cur)?;
                let b = read_auth_tower128_share(bytes, &mut cur)?;
                let c = read_auth_tower128_share(bytes, &mut cur)?;
                tower_triples.push(PcgAuthTower128TripleShare { a, b, c });
            }
            if cur != bytes.len() {
                return Err(PreprocessError::PcgInvalidWireSeed);
            }
            Ok(Self {
                session_id,
                party_id,
                num_parties,
                tree_depth,
                mac_alpha: [alpha0, alpha1],
                diag_mask_seed,
                peers,
                delta_words,
                tilde_c_sums: [csum0, csum1],
                tower_triples,
            })
        }

        /// Expand this `< 24 KB` seed **locally with ZERO network I/O** (consuming the seed) into
        /// `65,600` (`> 65,536`) 2-lane `Tower128` BDOZ-authenticated Boolean Beaver triples +
        /// `8` authenticated 128-bit `Tower128` Beaver triples + sacrifice companion masks.
        pub fn expand_local(mut self) -> PcgExpandedPartyVault {
            let n = self.num_parties;
            let me = self.party_id;
            let tower_depth = PCG_MIN_TREE_DEPTH;

            let sched_x = QcLpnParitySchedule::derive(
                &self.session_id,
                b"BIN_X",
                self.tree_depth,
                PCG_NUM_WORDS,
            );
            let sched_y = QcLpnParitySchedule::derive(
                &self.session_id,
                b"BIN_Y",
                self.tree_depth,
                PCG_NUM_WORDS,
            );
            let sched_z = QcLpnParitySchedule::derive(
                &self.session_id,
                b"BIN_Z",
                self.tree_depth,
                PCG_NUM_WORDS,
            );
            let sched_a0 = QcLpnParitySchedule::derive(
                &self.session_id,
                b"TOW_A0",
                tower_depth,
                PCG_NUM_WORDS,
            );
            let sched_a1 = QcLpnParitySchedule::derive(
                &self.session_id,
                b"TOW_A1",
                tower_depth,
                PCG_NUM_WORDS,
            );

            let mut bool_triple_words: Vec<PcgAuthBoolTripleWord64> = (0..PCG_NUM_WORDS)
                .map(|_| PcgAuthBoolTripleWord64 {
                    a_word: 0,
                    b_word: 0,
                    c_word: 0,
                    a_macs: vec![[[Tower128::ZERO; 2]; 64]; n],
                    a_keys: vec![[[Tower128::ZERO; 2]; 64]; n],
                    b_macs: vec![[[Tower128::ZERO; 2]; 64]; n],
                    b_keys: vec![[[Tower128::ZERO; 2]; 64]; n],
                    c_macs: vec![[[Tower128::ZERO; 2]; 64]; n],
                    c_keys: vec![[[Tower128::ZERO; 2]; 64]; n],
                })
                .collect();

            let num_triples = PCG_NUM_BOOL_TRIPLES;
            let mut companion_a: [Vec<PcgAuthTower128Share>; 2] = [
                (0..num_triples)
                    .map(|_| PcgAuthTower128Share::zero(n))
                    .collect(),
                (0..num_triples)
                    .map(|_| PcgAuthTower128Share::zero(n))
                    .collect(),
            ];

            let mut my_bits_populated = false;
            for peer in &self.peers {
                let q = peer.peer_id as usize;

                // 1. Expand `me` as Sender (`keys[q]` authenticating peer `q`'s sparse vector under `me`'s `mac_alpha`)
                let mut s_leaves = Vec::with_capacity(3 * PCG_TREES_PER_BUNDLE);
                for (t_idx, tree) in peer.bin_sender_trees.iter().enumerate() {
                    let tree_tag = ((me * 16 + q) as u8)
                        .wrapping_mul(31)
                        .wrapping_add(t_idx as u8);
                    let (lt, _) = ggm_eval_sender_full(
                        &self.session_id,
                        tree_tag,
                        self.tree_depth,
                        &tree.root_seed,
                    );
                    s_leaves.push(lt);
                }
                let (_, kx) = sched_x.compress_binary_bundle(PCG_NUM_WORDS, &s_leaves[0..4], None);
                let (_, ky) = sched_y.compress_binary_bundle(PCG_NUM_WORDS, &s_leaves[4..8], None);
                let (_, kz) = sched_z.compress_binary_bundle(PCG_NUM_WORDS, &s_leaves[8..12], None);
                for k in 0..PCG_NUM_WORDS {
                    for bit in 0..64 {
                        for lane in 0..2 {
                            bool_triple_words[k].a_keys[q][bit][lane] = Tower128(kx[k][bit][lane]);
                            bool_triple_words[k].b_keys[q][bit][lane] = Tower128(ky[k][bit][lane]);
                            bool_triple_words[k].c_keys[q][bit][lane] = Tower128(kz[k][bit][lane]);
                        }
                    }
                }

                // 2. Expand `me` as Receiver (`macs[q]` authenticating `me`'s sparse vector under peer `q`'s `mac_alpha`)
                let mut r_leaves = Vec::with_capacity(3 * PCG_TREES_PER_BUNDLE);
                let mut p_indices = [0usize; 12];
                for (t_idx, p_indices_t_idx_item) in p_indices[..(3 * PCG_TREES_PER_BUNDLE)]
                    .iter_mut()
                    .enumerate()
                {
                    let rt = &peer.bin_receiver_trees[t_idx];
                    let p_star = rt.punctured_idx as usize;
                    *p_indices_t_idx_item = p_star;
                    let tree_tag = ((q * 16 + me) as u8)
                        .wrapping_mul(31)
                        .wrapping_add(t_idx as u8);
                    let lt = ggm_eval_receiver_punctured(
                        &self.session_id,
                        tree_tag,
                        self.tree_depth,
                        p_star,
                        &rt.copath,
                        (
                            [rt.punctured_mac_corr[0].0, rt.punctured_mac_corr[1].0],
                            true,
                        ),
                    );
                    r_leaves.push(lt);
                }
                let px: [usize; 4] =
                    core::array::from_fn(|array_index| (p_indices[0..4])[array_index]);
                let py: [usize; 4] =
                    core::array::from_fn(|array_index| (p_indices[4..8])[array_index]);
                let pz: [usize; 4] =
                    core::array::from_fn(|array_index| (p_indices[8..12])[array_index]);
                let (wx, mx) =
                    sched_x.compress_binary_bundle(PCG_NUM_WORDS, &r_leaves[0..4], Some(px));
                let (wy, my) =
                    sched_y.compress_binary_bundle(PCG_NUM_WORDS, &r_leaves[4..8], Some(py));
                let (wz, mz) =
                    sched_z.compress_binary_bundle(PCG_NUM_WORDS, &r_leaves[8..12], Some(pz));

                for k in 0..PCG_NUM_WORDS {
                    if !my_bits_populated {
                        bool_triple_words[k].a_word = wx[k];
                        bool_triple_words[k].b_word = wy[k];
                        bool_triple_words[k].c_word = wz[k];
                    }
                    for bit in 0..64 {
                        for lane in 0..2 {
                            bool_triple_words[k].a_macs[q][bit][lane] = Tower128(mx[k][bit][lane]);
                            bool_triple_words[k].b_macs[q][bit][lane] = Tower128(my[k][bit][lane]);
                            bool_triple_words[k].c_macs[q][bit][lane] = Tower128(mz[k][bit][lane]);
                        }
                    }
                }

                // 3. Expand Tower128 companion bundles (`A0`, `A1`) as Sender & Receiver
                let mut ts_leaves = Vec::with_capacity(2 * PCG_TREES_PER_BUNDLE);
                for (t_idx, tree) in peer.tower_sender_trees.iter().enumerate() {
                    let tree_tag = 0x80u8
                        .wrapping_add(((me * 16 + q) as u8).wrapping_mul(17))
                        .wrapping_add(t_idx as u8);
                    let (lt, _) = ggm_eval_sender_full(
                        &self.session_id,
                        tree_tag,
                        tower_depth,
                        &tree.root_seed,
                    );
                    ts_leaves.push(lt);
                }
                let (_, tk0) =
                    sched_a0.compress_tower_bundle(PCG_NUM_WORDS, &ts_leaves[0..4], None);
                let (_, tk1) =
                    sched_a1.compress_tower_bundle(PCG_NUM_WORDS, &ts_leaves[4..8], None);

                let mut tr_leaves = Vec::with_capacity(2 * PCG_TREES_PER_BUNDLE);
                let mut tp_info = [(0usize, Tower128::ZERO); 8];
                for (t_idx, tp_info_t_idx_item) in
                    tp_info[..(2 * PCG_TREES_PER_BUNDLE)].iter_mut().enumerate()
                {
                    let rt = &peer.tower_receiver_trees[t_idx];
                    let p_star = rt.punctured_idx as usize;
                    *tp_info_t_idx_item = (p_star, rt.punctured_beta);
                    let tree_tag = 0x80u8
                        .wrapping_add(((q * 16 + me) as u8).wrapping_mul(17))
                        .wrapping_add(t_idx as u8);
                    let lt = ggm_eval_receiver_punctured(
                        &self.session_id,
                        tree_tag,
                        tower_depth,
                        p_star,
                        &rt.copath,
                        (
                            [rt.punctured_mac_val[0].0, rt.punctured_mac_val[1].0],
                            false,
                        ),
                    );
                    tr_leaves.push(lt);
                }
                let pa0: [(usize, Tower128); 4] =
                    core::array::from_fn(|array_index| (tp_info[0..4])[array_index]);
                let pa1: [(usize, Tower128); 4] =
                    core::array::from_fn(|array_index| (tp_info[4..8])[array_index]);
                let (tv0, tm0) =
                    sched_a0.compress_tower_bundle(PCG_NUM_WORDS, &tr_leaves[0..4], Some(pa0));
                let (tv1, tm1) =
                    sched_a1.compress_tower_bundle(PCG_NUM_WORDS, &tr_leaves[4..8], Some(pa1));

                for ell in 0..num_triples {
                    if !my_bits_populated {
                        companion_a[0][ell].value = tv0[ell];
                        companion_a[1][ell].value = tv1[ell];
                    }
                    for lane in 0..2 {
                        companion_a[0][ell].keys[q][lane] = Tower128(tk0[ell][lane]);
                        companion_a[1][ell].keys[q][lane] = Tower128(tk1[ell][lane]);
                        companion_a[0][ell].macs[q][lane] = Tower128(tm0[ell][lane]);
                        companion_a[1][ell].macs[q][lane] = Tower128(tm1[ell][lane]);
                    }
                }

                my_bits_populated = true;
            }

            // 4. Populate diagonal self-MACs (`q == me`) from `diag_mask_seed` AND apply public `delta_words`
            // affine shift (`[c_\ell] = [z_\ell] \oplus \delta_\ell`) preserving 2-lane `Tower128` BDOZ MACs!
            let mut diag_rng = PartyPrivateRng::from_seed(self.diag_mask_seed, b"PCG_DIAG");
            for (k, bool_triple_words_k_item) in
                bool_triple_words[..PCG_NUM_WORDS].iter_mut().enumerate()
            {
                let dw = self.delta_words[k];
                if me == 0 {
                    bool_triple_words_k_item.c_word ^= dw;
                }
                let aw = bool_triple_words_k_item.a_word;
                let bw = bool_triple_words_k_item.b_word;
                let cw = bool_triple_words_k_item.c_word;

                for bit in 0..64 {
                    let a_bit = ((aw >> bit) & 1) == 1;
                    let b_bit = ((bw >> bit) & 1) == 1;
                    let c_bit = ((cw >> bit) & 1) == 1;
                    let d_bit = ((dw >> bit) & 1) == 1;

                    for lane in 0..2 {
                        let alpha_l = self.mac_alpha[lane];
                        let ka = diag_rng.next_tower128();
                        let kb = diag_rng.next_tower128();
                        let kc = diag_rng.next_tower128();
                        bool_triple_words_k_item.a_keys[me][bit][lane] = ka;
                        bool_triple_words_k_item.a_macs[me][bit][lane] =
                            if a_bit { ka.add(alpha_l) } else { ka };
                        bool_triple_words_k_item.b_keys[me][bit][lane] = kb;
                        bool_triple_words_k_item.b_macs[me][bit][lane] =
                            if b_bit { kb.add(alpha_l) } else { kb };
                        bool_triple_words_k_item.c_keys[me][bit][lane] = kc;
                        bool_triple_words_k_item.c_macs[me][bit][lane] =
                            if c_bit { kc.add(alpha_l) } else { kc };

                        if me != 0 && d_bit {
                            bool_triple_words_k_item.c_keys[0][bit][lane] =
                                bool_triple_words_k_item.c_keys[0][bit][lane].add(alpha_l);
                        }
                    }
                }
            }

            #[expect(
                clippy::needless_range_loop,
                reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows"
            )]
            for sac_lane in 0..2 {
                #[expect(
                    clippy::needless_range_loop,
                    reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows"
                )]
                for ell in 0..num_triples {
                    let v = companion_a[sac_lane][ell].value;
                    for lane in 0..2 {
                        let kd = diag_rng.next_tower128();
                        companion_a[sac_lane][ell].keys[me][lane] = kd;
                        companion_a[sac_lane][ell].macs[me][lane] =
                            kd.add(self.mac_alpha[lane].mul(v));
                    }
                }
            }

            PcgExpandedPartyVault {
                session_id: self.session_id,
                party_id: me,
                num_parties: n,
                mac_alpha: self.mac_alpha,
                bool_triple_words,
                tower_triples: core::mem::take(&mut self.tower_triples),
                companion_a,
                companion_c_sums: core::mem::replace(
                    &mut self.tilde_c_sums,
                    core::array::from_fn(|_| PcgAuthTower128Share::zero(0)),
                ),
            }
        }
    }
}
#[cfg(test)]
use legacy_sparse_pcg::*;

/// Compatibility entry point using uniform KOS/MASCOT preprocessing.
/// Compact sparse PCG correlations are not suitable as online Beaver masks.
pub fn run_dealerless_pcg_keccak_vaults(
    session_id: [u8; 32],
    t: usize,
    eval_points: &[TowerGf256],
    tree_depth: usize,
    num_triples_words: usize,
    ot_mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<PreprocessedKeccakPartyVault>, PreprocessError> {
    let n = eval_points.len();
    if t == 0 || t > n || n < 2 || num_triples_words > PCG_NUM_WORDS - 10 || party_rngs.len() != n {
        return Err(PreprocessError::InvalidThreshold { t, n });
    }
    validate_all_eval_points_gf256(eval_points)?;

    PcgTreeDepth::try_from(tree_depth)?;
    run_dealerless_pi_triple_f2(
        session_id,
        t,
        eval_points,
        num_triples_words,
        ot_mesh,
        party_rngs,
    )
}

/// Generate uniform authenticated masks in bounded KOS/MASCOT chunks under an existing MAC key.
/// The returned vault owns all chunks; this API is not a streaming source.
#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the public preprocessing API used by other protocol modules"
)]
pub fn run_dealerless_pcg_keccak_vaults_with_alpha(
    session_id: [u8; 32],
    t: usize,
    eval_points: &[TowerGf256],
    tree_depth: usize,
    num_triples_words: usize,
    alpha_contribs: &[[Tower128; 2]],
    alpha_shamir: &[[Tower128; 2]],
    ot_mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<PreprocessedKeccakPartyVault>, PreprocessError> {
    let n = eval_points.len();
    if t == 0
        || t > n
        || n < 2
        || party_rngs.len() != n
        || alpha_contribs.len() != n
        || alpha_shamir.len() != n
    {
        return Err(PreprocessError::InvalidThreshold { t, n });
    }
    validate_all_eval_points_gf256(eval_points)?;
    PcgTreeDepth::try_from(tree_depth)?;

    let mut acc_triples: Vec<Vec<KeccakBitTripleShare64>> = (0..n)
        .map(|_| Vec::with_capacity(num_triples_words))
        .collect();
    let mut chunk_idx = 0u64;
    let mut remaining = num_triples_words;
    // Reserve 10 words per `PCG_NUM_WORDS` (`1025`) batch for Shamir Booleanity (8) + Shamir sacrifice (2)!
    const CHUNK_CAP: usize = PCG_NUM_WORDS - 10;

    while remaining > 0 {
        let take = remaining.min(CHUNK_CAP);
        let mut chunk_sid = [0u8; 32];
        let mut xof = Cshake256Xof::new(b"QSAG.PCG.SPDZ.CHUNK/v1");
        xof.absorb(&session_id);
        xof.absorb(&chunk_idx.to_be_bytes());
        xof.squeeze(&mut chunk_sid);
        chunk_idx += 1;

        let mut chunk_vaults = run_dealerless_pi_triple_f2_with_alpha(
            chunk_sid,
            t,
            eval_points,
            take,
            alpha_contribs,
            alpha_shamir,
            ot_mesh,
            party_rngs,
        )?;
        for p in 0..n {
            acc_triples[p].append(&mut chunk_vaults[p].triples);
        }
        remaining -= take;
    }

    Ok((0..n)
        .map(|p| PreprocessedKeccakPartyVault {
            party_id: p,
            eval_point: eval_points[p],
            mac_alpha_lanes: alpha_shamir[p],
            triples: core::mem::take(&mut acc_triples[p]),
            cursor: 0,
            poisoned: false,
        })
        .collect())
}

impl core::error::Error for PreprocessError {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sponge::poseidon2::poseidon2_sbox7;

    fn make_party_rngs(n: usize, tag: u8) -> Vec<PartyPrivateRng> {
        (0..n)
            .map(|i| {
                let mut seed = [0u8; 32];
                seed[0] = tag;
                seed[1] = (i + 1) as u8;
                PartyPrivateRng::from_seed(seed, b"test")
            })
            .collect()
    }

    #[test]
    fn private_rng_batched_refill_matches_scalar_stream_and_rekey() {
        fn scalar_stream(seed: &[u8; 32], counter: u64, blocks: usize) -> Vec<u8> {
            let mut bytes = Vec::with_capacity(136 * blocks);
            for block in 0..blocks {
                let mut state = [0u64; 25];
                state[0] = u64::from_le_bytes(*b"QSAG.PRG");
                state[1] = u64::from_le_bytes(*b"NG.BLK\x01\x00");
                for i in 0..4 {
                    state[2 + i] = u64::from_le_bytes(core::array::from_fn(|j| seed[8 * i + j]));
                }
                state[6] = counter.wrapping_add(block as u64);
                state[7] = 0x1f;
                state[16] = 0x8000_0000_0000_0000;
                keccak_f1600(&mut state);
                for word in &state[..17] {
                    bytes.extend_from_slice(&word.to_le_bytes());
                }
            }
            bytes
        }
        for counter in [0, u64::MAX - 16] {
            for chunk in [1, 8, 26, 135, 136, 137, 543, 544, 545, 1088] {
                let mut rng = PartyPrivateRng::from_seed([0x93; 32], b"batch-stream-test");
                rng.counter = counter;
                let expected = scalar_stream(&rng.seed, counter, 12);
                let mut actual = vec![0; expected.len()];
                for part in actual.chunks_mut(chunk) {
                    rng.fill_bytes(part);
                }
                assert_eq!(actual, expected);
            }
        }
        // A rekey must discard every prefetched block, even after a partial read.
        for consumed in [0, 1, 135, 136, 513, 544] {
            let mut rng = PartyPrivateRng::from_seed([0x93; 32], b"batch-stream-test");
            let old = scalar_stream(&rng.seed, 0, 8);
            let mut discard = vec![0; consumed];
            rng.fill_bytes(&mut discard);
            let mut seed = [0; 32];
            HedgedTranscriptRng::derive(
                &rng.seed,
                0,
                &old[consumed..consumed + 32],
                b"rekey",
                &mut seed,
            );
            rng.hedge_transcript(b"rekey");
            let mut actual = vec![0; 1088];
            rng.fill_bytes(&mut actual);
            assert_eq!(actual, scalar_stream(&seed, 0, 8));
        }
    }

    #[test]
    fn kos_batched_inner_product_matches_scalar_including_tails() {
        let mut rng = PartyPrivateRng::from_seed([0x73; 32], b"kos-dot");
        let rows: Vec<_> = (0..257).map(|_| rng.next_u128()).collect();
        let weights: Vec<_> = (0..257).map(|_| rng.next_tower128()).collect();
        for n in [0, 1, 2, 63, 64, 127, 128, 129, 256, 257] {
            let expected = rows[..n]
                .iter()
                .zip(&weights[..n])
                .fold(Tower128::ZERO, |sum, (&x, &y)| sum.add(Tower128(x).mul(y)));
            assert_eq!(kos_inner_product(&rows[..n], &weights[..n]), expected);
        }
    }

    #[test]
    fn dense_active_three_party_product() {
        let sid = [0x19; 32];
        let mut rngs: Vec<_> = (0..3)
            .map(|i| PartyPrivateRng::from_seed([i + 1; 32], b"dense-active-test"))
            .collect();
        let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut rngs);
        let a = vec![
            vec![0x123456789abcdef0],
            vec![0xdeadbeefcafebabe],
            vec![0x33335555ffff0000],
        ];
        let b = vec![
            vec![0x12340000ffff9876],
            vec![0x5555aaaa12344321],
            vec![0x777788889999aaaa],
        ];
        let c = checked_boolean_product(&sid, &a, &b, &mut mesh, &mut rngs).unwrap();
        assert_eq!(
            c.iter().fold(0, |x, p| x ^ p[0]),
            a.iter().fold(0, |x, p| x ^ p[0]) & b.iter().fold(0, |x, p| x ^ p[0])
        );
        assert!(
            checked_boolean_product_with_hook(&sid, &a, &b, &mut mesh, &mut rngs, |shares| {
                shares[0][0][0] ^= 1
            })
            .is_err()
        );
    }

    #[test]
    fn test_rlwe_crs_orsigma_fo_and_kos_regressions() {
        // Worst-case ternary noise at `RLWE_N = 1024`: `|e| <= 1024 + 1024 + 1 = 2049 < 3072 = floor(q/4)`
        for &mag in &[0u16, 1, 512, 1025, 2049, 3071] {
            let f_pos = mag % RLWE_Q;
            let f_neg = (RLWE_Q - (mag % RLWE_Q)) % RLWE_Q;
            let t_pos = (RLWE_HALF_Q + mag) % RLWE_Q;
            let t_neg = (RLWE_HALF_Q + RLWE_Q - mag) % RLWE_Q;
            assert_eq!(rlwe_decode_bit_ct(f_pos), 0);
            assert_eq!(rlwe_decode_bit_ct(f_neg), 0);
            assert_eq!(rlwe_decode_bit_ct(t_pos), 1);
            assert_eq!(rlwe_decode_bit_ct(t_neg), 1);
        }

        let mut rng_s = PartyPrivateRng::from_seed([0x11; 32], b"ot-s");
        let mut rng_r = PartyPrivateRng::from_seed([0x22; 32], b"ot-r");
        let sid = [0xAA; 32];
        for idx in 0..2u32 {
            let choice = (idx & 1) == 1;
            let s0 = rng_s.next_bytes32();
            let s1 = rng_s.next_bytes32();
            let (sec, mut req) = rlwe_ot_choose(&sid, 0, 1, idx, choice, &mut rng_r);
            let mut resp =
                try_rlwe_ot_transfer(&sid, 0, 1, idx, &req, &s0, &s1, &mut rng_s).unwrap();
            let got = rlwe_ot_decrypt(&sec, &resp).unwrap();
            assert_eq!(got, if choice { s1 } else { s0 });

            // Forged Receiver OR-Sigma ZKPoK MUST abort at `try_rlwe_ot_transfer` (`[P0-11]`)!
            req.pok.chal0[0] ^= 0x01;
            assert_eq!(
                try_rlwe_ot_transfer(&sid, 0, 1, idx, &req, &s0, &s1, &mut rng_s).unwrap_err(),
                PreprocessError::BaseOtReceiverProofFailed {
                    sender_id: 0,
                    receiver_id: 1,
                }
            );

            // Active Chou-Orlandi / selective-failure ciphertext tamper on Receiver's chosen branch
            // (`b = 0` when `choice == false`, `b = 1` when `choice == true`) MUST abort via FO re-encryption!
            if choice {
                resp.u1.0[0] = (resp.u1.0[0] + 1) % RLWE_Q;
            } else {
                resp.u0.0[0] = (resp.u0.0[0] + 1) % RLWE_Q;
            }
            assert_eq!(
                rlwe_ot_decrypt(&sec, &resp),
                Err(PreprocessError::BaseOtFoCheckFailed {
                    sender_id: 0,
                    receiver_id: 1,
                    ot_idx: idx,
                })
            );
        }

        // Verify isolated committed-CRS + OR-Sigma + 384-branch FO + 4-ciphertext combiner ceremony
        let (crs_r0, crs_com) = BaseOtCrsReceiverRound0::commit(sid, 0, 1, &mut rng_r);
        let (crs_s0, crs_sh) = BaseOtCrsSenderRound0::respond(sid, 0, 1, &crs_com, &mut rng_s);
        let (r_crs_coin, mut bad_crs_open) = crs_r0.open_and_derive_crs_coin(&crs_sh);
        let good_crs_open = bad_crs_open;
        bad_crs_open.receiver_crs_share[0] ^= 0x80;
        assert_eq!(
            crs_s0.verify_and_derive_crs_coin(&bad_crs_open),
            Err(PreprocessError::CoinCommitMismatch { party_id: 1 })
        );
        let (_, crs_s0_ok_sh) = BaseOtCrsSenderRound0::respond(sid, 0, 1, &crs_com, &mut rng_s);
        let _ = crs_s0_ok_sh;
        // Exercise KOS with ideal base OTs; the full bootstrap has a separate soak.
        let (mut s_chan, mut r_chan) =
            establish_ideal_ot_ext_channel_for_test(sid, 0, 1, &mut rng_s, &mut rng_r);
        let _ = (r_crs_coin, good_crs_open);

        let choices = [0xCAFE_BABE_1234_5678u64];
        let (pend_r, u_msg) = r_chan.round1_send_u_cols(&choices, &mut rng_r);
        let (pend_s, chal_msg) = s_chan.round2_sample_challenge(&u_msg, &mut rng_s).unwrap();
        let (proof_msg, r_pads) = r_chan.round3_prove_and_finish(pend_r, &chal_msg);
        let s_pads = s_chan.round4_verify_and_finish(pend_s, &proof_msg).unwrap();
        for b in 0..64 {
            let bit = ((choices[0] >> b) & 1) == 1;
            assert_eq!(r_pads[b], if bit { s_pads[b].1 } else { s_pads[b].0 });
        }
    }

    #[test]
    fn test_interactive_kos_ot_extension_kills_roy22_and_poisons_channel() {
        let mut rng_s = PartyPrivateRng::from_seed([0x31; 32], b"kos-s");
        let mut rng_r = PartyPrivateRng::from_seed([0x32; 32], b"kos-r");
        let (mut s_chan, mut r_chan) =
            establish_ideal_ot_ext_channel_for_test([0x55; 32], 0, 1, &mut rng_s, &mut rng_r);
        let choices = [0xDEAD_BEEF_CAFE_BABEu64, 0x0123_4567_89AB_CDEFu64];

        let (pend_r, u_msg) = r_chan.round1_send_u_cols(&choices, &mut rng_r);
        let (pend_s, chal_msg) = s_chan.round2_sample_challenge(&u_msg, &mut rng_s).unwrap();
        let (proof_msg, recv_pads) = r_chan.round3_prove_and_finish(pend_r, &chal_msg);
        let send_pads = s_chan.round4_verify_and_finish(pend_s, &proof_msg).unwrap();
        for w in 0..choices.len() {
            for b in 0..64 {
                let bit = ((choices[w] >> b) & 1) == 1;
                let exp = if bit {
                    send_pads[64 * w + b].1
                } else {
                    send_pads[64 * w + b].0
                };
                assert_eq!(recv_pads[64 * w + b], exp);
            }
        }

        // Corrupt 1 bit in column 127 (full 128-column KOS!) BEFORE seeing `chi_seed` -> rejects & poisons!
        let (pend_r_bad, mut u_msg_bad) = r_chan.round1_send_u_cols(&choices, &mut rng_r);
        u_msg_bad.u_cols[127][0] ^= 1;
        let (pend_s_bad, chal_bad) = s_chan
            .round2_sample_challenge(&u_msg_bad, &mut rng_s)
            .unwrap();
        let (proof_bad, _) = r_chan.round3_prove_and_finish(pend_r_bad, &chal_bad);
        assert_eq!(
            s_chan.round4_verify_and_finish(pend_s_bad, &proof_bad),
            Err(PreprocessError::KosOtCheckFailed {
                sender_id: 0,
                receiver_id: 1
            })
        );

        let (_, u_msg_after) = r_chan.round1_send_u_cols(&choices, &mut rng_r);
        assert!(matches!(
            s_chan.round2_sample_challenge(&u_msg_after, &mut rng_s),
            Err(PreprocessError::ChannelPoisoned {
                sender_id: 0,
                receiver_id: 1
            })
        ));
    }

    #[test]
    fn test_pcg_seed_expansion_sub24kb_65600_triples_and_2lane_bdoz_sacrifice() {
        let sid = [0x99; 32];
        let n = 2usize;
        let mut rngs = make_party_rngs(n, 0x71);
        let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut rngs);

        let seeds = PcgSeedExpansion::setup_seeds(sid, 14, &mut mesh, &mut rngs).unwrap();
        for s in &seeds {
            let wire = s.to_wire_bytes();
            assert!(
                wire.len() < PCG_MAX_SEED_WIRE_BYTES,
                "PCG wire seed {} bytes must be strictly < 24 KB ({})",
                wire.len(),
                PCG_MAX_SEED_WIRE_BYTES
            );
            let decoded = PcgPartySeed::from_wire_bytes(&wire).unwrap();
            assert_eq!(decoded.to_wire_bytes(), wire);
        }

        let vaults: Vec<PcgExpandedPartyVault> =
            seeds.into_iter().map(|s| s.expand_local()).collect();
        assert_eq!(vaults[0].num_boolean_triples(), 65_600);
        assert!(vaults[0].num_boolean_triples() > 65_536);
        assert_eq!(vaults[0].tower_triples.len(), PCG_NUM_TOWER_TRIPLES);

        for k in 0..PCG_NUM_WORDS {
            let a = vaults[0].bool_triple_words[k].a_word ^ vaults[1].bool_triple_words[k].a_word;
            let b = vaults[0].bool_triple_words[k].b_word ^ vaults[1].bool_triple_words[k].b_word;
            let c = vaults[0].bool_triple_words[k].c_word ^ vaults[1].bool_triple_words[k].c_word;
            assert_eq!(c, a & b, "Boolean triple word {} mismatch", k);
        }
        for k in 0..PCG_NUM_TOWER_TRIPLES {
            let a = vaults[0].tower_triples[k]
                .a
                .value
                .add(vaults[1].tower_triples[k].a.value);
            let b = vaults[0].tower_triples[k]
                .b
                .value
                .add(vaults[1].tower_triples[k].b.value);
            let c = vaults[0].tower_triples[k]
                .c
                .value
                .add(vaults[1].tower_triples[k].c.value);
            assert_eq!(c, a.mul(b));
        }

        PcgSeedExpansion::verify_2lane_bdoz_sacrifice(&vaults, &mut rngs).unwrap();

        let bad_seeds = PcgSeedExpansion::setup_seeds_with_fault(
            [0x9A; 32],
            14,
            &mut mesh,
            &mut rngs,
            |p, d_words| {
                if p == 0 {
                    d_words[512] ^= 1u64 << 37;
                }
            },
        )
        .unwrap();
        let bad_vaults: Vec<PcgExpandedPartyVault> =
            bad_seeds.into_iter().map(|s| s.expand_local()).collect();
        assert_eq!(
            PcgSeedExpansion::verify_2lane_bdoz_sacrifice(&bad_vaults, &mut rngs),
            Err(PreprocessError::SacrificeResidualNonZero {
                phase: "pcg_boolean_triples"
            })
        );
    }

    #[test]
    fn test_dealerless_pi_triple_f2_dishonest_majority_booleanity_and_mac_abort() {
        let sid = [0x77; 32];
        // Dishonest majority 3-of-4 (`2t - 1 = 5 > 4`, up to `2` active corruptions)
        let t = 3usize;
        let n = 4usize;
        let pts: Vec<TowerGf256> = (1..=n as u8).map(TowerGf256).collect();
        let mut rngs = make_party_rngs(n, 0x40);
        let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut rngs);

        // `[P0-10]` regression guard: zero or duplicate `eval_point` at index `>= t` MUST be rejected!
        let mut bad_pts_zero = pts.clone();
        bad_pts_zero[3] = TowerGf256::ZERO;
        assert_eq!(
            run_dealerless_pi_triple_f2(sid, t, &bad_pts_zero, 1, &mut mesh, &mut rngs)
                .unwrap_err(),
            PreprocessError::DuplicateOrZeroEvalPoint
        );
        let mut bad_pts_dup = pts.clone();
        bad_pts_dup[3] = bad_pts_dup[1];
        assert_eq!(
            run_dealerless_pi_triple_f2(sid, t, &bad_pts_dup, 1, &mut mesh, &mut rngs).unwrap_err(),
            PreprocessError::DuplicateOrZeroEvalPoint
        );

        let mut vaults =
            run_dealerless_pi_triple_f2(sid, t, &pts, 2, &mut mesh, &mut rngs).unwrap();
        for k in 0..2 {
            let a_sh: Vec<BitslicedGf256x64> = (0..n).map(|p| vaults[p].triples[k].a).collect();
            let b_sh: Vec<BitslicedGf256x64> = (0..n).map(|p| vaults[p].triples[k].b).collect();
            let c_sh: Vec<BitslicedGf256x64> = (0..n).map(|p| vaults[p].triples[k].c).collect();
            let a_macs: Vec<[[Tower128; 64]; 2]> =
                (0..t).map(|q| vaults[q].triples[k].a_mac).collect();
            let alpha_sh: Vec<[Tower128; 2]> = (0..t).map(|q| vaults[q].mac_alpha_lanes).collect();

            // Honest quorum SPDZ opening passes (`t=3` out of `n=4`)
            let a = commit_and_open_spdz_bs_gf256_quorum(
                &sid,
                "test_spdz_open",
                t,
                &pts[..t],
                &a_sh[..t],
                &a_macs,
                &alpha_sh,
                &mut rngs[..t],
            )
            .unwrap();
            let b = open_and_check_degree_bs_gf256(t, &pts, &b_sh, "test").unwrap();
            let c = open_and_check_degree_bs_gf256(t, &pts, &c_sh, "test").unwrap();
            assert_eq!(&a[1..], &[0u64; 7]);
            assert_eq!(&b[1..], &[0u64; 7]);
            assert_eq!(&c[1..], &[0u64; 7]);
            assert_eq!(c[0], a[0] & b[0]);

            // Dishonest-majority (`c = 2` corrupt parties in `0..t`) share forgery (`f(0)` flipped by `1`)
            // MUST fail SPDZ `MacCheck`! (Note: on `[1, 2, 3]` in `GF(2^8)`, `lambda = [1, 1, 1]`, so
            // flipping plane 0 at `p = 0` and cancelling plane 1 across `p = 0, 1` shifts `f(0)` by `1`!)
            let mut forged_a = a_sh[..t].to_vec();
            forged_a[0][0] ^= 1;
            forged_a[0][1] ^= 1;
            forged_a[1][1] ^= 1;
            assert!(matches!(
                commit_and_open_spdz_bs_gf256_quorum(
                    &sid,
                    "test_spdz_forge",
                    t,
                    &pts[..t],
                    &forged_a,
                    &a_macs,
                    &alpha_sh,
                    &mut rngs[..t],
                ),
                Err(PreprocessError::MacCheckFailed { .. })
            ));
        }

        // Poisoning burns `mac_alpha_lanes` and blocks all future `pop_triple()` calls (`[P0-07]`)
        vaults[0].poison_and_wipe();
        assert_eq!(vaults[0].mac_alpha_lanes, [Tower128::ZERO; 2]);
        assert_eq!(
            vaults[0].pop_triple().unwrap_err(),
            PreprocessError::VaultPoisoned {
                kind: "Keccak triple"
            }
        );

        // `[P0-06]` single-lane non-Boolean injection (`TowerGf256(2) \in GF(256) \ GF(2)` at bit `37`)
        // MUST pass `0..n` degree check AND abort with `NonBooleanBitDetected` (`2^{-256}` soundness, 0 blind spots)!
        let mut non_bool_planes = [[0u64; 8]; 4];
        let nb_poly = [TowerGf256(2), TowerGf256(9), TowerGf256(17)];
        for p in 0..n {
            bs_gf256_insert_lane(
                &mut non_bool_planes[p],
                37,
                eval_poly_gf256(&nb_poly, pts[p]),
            );
        }
        let err_nb = run_dealerless_pi_triple_f2_with_fault(
            [0x78; 32],
            t,
            &pts,
            1,
            &mut mesh,
            &mut rngs,
            |p, a_vec, _| {
                bs_gf256_xor_assign(&mut a_vec[0], &non_bool_planes[p]);
            },
        )
        .unwrap_err();
        // The hook mutates already-authenticated Shamir shares, so PiMAC rejects
        // before the value can be released or combined.
        assert_eq!(
            err_nb,
            PreprocessError::MacCheckFailed {
                phase: "spdz_bs_gf256_pimac",
                accused_party: None,
            }
        );

        // Corrupt `c_sh` with a consistent degree-`<t` Boolean offset -> SPDZ companion sacrifice MUST abort!
        let bad_offset = shamir_share_bits64_gf256(t, &pts, 1u64, &mut rngs[0]);
        let err = run_dealerless_pi_triple_f2_with_fault(
            [0x79; 32],
            t,
            &pts,
            1,
            &mut mesh,
            &mut rngs,
            |p, _, c_vec| {
                bs_gf256_xor_assign(&mut c_vec[0], &bad_offset[p]);
            },
        )
        .unwrap_err();
        assert_eq!(
            err,
            PreprocessError::MacCheckFailed {
                phase: "spdz_bs_gf256_pimac",
                accused_party: None,
            }
        );
    }

    type PiTripleF2Run = Result<(Vec<PreprocessedKeccakPartyVault>, Vec<u32>), PreprocessError>;

    /// One `Π_triple_f2` run from party seeds `rng_tag`, returning the vaults and the public
    /// bucket permutation.
    fn run_pi_triple_f2_with_buckets<F>(
        sid: [u8; 32],
        t: usize,
        pts: &[TowerGf256],
        num_triples: usize,
        rng_tag: u8,
        fault_hook: F,
    ) -> PiTripleF2Run
    where
        F: FnMut(usize, &mut [BitslicedGf256x64], &mut [BitslicedGf256x64]),
    {
        let mut rngs = make_party_rngs(pts.len(), rng_tag);
        let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut rngs);
        let (alpha_contribs, alpha_shamir) = spdz_setup_alpha_gf256(&sid, t, pts, &mut rngs)?;
        run_dealerless_pi_triple_f2_with_alpha_and_fault(
            sid,
            t,
            pts,
            num_triples,
            &alpha_contribs,
            &alpha_shamir,
            &mut mesh,
            &mut rngs,
            fault_hook,
        )
    }

    /// Raw indices sharing a bucket with raw index `raw` under `perm`.
    fn bucket_members(perm: &[u32], num_triples: usize, raw: usize) -> [usize; 3] {
        let pos = perm
            .iter()
            .position(|&x| x as usize == raw)
            .expect("raw index in permutation");
        let bucket = pos % num_triples;
        [
            perm[bucket] as usize,
            perm[num_triples + bucket] as usize,
            perm[2 * num_triples + bucket] as usize,
        ]
    }

    #[test]
    fn test_coin_permutation_is_a_permutation_and_roughly_uniform() {
        for len in [0usize, 1, 2, 3, 12, 97, 1000] {
            let perm = derive_coin_permutation(&[0x42; 32], b"test", len);
            let mut sorted = perm.clone();
            sorted.sort_unstable();
            assert_eq!(sorted, (0..len as u32).collect::<Vec<u32>>());
        }
        // Domain and coin both select the permutation.
        let base = derive_coin_permutation(&[0x42; 32], b"test", 97);
        assert_ne!(base, derive_coin_permutation(&[0x43; 32], b"test", 97));
        assert_ne!(base, derive_coin_permutation(&[0x42; 32], b"other", 97));
        assert_eq!(base, derive_coin_permutation(&[0x42; 32], b"test", 97));

        // Every value lands on every position about equally often (expected 1200 of 6000
        // each, standard deviation about 31; the bounds are more than 6 sigma wide).
        let mut hits = [[0u32; 5]; 5];
        for trial in 0u32..6000 {
            let mut coin = [0u8; 32];
            coin[0..4].copy_from_slice(&trial.to_le_bytes());
            let perm = derive_coin_permutation(&coin, b"test", 5);
            for (pos, &val) in perm.iter().enumerate() {
                hits[pos][val as usize] += 1;
            }
        }
        for row in &hits {
            for &count in row {
                assert!(
                    (1000..=1400).contains(&count),
                    "position/value count {}",
                    count
                );
            }
        }
    }

    #[test]
    fn test_pi_triple_f2_random_buckets_honest_valid_and_coin_dependent() {
        let sid = [0x7A; 32];
        let t = 2usize;
        let n = 2usize;
        let num_triples = 4usize;
        let pts: Vec<TowerGf256> = (1..=n as u8).map(TowerGf256).collect();

        let mut perms = Vec::new();
        for rng_tag in [0x51u8, 0x52] {
            let (vaults, perm) =
                run_pi_triple_f2_with_buckets(sid, t, &pts, num_triples, rng_tag, |_, _, _| {})
                    .expect("honest run");

            // (a) Honest runs still produce Boolean triples with `c = a & b`.
            for k in 0..num_triples {
                let a_sh: Vec<BitslicedGf256x64> = (0..n).map(|p| vaults[p].triples[k].a).collect();
                let b_sh: Vec<BitslicedGf256x64> = (0..n).map(|p| vaults[p].triples[k].b).collect();
                let c_sh: Vec<BitslicedGf256x64> = (0..n).map(|p| vaults[p].triples[k].c).collect();
                let a = open_and_check_degree_bs_gf256(t, &pts, &a_sh, "test").unwrap();
                let b = open_and_check_degree_bs_gf256(t, &pts, &b_sh, "test").unwrap();
                let c = open_and_check_degree_bs_gf256(t, &pts, &c_sh, "test").unwrap();
                assert_eq!(&a[1..], &[0u64; 7]);
                assert_eq!(&b[1..], &[0u64; 7]);
                assert_eq!(&c[1..], &[0u64; 7]);
                assert_eq!(c[0], a[0] & b[0]);
            }

            // The bucket assignment is a permutation of all `3 * num_triples` raw triples.
            let mut sorted = perm.clone();
            sorted.sort_unstable();
            assert_eq!(sorted, (0..(3 * num_triples) as u32).collect::<Vec<u32>>());

            // The fixed layout paired raw `k` with `k + N` and `k + 2N` for every `k`.
            let fixed_layout = (0..num_triples).all(|k| {
                let members = bucket_members(&perm, num_triples, k);
                members.contains(&(k + num_triples)) && members.contains(&(k + 2 * num_triples))
            });
            assert!(
                !fixed_layout,
                "buckets must not follow the fixed k, k+N, k+2N layout"
            );
            perms.push(perm);
        }

        // (b) Different party coin randomness gives a different pairing.
        assert_ne!(perms[0], perms[1]);
        let partners_differ = (0..3 * num_triples).any(|raw| {
            let mut m0 = bucket_members(&perms[0], num_triples, raw);
            let mut m1 = bucket_members(&perms[1], num_triples, raw);
            m0.sort_unstable();
            m1.sort_unstable();
            m0 != m1
        });
        assert!(partners_differ);
    }

    #[test]
    fn test_pi_triple_f2_targeted_pair_deviation_is_detected_and_partner_not_fixed() {
        let sid = [0x7B; 32];
        let t = 2usize;
        let n = 2usize;
        let num_triples = 2usize;
        let pts: Vec<TowerGf256> = (1..=n as u8).map(TowerGf256).collect();
        let target = 1usize;
        let old_partner = target + 2 * num_triples;

        // The reviewed attack deviates on raw triple `k` and on `k + 2N`, the raw triple that
        // the fixed layout combined it with. A deviation that changes the product (the case
        // where the targeted receiver bit is 1) is a consistent offset on `c`; the companion
        // sacrifice rejects it.
        let mut offset_rng = PartyPrivateRng::from_seed([0x7C; 32], b"test");
        let bad_offset = shamir_share_bits64_gf256(t, &pts, 1u64 << 17, &mut offset_rng);
        let err = run_pi_triple_f2_with_buckets(sid, t, &pts, num_triples, 0x53, |p, _, c_vec| {
            bs_gf256_xor_assign(&mut c_vec[target], &bad_offset[p]);
            bs_gf256_xor_assign(&mut c_vec[old_partner], &bad_offset[p]);
        })
        .unwrap_err();
        assert_eq!(
            err,
            PreprocessError::MacCheckFailed {
                phase: "spdz_bs_gf256_pimac",
                accused_party: None,
            }
        );

        // The partner of `k` is decided by the coin, which is drawn after the shares (and so
        // any deviation) are fixed. Over independent coins the old partner shares a bucket with
        // `k` only at the chance rate `2 / (3N - 1)`, here 2/47: about 17 of 400, and 400 of 400
        // under the fixed layout.
        let wide = 16usize;
        let wide_partner = target + 2 * wide;
        let mut same_bucket = 0usize;
        let mut distinct_partner_sets = alloc::collections::BTreeSet::new();
        for trial in 0u32..400 {
            let mut coin = [0x7Du8; 32];
            coin[0..4].copy_from_slice(&trial.to_le_bytes());
            let perm = derive_coin_permutation(&coin, b"PI_TRIPLE_F2_BUCKET", 3 * wide);
            let mut members = bucket_members(&perm, wide, target);
            if members.contains(&wide_partner) {
                same_bucket += 1;
            }
            members.sort_unstable();
            distinct_partner_sets.insert(members);
        }
        assert!(
            same_bucket <= 50,
            "old partner hit {} of 400 times",
            same_bucket
        );
        assert!(distinct_partner_sets.len() >= 300);

        // In full runs the pairing of `k` likewise varies with the parties' coin shares.
        let mut partner_sets = alloc::collections::BTreeSet::new();
        for rng_tag in [0x54u8, 0x55, 0x56] {
            let (_, perm) =
                run_pi_triple_f2_with_buckets(sid, t, &pts, num_triples, rng_tag, |_, _, _| {})
                    .expect("honest run");
            let mut members = bucket_members(&perm, num_triples, target);
            members.sort_unstable();
            partner_sets.insert(members);
        }
        assert!(
            partner_sets.len() >= 2,
            "bucket of raw triple {} never changed",
            target
        );
    }

    #[test]
    fn test_dealerless_pi_pow7_and_canonical_a2b_masks() {
        let sid = [0x88; 32];
        // Dishonest majority 3-of-4 (`2t - 1 = 5 > 4`)
        let t = 3usize;
        let n = 4usize;
        let pts: Vec<Goldilocks> = (1..=n as u64).map(Goldilocks::from_u64_reduced).collect();
        let mut rngs = make_party_rngs(n, 0x60);
        let mut mesh = OtMesh::establish_ideal_for_test(sid, &mut rngs);

        let mut vaults =
            run_dealerless_pi_pow7(sid, t, &pts, 2, 2, 1, &mut mesh, &mut rngs).unwrap();
        let alpha_sh: Vec<GoldilocksExt2> = (0..n).map(|p| vaults[p].mac_alpha_share).collect();
        let alpha_global = open_and_check_degree_ext2(t, &pts, &alpha_sh, "alpha").unwrap();

        for k in 0..2 {
            let mut pows = [Goldilocks::ZERO; 7];
            for (d, pows_d_item) in pows[..7].iter_mut().enumerate() {
                let sh: Vec<Goldilocks> =
                    (0..n).map(|p| vaults[p].pow7_tuples[k].r_pows[d]).collect();
                *pows_d_item = open_and_check_degree_goldilocks(t, &pts, &sh, "test").unwrap();
                let mac_sh: Vec<GoldilocksExt2> =
                    (0..n).map(|p| vaults[p].pow7_tuples[k].r_macs[d]).collect();
                let mac = open_and_check_degree_ext2(t, &pts, &mac_sh, "mac").unwrap();
                assert_eq!(mac, alpha_global.mul_base(*pows_d_item));
            }
            let r = pows[0];
            assert_eq!(pows[1], r * r);
            assert_eq!(pows[2], r * r * r);
            assert_eq!(pows[6], poseidon2_sbox7(r));
        }

        // Verify A2B masks are Boolean, sum strictly `< p`, and carry valid SPDZ MACs
        for m in 0..1 {
            let mut acc_u128 = 0u128;
            for bit in 0..64 {
                let b_sh: Vec<Goldilocks> = (0..n)
                    .map(|p| vaults[p].a2b_masks[m].bit_shares[bit])
                    .collect();
                let b_mac: Vec<GoldilocksExt2> = (0..n)
                    .map(|p| vaults[p].a2b_masks[m].bit_macs[bit])
                    .collect();
                let b_f = commit_and_open_spdz_goldilocks_quorum(
                    &sid,
                    "a2b_bit_spdz",
                    t,
                    &pts[..t],
                    &b_sh[..t],
                    &b_mac[..t],
                    &alpha_sh[..t],
                    &mut rngs[..t],
                )
                .unwrap();
                let b_val = b_f.to_canonical_u64();
                assert!(b_val == 0 || b_val == 1);
                acc_u128 |= (b_val as u128) << bit;
            }
            assert!(acc_u128 < (crate::field::goldilocks::GOLDILOCKS_PRIME as u128));
            let f_sh: Vec<Goldilocks> = (0..n)
                .map(|p| vaults[p].a2b_masks[m].field_sum_share)
                .collect();
            let f_mac: Vec<GoldilocksExt2> = (0..n)
                .map(|p| vaults[p].a2b_masks[m].field_sum_mac)
                .collect();
            let f_val = commit_and_open_spdz_goldilocks_quorum(
                &sid,
                "a2b_sum_spdz",
                t,
                &pts[..t],
                &f_sh[..t],
                &f_mac[..t],
                &alpha_sh[..t],
                &mut rngs[..t],
            )
            .unwrap()
            .to_canonical_u64();
            assert_eq!(f_val as u128, acc_u128);
        }

        // Poisoning wipes `mac_alpha_share` and blocks vault pops
        vaults[0].poison_and_wipe();
        assert_eq!(vaults[0].mac_alpha_share, GoldilocksExt2::ZERO);
        assert_eq!(
            vaults[0].pop_pow7().unwrap_err(),
            PreprocessError::VaultPoisoned {
                kind: "Poseidon2 pow7"
            }
        );

        let bad_off = shamir_share_goldilocks(t, &pts, Goldilocks::ONE, &mut rngs[0]);
        let err = run_dealerless_pi_pow7_with_fault(
            [0x89; 32],
            t,
            &pts,
            1,
            0,
            0,
            &mut mesh,
            &mut rngs,
            |p, c_vec| {
                c_vec[0] += bad_off[p];
            },
        )
        .unwrap_err();
        assert_eq!(
            err,
            PreprocessError::SacrificeResidualNonZero { phase: "pi_pow7" }
        );
    }
}

#[cfg(test)]
mod hardening_regressions {
    #[test]
    fn test_negacyclic_ntt_matches_schoolbook_exact() {
        // Independent integer convolution, including wraparound signs, checks
        // every coefficient rather than an evaluation or a digest of the result.
        let mut rng = PartyPrivateRng::from_seed([0x97; 32], b"ntt-differential");
        for case in 0..12 {
            let mut a = RlwePoly::ZERO;
            let mut b = RlwePoly::ZERO;
            for (x, y) in a.0.iter_mut().zip(&mut b.0) {
                *x = (rng.next_u64() % u64::from(RLWE_Q)) as u16;
                *y = (rng.next_u64() % u64::from(RLWE_Q)) as u16;
            }
            match case {
                0 => a.0.fill(0),
                1 => {
                    a.0.fill(0);
                    a.0[0] = 1;
                }
                2 => {
                    a.0.fill(0);
                    a.0[RLWE_N - 1] = 1;
                }
                3 => {
                    a.0.fill(RLWE_Q - 1);
                    b.0.fill(RLWE_Q - 1);
                }
                _ => {}
            }
            let mut convolution = [0i64; RLWE_N];
            for (i, &x) in a.0.iter().enumerate() {
                for (j, &y) in b.0.iter().enumerate() {
                    let product = i64::from(x) * i64::from(y);
                    if i + j < RLWE_N {
                        convolution[i + j] += product;
                    } else {
                        convolution[i + j - RLWE_N] -= product;
                    }
                }
            }
            let expected = RlwePoly(convolution.map(|x| x.rem_euclid(i64::from(RLWE_Q)) as u16));
            assert_eq!(a.mul_negacyclic(&b), expected, "case {case}");
            let cached = a.to_ntt();
            assert_eq!(b.mul_ntt(&cached), expected, "cached case {case}");
            assert_eq!(cached.from_ntt(), a, "round trip case {case}");
        }
    }

    #[test]
    fn gaussian_witness_energy_rejects_overweight_and_nonternary_inputs() {
        let s = RlwePoly([1; RLWE_N]);
        let mut e = RlwePoly([0; RLWE_N]);
        e.0[..RLWE_WITNESS_ENERGY_BOUND - RLWE_N].fill(RLWE_Q - 1);
        assert!(bounded_ternary_witness(&s, &e));
        e.0[RLWE_WITNESS_ENERGY_BOUND - RLWE_N] = 1;
        assert!(!bounded_ternary_witness(&s, &e));
        e.0.fill(0);
        e.0[0] = 2;
        assert!(!bounded_ternary_witness(&s, &e));
    }

    #[test]
    fn gaussian_early_rejection_preserves_exact_samples() {
        // Exhaust the mask domain, including the wider box endpoints.
        for x in -3072i64..=3072 {
            let exponent = (x * x) as u64;
            let exact = gaussian_exp_probability::<24>(exponent);
            let upper = gaussian_exp_upper_bound(exponent);
            assert!(u128::from(exact[2]) < upper);
            let rounded = gaussian_exp_probability::<24>(exponent & !0x3fff);
            assert!(upper - u128::from(rounded[2]) <= 21);
            // A high limb below the lower bound accepts whatever the low limbs are.
            let lower = gaussian_exp_lower_bound(exponent);
            assert!(lower <= exact[2] && exact[2] - lower < 49);
            assert!(lower == 0 || gaussian_fraction_lt([u64::MAX, u64::MAX, lower - 1], exact));
        }
        for response in [false, true] {
            let mut fast = PartyPrivateRng::from_seed([0x61; 32], b"gaussian-parity");
            let mut reference = PartyPrivateRng::from_seed([0x61; 32], b"gaussian-parity");
            let half = if response {
                RLWE_ZKPOK_Z_BOUND
            } else {
                RLWE_ZKPOK_Z_BOUND + 2
            };
            for _ in 0..8 {
                let expected: [i16; RLWE_N] = core::array::from_fn(|_| {
                    loop {
                        let mut coins = [0; 26];
                        reference.fill_bytes(&mut coins[..10]);
                        let proposal = u16::from_le_bytes([coins[0], coins[1]]) & 0x1fff;
                        let valid = proposal < 2 * half as u16;
                        let x = (proposal & 0u16.wrapping_sub(u16::from(valid))) as i16 - half;
                        let exponent = (i64::from(x) * i64::from(x)) as u64;
                        let probability = gaussian_exp_probability::<24>(exponent);
                        let high = u64::from_le_bytes(core::array::from_fn(|j| coins[2 + j]));
                        if u128::from(high) >= gaussian_exp_upper_bound(exponent) {
                            // Even all-zero lower limbs cannot accept this proposal.
                            assert!(!gaussian_fraction_lt([0, 0, high], probability));
                            continue;
                        }
                        reference.fill_bytes(&mut coins[10..]);
                        let random = [
                            u64::from_le_bytes(core::array::from_fn(|j| coins[10 + j])),
                            u64::from_le_bytes(core::array::from_fn(|j| coins[18 + j])),
                            high,
                        ];
                        if gaussian_fraction_lt(random, probability) & valid {
                            break x;
                        }
                    }
                });
                assert_eq!(sample_gaussian_box(&mut fast, response), expected);
            }
            assert_eq!(fast.next_bytes32(), reference.next_bytes32());
        }
    }

    #[test]
    fn gaussian_fixed_point_and_signed_encoding_regressions() {
        let vectors = [
            (
                [0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
                [0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
                [0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
            ),
            (
                [0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff],
                [0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff],
                [0xfffffffffffffffe, 0xffffffffffffffff, 0xffffffffffffffff],
            ),
            (
                [0x0000000000000000, 0x0000000000000000, 0x8000000000000000],
                [0x0000000000000000, 0x0000000000000000, 0x8000000000000000],
                [0x0000000000000000, 0x0000000000000000, 0x4000000000000000],
            ),
            (
                [0x6014507ff930c949, 0x2cf7b739274dff8c, 0x61bcb43777160001],
                [0x4ddb63c11326c96a, 0x928291a04d74bd65, 0x8bba6dff24ffe4a1],
                [0x994355c4fa1a380c, 0xb14c99d84fa1d3b4, 0x3558a2f3cfc8d489],
            ),
            (
                [0x6004fe755afeb7fa, 0x99589bc0a8523e54, 0x0057101def3c8efc],
                [0xb447956ab300c18e, 0xc381f70308d60d1b, 0x052d3beeac8875ef],
                [0x7362140f8fb0a529, 0x3932d5ccc26f171d, 0x0001c2b2ccd1cba4],
            ),
            (
                [0xf7ac7bbe142ae0fa, 0x7a177925c88483e4, 0x965179c14ec364d6],
                [0x463bb39b81c52669, 0x212422d54eb4541b, 0xfa5dd0c6b3c0c132],
                [0xa9bbc172d8257923, 0x196b76b6cf0df9e1, 0x9302a716e1a1cfa5],
            ),
            (
                [0x60e666f9bd0f7d26, 0xa92e05e46db888d2, 0x6f1e3fe1377d50b3],
                [0x1c0ad2df2abe85f1, 0x8fe7168433e8cb02, 0x5104d2d66fd6eb12],
                [0x2200f7fffb8fb5c7, 0x2ad933d245dcd267, 0x232aaa33264f114c],
            ),
            (
                [0xc15a4ede0be61b32, 0x6735231d6c88fce9, 0x60b24dcef7168b11],
                [0x7e500f7fe9114bf6, 0x5d9b4e6816a7c70c, 0xfbe4672753993448],
                [0x139ab51a5e768557, 0xca318cbaff11e1da, 0x5f25180dd0a2f7e9],
            ),
            (
                [0x2819bcd0144b1fc2, 0x5f54ab4b0224d706, 0xd4203e771187f9b0],
                [0xe333474131549297, 0x64664ddd53c99715, 0xd45d20e208af1cf2],
                [0xbee22b75ef5620e5, 0x09b7e53a38eb5adb, 0xaff7deb09f3e1c75],
            ),
            (
                [0xf661780090c57d30, 0x098bf69e15023400, 0x68d3f90b8e7a7768],
                [0xea3acbb94239efff, 0x7689678e497106b8, 0xebd2970f3d43d0f7],
                [0x4a723e06d370dadc, 0x8818cbfbb405c161, 0x6090d15b2cacfc2d],
            ),
            (
                [0x3cfb5b7151707404, 0x880087b562bae564, 0x580fa697214fefca],
                [0x74f4c085da2221ee, 0xeec40f38322beba1, 0x630354181ec6d6b8],
                [0xb429ae69f91bc144, 0xbd93ee97eb7edc3c, 0x220f3288d45ebe41],
            ),
            (
                [0x3447b2216365d2a5, 0xeec753bf6f2aba9f, 0xb61dd1ba35c4f4af],
                [0x09da5a75f2152d42, 0x0835ba039102776f, 0xda91eb0cf2b40702],
                [0xb9dc372a3f51b286, 0x7b65d46d3a16bb06, 0x9b7d32b2f1d63338],
            ),
            (
                [0x6343e36b763c134b, 0x6c60f7581a504718, 0x50d06ff03873a409],
                [0x9d9b71229ad2551c, 0x3142cea4b94b437c, 0xbd6b015a2504e0fe],
                [0xdb3b7bea22836b35, 0xe9776e8698395d5a, 0x3bcbaa30687bed92],
            ),
            (
                [0x0e0e6f9f27252c47, 0xed938ededc8401bb, 0x36687a9a96e81572],
                [0xec99e2ae26b8f518, 0xdfef2c778e994ec2, 0xd62d34da314b3891],
                [0x1574924fa47891f7, 0xdb8e74f4b6335435, 0x2d84f2165fac531e],
            ),
            (
                [0x0f5e9b4953bc2d90, 0x3e104c2896c2c2da, 0x80d4681b0bab50c5],
                [0xb6db9067f9169b21, 0x99eff90ea26a4d0d, 0xdc56a7499f155f11],
                [0x174ad8491040ed11, 0xbdcf93db986f2d37, 0x6ee22501d3a72736],
            ),
            (
                [0x480c438810f20565, 0x796d0c6bbbdf1b32, 0x9adf1a43a6c20ea6],
                [0xfa0958ff3f6761b9, 0x8daa6cf1ec56fcfb, 0xaa8de815d392bf58],
                [0x7824d1977bc289ee, 0xed89e5f505d1d778, 0x672e00b9c818d6ed],
            ),
            (
                [0xbd56cdf245df737d, 0xe43ee088dff86a9f, 0xe3518d8dc7adff5e],
                [0xb972e8e63c6cc1b5, 0xe1c645d9d5ea329a, 0x59ca12c7e7a908bb],
                [0x684ef1ec9ee10999, 0xb5b0891a9d998f13, 0x4fbac93d3a58bda6],
            ),
            (
                [0xdb5c5ca15e439cff, 0xcb0c0db7f3eee465, 0x9f3c2e4e18210981],
                [0xe3553d6c77956d75, 0xf1e6567405bd7735, 0x252fa2738eb1efcb],
                [0x288ce05b1548ca25, 0x9fd3fcfefed6b0e8, 0x172153c9bfeb7c3d],
            ),
            (
                [0xd6eeb05ab8bbf310, 0x11d333606941a5ce, 0x6190b31b084e4cdc],
                [0xdbd03ebcb6c9c24b, 0x61a8d6ae2982baec, 0x9f9c7ee38bbbfdb7],
                [0x1aaf2e5fc5b68b33, 0xd35b02a003d4809d, 0x3cd483c6df590726],
            ),
        ];
        for (a, b, expected) in vectors {
            assert_eq!(gaussian_fraction_mul(a, b), expected);
            assert_eq!(
                gaussian_fraction_lt(a, b),
                a.iter().rev().cmp(b.iter().rev()).is_lt()
            );
        }
        let mut rng = PartyPrivateRng::from_seed([0x79; 32], b"gaussian-test");
        for _ in 0..8 {
            let response = sample_gaussian_box(&mut rng, true);
            assert!(
                response
                    .iter()
                    .all(|x| (-RLWE_ZKPOK_Z_BOUND..RLWE_ZKPOK_Z_BOUND).contains(x))
            );
        }
        for value in [-12000, -6145, -1, 0, 6145, 12000] {
            let encoded = signed_box_to_rlwe_poly(&[value; RLWE_N]);
            assert!(
                encoded
                    .0
                    .iter()
                    .all(|&x| i32::from(x) == i32::from(value).rem_euclid(i32::from(RLWE_Q)))
            );
        }
        // Even a large positive log ratio must not wrap the fixed-point
        // exponent into an accepting probability.
        assert!(!gaussian_accept(690_000_000, &mut rng));
        assert!(!gaussian_accept(1 << 40, &mut rng));
        assert!(gaussian_accept(-690_000_000, &mut rng));
    }

    #[test]
    fn test_real_rlwe_base_ot_bootstrap_end_to_end() {
        let mut sender = PartyPrivateRng::from_seed([0x31; 32], b"bootstrap-soak");
        let mut receiver = PartyPrivateRng::from_seed([0x32; 32], b"bootstrap-soak");
        let (mut send, mut recv) =
            try_establish_rlwe_ot_ext_channel([0x33; 32], 0, 1, &mut sender, &mut receiver)
                .unwrap();
        let choices = [0x1234_5678_9abc_def0];
        let (rp, u) = recv.round1_send_u_cols(&choices, &mut receiver);
        let (sp, challenge) = send.round2_sample_challenge(&u, &mut sender).unwrap();
        let (proof, received) = recv.round3_prove_and_finish(rp, &challenge);
        let sent = send.round4_verify_and_finish(sp, &proof).unwrap();
        for (bit, (&got, &(zero, one))) in received.iter().zip(&sent).enumerate() {
            assert_eq!(
                got,
                if (choices[0] >> bit) & 1 == 0 {
                    zero
                } else {
                    one
                }
            );
        }
    }

    /// X^1024+1 splits into 1024 distinct roots modulo 12289. At every root,
    /// all 2048 signed monomials have different evaluations, so no distinct
    /// challenge difference vanishes in any CRT factor: every difference is a unit.
    #[test]
    fn signed_monomial_challenge_differences_are_units_in_every_crt_factor() {
        fn power(mut a: u32, mut e: usize) -> u32 {
            let mut out = 1;
            while e != 0 {
                if e & 1 != 0 {
                    out = out * a % u32::from(RLWE_Q);
                }
                a = a * a % u32::from(RLWE_Q);
                e >>= 1;
            }
            out
        }
        let mut roots = 0;
        for root in 1..u32::from(RLWE_Q) {
            if power(root, RLWE_N) != u32::from(RLWE_Q) - 1 {
                continue;
            }
            roots += 1;
            let mut seen = vec![false; usize::from(RLWE_Q)];
            let mut value = 1u32;
            for _ in 0..2 * RLWE_N {
                assert!(!seen[value as usize], "colliding challenges at root {root}");
                seen[value as usize] = true;
                value = value * root % u32::from(RLWE_Q);
            }
            assert_eq!(value, 1);
        }
        assert_eq!(roots, RLWE_N);
        assert!(RLWE_ZKPOK_REPS * RLWE_ZKPOK_CHAL_BITS as usize >= 132);
    }

    #[test]
    fn joint_proof_ot_roundtrip_both_choices() {
        let mut rng_diff = PartyPrivateRng::from_seed([0x44; 32], b"chal11-diff");
        let mut signed_a = [0i16; RLWE_N];
        for coeff in &mut signed_a {
            *coeff = ((rng_diff.next_u64() % 2001) as i16) - 1000;
        }
        let poly_a = signed_box_to_rlwe_poly(&signed_a);
        for u in [0u32, 1, 511, 1023, 1024, 1025, 1536, 2047] {
            let expected = poly_from_chal11(u).mul_negacyclic(&poly_a);
            assert_eq!(mul_chal11_public(&poly_a, u), expected);
            assert_eq!(
                signed_box_to_rlwe_poly(&mul_chal11_signed_ct(&signed_a, u)),
                expected
            );
        }

        let sid = [0xaa; 32];
        let mut receiver = PartyPrivateRng::from_seed([0x22; 32], b"joint-proof");
        let mut sender = PartyPrivateRng::from_seed([0x11; 32], b"joint-proof");
        for index in 0..2 {
            let (secret, request) = rlwe_ot_choose(&sid, 0, 1, index, index == 1, &mut receiver);
            let mut malformed = request.clone();
            malformed.pok.chal0[0] |= 1 << RLWE_ZKPOK_CHAL_BITS;
            assert!(
                try_rlwe_ot_transfer(
                    &sid,
                    0,
                    1,
                    index,
                    &malformed,
                    &[0x31; 32],
                    &[0x72; 32],
                    &mut sender
                )
                .is_err()
            );
            let mut malformed = request.clone();
            malformed.pok.chal0[0] |= 1 << 20;
            assert!(
                try_rlwe_ot_transfer(
                    &sid,
                    0,
                    1,
                    index,
                    &malformed,
                    &[0x31; 32],
                    &[0x72; 32],
                    &mut sender
                )
                .is_err()
            );
            let mut malformed = request.clone();
            malformed.pok.z_s0[0][0] = RLWE_ZKPOK_Z_BOUND;
            assert!(
                try_rlwe_ot_transfer(
                    &sid,
                    0,
                    1,
                    index,
                    &malformed,
                    &[0x31; 32],
                    &[0x72; 32],
                    &mut sender
                )
                .is_err()
            );
            let response = try_rlwe_ot_transfer(
                &sid,
                0,
                1,
                index,
                &request,
                &[0x31; 32],
                &[0x72; 32],
                &mut sender,
            )
            .unwrap();
            assert_eq!(
                rlwe_ot_decrypt(&secret, &response).unwrap(),
                if index == 1 { [0x72; 32] } else { [0x31; 32] }
            );
        }
    }

    #[test]
    fn opening_tables_reconstruct_and_reject_off_polynomial() {
        let points: Vec<_> = (1..=5).map(Goldilocks::from_u64_reduced).collect();
        let tables = GoldilocksOpeningTables::new(3, &points).unwrap();
        let mut shares: Vec<_> = points
            .iter()
            .map(|&x| Goldilocks::from_u64_reduced(17) + x + x * x)
            .collect();
        assert_eq!(
            tables.open(&shares, "table").unwrap(),
            Goldilocks::from_u64_reduced(17)
        );
        shares[4] += Goldilocks::ONE;
        assert!(tables.open(&shares, "table").is_err());
        let points: Vec<_> = (1..=5).map(TowerGf256).collect();
        let tables = Gf256OpeningTables::new(3, &points).unwrap();
        let mut shares: Vec<_> = points
            .iter()
            .map(|&x| TowerGf256(17).add(x).add(x.mul(x)))
            .collect();
        assert_eq!(tables.open(&shares, "table").unwrap(), TowerGf256(17));
        shares[4] = shares[4].add(TowerGf256::ONE);
        assert!(tables.open(&shares, "table").is_err());
    }

    use super::*;
    #[test]
    fn kos_transpose_orientation_and_tail() {
        let cols: Vec<Vec<u64>> = (0..128).map(|i| vec![1u64 << (i % 64), !0u64]).collect();
        let rows = transpose_cols128_to_rows(&cols, 2);
        for b in 0..64 {
            let expected = (1u128 << b) | (1u128 << (b + 64));
            assert_eq!(rows[b], expected);
            assert_eq!(rows[64 + b], u128::MAX);
        }
        for col in 0..128 {
            for bit in 0..64 {
                let mut cols = vec![vec![0]; 128];
                cols[col][0] = 1u64 << bit;
                let rows = transpose_cols128_to_rows(&cols, 1);
                assert_eq!(rows[bit], 1u128 << col);
                assert_eq!(rows.iter().filter(|&&x| x != 0).count(), 1);
            }
        }
    }
    #[test]
    fn joint_challenge_binds_every_repetition() {
        let zero = RlwePoly([0; RLWE_N]);
        let mut commitments = vec![(zero, zero); RLWE_ZKPOK_REPS];
        let base = hash_rlwe_zkpok_joint_challenges(
            &[0; 32],
            &[1; 32],
            0,
            1,
            0,
            &zero,
            &zero,
            &commitments,
        );
        for rep in 0..RLWE_ZKPOK_REPS {
            commitments[rep].0.0[0] ^= 1;
            let changed = hash_rlwe_zkpok_joint_challenges(
                &[0; 32],
                &[1; 32],
                0,
                1,
                0,
                &zero,
                &zero,
                &commitments,
            );
            assert!(base.iter().zip(changed).all(|(a, b)| *a != b));
            commitments[rep].0.0[0] ^= 1;
        }
    }
}

#[cfg(test)]
mod assurance_tests {
    use super::*;
    #[test]
    fn hostile_counts_are_rejected_before_allocation() {
        assert!(validate_frame_count(usize::MAX, 64, usize::MAX).is_err());
        assert!(validate_frame_count(1, MAX_FRAME_BUDGET + 1, usize::MAX).is_err());
        assert!(validate_frame_count(2, 64, 127).is_err());
        assert!(validate_frame_count(2, 64, 128).is_ok());
        let mut wire = vec![0u8; 111];
        wire[..8].copy_from_slice(PCG_WIRE_MAGIC);
        wire[42..44].copy_from_slice(&u16::MAX.to_le_bytes());
        wire[44] = PCG_MIN_TREE_DEPTH as u8;
        wire[109..111].copy_from_slice(&(u16::MAX - 1).to_le_bytes());
        assert!(PcgPartySeed::from_wire_bytes(&wire).is_err());
    }
    #[test]
    fn reservations_are_disjoint_and_fail_without_rewind() {
        let mut cursor = 0;
        assert_eq!(
            reserve_material(&mut cursor, 8, 3, false, "test").unwrap(),
            0..3
        );
        assert_eq!(
            reserve_material(&mut cursor, 8, 2, false, "test").unwrap(),
            3..5
        );
        assert!(reserve_material(&mut cursor, 8, usize::MAX, false, "test").is_err());
        assert_eq!(cursor, 5);
        assert!(reserve_material(&mut cursor, 8, 1, true, "test").is_err());
        assert_eq!(cursor, 5);
    }
    #[test]
    fn zero_entropy_randomizers_bind_messages() {
        use crate::fips205::fips205_prf_msg;
        let key = [0x51; 32];
        let entropy = [0; 32];
        let a = fips205_prf_msg(32, &key, &entropy, b"message one");
        let b = fips205_prf_msg(32, &key, &entropy, b"message two");
        assert_ne!(a.as_slice(), b.as_slice());
    }
    #[test]
    fn subtraction_reducer_matches_remainder_oracle() {
        let p = crate::field::goldilocks::GOLDILOCKS_PRIME as u128;
        for x in [0, 1, p - 1, p, p + 1, u64::MAX as u128, u128::MAX] {
            assert_eq!(Goldilocks::reduce128(x).to_canonical_u64(), (x % p) as u64);
        }
        let mut rng = PartyPrivateRng::from_seed([2; 32], b"reduction test");
        for _ in 0..4096 {
            let x = rng.next_u128();
            assert_eq!(Goldilocks::reduce128(x).to_canonical_u64(), (x % p) as u64);
        }
    }
    #[test]
    fn restored_rng_new_message_changes_masks() {
        let mut a = PartyPrivateRng::from_seed([19; 32], b"test");
        let mut b = PartyPrivateRng::from_seed([19; 32], b"test");
        a.hedge_transcript(b"session/message one");
        b.hedge_transcript(b"session/message two");
        assert_ne!(a.next_bytes32(), b.next_bytes32());
        let mut a = HedgedTranscriptRng::new([7; 32], 0);
        let mut b = HedgedTranscriptRng::new([7; 32], 0);
        let (mut x, mut y) = ([0; 32], [0; 32]);
        a.fill_bytes(&[0; 32], b"one", &mut x).unwrap();
        b.fill_bytes(&[0; 32], b"two", &mut y).unwrap();
        assert_ne!(x, y);
        let mut exhausted = HedgedTranscriptRng::new([7; 32], u64::MAX);
        assert!(exhausted.fill_bytes(&[], &[], &mut x).is_err());
    }
}

#[cfg(test)]
mod combiner_batch_tests {
    use super::*;
    #[test]
    fn four_branches_match_scalar_combiner() {
        let labels = ([0x19; 32], [0xe1; 32]);
        let seeds = ([0x28; 32], [0x83; 32]);
        for row in [0, 127] {
            for step in [0, 1, 383] {
                let batch = combiner_step_hash32_x4(&[0x57; 32], row, step, &labels, &seeds);
                for (slot, value) in batch.iter().enumerate() {
                    assert_eq!(
                        *value,
                        combiner_step_hash32(
                            &[0x57; 32],
                            row,
                            step,
                            (slot / 2) as u8,
                            (slot % 2) as u8,
                            if slot / 2 == 0 { &labels.0 } else { &labels.1 },
                            if slot % 2 == 0 { &seeds.0 } else { &seeds.1 }
                        )
                    );
                }
            }
        }
    }
}
