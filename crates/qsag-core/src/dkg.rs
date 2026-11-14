//! Dealerless Post-Quantum Key Lifecycle (`Π_dkg`, `Π_refresh`, `Π_reshare`), SPDZ-Authenticated
//! Booleanity Verification, and Durable `fsync`-Backed Monotonic `EpochLatch` (`FsWalEpochLatch`).
//!
//! ### Implemented Protocols & Active-Security Invariants
//! 1. **Strict 2-Round Commit-Then-Open `Π_dkg` (`Goldilocks` & `TowerGf256`):**
//!    - Round 1 (`*DealerRound1Commit`) broadcasts ONLY `(pk_seed_commitment, share_commitments)`.
//!    - Round 2 (`*DealerRound2Open`) computes masked polynomials AND opens `(pk_seed_contrib, pk_seed_salt)`
//!      strictly *after* all $n$ parties' Round-1 commitments are locked into `joint_round1_digest`,
//!      binding `(session_id, t, n, eval_points[0..n], joint_round1_digest, dealer_idx)` into every
//!      Fiat–Shamir challenge (preventing rushing `pk_seed` bias and cross-session replay).
//!    - Validates **all** `eval_points[0..n]` (`[P0-10]`), never just `&eval_points[..t]`.
//! 2. **SPDZ-MAC-Authenticated Booleanity & Global Degree-`< t` Consistency (`2t - 1 > n` Safe):**
//!    - Over `TowerGf256`: `spdz_verify_seed256_boolean_gf256` authenticates the 256 dealt bit shares
//!      together with 4 `3 -> 1` privacy-amplified $\mathbb{F}_2^{64}$ mask words under 2-lane `Tower128`
//!      SPDZ Shamir MACs across all `0..n` parties (`spdz_authenticate_bs_gf256_words`), then opens
//!      `[s_k \oplus m_k]` via committed `commit_and_open_spdz_bs_gf256_quorum` and enforces upper
//!      bit-planes `1..8 == 0` (`1 - 2^{-255}` soundness, `0` Frobenius linearity bypass, `0` central RAM).
//!    - Over `Goldilocks`: `spdz_verify_seed256_boolean_goldilocks` authenticates all 256 bit shares
//!      under `GoldilocksExt2` SPDZ Shamir MACs across `0..n`, verifies `bsq_m = b_m^2` via LHL-amplified
//!      (`320`-bit, `< 2^{-129}`) Gilboa/MASCOT companion sacrifice, and opens `[bsq_m - b_m]`
//!      via committed `commit_and_open_spdz_goldilocks_batch_quorum`. Failure is unindexed.
//! 3. **`Π_refresh` (`Π_deg0`) & Dynamic Quorum Redistribution `Π_reshare` (`(t, n) -> (t', n')`):**
//!    - Rotates or redistributes shares under the bit-identical `PK`, enforces global degree
//!      consistency across all recipients and SPDZ Booleanity preservation on reshared committees,
//!      and volatile-wipes (`write_volatile` + `SeqCst` fence) all old committee shares in place.
//! 4. **Durable Persist-Before-Sign `FsWalEpochLatch` (`#[cfg(feature = "std")]`) & `EpochLatchState`:**
//!    - Implements [`crate::tsw_baggy::StatefulEpochLatch`] backed by an authenticated 97-byte WAL record
//!      written via `.tmp` `write_all` + `File::sync_all()` + atomic `fs::rename` + parent-directory
//!      `sync_all()` strictly *before* returning `Ok(epoch)` (`[P0-04]`).

use alloc::vec;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::fmt;

use crate::field::goldilocks::{Goldilocks, GoldilocksExt2};
use crate::field::tower::{
    PublicGf256Matrix, Tower128, TowerGf256, bs_gf256_insert_lane, bs_gf256_xor,
    lagrange_weights_zero_gf256,
};
use crate::preprocessing::{
    OtMesh, PartyPrivateRng, PreprocessError, commit_and_open_degree_ext2,
    commit_and_open_degree_tower128, commit_and_open_spdz_bs_gf256_quorum,
    commit_and_open_spdz_ext2_quorum, commit_and_open_spdz_goldilocks_batch_quorum,
    eval_poly_ext2_at_base, eval_poly_gf256, eval_poly_goldilocks,
    lagrange_weights_zero_goldilocks, pairwise_gilboa_ole_goldilocks, run_commit_and_open_coin,
    run_dealerless_pi_triple_f2, spdz_authenticate_bs_gf256_words,
    spdz_authenticate_goldilocks_batch_ext2, spdz_setup_alpha_gf256, spdz_setup_alpha_goldilocks,
    validate_all_eval_points_gf256, validate_all_eval_points_goldilocks,
};
use crate::sponge::keccak::{Cshake256Xof, cshake256_32 as cshake256_hash32, encode_multi_frame};
use crate::tsw_baggy::{
    EpochLatchError as StatefulLatchError, MonotonicEpochLatch, StatefulEpochLatch,
};
use crate::wipe::{
    ct_eq_bytes, ct_eq_bytes32, wipe_bytes, wipe_bytes32, wipe_ext2, wipe_gf256_slice,
    wipe_goldilocks, wipe_tower128_slice, wipe_u64s,
};

/// Canonical domain customization tag for Round-1 PQ DKG / Refresh / Reshare commitments.
pub const TAG_DKG_COMMIT: &[u8] = b"QSAG.PQ.DKG.COMMIT/v1";
/// Canonical domain customization tag for DKG joint Round-1 transcript hashing.
pub const TAG_DKG_ROUND1_TRANSCRIPT: &[u8] = b"QSAG.PQ.DKG.R1.TRANS/v2";
/// Canonical domain customization tag for DKG Fiat–Shamir masked-polynomial challenges.
pub const TAG_DKG_CHALLENGE: &[u8] = b"QSAG.PQ.DKG.CHAL/v2";
/// Canonical domain customization tag for authenticated `EpochLatchState` persistence.
pub const TAG_EPOCH_LATCH_MAC: &[u8] = b"QSAG.PQ.EPOCH_LATCH/v1";
/// Domain tag of the `(key, epoch, message digest)` binding a committee latch quorum reserves.
pub const TAG_EPOCH_LATCH_BINDING: &[u8] = b"QSAG.PQ.EPOCH_LATCH.BIND/v1";
/// Canonical domain customization tag for `fsync`-backed `FsWalEpochLatch` records.
pub const TAG_FS_WAL_LATCH_MAC: &[u8] = b"QSAG.PQ.FS_WAL_LATCH/v1";

/// Errors returned by `Π_dkg`, `Π_refresh`, or `Π_reshare`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DkgError {
    InvalidQuorum { t: usize, n: usize },
    InvalidEvaluationPoints,
    DuplicateOrInvalidOldSigner { party_id: usize },
    ShareAlreadyInvalidated { party_id: usize },
    DealerDisqualified { dealer_idx: usize },
    PrivatePacketVerificationFailed { dealer_idx: usize, recv_idx: usize },
    ZeroConstantCheckFailed { dealer_idx: usize },
    NonBooleanSeedBitDetected { bit_idx: usize },
    NonBooleanSeedDetected,
    PublicRootMismatch,
    PreprocessingFailed(PreprocessError),
    MalformedLatchBytes,
    LatchAuthenticationFailed,
}

impl fmt::Display for DkgError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidQuorum { t, n } => write!(f, "invalid DKG quorum t={}, n={}", t, n),
            Self::InvalidEvaluationPoints => {
                write!(f, "zero or duplicate Shamir evaluation point in 0..n")
            }
            Self::DuplicateOrInvalidOldSigner { party_id } => {
                write!(f, "duplicate or out-of-range old signer {}", party_id)
            }
            Self::ShareAlreadyInvalidated { party_id } => {
                write!(f, "custody share for party {} is invalidated", party_id)
            }
            Self::DealerDisqualified { dealer_idx } => {
                write!(f, "dealer {} disqualified during DKG verification", dealer_idx)
            }
            Self::PrivatePacketVerificationFailed {
                dealer_idx,
                recv_idx,
            } => write!(
                f,
                "private DKG packet verification failed (dealer {}, recipient {})",
                dealer_idx, recv_idx
            ),
            Self::ZeroConstantCheckFailed { dealer_idx } => {
                write!(f, "proactive refresh zero-constant check failed for dealer {}", dealer_idx)
            }
            Self::NonBooleanSeedBitDetected { bit_idx } => {
                write!(f, "non-Boolean dealt seed bit detected at bit {}", bit_idx)
            }
            Self::NonBooleanSeedDetected => write!(f, "non-Boolean seed detected"),
            Self::PublicRootMismatch => write!(f, "reshared public root differs from enrollment"),
            Self::PreprocessingFailed(e) => write!(f, "DKG SPDZ verification failed: {}", e),
            Self::MalformedLatchBytes => write!(f, "malformed EpochLatch record bytes"),
            Self::LatchAuthenticationFailed => write!(f, "EpochLatch MAC authentication failed"),
        }
    }
}

impl From<PreprocessError> for DkgError {
    fn from(e: PreprocessError) -> Self {
        match e {
            PreprocessError::DuplicateOrZeroEvalPoint => Self::InvalidEvaluationPoints,
            PreprocessError::NonBooleanBitDetected { .. } => {
                Self::NonBooleanSeedDetected
            }
            other => Self::PreprocessingFailed(other),
        }
    }
}

// ============================================================================
// 1. Secret-Share Custody Types (`!Clone`, Redacted `Debug`, Volatile `Drop` Wipe)
// ============================================================================

/// One party's $t$-of-$n$ Shamir share of a 32-byte (256-bit) seed over `TowerGf256` ($\mathcal{T}_3$).
///
/// Intentionally **`!Clone`** with redacted [`fmt::Debug`] and `write_volatile` wipe on [`Drop`].
pub struct ShamirSeedShare256 {
    pub party_id: usize,
    pub generation: u64,
    pub eval_point: TowerGf256,
    pub bit_shares: [TowerGf256; 256],
    invalidated: bool,
}

impl fmt::Debug for ShamirSeedShare256 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ShamirSeedShare256")
            .field("party_id", &self.party_id)
            .field("generation", &self.generation)
            .field("invalidated", &self.invalidated)
            .field("bit_shares", &"[REDACTED]")
            .finish()
    }
}

impl ShamirSeedShare256 {
    pub fn new(
        party_id: usize,
        generation: u64,
        eval_point: TowerGf256,
        bit_shares: [TowerGf256; 256],
    ) -> Self {
        Self {
            party_id,
            generation,
            eval_point,
            bit_shares,
            invalidated: false,
        }
    }

    #[inline]
    pub fn is_valid(&self) -> bool {
        !self.invalidated && self.eval_point != TowerGf256::ZERO
    }

    /// Deterministically zeroize all 256 `GF(2^8)` share bytes via `write_volatile` and mark
    /// this share permanently invalidated.
    pub fn wipe_and_invalidate(&mut self) {
        wipe_gf256_slice(core::slice::from_mut(&mut self.eval_point));
        wipe_gf256_slice(&mut self.bit_shares);
        self.invalidated = true;
    }

    /// Serialize this party's share for encrypted/local custody storage (`270` bytes).
    pub fn to_custody_bytes(&self) -> [u8; 270] {
        let mut out = [0u8; 270];
        out[0..4].copy_from_slice(&(self.party_id as u32).to_le_bytes());
        out[4..12].copy_from_slice(&self.generation.to_le_bytes());
        out[12] = self.eval_point.0;
        out[13] = self.invalidated as u8;
        for i in 0..256 {
            out[14 + i] = self.bit_shares[i].0;
        }
        out
    }

    pub fn from_custody_bytes(bytes: &[u8; 270]) -> Self {
        let party_id = u32::from_le_bytes(core::array::from_fn(|array_index| (bytes[0..4])[array_index])) as usize;
        let generation = u64::from_le_bytes(core::array::from_fn(|array_index| (bytes[4..12])[array_index]));
        let eval_point = TowerGf256(bytes[12]);
        let invalidated = bytes[13] != 0;
        let mut bit_shares = [TowerGf256::ZERO; 256];
        for i in 0..256 {
            bit_shares[i] = TowerGf256(bytes[14 + i]);
        }
        Self {
            party_id,
            generation,
            eval_point,
            bit_shares,
            invalidated,
        }
    }
}

impl Drop for ShamirSeedShare256 {
    fn drop(&mut self) {
        self.wipe_and_invalidate();
    }
}

/// One party's $t$-of-$n$ Shamir share of a 32-byte seed over `Goldilocks` (`bit_shares[0..256]`
/// verified in `{0, 1}` and packed linearly into canonical `0..=255` `byte_shares[0..32]`, enabling
/// zero-communication `< 2^56` limb assembly and verified Boolean preservation across reshares).
///
/// Intentionally **`!Clone`** with redacted [`fmt::Debug`] and `write_volatile` zeroization on [`Drop`].
pub struct ShamirPoseidonSeedShare {
    pub party_id: usize,
    pub generation: u64,
    pub eval_point: Goldilocks,
    pub bit_shares: [Goldilocks; 256],
    pub byte_shares: [Goldilocks; 32],
    invalidated: bool,
}

impl fmt::Debug for ShamirPoseidonSeedShare {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ShamirPoseidonSeedShare")
            .field("party_id", &self.party_id)
            .field("generation", &self.generation)
            .field("invalidated", &self.invalidated)
            .field("byte_shares", &"[REDACTED]")
            .finish()
    }
}

#[inline]
fn pack_goldilocks_bits_to_bytes(bit_shares: &[Goldilocks; 256]) -> [Goldilocks; 32] {
    let mut byte_shares = [Goldilocks::ZERO; 32];
    for k in 0..32 {
        let mut acc = Goldilocks::ZERO;
        for bit in 0..8 {
            acc += Goldilocks::from_u64_reduced(1u64 << bit) * bit_shares[8 * k + bit];
        }
        byte_shares[k] = acc;
    }
    byte_shares
}

impl ShamirPoseidonSeedShare {
    pub fn from_bit_shares(
        party_id: usize,
        generation: u64,
        eval_point: Goldilocks,
        bit_shares: [Goldilocks; 256],
    ) -> Self {
        let byte_shares = pack_goldilocks_bits_to_bytes(&bit_shares);
        Self {
            party_id,
            generation,
            eval_point,
            bit_shares,
            byte_shares,
            invalidated: false,
        }
    }

    pub fn new(
        party_id: usize,
        generation: u64,
        eval_point: Goldilocks,
        byte_shares: [Goldilocks; 32],
    ) -> Self {
        Self {
            party_id,
            generation,
            eval_point,
            bit_shares: [Goldilocks::ZERO; 256],
            byte_shares,
            invalidated: false,
        }
    }

    #[inline]
    pub fn is_valid(&self) -> bool {
        !self.invalidated && self.eval_point != Goldilocks::ZERO
    }

    pub fn wipe_and_invalidate(&mut self) {
        wipe_goldilocks(core::slice::from_mut(&mut self.eval_point));
        wipe_goldilocks(&mut self.bit_shares);
        wipe_goldilocks(&mut self.byte_shares);
        self.invalidated = true;
    }

    /// Custody serialization (`2,325` bytes: `21` header + `2,048` bit_shares + `256` byte_shares).
    pub fn to_custody_bytes(&self) -> [u8; 2325] {
        let mut out = [0u8; 2325];
        out[0..4].copy_from_slice(&(self.party_id as u32).to_le_bytes());
        out[4..12].copy_from_slice(&self.generation.to_le_bytes());
        out[12..20].copy_from_slice(&self.eval_point.to_be_bytes());
        out[20] = self.invalidated as u8;
        for (i, share) in self.bit_shares.iter().enumerate() {
            let off = 21 + 8 * i;
            out[off..off + 8].copy_from_slice(&share.to_be_bytes());
        }
        for (i, share) in self.byte_shares.iter().enumerate() {
            let off = 21 + 2048 + 8 * i;
            out[off..off + 8].copy_from_slice(&share.to_be_bytes());
        }
        out
    }

    pub fn from_custody_bytes(bytes: &[u8; 2325]) -> Option<Self> {
        let party_id = u32::from_le_bytes(core::array::from_fn(|array_index| (bytes[0..4])[array_index])) as usize;
        let generation = u64::from_le_bytes(core::array::from_fn(|array_index| (bytes[4..12])[array_index]));
        let eval_point =
            Goldilocks::from_be_bytes_canonical(core::array::from_fn(|array_index| (bytes[12..20])[array_index])).ok()?;
        let invalidated = bytes[20] != 0;
        let mut bit_shares = [Goldilocks::ZERO; 256];
        for (i, bit_shares_i_item) in bit_shares[..256].iter_mut().enumerate() {
            let off = 21 + 8 * i;
            *bit_shares_i_item =
                Goldilocks::from_be_bytes_canonical(core::array::from_fn(|array_index| (bytes[off..off + 8])[array_index]))
                    .ok()?;
        }
        let mut byte_shares = [Goldilocks::ZERO; 32];
        for (i, byte_shares_i_item) in byte_shares[..32].iter_mut().enumerate() {
            let off = 21 + 2048 + 8 * i;
            *byte_shares_i_item =
                Goldilocks::from_be_bytes_canonical(core::array::from_fn(|array_index| (bytes[off..off + 8])[array_index]))
                    .ok()?;
        }
        Some(Self {
            party_id,
            generation,
            eval_point,
            bit_shares,
            byte_shares,
            invalidated,
        })
    }
}

impl Drop for ShamirPoseidonSeedShare {
    fn drop(&mut self) {
        self.wipe_and_invalidate();
    }
}

/// Reconstruct a 32-byte secret from any `>= t` valid [`ShamirSeedShare256`] shares (used in tests).
pub fn shamir_reconstruct_seed32_gf256(shares: &[&ShamirSeedShare256]) -> Option<[u8; 32]> {
    if shares.is_empty() || shares.iter().any(|s| !s.is_valid()) {
        return None;
    }
    let pts: Vec<TowerGf256> = shares.iter().map(|s| s.eval_point).collect();
    let lambdas = lagrange_weights_zero_gf256(&pts)?;
    let l_mats: Vec<PublicGf256Matrix> = lambdas
        .iter()
        .map(|&l| PublicGf256Matrix::from_mul_const(l))
        .collect();
    let mut out = [0u8; 32];
    for bit_idx in 0..256 {
        let mut acc = TowerGf256::ZERO;
        for (s, mat) in shares.iter().zip(l_mats.iter()) {
            acc = acc.add(mat.mul_elem(s.bit_shares[bit_idx]));
        }
        match acc.0 {
            0 => {}
            1 => out[bit_idx / 8] |= 1u8 << (bit_idx % 8),
            _ => return None,
        }
    }
    Some(out)
}

/// Reconstruct a 32-byte secret from any `>= t` valid [`ShamirPoseidonSeedShare`] shares (used in tests).
pub fn shamir_reconstruct_seed32_goldilocks(
    shares: &[&ShamirPoseidonSeedShare],
) -> Option<[u8; 32]> {
    if shares.is_empty() || shares.iter().any(|s| !s.is_valid()) {
        return None;
    }
    let pts: Vec<Goldilocks> = shares.iter().map(|s| s.eval_point).collect();
    let lambdas = lagrange_weights_zero_goldilocks(&pts)?;
    let mut out = [0u8; 32];
    for (b_idx, out_b_idx_item) in out[..32].iter_mut().enumerate() {
        let mut acc = Goldilocks::ZERO;
        for (s, &lam) in shares.iter().zip(lambdas.iter()) {
            acc += lam * s.byte_shares[b_idx];
        }
        let v = acc.to_canonical_u64();
        if v > 255 {
            return None;
        }
        *out_b_idx_item = v as u8;
    }
    Some(out)
}

// ============================================================================
// 2. Polynomial Consistency Primitives & Transcript-Bound Commitments
// ============================================================================

/// Round-1 PQ share commitment `cSHAKE256("QSAG.PQ.DKG.COMMIT/v1", encodeMultiFrame [be4(dealer), be4(recv), salt, share_bytes])`.
#[inline]
pub fn dkg_commit_share(dealer: u32, recv: u32, salt: &[u8], share_bytes: &[u8]) -> [u8; 32] {
    let d_be = dealer.to_be_bytes();
    let r_be = recv.to_be_bytes();
    let frame = encode_multi_frame(&[&d_be, &r_be, salt, share_bytes]);
    cshake256_hash32(TAG_DKG_COMMIT, &frame)
}

/// Session-bound `pk_seed` contribution commitment (`Round 1`).
#[inline]
pub fn dkg_commit_pk_seed(
    session_id: &[u8; 32],
    dealer: usize,
    pk_seed_salt: &[u8; 32],
    pk_seed_contrib: &[u8; 32],
) -> [u8; 32] {
    let d_be = (dealer as u64).to_be_bytes();
    let frame = encode_multi_frame(&[
        session_id.as_slice(),
        b"PK_SEED",
        &d_be,
        pk_seed_salt.as_slice(),
        pk_seed_contrib.as_slice(),
    ]);
    cshake256_hash32(TAG_DKG_COMMIT, &frame)
}

/// Evaluate polynomial `coeffs[0] + coeffs[1] * x + ...` over 128-bit `Tower128` at `TowerGf256` point `x`.
#[inline]
pub fn eval_poly_tower128_at_gf256(coeffs: &[Tower128], x: TowerGf256) -> Tower128 {
    let xb = Tower128::embed_gf256(x);
    let mut acc = Tower128::ZERO;
    for &c in coeffs.iter().rev() {
        acc = acc.mul(xb).add(c);
    }
    acc
}

/// Public `Π_deg` Reed–Solomon degree-`< t` consistency check over `Goldilocks` across ALL `pts[0..n]`.
pub fn check_reed_solomon_deg_lt_t_goldilocks(
    t: usize,
    pts: &[Goldilocks],
    coeffs: &[Goldilocks],
    evals: &[Goldilocks],
) -> bool {
    if t == 0
        || coeffs.len() > t
        || pts.len() != evals.len()
        || validate_all_eval_points_goldilocks(pts).is_err()
    {
        return false;
    }
    pts.iter()
        .zip(evals.iter())
        .all(|(&x, &y)| eval_poly_goldilocks(coeffs, x) == y)
}

/// Public `Π_deg` Reed–Solomon degree-`< t` consistency check over `TowerGf256` across ALL `pts[0..n]`.
pub fn check_reed_solomon_deg_lt_t_gf256(
    t: usize,
    pts: &[TowerGf256],
    coeffs: &[TowerGf256],
    evals: &[TowerGf256],
) -> bool {
    if t == 0
        || coeffs.len() > t
        || pts.len() != evals.len()
        || validate_all_eval_points_gf256(pts).is_err()
    {
        return false;
    }
    pts.iter()
        .zip(evals.iter())
        .all(|(&x, &y)| eval_poly_gf256(coeffs, x) == y)
}

/// Public `Π_deg0` zero-constant proactive refresh check over `Goldilocks` (`p(0) == 0`).
pub fn check_zero_constant_refresh_goldilocks(
    t: usize,
    pts: &[Goldilocks],
    refresh_coeffs: &[Goldilocks],
    refresh_shares: &[Goldilocks],
) -> bool {
    check_reed_solomon_deg_lt_t_goldilocks(t, pts, refresh_coeffs, refresh_shares)
        && eval_poly_goldilocks(refresh_coeffs, Goldilocks::ZERO) == Goldilocks::ZERO
}

/// Public `Π_deg0` zero-constant proactive refresh check over `TowerGf256` (`p(0) == 0`).
pub fn check_zero_constant_refresh_gf256(
    t: usize,
    pts: &[TowerGf256],
    refresh_coeffs: &[TowerGf256],
    refresh_shares: &[TowerGf256],
) -> bool {
    check_reed_solomon_deg_lt_t_gf256(t, pts, refresh_coeffs, refresh_shares)
        && eval_poly_gf256(refresh_coeffs, TowerGf256::ZERO) == TowerGf256::ZERO
}

// ============================================================================
// 3. Strict 2-Round Commit-Then-Open Scalar `Π_dkg` over `Goldilocks` + `Ext2`
// ============================================================================

/// Public allegation against a dealer. Only an opening matching the dealer's
/// broadcast commitment constitutes evidence; arbitrary recipient bytes do not.
/// `committed_digest` is an untrusted transport hint, never an attribution source.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DkgShareComplaint {
    pub recv_idx: usize,
    pub committed_digest: [u8; 32],
    pub dealer_opened_salt: Vec<u8>,
    pub dealer_opened_share_bytes: Vec<u8>,
}

/// Point-to-point private share packet over `Goldilocks` (`!Clone`, redacted `Debug`, `Drop` wipe).
pub struct DkgPrivateSharePacket {
    pub recv_idx: usize,
    pub f_share: Goldilocks,
    pub m_share: GoldilocksExt2,
    pub salt: [u8; 32],
}

impl fmt::Debug for DkgPrivateSharePacket {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("DkgPrivateSharePacket([REDACTED])")
    }
}

impl Drop for DkgPrivateSharePacket {
    fn drop(&mut self) {
        wipe_goldilocks(core::slice::from_mut(&mut self.f_share));
        wipe_ext2(core::slice::from_mut(&mut self.m_share));
        wipe_bytes32(&mut self.salt);
    }
}

impl DkgPrivateSharePacket {
    #[inline]
    pub fn encode_share_bytes(&self) -> [u8; 24] {
        let mut out = [0u8; 24];
        out[0..8].copy_from_slice(&self.f_share.to_be_bytes());
        out[8..16].copy_from_slice(&self.m_share.c0.to_be_bytes());
        out[16..24].copy_from_slice(&self.m_share.c1.to_be_bytes());
        out
    }
}

/// Round-1 public commitment broadcast by dealer `dealer_idx` (`0` cleartext `pk_seed_contrib`!).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GoldilocksDealerRound1Commit {
    pub dealer_idx: usize,
    pub pk_seed_commitment: [u8; 32],
    pub share_commitments: Vec<[u8; 32]>,
}

/// Round-2 public opening broadcast by dealer `dealer_idx` (published ONLY after all Round-1
/// commitments across the committee are locked into `joint_round1_digest`!).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GoldilocksDealerRound2Open {
    pub dealer_idx: usize,
    pub masked_poly_coeffs: Vec<GoldilocksExt2>,
    pub pk_seed_contrib: [u8; 32],
    pub pk_seed_salt: [u8; 32],
}

/// Ephemeral dealer secret state held between Round 1 and Round 2 (`!Clone`, wiped on `Drop`).
pub struct GoldilocksDealerPendingSecret {
    dealer_idx: usize,
    f_coeffs: Vec<Goldilocks>,
    m_coeffs: Vec<GoldilocksExt2>,
    pk_seed_contrib: [u8; 32],
    pk_seed_salt: [u8; 32],
}

impl fmt::Debug for GoldilocksDealerPendingSecret {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("GoldilocksDealerPendingSecret([REDACTED])")
    }
}

impl Drop for GoldilocksDealerPendingSecret {
    fn drop(&mut self) {
        wipe_goldilocks(&mut self.f_coeffs);
        wipe_ext2(&mut self.m_coeffs);
        wipe_bytes32(&mut self.pk_seed_contrib);
        wipe_bytes32(&mut self.pk_seed_salt);
    }
}

/// Hash ALL dealers' Round-1 commitments together with `(session_id, t, n, eval_points[0..n])`
/// into an immutable Round-1 transcript digest before Round-2 openings begin.
pub fn compute_goldilocks_round1_transcript(
    session_id: &[u8; 32],
    t: usize,
    pts: &[Goldilocks],
    r1_commits: &[GoldilocksDealerRound1Commit],
) -> [u8; 32] {
    let mut xof = Cshake256Xof::new(TAG_DKG_ROUND1_TRANSCRIPT);
    xof.absorb(b"GL_SCALAR");
    xof.absorb(session_id);
    xof.absorb(&(t as u64).to_be_bytes());
    xof.absorb(&(pts.len() as u64).to_be_bytes());
    for pt in pts {
        xof.absorb(&pt.to_be_bytes());
    }
    xof.absorb(&(r1_commits.len() as u64).to_be_bytes());
    for c in r1_commits {
        xof.absorb(&(c.dealer_idx as u64).to_be_bytes());
        xof.absorb(&c.pk_seed_commitment);
        xof.absorb(&(c.share_commitments.len() as u64).to_be_bytes());
        for sc in &c.share_commitments {
            xof.absorb(sc);
        }
    }
    let mut out = [0u8; 32];
    xof.squeeze(&mut out);
    out
}

/// Derive a non-zero 128-bit `GoldilocksExt2` challenge bound to `(session_id, t, n, pts, joint_round1_digest, dealer_idx)`.
pub fn derive_dkg_transcript_challenge_goldilocks(
    session_id: &[u8; 32],
    t: usize,
    pts: &[Goldilocks],
    joint_round1_digest: &[u8; 32],
    dealer_idx: usize,
) -> GoldilocksExt2 {
    let mut xof = Cshake256Xof::new(TAG_DKG_CHALLENGE);
    xof.absorb(b"GL_SCALAR_CHAL");
    xof.absorb(session_id);
    xof.absorb(&(t as u64).to_be_bytes());
    xof.absorb(&(pts.len() as u64).to_be_bytes());
    for pt in pts {
        xof.absorb(&pt.to_be_bytes());
    }
    xof.absorb(joint_round1_digest);
    xof.absorb(&(dealer_idx as u64).to_be_bytes());
    let mut digest = [0u8; 32];
    xof.squeeze(&mut digest);
    let c0 = Goldilocks::from_u128_reduced(u128::from_be_bytes(core::array::from_fn(|array_index| (digest[0..16])[array_index])));
    let mut c1 =
        Goldilocks::from_u128_reduced(u128::from_be_bytes(core::array::from_fn(|array_index| (digest[16..32])[array_index])));
    if c0 == Goldilocks::ZERO && c1 == Goldilocks::ZERO {
        c1 = Goldilocks::ONE;
    }
    GoldilocksExt2::new(c0, c1)
}

impl GoldilocksDealerRound1Commit {
    #[expect(clippy::too_many_arguments, reason = "Preserve the explicit statement, role, witness and randomness bindings in this protocol API")]
    pub fn commit_round1(
        session_id: &[u8; 32],
        dealer_idx: usize,
        t: usize,
        pts: &[Goldilocks],
        f_coeffs: Vec<Goldilocks>,
        m_coeffs: Vec<GoldilocksExt2>,
        salts: &[[u8; 32]],
        pk_seed_contrib: [u8; 32],
        pk_seed_salt: [u8; 32],
    ) -> Result<
        (
            Self,
            GoldilocksDealerPendingSecret,
            Vec<DkgPrivateSharePacket>,
        ),
        DkgError,
    > {
        let n = pts.len();
        if t == 0 || f_coeffs.len() > t || m_coeffs.len() > t || n < t || salts.len() != n {
            return Err(DkgError::InvalidQuorum { t, n });
        }
        validate_all_eval_points_goldilocks(pts)?;

        let pk_seed_commitment =
            dkg_commit_pk_seed(session_id, dealer_idx, &pk_seed_salt, &pk_seed_contrib);
        let mut share_commitments = Vec::with_capacity(n);
        let mut private_packets = Vec::with_capacity(n);
        for j in 0..n {
            let fj = eval_poly_goldilocks(&f_coeffs, pts[j]);
            let mj = eval_poly_ext2_at_base(&m_coeffs, pts[j]);
            let pkt = DkgPrivateSharePacket {
                recv_idx: j,
                f_share: fj,
                m_share: mj,
                salt: salts[j],
            };
            let mut pkt_bytes = pkt.encode_share_bytes();
            let comm = dkg_commit_share(dealer_idx as u32, j as u32, &salts[j], &pkt_bytes);
            wipe_bytes(&mut pkt_bytes);
            share_commitments.push(comm);
            private_packets.push(pkt);
        }

        Ok((
            Self {
                dealer_idx,
                pk_seed_commitment,
                share_commitments,
            },
            GoldilocksDealerPendingSecret {
                dealer_idx,
                f_coeffs,
                m_coeffs,
                pk_seed_contrib,
                pk_seed_salt,
            },
            private_packets,
        ))
    }
}

impl GoldilocksDealerPendingSecret {
    pub fn open_round2(
        self,
        session_id: &[u8; 32],
        t: usize,
        pts: &[Goldilocks],
        joint_round1_digest: &[u8; 32],
    ) -> GoldilocksDealerRound2Open {
        let chal = derive_dkg_transcript_challenge_goldilocks(
            session_id,
            t,
            pts,
            joint_round1_digest,
            self.dealer_idx,
        );
        let deg_len = self.f_coeffs.len().max(self.m_coeffs.len());
        let mut masked_poly_coeffs = Vec::with_capacity(deg_len);
        for k in 0..deg_len {
            let fk = self.f_coeffs.get(k).copied().unwrap_or(Goldilocks::ZERO);
            let mk = self
                .m_coeffs
                .get(k)
                .copied()
                .unwrap_or(GoldilocksExt2::ZERO);
            masked_poly_coeffs.push(chal.mul_base(fk) + mk);
        }
        GoldilocksDealerRound2Open {
            dealer_idx: self.dealer_idx,
            masked_poly_coeffs,
            pk_seed_contrib: self.pk_seed_contrib,
            pk_seed_salt: self.pk_seed_salt,
        }
    }
}

/// Recipient-side local verification of private `DkgPrivateSharePacket` against `(Round1Commit, Round2Open)`.
pub fn verify_dkg_private_packet_goldilocks(
    session_id: &[u8; 32],
    t: usize,
    pts: &[Goldilocks],
    joint_round1_digest: &[u8; 32],
    r1: &GoldilocksDealerRound1Commit,
    r2: &GoldilocksDealerRound2Open,
    packet: &DkgPrivateSharePacket,
) -> bool {
    if r1.dealer_idx != r2.dealer_idx
        || packet.recv_idx >= pts.len()
        || r1.share_commitments.len() != pts.len()
        || validate_all_eval_points_goldilocks(pts).is_err()
    {
        return false;
    }
    let mut pkt_bytes = packet.encode_share_bytes();
    let comm = dkg_commit_share(
        r1.dealer_idx as u32,
        packet.recv_idx as u32,
        &packet.salt,
        &pkt_bytes,
    );
    wipe_bytes(&mut pkt_bytes);
    if !ct_eq_bytes32(&comm, &r1.share_commitments[packet.recv_idx]) {
        return false;
    }
    let chal = derive_dkg_transcript_challenge_goldilocks(
        session_id,
        t,
        pts,
        joint_round1_digest,
        r1.dealer_idx,
    );
    let expected = eval_poly_ext2_at_base(&r2.masked_poly_coeffs, pts[packet.recv_idx]);
    (chal.mul_base(packet.f_share) + packet.m_share).ct_eq(expected)
}

/// Publicly qualify or disqualify a dealer in 2-round PQ dealerless DKG (`Π_deg`) over `Goldilocks`.
pub fn verify_and_qualify_dkg_dealer_goldilocks(
    session_id: &[u8; 32],
    t: usize,
    pts: &[Goldilocks],
    joint_round1_digest: &[u8; 32],
    r1: &GoldilocksDealerRound1Commit,
    r2: &GoldilocksDealerRound2Open,
    complaints: &[DkgShareComplaint],
) -> bool {
    let n = pts.len();
    if t == 0
        || t > n
        || r1.dealer_idx != r2.dealer_idx
        || r1.share_commitments.len() != n
        || r2.masked_poly_coeffs.len() > t
        || validate_all_eval_points_goldilocks(pts).is_err()
    {
        return false;
    }
    let expected_pk_comm =
        dkg_commit_pk_seed(session_id, r1.dealer_idx, &r2.pk_seed_salt, &r2.pk_seed_contrib);
    if !ct_eq_bytes32(&expected_pk_comm, &r1.pk_seed_commitment) {
        return false;
    }

    let c0_coeffs: Vec<Goldilocks> = r2.masked_poly_coeffs.iter().map(|c| c.c0).collect();
    let c1_coeffs: Vec<Goldilocks> = r2.masked_poly_coeffs.iter().map(|c| c.c1).collect();
    let c0_evals: Vec<Goldilocks> = pts
        .iter()
        .map(|&x| eval_poly_goldilocks(&c0_coeffs, x))
        .collect();
    let c1_evals: Vec<Goldilocks> = pts
        .iter()
        .map(|&x| eval_poly_goldilocks(&c1_coeffs, x))
        .collect();
    if !check_reed_solomon_deg_lt_t_goldilocks(t, pts, &c0_coeffs, &c0_evals)
        || !check_reed_solomon_deg_lt_t_goldilocks(t, pts, &c1_coeffs, &c1_evals)
    {
        return false;
    }

    let chal = derive_dkg_transcript_challenge_goldilocks(
        session_id,
        t,
        pts,
        joint_round1_digest,
        r1.dealer_idx,
    );

    for comp in complaints {
        // A recipient's unauthenticated allegation is not evidence against a dealer.
        // Only an opening of the dealer's broadcast commitment can disqualify it.
        if comp.recv_idx >= n {
            continue;
        }
        let comm = dkg_commit_share(
            r1.dealer_idx as u32,
            comp.recv_idx as u32,
            &comp.dealer_opened_salt,
            &comp.dealer_opened_share_bytes,
        );
        if !ct_eq_bytes32(&comm, &r1.share_commitments[comp.recv_idx]) {
            continue;
        }
        // The complainant's copy of the digest is not an authenticated source.
        // A binding opening with malformed encoding *is* dealer misconduct.
        if comp.dealer_opened_share_bytes.len() != 24 {
            return false;
        }
        let Ok(f_open) = Goldilocks::from_be_bytes_canonical(
            core::array::from_fn(|array_index| (comp.dealer_opened_share_bytes[0..8])[array_index]),
        ) else {
            return false;
        };
        let Ok(m0_open) = Goldilocks::from_be_bytes_canonical(
            core::array::from_fn(|array_index| (comp.dealer_opened_share_bytes[8..16])[array_index]),
        ) else {
            return false;
        };
        let Ok(m1_open) = Goldilocks::from_be_bytes_canonical(
            core::array::from_fn(|array_index| (comp.dealer_opened_share_bytes[16..24])[array_index]),
        ) else {
            return false;
        };
        let m_open = GoldilocksExt2::new(m0_open, m1_open);
        let expected_eval = GoldilocksExt2::new(c0_evals[comp.recv_idx], c1_evals[comp.recv_idx]);
        if !(chal.mul_base(f_open) + m_open).ct_eq(expected_eval) {
            return false;
        }
    }

    true
}

// ============================================================================
// 4. Strict 2-Round Vector `Π_dkg` / `Π_refresh` / `Π_reshare` over `TowerGf256`
// ============================================================================

/// Point-to-point private packet for 256-bit seed dealing over `TowerGf256` + `Tower128`
/// (`!Clone`, redacted `Debug`, `write_volatile` `Drop` wipe).
pub struct Gf256SeedPrivatePacket {
    pub recv_idx: usize,
    pub f_shares: [TowerGf256; 256],
    pub m_shares: [Tower128; 256],
    pub salt: [u8; 32],
}

impl fmt::Debug for Gf256SeedPrivatePacket {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Gf256SeedPrivatePacket([REDACTED])")
    }
}

impl Drop for Gf256SeedPrivatePacket {
    fn drop(&mut self) {
        wipe_gf256_slice(&mut self.f_shares);
        wipe_tower128_slice(&mut self.m_shares);
        wipe_bytes32(&mut self.salt);
    }
}

impl Gf256SeedPrivatePacket {
    pub fn encode_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(256 * 17);
        for b in 0..256 {
            out.push(self.f_shares[b].0);
            out.extend_from_slice(&self.m_shares[b].0.to_le_bytes());
        }
        out
    }
}

/// Round-1 public commitment wire message for 256-bit `TowerGf256` seed dealing
/// (contains **zero** cleartext `pk_seed_contrib` or `masked_polys`!).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Gf256SeedDealerRound1Commit {
    pub dealer_idx: usize,
    pub pk_seed_commitment: [u8; 32],
    pub share_commitments: Vec<[u8; 32]>,
}

/// Round-2 public opening wire message for 256-bit `TowerGf256` seed dealing
/// (published strictly *after* all Round-1 commitments are locked into `joint_round1_digest`!).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Gf256SeedDealerRound2Open {
    pub dealer_idx: usize,
    pub masked_polys: Vec<Vec<Tower128>>,
    pub pk_seed_contrib: [u8; 32],
    pub pk_seed_salt: [u8; 32],
}

/// Ephemeral dealer secret state held between Round 1 and Round 2 (`!Clone`, wiped on `Drop`).
pub struct Gf256SeedDealerPendingSecret {
    dealer_idx: usize,
    t: usize,
    f_polys: Vec<Vec<TowerGf256>>,
    m_polys: Vec<Vec<Tower128>>,
    pk_seed_contrib: [u8; 32],
    pk_seed_salt: [u8; 32],
}

impl fmt::Debug for Gf256SeedDealerPendingSecret {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Gf256SeedDealerPendingSecret([REDACTED])")
    }
}

impl Drop for Gf256SeedDealerPendingSecret {
    fn drop(&mut self) {
        for fp in &mut self.f_polys {
            wipe_gf256_slice(fp);
        }
        for mp in &mut self.m_polys {
            wipe_tower128_slice(mp);
        }
        wipe_bytes32(&mut self.pk_seed_contrib);
        wipe_bytes32(&mut self.pk_seed_salt);
    }
}

/// Hash ALL dealers' Round-1 commitments together with `(session_id, t, n, eval_points[0..n])`.
pub fn compute_gf256_round1_transcript(
    session_id: &[u8; 32],
    t: usize,
    pts: &[TowerGf256],
    r1_commits: &[Gf256SeedDealerRound1Commit],
) -> [u8; 32] {
    let mut xof = Cshake256Xof::new(TAG_DKG_ROUND1_TRANSCRIPT);
    xof.absorb(b"GF256_VEC");
    xof.absorb(session_id);
    xof.absorb(&(t as u64).to_be_bytes());
    xof.absorb(&(pts.len() as u64).to_be_bytes());
    for pt in pts {
        xof.absorb(&[pt.0]);
    }
    xof.absorb(&(r1_commits.len() as u64).to_be_bytes());
    for c in r1_commits {
        xof.absorb(&(c.dealer_idx as u64).to_be_bytes());
        xof.absorb(&c.pk_seed_commitment);
        xof.absorb(&(c.share_commitments.len() as u64).to_be_bytes());
        for sc in &c.share_commitments {
            xof.absorb(sc);
        }
    }
    let mut out = [0u8; 32];
    xof.squeeze(&mut out);
    out
}

fn derive_gf256_vector_challenges(
    session_id: &[u8; 32],
    t: usize,
    pts: &[TowerGf256],
    joint_round1_digest: &[u8; 32],
    dealer_idx: usize,
) -> [Tower128; 256] {
    let mut xof = Cshake256Xof::new(TAG_DKG_CHALLENGE);
    xof.absorb(b"GF256_VEC_CHAL");
    xof.absorb(session_id);
    xof.absorb(&(t as u64).to_be_bytes());
    xof.absorb(&(pts.len() as u64).to_be_bytes());
    for pt in pts {
        xof.absorb(&[pt.0]);
    }
    xof.absorb(joint_round1_digest);
    xof.absorb(&(dealer_idx as u64).to_be_bytes());
    let mut root = [0u8; 32];
    xof.squeeze(&mut root);

    let mut prg = PartyPrivateRng::from_seed(root, b"GF256_VEC_CHAL_EXPAND");
    wipe_bytes32(&mut root);
    let mut out = [Tower128::ZERO; 256];
    for ch in &mut out {
        let mut v = prg.next_tower128();
        if v.0 == 0 {
            v = Tower128::ONE;
        }
        *ch = v;
    }
    out
}

/// Round 1 of 256-bit `TowerGf256` seed dealing: commits to `pk_seed_contrib` and all recipient
/// packets without revealing `pk_seed_contrib` or `masked_polys`.
pub fn deal_gf256_seed_round1(
    session_id: &[u8; 32],
    dealer_idx: usize,
    t: usize,
    pts: &[TowerGf256],
    mode_constants: Option<[TowerGf256; 256]>,
    zero_constant_mask: bool,
    rng: &mut PartyPrivateRng,
) -> Result<
    (
        Gf256SeedDealerRound1Commit,
        Gf256SeedDealerPendingSecret,
        Vec<Gf256SeedPrivatePacket>,
    ),
    DkgError,
> {
    let n = pts.len();
    if t == 0 || t > n {
        return Err(DkgError::InvalidQuorum { t, n });
    }
    validate_all_eval_points_gf256(pts)?;

    let pk_seed_contrib = rng.next_bytes32();
    let pk_seed_salt = rng.next_bytes32();
    let pk_seed_commitment =
        dkg_commit_pk_seed(session_id, dealer_idx, &pk_seed_salt, &pk_seed_contrib);

    let mut f_polys = vec![vec![TowerGf256::ZERO; t]; 256];
    let mut m_polys = vec![vec![Tower128::ZERO; t]; 256];

    for b in 0..256 {
        f_polys[b][0] = match mode_constants {
            Some(ref arr) => arr[b],
            None => TowerGf256((rng.next_u64() & 1) as u8),
        };
        m_polys[b][0] = if zero_constant_mask {
            Tower128::ZERO
        } else {
            rng.next_tower128()
        };
        for k in 1..t {
            f_polys[b][k] = TowerGf256((rng.next_u64() & 0xFF) as u8);
            m_polys[b][k] = rng.next_tower128();
        }
    }

    let mut share_commitments = Vec::with_capacity(n);
    let mut packets = Vec::with_capacity(n);
    for (j, pts_j_item) in pts[..n].iter().enumerate() {
        let mut f_shares = [TowerGf256::ZERO; 256];
        let mut m_shares = [Tower128::ZERO; 256];
        for b in 0..256 {
            f_shares[b] = eval_poly_gf256(&f_polys[b], *pts_j_item);
            m_shares[b] = eval_poly_tower128_at_gf256(&m_polys[b], *pts_j_item);
        }
        let salt = rng.next_bytes32();
        let pkt = Gf256SeedPrivatePacket {
            recv_idx: j,
            f_shares,
            m_shares,
            salt,
        };
        let mut raw = pkt.encode_bytes();
        let comm = dkg_commit_share(dealer_idx as u32, j as u32, &salt, &raw);
        wipe_bytes(&mut raw);
        share_commitments.push(comm);
        packets.push(pkt);
    }

    Ok((
        Gf256SeedDealerRound1Commit {
            dealer_idx,
            pk_seed_commitment,
            share_commitments,
        },
        Gf256SeedDealerPendingSecret {
            dealer_idx,
            t,
            f_polys,
            m_polys,
            pk_seed_contrib,
            pk_seed_salt,
        },
        packets,
    ))
}

impl Gf256SeedDealerPendingSecret {
    /// Round 2 of 256-bit `TowerGf256` seed dealing: opens `(masked_polys, pk_seed_contrib, pk_seed_salt)`
    /// against the locked `joint_round1_digest`.
    pub fn open_round2(
        self,
        session_id: &[u8; 32],
        pts: &[TowerGf256],
        joint_round1_digest: &[u8; 32],
    ) -> Gf256SeedDealerRound2Open {
        let chals = derive_gf256_vector_challenges(
            session_id,
            self.t,
            pts,
            joint_round1_digest,
            self.dealer_idx,
        );
        let mut masked_polys = Vec::with_capacity(256);
        for (b, chals_b_item) in chals[..256].iter().enumerate() {
            let mut mp = Vec::with_capacity(self.t);
            for k in 0..self.t {
                mp.push(
                    (*chals_b_item)
                        .mul(Tower128::embed_gf256(self.f_polys[b][k]))
                        .add(self.m_polys[b][k]),
                );
            }
            masked_polys.push(mp);
        }
        Gf256SeedDealerRound2Open {
            dealer_idx: self.dealer_idx,
            masked_polys,
            pk_seed_contrib: self.pk_seed_contrib,
            pk_seed_salt: self.pk_seed_salt,
        }
    }
}

/// Verify both the public `(Gf256SeedDealerRound1Commit, Gf256SeedDealerRound2Open)` pair and
/// recipient `recv_idx`'s own private `Gf256SeedPrivatePacket`.
#[expect(clippy::too_many_arguments, reason = "Keep commitment, opening, private packet and session/quorum bindings explicit")]
pub fn verify_gf256_seed_dealing(
    session_id: &[u8; 32],
    t: usize,
    pts: &[TowerGf256],
    joint_round1_digest: &[u8; 32],
    r1: &Gf256SeedDealerRound1Commit,
    r2: &Gf256SeedDealerRound2Open,
    packet: &Gf256SeedPrivatePacket,
    require_zero_constant: bool,
) -> Result<(), DkgError> {
    let n = pts.len();
    if t == 0 || t > n {
        return Err(DkgError::InvalidQuorum { t, n });
    }
    validate_all_eval_points_gf256(pts)?;

    if r1.dealer_idx != r2.dealer_idx
        || r1.share_commitments.len() != n
        || r2.masked_polys.len() != 256
    {
        return Err(DkgError::DealerDisqualified {
            dealer_idx: r1.dealer_idx,
        });
    }
    let pk_comm =
        dkg_commit_pk_seed(session_id, r1.dealer_idx, &r2.pk_seed_salt, &r2.pk_seed_contrib);
    if !ct_eq_bytes32(&pk_comm, &r1.pk_seed_commitment) {
        return Err(DkgError::DealerDisqualified {
            dealer_idx: r1.dealer_idx,
        });
    }
    for poly in r2.masked_polys.iter().take(256) {
        if poly.len() > t {
            return Err(DkgError::DealerDisqualified {
                dealer_idx: r1.dealer_idx,
            });
        }
        if require_zero_constant
            && !poly
                .first()
                .copied()
                .unwrap_or(Tower128::ZERO)
                .ct_eq(Tower128::ZERO)
        {
            return Err(DkgError::ZeroConstantCheckFailed {
                dealer_idx: r1.dealer_idx,
            });
        }
    }

    if packet.recv_idx >= n {
        return Err(DkgError::PrivatePacketVerificationFailed {
            dealer_idx: r1.dealer_idx,
            recv_idx: packet.recv_idx,
        });
    }
    let mut raw = packet.encode_bytes();
    let comm = dkg_commit_share(
        r1.dealer_idx as u32,
        packet.recv_idx as u32,
        &packet.salt,
        &raw,
    );
    wipe_bytes(&mut raw);
    if !ct_eq_bytes32(&comm, &r1.share_commitments[packet.recv_idx]) {
        return Err(DkgError::PrivatePacketVerificationFailed {
            dealer_idx: r1.dealer_idx,
            recv_idx: packet.recv_idx,
        });
    }

    let chals =
        derive_gf256_vector_challenges(session_id, t, pts, joint_round1_digest, r1.dealer_idx);
    let x = pts[packet.recv_idx];
    for (b, chals_b_item) in chals[..256].iter().enumerate() {
        let lhs = (*chals_b_item)
            .mul(Tower128::embed_gf256(packet.f_shares[b]))
            .add(packet.m_shares[b]);
        let rhs = eval_poly_tower128_at_gf256(&r2.masked_polys[b], x);
        if !lhs.ct_eq(rhs) {
            return Err(DkgError::PrivatePacketVerificationFailed {
                dealer_idx: r1.dealer_idx,
                recv_idx: packet.recv_idx,
            });
        }
    }
    Ok(())
}

/// SPDZ-MAC-authenticated Booleanity + global `0..n` degree-`< t` verification for 256-bit
/// `TowerGf256` seed shares (`1 - 2^{-255}` soundness even under dishonest majority $2t - 1 > n$,
/// `0` central-RAM masks, `0` Frobenius linearity bypass, `0` secret leakage).
pub fn spdz_verify_seed256_boolean_gf256(
    session_id: &[u8; 32],
    t: usize,
    eval_points: &[TowerGf256],
    ot_mesh: &mut OtMesh,
    bit_shares_per_party: &[[TowerGf256; 256]],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<(), DkgError> {
    let n = eval_points.len();
    if t == 0
        || t > n
        || n < 2
        || ot_mesh.n != n
        || bit_shares_per_party.len() != n
        || party_rngs.len() != n
    {
        return Err(DkgError::InvalidQuorum { t, n });
    }
    validate_all_eval_points_gf256(eval_points)?;

    // 1. Pack `256` `TowerGf256` shares per party into `4` `BitslicedGf256x64` words
    let mut s_words = vec![vec![[0u64; 8]; 4]; n];
    for p in 0..n {
        for w in 0..4 {
            for lane in 0..64 {
                bs_gf256_insert_lane(
                    &mut s_words[p][w],
                    lane,
                    bit_shares_per_party[p][64 * w + lane],
                );
            }
        }
    }

    // 2. Generate `4` 2-lane-BDOZ + SPDZ-Booleanity-verified Boolean mask words `m_k \in F_2^{64}`
    let mask_sid = cshake256_hash32(b"QSAG.DKG.GF256.BOOL.MASK/v1", session_id);
    let mut mask_vaults =
        run_dealerless_pi_triple_f2(mask_sid, t, eval_points, 4, ot_mesh, party_rngs)?;

    // 3. Authenticate `[s_0..s_3, m_0..m_3]` under a unified 2-lane `Tower128` SPDZ MAC key across `0..n`
    // (`spdz_authenticate_bs_gf256_words` also enforces global degree `< t` across ALL `0..n` parties!)
    let auth_sid = cshake256_hash32(b"QSAG.DKG.GF256.BOOL.AUTH/v1", session_id);
    let (mut alpha_contribs, mut alpha_shamir) =
        spdz_setup_alpha_gf256(&auth_sid, t, eval_points, party_rngs)?;

    let mut flat_words = vec![Vec::with_capacity(8); n];
    for p in 0..n {
        flat_words[p].extend_from_slice(&s_words[p]);
        for _ in 0..4 {
            let tr = mask_vaults[p].pop_triple()?;
            flat_words[p].push(tr.a);
        }
        for w in &mut s_words[p] {
            wipe_u64s(w);
        }
    }
    let mut flat_macs = spdz_authenticate_bs_gf256_words(
        &auth_sid,
        t,
        eval_points,
        ot_mesh,
        &alpha_contribs,
        &alpha_shamir,
        &flat_words,
        party_rngs,
    )?;
    for ac in &mut alpha_contribs {
        wipe_tower128_slice(ac);
    }

    // 4. Commit-before-open `[u_w] = [s_w \oplus m_w]` (`w = 0..4`) with SPDZ `MacCheck`:
    // - Plane `0` is masked by uniform `m_w[0] \in {0,1}^{64}` -> `0` bits of `s_w` leaked!
    // - Planes `1..8` of `m_w` are `0` -> ANY `s_{64w+bit} \notin F_2` sets `(u_w[pl] >> bit) & 1 == 1`
    //   and CANNOT be cancelled by corrupt signers without breaking the 2-lane `Tower128` SPDZ MAC!
    let mut u_shares = vec![[0u64; 8]; n];
    let mut u_macs = vec![[[Tower128::ZERO; 64]; 2]; n];
    for w in 0..4 {
        for p in 0..n {
            u_shares[p] = bs_gf256_xor(&flat_words[p][w], &flat_words[p][4 + w]);
            for lane in 0..2 {
                for bit in 0..64 {
                    u_macs[p][lane][bit] =
                        flat_macs[p][w][lane][bit].add(flat_macs[p][4 + w][lane][bit]);
                }
            }
        }
        let u_open = commit_and_open_spdz_bs_gf256_quorum(
            &auth_sid,
            "dkg_gf256_seed_bool_check",
            t,
            eval_points,
            &u_shares,
            &u_macs,
            &alpha_shamir,
            party_rngs,
        )?;
        for bit in 0..64 {
            let mut upper_nonzero = 0u64;
            for u_open_pl_item in u_open[..8].iter().skip(1) {
                upper_nonzero |= (*u_open_pl_item >> bit) & 1;
            }
            if upper_nonzero != 0 {
                for p in 0..n {
                    for fw in &mut flat_words[p] {
                        wipe_u64s(fw);
                    }
                    for fm in &mut flat_macs[p] {
                        wipe_tower128_slice(&mut fm[0]);
                        wipe_tower128_slice(&mut fm[1]);
                    }
                    wipe_tower128_slice(&mut alpha_shamir[p]);
                }
                return Err(DkgError::NonBooleanSeedBitDetected {
                    bit_idx: 64 * w + bit,
                });
            }
        }
    }

    for p in 0..n {
        for fw in &mut flat_words[p] {
            wipe_u64s(fw);
        }
        for fm in &mut flat_macs[p] {
            wipe_tower128_slice(&mut fm[0]);
            wipe_tower128_slice(&mut fm[1]);
        }
        wipe_tower128_slice(&mut alpha_shamir[p]);
    }
    Ok(())
}

/// Run full 2-round commit-then-open dealerless `Π_dkg` over `TowerGf256` generating `([sk_seed], pk_seed)`:
/// - Round 1: all parties broadcast `Gf256SeedDealerRound1Commit` (`pk_seed_commitment` + `share_commitments`)
///   and deliver private packets; `joint_round1_digest` is locked before any Round-2 opening is computed;
/// - Round 2: all parties broadcast `Gf256SeedDealerRound2Open`, each recipient verifies its own inbox,
///   and the committee runs `spdz_verify_seed256_boolean_gf256` (`2^{-256}` SPDZ Booleanity + global `0..n` degree `< t`)!
pub fn run_dealerless_dkg_seed32_gf256(
    session_id: [u8; 32],
    t: usize,
    eval_points: &[TowerGf256],
    ot_mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
) -> Result<(Vec<ShamirSeedShare256>, [u8; 32]), DkgError> {
    let n = eval_points.len();
    if t == 0 || t > n || n < 2 || party_rngs.len() != n || ot_mesh.n != n {
        return Err(DkgError::InvalidQuorum { t, n });
    }
    validate_all_eval_points_gf256(eval_points)?;

    // Round 1: Commit
    let mut r1_commits = Vec::with_capacity(n);
    let mut pending_dealers = Vec::with_capacity(n);
    let mut inboxes: Vec<Vec<Option<Gf256SeedPrivatePacket>>> =
        (0..n).map(|_| (0..n).map(|_| None).collect()).collect();

    for i in 0..n {
        let (r1, pend, pkts) = deal_gf256_seed_round1(
            &session_id,
            i,
            t,
            eval_points,
            None,
            false,
            &mut party_rngs[i],
        )?;
        r1_commits.push(r1);
        pending_dealers.push(pend);
        for pkt in pkts {
            let j = pkt.recv_idx;
            inboxes[j][i] = Some(pkt);
        }
    }

    let joint_r1_digest =
        compute_gf256_round1_transcript(&session_id, t, eval_points, &r1_commits);

    // Round 2: Open against `joint_r1_digest`
    let r2_opens: Vec<Gf256SeedDealerRound2Open> = pending_dealers
        .into_iter()
        .map(|pend| pend.open_round2(&session_id, eval_points, &joint_r1_digest))
        .collect();

    // Each recipient `j` verifies ONLY its own inbox `inboxes[j][0..n]`
    let mut agg_bits = vec![[TowerGf256::ZERO; 256]; n];
    for j in 0..n {
        for i in 0..n {
            let pkt = inboxes[j][i]
                .as_ref()
                .ok_or(DkgError::DealerDisqualified { dealer_idx: i })?;
            verify_gf256_seed_dealing(
                &session_id,
                t,
                eval_points,
                &joint_r1_digest,
                &r1_commits[i],
                &r2_opens[i],
                pkt,
                false,
            )?;
            for b in 0..256 {
                agg_bits[j][b] = agg_bits[j][b].add(pkt.f_shares[b]);
            }
        }
    }

    let mut pk_seed = [0u8; 32];
    for r2_opens_i_item in r2_opens[..n].iter() {
        for (k, pk_seed_k_item) in pk_seed[..32].iter_mut().enumerate() {
            *pk_seed_k_item ^= r2_opens_i_item.pk_seed_contrib[k];
        }
    }

    // Interactive SPDZ-MAC-authenticated Booleanity & global `0..n` degree-`< t` verification
    spdz_verify_seed256_boolean_gf256(
        &session_id,
        t,
        eval_points,
        ot_mesh,
        &agg_bits,
        party_rngs,
    )?;

    let mut shares = Vec::with_capacity(n);
    for p in 0..n {
        let bits = agg_bits[p];
        wipe_gf256_slice(&mut agg_bits[p]);
        shares.push(ShamirSeedShare256::new(p, 0, eval_points[p], bits));
    }
    Ok((shares, pk_seed))
}

/// Multi-party 2-round dealerless `Π_refresh` (`Π_deg0`) over `TowerGf256` with global `0..n`
/// `Tower128` mask-polynomial degree-`< t` verification (`2t - 1 > n` dishonest-majority safe).
pub fn run_dealerless_refresh_seed32_gf256(
    session_id: [u8; 32],
    t: usize,
    eval_points: &[TowerGf256],
    shares: &mut [ShamirSeedShare256],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<(), DkgError> {
    let n = eval_points.len();
    if t < 2 || t > n || shares.len() != n || party_rngs.len() != n {
        return Err(DkgError::InvalidQuorum { t, n });
    }
    validate_all_eval_points_gf256(eval_points)?;
    for (p, s) in shares.iter().enumerate() {
        if !s.is_valid() || s.eval_point != eval_points[p] {
            return Err(DkgError::ShareAlreadyInvalidated { party_id: p });
        }
    }

    let zeros = [TowerGf256::ZERO; 256];
    let mut r1_commits = Vec::with_capacity(n);
    let mut pending = Vec::with_capacity(n);
    let mut inboxes: Vec<Vec<Option<Gf256SeedPrivatePacket>>> =
        (0..n).map(|_| (0..n).map(|_| None).collect()).collect();

    for i in 0..n {
        let (r1, pend, pkts) = deal_gf256_seed_round1(
            &session_id,
            i,
            t,
            eval_points,
            Some(zeros),
            true,
            &mut party_rngs[i],
        )?;
        r1_commits.push(r1);
        pending.push(pend);
        for pkt in pkts {
            let j = pkt.recv_idx;
            inboxes[j][i] = Some(pkt);
        }
    }

    let joint_r1_digest =
        compute_gf256_round1_transcript(&session_id, t, eval_points, &r1_commits);
    let r2_opens: Vec<Gf256SeedDealerRound2Open> = pending
        .into_iter()
        .map(|pend| pend.open_round2(&session_id, eval_points, &joint_r1_digest))
        .collect();

    let mut delta_bits = vec![[TowerGf256::ZERO; 256]; n];
    for j in 0..n {
        for i in 0..n {
            let pkt = inboxes[j][i]
                .as_ref()
                .ok_or(DkgError::DealerDisqualified { dealer_idx: i })?;
            verify_gf256_seed_dealing(
                &session_id,
                t,
                eval_points,
                &joint_r1_digest,
                &r1_commits[i],
                &r2_opens[i],
                pkt,
                true,
            )?;
            for b in 0..256 {
                delta_bits[j][b] = delta_bits[j][b].add(pkt.f_shares[b]);
            }
        }
    }

    // Global `0..n` degree-`< t` + zero-constant verification on `delta_bits` via random `Tower128`
    // zero-constant mask polynomial (`P_mask(0) == 0`, `2^{-128}` soundness even when `2t - 1 > n`!)
    let mut mask_shares = vec![Tower128::ZERO; n];
    for party_rngs_i_item in party_rngs[..n].iter_mut() {
        let mut m_coeffs = vec![Tower128::ZERO; t];
        for m_coeffs_k_item in m_coeffs[..t].iter_mut().skip(1) {
            *m_coeffs_k_item = (*party_rngs_i_item).next_tower128();
        }
        for p in 0..n {
            mask_shares[p] = mask_shares[p].add(eval_poly_tower128_at_gf256(&m_coeffs, eval_points[p]));
        }
        wipe_tower128_slice(&mut m_coeffs);
    }
    let coin = run_commit_and_open_coin(
        &session_id,
        b"GF256_REFRESH_DEG0_CHECK",
        &joint_r1_digest,
        party_rngs,
    )?;
    let mut ch_rng = PartyPrivateRng::from_seed(coin, b"GF256_REF_CHIS");
    let mut comb = vec![Tower128::ZERO; n];
    comb[..n].copy_from_slice(&mask_shares[..n]);
    wipe_tower128_slice(&mut mask_shares);
    #[expect(clippy::needless_range_loop, reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows")]
    for b in 0..256 {
        let chi = Tower128(ch_rng.next_u128() | 1);
        for p in 0..n {
            comb[p] = comb[p].add(chi.mul(Tower128::embed_gf256(delta_bits[p][b])));
        }
    }
    let zero_opened = commit_and_open_degree_tower128(
        &session_id,
        "gf256_refresh_deg0_check",
        t,
        eval_points,
        &comb,
        party_rngs,
    )?;
    wipe_tower128_slice(&mut comb);
    if !zero_opened.ct_eq(Tower128::ZERO) {
        return Err(DkgError::ZeroConstantCheckFailed { dealer_idx: 0 });
    }

    for j in 0..n {
        for b in 0..256 {
            shares[j].bit_shares[b] = shares[j].bit_shares[b].add(delta_bits[j][b]);
        }
        wipe_gf256_slice(&mut delta_bits[j]);
        shares[j].generation = shares[j].generation.saturating_add(1);
    }
    Ok(())
}

// A single retirement boundary for both sharing fields. On any verification
// error the new custody is dropped and wiped; old custody remains usable.
fn finish_reshare<T>(
    old: &mut [T],
    new: Vec<T>,
    enrolled_root: &[u8; 32],
    recompute: impl FnOnce(&[T]) -> Result<[u8; 32], DkgError>,
    retire: impl Fn(&mut T),
) -> Result<Vec<T>, DkgError> {
    let root = recompute(&new)?;
    if !ct_eq_bytes32(&root, enrolled_root) {
        return Err(DkgError::PublicRootMismatch);
    }
    for share in old {
        retire(share);
    }
    Ok(new)
}

/// Dynamic Quorum Redistribution `Π_reshare` (`(t, n) -> (t', n')`, e.g. `3-of-5 -> 5-of-9`) over `TowerGf256`:
/// - Authorized old quorum `old_quorum_indices` (`len == old_t`) runs 2-round commit-then-open sub-dealing
///   to all `new_n` new committee members;
/// - New committee runs `spdz_verify_seed256_boolean_gf256` (`2^{-256}` SPDZ Booleanity + global `0..new_n`
///   degree-`< new_t` verification, `0` central RAM, `0` unmasked Frobenius leak);
/// - Recomputes the enrolled public root before retiring old shares. The caller
///   supplies its suite-specific MPC root computation, bound to the enrolled
///   public parameters; it must not reconstruct the secret in production.
///   A constant or unverified callback defeats this check and is forbidden.
#[expect(clippy::too_many_arguments, reason = "Old/new committees and the enrolled-root verifier are separate trust-boundary inputs")]
pub fn run_dealerless_reshare_seed32_gf256(
    session_id: [u8; 32],
    old_t: usize,
    old_quorum_indices: &[usize],
    old_shares: &mut [ShamirSeedShare256],
    new_t: usize,
    new_eval_points: &[TowerGf256],
    new_ot_mesh: &mut OtMesh,
    old_quorum_rngs: &mut [PartyPrivateRng],
    new_party_rngs: &mut [PartyPrivateRng],
    enrolled_root: &[u8; 32],
    recompute_public_root: impl FnOnce(&[ShamirSeedShare256]) -> Result<[u8; 32], DkgError>,
) -> Result<Vec<ShamirSeedShare256>, DkgError> {
    let new_n = new_eval_points.len();
    if old_t == 0
        || old_quorum_indices.len() != old_t
        || old_quorum_rngs.len() != old_t
        || new_t == 0
        || new_t > new_n
        || new_n < 2
        || new_ot_mesh.n != new_n
        || new_party_rngs.len() != new_n
    {
        return Err(DkgError::InvalidQuorum { t: new_t, n: new_n });
    }
    validate_all_eval_points_gf256(new_eval_points)?;

    let mut seen = vec![false; old_shares.len()];
    let mut quorum_pts = Vec::with_capacity(old_t);
    let mut next_gen = 1u64;
    for &idx in old_quorum_indices {
        if idx >= old_shares.len() || seen[idx] {
            return Err(DkgError::DuplicateOrInvalidOldSigner { party_id: idx });
        }
        if !old_shares[idx].is_valid() {
            return Err(DkgError::ShareAlreadyInvalidated { party_id: idx });
        }
        seen[idx] = true;
        quorum_pts.push(old_shares[idx].eval_point);
        next_gen = next_gen.max(old_shares[idx].generation.saturating_add(1));
    }
    validate_all_eval_points_gf256(&quorum_pts)?;
    let lambdas =
        lagrange_weights_zero_gf256(&quorum_pts).ok_or(DkgError::InvalidEvaluationPoints)?;

    let mut r1_commits = Vec::with_capacity(old_t);
    let mut pending = Vec::with_capacity(old_t);
    let mut inboxes: Vec<Vec<Option<Gf256SeedPrivatePacket>>> = (0..new_n)
        .map(|_| (0..old_t).map(|_| None).collect())
        .collect();

    for (slot, &old_idx) in old_quorum_indices.iter().enumerate() {
        let lam_mat = PublicGf256Matrix::from_mul_const(lambdas[slot]);
        let mut weighted = [TowerGf256::ZERO; 256];
        for (b, weighted_b_item) in weighted[..256].iter_mut().enumerate() {
            *weighted_b_item = lam_mat.mul_elem(old_shares[old_idx].bit_shares[b]);
        }
        let (r1, pend, pkts) = deal_gf256_seed_round1(
            &session_id,
            old_idx,
            new_t,
            new_eval_points,
            Some(weighted),
            false,
            &mut old_quorum_rngs[slot],
        )?;
        wipe_gf256_slice(&mut weighted);
        r1_commits.push(r1);
        pending.push(pend);
        for pkt in pkts {
            let j = pkt.recv_idx;
            inboxes[j][slot] = Some(pkt);
        }
    }

    let joint_r1_digest =
        compute_gf256_round1_transcript(&session_id, new_t, new_eval_points, &r1_commits);
    let r2_opens: Vec<Gf256SeedDealerRound2Open> = pending
        .into_iter()
        .map(|pend| pend.open_round2(&session_id, new_eval_points, &joint_r1_digest))
        .collect();

    let mut new_bits = vec![[TowerGf256::ZERO; 256]; new_n];
    for j in 0..new_n {
        for slot in 0..old_t {
            let pkt = inboxes[j][slot].as_ref().ok_or(DkgError::DealerDisqualified {
                dealer_idx: old_quorum_indices[slot],
            })?;
            verify_gf256_seed_dealing(
                &session_id,
                new_t,
                new_eval_points,
                &joint_r1_digest,
                &r1_commits[slot],
                &r2_opens[slot],
                pkt,
                false,
            )?;
            for b in 0..256 {
                new_bits[j][b] = new_bits[j][b].add(pkt.f_shares[b]);
            }
        }
    }

    // SPDZ-MAC-authenticated Booleanity + global `0..new_n` degree `< new_t` verification!
    spdz_verify_seed256_boolean_gf256(
        &session_id,
        new_t,
        new_eval_points,
        new_ot_mesh,
        &new_bits,
        new_party_rngs,
    )?;

    let mut out = Vec::with_capacity(new_n);
    for j in 0..new_n {
        let bits = new_bits[j];
        wipe_gf256_slice(&mut new_bits[j]);
        out.push(ShamirSeedShare256::new(j, next_gen, new_eval_points[j], bits));
    }
    finish_reshare(old_shares, out, enrolled_root, recompute_public_root,
        ShamirSeedShare256::wipe_and_invalidate)
}

// ============================================================================
// 5. Strict 2-Round Vector `Π_dkg`, `Π_refresh` & `Π_reshare` over `Goldilocks`
// ============================================================================

/// Private share packet for 256-bit `Goldilocks` seed dealing (`!Clone`, redacted `Debug`, `Drop` wipe).
pub struct GoldilocksSeedPrivatePacket {
    pub recv_idx: usize,
    pub f_shares: [Goldilocks; 256],
    pub m_shares: [GoldilocksExt2; 256],
    pub salt: [u8; 32],
}

impl fmt::Debug for GoldilocksSeedPrivatePacket {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("GoldilocksSeedPrivatePacket([REDACTED])")
    }
}

impl Drop for GoldilocksSeedPrivatePacket {
    fn drop(&mut self) {
        wipe_goldilocks(&mut self.f_shares);
        wipe_ext2(&mut self.m_shares);
        wipe_bytes32(&mut self.salt);
    }
}

impl GoldilocksSeedPrivatePacket {
    pub fn encode_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(256 * 24);
        for b in 0..256 {
            out.extend_from_slice(&self.f_shares[b].to_be_bytes());
            out.extend_from_slice(&self.m_shares[b].c0.to_be_bytes());
            out.extend_from_slice(&self.m_shares[b].c1.to_be_bytes());
        }
        out
    }
}

/// Round-1 commitment wire message for 256-bit `Goldilocks` seed dealing (`Π_refresh` / `Π_reshare`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GoldilocksSeedDealerRound1Commit {
    pub dealer_idx: usize,
    pub share_commitments: Vec<[u8; 32]>,
}

/// Round-2 opening wire message for 256-bit `Goldilocks` seed dealing (`Π_refresh` / `Π_reshare`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GoldilocksSeedDealerRound2Open {
    pub dealer_idx: usize,
    pub masked_polys: Vec<Vec<GoldilocksExt2>>,
}

/// Ephemeral dealer secret state held between Round 1 and Round 2 (`!Clone`, wiped on `Drop`).
pub struct GoldilocksSeedDealerPendingSecret {
    dealer_idx: usize,
    t: usize,
    f_polys: Vec<Vec<Goldilocks>>,
    m_polys: Vec<Vec<GoldilocksExt2>>,
}

impl fmt::Debug for GoldilocksSeedDealerPendingSecret {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("GoldilocksSeedDealerPendingSecret([REDACTED])")
    }
}

impl Drop for GoldilocksSeedDealerPendingSecret {
    fn drop(&mut self) {
        for fp in &mut self.f_polys {
            wipe_goldilocks(fp);
        }
        for mp in &mut self.m_polys {
            wipe_ext2(mp);
        }
    }
}

pub fn compute_goldilocks_vec_round1_transcript(
    session_id: &[u8; 32],
    t: usize,
    pts: &[Goldilocks],
    r1_commits: &[GoldilocksSeedDealerRound1Commit],
) -> [u8; 32] {
    let mut xof = Cshake256Xof::new(TAG_DKG_ROUND1_TRANSCRIPT);
    xof.absorb(b"GL_VEC256");
    xof.absorb(session_id);
    xof.absorb(&(t as u64).to_be_bytes());
    xof.absorb(&(pts.len() as u64).to_be_bytes());
    for pt in pts {
        xof.absorb(&pt.to_be_bytes());
    }
    xof.absorb(&(r1_commits.len() as u64).to_be_bytes());
    for c in r1_commits {
        xof.absorb(&(c.dealer_idx as u64).to_be_bytes());
        xof.absorb(&(c.share_commitments.len() as u64).to_be_bytes());
        for sc in &c.share_commitments {
            xof.absorb(sc);
        }
    }
    let mut out = [0u8; 32];
    xof.squeeze(&mut out);
    out
}

fn derive_goldilocks_vector_challenges(
    session_id: &[u8; 32],
    t: usize,
    pts: &[Goldilocks],
    joint_round1_digest: &[u8; 32],
    dealer_idx: usize,
) -> [GoldilocksExt2; 256] {
    let mut xof = Cshake256Xof::new(TAG_DKG_CHALLENGE);
    xof.absorb(b"GL_VEC256_CHAL");
    xof.absorb(session_id);
    xof.absorb(&(t as u64).to_be_bytes());
    xof.absorb(&(pts.len() as u64).to_be_bytes());
    for pt in pts {
        xof.absorb(&pt.to_be_bytes());
    }
    xof.absorb(joint_round1_digest);
    xof.absorb(&(dealer_idx as u64).to_be_bytes());
    let mut root = [0u8; 32];
    xof.squeeze(&mut root);

    let mut prg = PartyPrivateRng::from_seed(root, b"GL_VEC256_CHAL_EXPAND");
    wipe_bytes32(&mut root);
    let mut out = [GoldilocksExt2::ZERO; 256];
    for ch in &mut out {
        let mut v = prg.next_ext2();
        if v.ct_eq(GoldilocksExt2::ZERO) {
            v = GoldilocksExt2::ONE;
        }
        *ch = v;
    }
    out
}

pub fn deal_goldilocks_seed_round1(
    dealer_idx: usize,
    t: usize,
    pts: &[Goldilocks],
    constants: [Goldilocks; 256],
    zero_constant_mask: bool,
    rng: &mut PartyPrivateRng,
) -> Result<
    (
        GoldilocksSeedDealerRound1Commit,
        GoldilocksSeedDealerPendingSecret,
        Vec<GoldilocksSeedPrivatePacket>,
    ),
    DkgError,
> {
    let n = pts.len();
    if t == 0 || t > n {
        return Err(DkgError::InvalidQuorum { t, n });
    }
    validate_all_eval_points_goldilocks(pts)?;

    let mut f_polys = vec![vec![Goldilocks::ZERO; t]; 256];
    let mut m_polys = vec![vec![GoldilocksExt2::ZERO; t]; 256];

    for b in 0..256 {
        f_polys[b][0] = constants[b];
        m_polys[b][0] = if zero_constant_mask {
            GoldilocksExt2::ZERO
        } else {
            rng.next_ext2()
        };
        for k in 1..t {
            f_polys[b][k] = rng.next_goldilocks();
            m_polys[b][k] = rng.next_ext2();
        }
    }

    let mut share_commitments = Vec::with_capacity(n);
    let mut packets = Vec::with_capacity(n);
    for (j, pts_j_item) in pts[..n].iter().enumerate() {
        let mut f_shares = [Goldilocks::ZERO; 256];
        let mut m_shares = [GoldilocksExt2::ZERO; 256];
        for b in 0..256 {
            f_shares[b] = eval_poly_goldilocks(&f_polys[b], *pts_j_item);
            m_shares[b] = eval_poly_ext2_at_base(&m_polys[b], *pts_j_item);
        }
        let salt = rng.next_bytes32();
        let pkt = GoldilocksSeedPrivatePacket {
            recv_idx: j,
            f_shares,
            m_shares,
            salt,
        };
        let mut raw = pkt.encode_bytes();
        let comm = dkg_commit_share(dealer_idx as u32, j as u32, &salt, &raw);
        wipe_bytes(&mut raw);
        share_commitments.push(comm);
        packets.push(pkt);
    }

    Ok((
        GoldilocksSeedDealerRound1Commit {
            dealer_idx,
            share_commitments,
        },
        GoldilocksSeedDealerPendingSecret {
            dealer_idx,
            t,
            f_polys,
            m_polys,
        },
        packets,
    ))
}

impl GoldilocksSeedDealerPendingSecret {
    pub fn open_round2(
        self,
        session_id: &[u8; 32],
        pts: &[Goldilocks],
        joint_round1_digest: &[u8; 32],
    ) -> GoldilocksSeedDealerRound2Open {
        let chals = derive_goldilocks_vector_challenges(
            session_id,
            self.t,
            pts,
            joint_round1_digest,
            self.dealer_idx,
        );
        let mut masked_polys = Vec::with_capacity(256);
        for (b, chals_b_item) in chals[..256].iter().enumerate() {
            let mut mp = Vec::with_capacity(self.t);
            for k in 0..self.t {
                mp.push((*chals_b_item).mul_base(self.f_polys[b][k]) + self.m_polys[b][k]);
            }
            masked_polys.push(mp);
        }
        GoldilocksSeedDealerRound2Open {
            dealer_idx: self.dealer_idx,
            masked_polys,
        }
    }
}

#[expect(clippy::too_many_arguments, reason = "Keep commitment, opening, private packet and session/quorum bindings explicit")]
pub fn verify_goldilocks_seed_dealing(
    session_id: &[u8; 32],
    t: usize,
    pts: &[Goldilocks],
    joint_round1_digest: &[u8; 32],
    r1: &GoldilocksSeedDealerRound1Commit,
    r2: &GoldilocksSeedDealerRound2Open,
    packet: &GoldilocksSeedPrivatePacket,
    require_zero_constant: bool,
) -> Result<(), DkgError> {
    let n = pts.len();
    if t == 0 || t > n {
        return Err(DkgError::InvalidQuorum { t, n });
    }
    validate_all_eval_points_goldilocks(pts)?;

    if r1.dealer_idx != r2.dealer_idx
        || r1.share_commitments.len() != n
        || r2.masked_polys.len() != 256
    {
        return Err(DkgError::DealerDisqualified {
            dealer_idx: r1.dealer_idx,
        });
    }
    for poly in r2.masked_polys.iter().take(256) {
        if poly.len() > t {
            return Err(DkgError::DealerDisqualified {
                dealer_idx: r1.dealer_idx,
            });
        }
        if require_zero_constant
            && !poly
                .first()
                .copied()
                .unwrap_or(GoldilocksExt2::ZERO)
                .ct_eq(GoldilocksExt2::ZERO)
        {
            return Err(DkgError::ZeroConstantCheckFailed {
                dealer_idx: r1.dealer_idx,
            });
        }
    }

    if packet.recv_idx >= n {
        return Err(DkgError::PrivatePacketVerificationFailed {
            dealer_idx: r1.dealer_idx,
            recv_idx: packet.recv_idx,
        });
    }
    let mut raw = packet.encode_bytes();
    let comm = dkg_commit_share(
        r1.dealer_idx as u32,
        packet.recv_idx as u32,
        &packet.salt,
        &raw,
    );
    wipe_bytes(&mut raw);
    if !ct_eq_bytes32(&comm, &r1.share_commitments[packet.recv_idx]) {
        return Err(DkgError::PrivatePacketVerificationFailed {
            dealer_idx: r1.dealer_idx,
            recv_idx: packet.recv_idx,
        });
    }

    let chals =
        derive_goldilocks_vector_challenges(session_id, t, pts, joint_round1_digest, r1.dealer_idx);
    let x = pts[packet.recv_idx];
    for (b, chals_b_item) in chals[..256].iter().enumerate() {
        let lhs = (*chals_b_item).mul_base(packet.f_shares[b]) + packet.m_shares[b];
        let rhs = eval_poly_ext2_at_base(&r2.masked_polys[b], x);
        if !lhs.ct_eq(rhs) {
            return Err(DkgError::PrivatePacketVerificationFailed {
                dealer_idx: r1.dealer_idx,
                recv_idx: packet.recv_idx,
            });
        }
    }
    Ok(())
}

/// SPDZ-MAC-authenticated Booleanity (`b_m^2 - b_m == 0`) + global `0..n` degree-`< t` verification
/// for 256 `Goldilocks` bit shares, including dishonest-majority committees.
/// Each authenticated residual is checked for zero without probabilistic batching.
/// Failure has no bit index; malicious-input abort transcripts are not claimed
/// to be zero knowledge.
pub fn spdz_verify_seed256_boolean_goldilocks(
    session_id: &[u8; 32],
    t: usize,
    eval_points: &[Goldilocks],
    ot_mesh: &mut OtMesh,
    bit_shares_per_party: &[[Goldilocks; 256]],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<(), DkgError> {
    let n = eval_points.len();
    if t == 0
        || t > n
        || n < 2
        || ot_mesh.n != n
        || bit_shares_per_party.len() != n
        || party_rngs.len() != n
    {
        return Err(DkgError::InvalidQuorum { t, n });
    }
    validate_all_eval_points_goldilocks(eval_points)?;

    let lambdas_0 = lagrange_weights_zero_goldilocks(&eval_points[..t])
        .ok_or(DkgError::InvalidEvaluationPoints)?;

    // Convert `0..t` shares to additive shares `u_add[i][m]` (`0` for `i >= t`), compute `bsq = b^2`
    // and MASCOT companion products `comp_w0, comp_w1` via LHL-amplified `pairwise_gilboa_ole_goldilocks` (`< 2^{-129}`)!
    let mut u_add = vec![vec![Goldilocks::ZERO; 256]; n];
    for q in 0..t {
        for m in 0..256 {
            u_add[q][m] = lambdas_0[q] * bit_shares_per_party[q][m];
        }
    }
    let mut bsq_add = pairwise_gilboa_ole_goldilocks(ot_mesh, &u_add, &u_add, party_rngs)?;
    let mut comp_u0 = vec![vec![Goldilocks::ZERO; 256]; n];
    let mut comp_u1 = vec![vec![Goldilocks::ZERO; 256]; n];
    for i in 0..n {
        for m in 0..256 {
            comp_u0[i][m] = party_rngs[i].next_goldilocks();
            comp_u1[i][m] = party_rngs[i].next_goldilocks();
        }
    }
    let mut comp_w0 = pairwise_gilboa_ole_goldilocks(ot_mesh, &comp_u0, &u_add, party_rngs)?;
    let mut comp_w1 = pairwise_gilboa_ole_goldilocks(ot_mesh, &comp_u1, &u_add, party_rngs)?;
    for u in &mut u_add {
        wipe_goldilocks(u);
    }

    // Re-share `bsq, comp_u0, comp_u1, comp_w0, comp_w1` at degree `< t` across `0..n`
    let mut bsq_sh = vec![vec![Goldilocks::ZERO; 256]; n];
    let mut cu0_sh = vec![vec![Goldilocks::ZERO; 256]; n];
    let mut cu1_sh = vec![vec![Goldilocks::ZERO; 256]; n];
    let mut cw0_sh = vec![vec![Goldilocks::ZERO; 256]; n];
    let mut cw1_sh = vec![vec![Goldilocks::ZERO; 256]; n];

    for i in 0..n {
        for m in 0..256 {
            let mut p_bsq = vec![bsq_add[i][m]];
            let mut p_u0 = vec![comp_u0[i][m]];
            let mut p_u1 = vec![comp_u1[i][m]];
            let mut p_w0 = vec![comp_w0[i][m]];
            let mut p_w1 = vec![comp_w1[i][m]];
            for _ in 1..t {
                p_bsq.push(party_rngs[i].next_goldilocks());
                p_u0.push(party_rngs[i].next_goldilocks());
                p_u1.push(party_rngs[i].next_goldilocks());
                p_w0.push(party_rngs[i].next_goldilocks());
                p_w1.push(party_rngs[i].next_goldilocks());
            }
            for p in 0..n {
                let x = eval_points[p];
                bsq_sh[p][m] += eval_poly_goldilocks(&p_bsq, x);
                cu0_sh[p][m] += eval_poly_goldilocks(&p_u0, x);
                cu1_sh[p][m] += eval_poly_goldilocks(&p_u1, x);
                cw0_sh[p][m] += eval_poly_goldilocks(&p_w0, x);
                cw1_sh[p][m] += eval_poly_goldilocks(&p_w1, x);
            }
            wipe_goldilocks(&mut p_bsq);
            wipe_goldilocks(&mut p_u0);
            wipe_goldilocks(&mut p_u1);
            wipe_goldilocks(&mut p_w0);
            wipe_goldilocks(&mut p_w1);
        }
        wipe_goldilocks(&mut bsq_add[i]);
        wipe_goldilocks(&mut comp_u0[i]);
        wipe_goldilocks(&mut comp_u1[i]);
        wipe_goldilocks(&mut comp_w0[i]);
        wipe_goldilocks(&mut comp_w1[i]);
    }

    // Authenticate `[b, bsq, cu0, cu1, cw0, cw1]` (`6 * 256 = 1536` wires) under `GoldilocksExt2` SPDZ MACs
    // across ALL `0..n` parties (simultaneously proving `bit_shares_per_party` has degree `< t` on `0..n`!)
    let auth_sid = cshake256_hash32(b"QSAG.DKG.GL.BOOL.AUTH/v1", session_id);
    let (mut alpha_contribs, mut alpha_shamir) =
        spdz_setup_alpha_goldilocks(&auth_sid, t, eval_points, party_rngs)?;
    let mut flat = vec![Vec::with_capacity(6 * 256); n];
    for p in 0..n {
        flat[p].extend_from_slice(&bit_shares_per_party[p]);
        flat[p].extend_from_slice(&bsq_sh[p]);
        flat[p].extend_from_slice(&cu0_sh[p]);
        flat[p].extend_from_slice(&cu1_sh[p]);
        flat[p].extend_from_slice(&cw0_sh[p]);
        flat[p].extend_from_slice(&cw1_sh[p]);
        wipe_goldilocks(&mut bsq_sh[p]);
        wipe_goldilocks(&mut cu0_sh[p]);
        wipe_goldilocks(&mut cu1_sh[p]);
        wipe_goldilocks(&mut cw0_sh[p]);
        wipe_goldilocks(&mut cw1_sh[p]);
    }
    let mut flat_macs = spdz_authenticate_goldilocks_batch_ext2(
        &auth_sid,
        t,
        eval_points,
        ot_mesh,
        &alpha_contribs,
        &alpha_shamir,
        &flat,
        party_rngs,
    )?;
    wipe_ext2(&mut alpha_contribs);

    // Step A: SPDZ-MAC-authenticated MASCOT companion sacrifice proving `bsq_m == b_m^2`!
    let sac_coin = run_commit_and_open_coin(&auth_sid, b"GL_DKG_BOOL_SAC", session_id, party_rngs)?;
    let rho = GoldilocksExt2::new(
        Goldilocks::from_u128_reduced(u128::from_be_bytes(core::array::from_fn(|array_index| (sac_coin[0..16])[array_index])) | 1),
        Goldilocks::from_u128_reduced(u128::from_be_bytes(core::array::from_fn(|array_index| (sac_coin[16..32])[array_index]))),
    );
    let mut u_c0_batch = vec![Vec::with_capacity(512); n];
    let mut u_c0_macs = vec![Vec::with_capacity(512); n];
    for p in 0..n {
        for m in 0..256 {
            let b_sh = flat[p][m];
            let b_mac = flat_macs[p][m];
            let cu0 = flat[p][512 + m];
            let cu0_mac = flat_macs[p][512 + m];
            let cu1 = flat[p][768 + m];
            let cu1_mac = flat_macs[p][768 + m];
            // `U_m = rho * b_m - (cu0 + u*cu1) = (rho.c0 * b_m - cu0) + u * (rho.c1 * b_m - cu1)`
            u_c0_batch[p].push(rho.c0 * b_sh - cu0);
            u_c0_macs[p].push(b_mac.mul_base(rho.c0) - cu0_mac);
            u_c0_batch[p].push(rho.c1 * b_sh - cu1);
            u_c0_macs[p].push(b_mac.mul_base(rho.c1) - cu1_mac);
        }
    }
    let u_opened_limbs = commit_and_open_spdz_goldilocks_batch_quorum(
        &auth_sid,
        "dkg_gl_bool_sac_u",
        t,
        eval_points,
        &u_c0_batch,
        &u_c0_macs,
        &alpha_shamir,
        party_rngs,
    )?;
    for p in 0..n {
        wipe_goldilocks(&mut u_c0_batch[p]);
        wipe_ext2(&mut u_c0_macs[p]);
    }

    let mut chi_rng = PartyPrivateRng::from_seed(sac_coin, b"GL_DKG_SAC_CHIS");
    let mut w_sh = vec![GoldilocksExt2::ZERO; n];
    let mut w_mac = vec![GoldilocksExt2::ZERO; n];
    for m in 0..256 {
        let mut chi = chi_rng.next_ext2();
        if chi.ct_eq(GoldilocksExt2::ZERO) {
            chi = GoldilocksExt2::ONE;
        }
        let u_m = GoldilocksExt2::new(u_opened_limbs[2 * m], u_opened_limbs[2 * m + 1]);
        for p in 0..n {
            let b_sh = flat[p][m];
            let b_mac = flat_macs[p][m];
            let bsq = flat[p][256 + m];
            let bsq_mac = flat_macs[p][256 + m];
            let ct = GoldilocksExt2::new(flat[p][1024 + m], flat[p][1280 + m]);
            let ct_mac = flat_macs[p][1024 + m]
                + GoldilocksExt2::new(Goldilocks::ZERO, Goldilocks::ONE) * flat_macs[p][1280 + m];

            let r_val = (rho.mul_base(bsq) - ct) - u_m.mul_base(b_sh);
            let r_mac = (rho * bsq_mac - ct_mac) - u_m * b_mac;
            w_sh[p] += chi * r_val;
            w_mac[p] += chi * r_mac;
        }
    }
    let w_open = commit_and_open_spdz_ext2_quorum(
        &auth_sid,
        "dkg_gl_bool_sac_w",
        t,
        eval_points,
        &w_sh,
        &w_mac,
        &alpha_shamir,
        party_rngs,
    )?;
    wipe_ext2(&mut w_sh);
    wipe_ext2(&mut w_mac);
    if !w_open.ct_eq(GoldilocksExt2::ZERO) {
        for p in 0..n {
            wipe_goldilocks(&mut flat[p]);
            wipe_ext2(&mut flat_macs[p]);
        }
        wipe_ext2(&mut alpha_shamir);
        return Err(DkgError::PreprocessingFailed(
            PreprocessError::SacrificeResidualNonZero {
                phase: "dkg_gl_bool_sac",
            },
        ));
    }

    // Commit-before-open every authenticated b^2-b residual. Keep the exact
    // zero check, but report an unindexed failure rather than claiming that a
    // public bit index identifies a faulty dealer.
    let mut diff_sh = vec![Vec::with_capacity(256); n];
    let mut diff_mac = vec![Vec::with_capacity(256); n];
    for p in 0..n {
        for m in 0..256 {
            diff_sh[p].push(flat[p][256 + m] - flat[p][m]);
            diff_mac[p].push(flat_macs[p][256 + m] - flat_macs[p][m]);
        }
        wipe_goldilocks(&mut flat[p]);
        wipe_ext2(&mut flat_macs[p]);
    }
    let diffs = commit_and_open_spdz_goldilocks_batch_quorum(
        &auth_sid,
        "dkg_gl_bool_diff",
        t,
        eval_points,
        &diff_sh,
        &diff_mac,
        &alpha_shamir,
        party_rngs,
    );
    for p in 0..n {
        wipe_goldilocks(&mut diff_sh[p]);
        wipe_ext2(&mut diff_mac[p]);
    }
    wipe_ext2(&mut alpha_shamir);
    if diffs?.iter().any(|&d| d != Goldilocks::ZERO) {
        return Err(DkgError::NonBooleanSeedDetected);
    }
    Ok(())
}

/// Dealerless `Π_dkg` over `Goldilocks` producing canonical `0..=255` byte shares
/// (`[ShamirPoseidonSeedShare]`) AND unbiased 2-round committed `pk_seed`:
/// - Validates ALL `eval_points[0..n]` (`[P0-10]`);
/// - Jointly XOR-folds 256 unbiased bits via LHL-amplified `pairwise_gilboa_ole_goldilocks`
///   (`x \oplus y = x + y - 2xy`, `< 2^{-129}` selective-failure advantage);
/// - Deals 2-round commit-then-open Shamir shares and runs `spdz_verify_seed256_boolean_goldilocks`
///   (`1 - 2^{-126}` SPDZ Booleanity + global `0..n` degree-`< t` consistency)!
pub fn run_dealerless_dkg_seed32_goldilocks(
    session_id: [u8; 32],
    t: usize,
    eval_points: &[Goldilocks],
    ot_mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
) -> Result<(Vec<ShamirPoseidonSeedShare>, [u8; 32]), DkgError> {
    let n = eval_points.len();
    if t == 0 || t > n || n < 2 || party_rngs.len() != n || ot_mesh.n != n {
        return Err(DkgError::InvalidQuorum { t, n });
    }
    validate_all_eval_points_goldilocks(eval_points)?;

    // 1. Two-round commit-and-open unbiased `pk_seed`
    let pk_seed =
        run_commit_and_open_coin(&session_id, b"GL_DKG_PK_SEED", &session_id, party_rngs)?;

    // 2. Jointly sample 256 unbiased bits in `{0, 1}` via LHL-amplified Gilboa OLE XOR-folding
    // (`x (+) y = x + y - 2*x*y` in `Goldilocks`, `< 2^{-129}` selective-failure advantage!)
    let two = Goldilocks::from_u64_reduced(2);
    let mut cur_shares = vec![vec![Goldilocks::ZERO; 256]; n];
    let w0 = [
        party_rngs[0].next_u64(),
        party_rngs[0].next_u64(),
        party_rngs[0].next_u64(),
        party_rngs[0].next_u64(),
    ];
    for m in 0..256 {
        cur_shares[0][m] = Goldilocks::from_u64_reduced((w0[m / 64] >> (m % 64)) & 1);
    }

    for i in 1..n {
        let mut y_vec = vec![vec![Goldilocks::ZERO; 256]; n];
        let mut wi = [
            party_rngs[i].next_u64(),
            party_rngs[i].next_u64(),
            party_rngs[i].next_u64(),
            party_rngs[i].next_u64(),
        ];
        for m in 0..256 {
            y_vec[i][m] = Goldilocks::from_u64_reduced((wi[m / 64] >> (m % 64)) & 1);
        }
        wipe_u64s(&mut wi);

        let mut prod = pairwise_gilboa_ole_goldilocks(ot_mesh, &cur_shares, &y_vec, party_rngs)?;
        for p in 0..n {
            for m in 0..256 {
                cur_shares[p][m] = cur_shares[p][m] + y_vec[p][m] - two * prod[p][m];
            }
            wipe_goldilocks(&mut y_vec[p]);
            wipe_goldilocks(&mut prod[p]);
        }
    }

    // 3. 2-round commit-then-open Shamir sub-dealing of `cur_shares[i][0..256]` across `eval_points[0..n]`
    let mut r1_commits = Vec::with_capacity(n);
    let mut pending = Vec::with_capacity(n);
    let mut inboxes: Vec<Vec<Option<GoldilocksSeedPrivatePacket>>> =
        (0..n).map(|_| (0..n).map(|_| None).collect()).collect();

    for i in 0..n {
        let mut consts = [Goldilocks::ZERO; 256];
        consts.copy_from_slice(&cur_shares[i]);
        wipe_goldilocks(&mut cur_shares[i]);
        let (r1, pend, pkts) =
            deal_goldilocks_seed_round1(i, t, eval_points, consts, false, &mut party_rngs[i])?;
        wipe_goldilocks(&mut consts);
        r1_commits.push(r1);
        pending.push(pend);
        for pkt in pkts {
            let j = pkt.recv_idx;
            inboxes[j][i] = Some(pkt);
        }
    }

    let joint_r1_digest =
        compute_goldilocks_vec_round1_transcript(&session_id, t, eval_points, &r1_commits);
    let r2_opens: Vec<GoldilocksSeedDealerRound2Open> = pending
        .into_iter()
        .map(|pend| pend.open_round2(&session_id, eval_points, &joint_r1_digest))
        .collect();

    let mut b_shamir = vec![[Goldilocks::ZERO; 256]; n];
    for j in 0..n {
        for i in 0..n {
            let pkt = inboxes[j][i]
                .as_ref()
                .ok_or(DkgError::DealerDisqualified { dealer_idx: i })?;
            verify_goldilocks_seed_dealing(
                &session_id,
                t,
                eval_points,
                &joint_r1_digest,
                &r1_commits[i],
                &r2_opens[i],
                pkt,
                false,
            )?;
            for m in 0..256 {
                b_shamir[j][m] += pkt.f_shares[m];
            }
        }
    }

    // 4. SPDZ-MAC-authenticated Booleanity (`b_m^2 - b_m == 0`) & global `0..n` degree `< t` check!
    spdz_verify_seed256_boolean_goldilocks(
        &session_id,
        t,
        eval_points,
        ot_mesh,
        &b_shamir,
        party_rngs,
    )?;

    let mut shares = Vec::with_capacity(n);
    for p in 0..n {
        let bits = b_shamir[p];
        wipe_goldilocks(&mut b_shamir[p]);
        shares.push(ShamirPoseidonSeedShare::from_bit_shares(
            p,
            0,
            eval_points[p],
            bits,
        ));
    }

    Ok((shares, pk_seed))
}

/// Multi-party 2-round dealerless `Π_refresh` (`Π_deg0`) over `Goldilocks` with global `0..n`
/// `GoldilocksExt2` mask-polynomial degree-`< t` verification (`2t - 1 > n` dishonest-majority safe).
pub fn run_dealerless_refresh_seed32_goldilocks(
    session_id: [u8; 32],
    t: usize,
    eval_points: &[Goldilocks],
    shares: &mut [ShamirPoseidonSeedShare],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<(), DkgError> {
    let n = eval_points.len();
    if t < 2 || t > n || shares.len() != n || party_rngs.len() != n {
        return Err(DkgError::InvalidQuorum { t, n });
    }
    validate_all_eval_points_goldilocks(eval_points)?;
    for (p, s) in shares.iter().enumerate() {
        if !s.is_valid() || s.eval_point != eval_points[p] {
            return Err(DkgError::ShareAlreadyInvalidated { party_id: p });
        }
    }

    let zeros = [Goldilocks::ZERO; 256];
    let mut r1_commits = Vec::with_capacity(n);
    let mut pending = Vec::with_capacity(n);
    let mut inboxes: Vec<Vec<Option<GoldilocksSeedPrivatePacket>>> =
        (0..n).map(|_| (0..n).map(|_| None).collect()).collect();

    for i in 0..n {
        let (r1, pend, pkts) =
            deal_goldilocks_seed_round1(i, t, eval_points, zeros, true, &mut party_rngs[i])?;
        r1_commits.push(r1);
        pending.push(pend);
        for pkt in pkts {
            let j = pkt.recv_idx;
            inboxes[j][i] = Some(pkt);
        }
    }

    let joint_r1_digest =
        compute_goldilocks_vec_round1_transcript(&session_id, t, eval_points, &r1_commits);
    let r2_opens: Vec<GoldilocksSeedDealerRound2Open> = pending
        .into_iter()
        .map(|pend| pend.open_round2(&session_id, eval_points, &joint_r1_digest))
        .collect();

    let mut delta_bits = vec![[Goldilocks::ZERO; 256]; n];
    for j in 0..n {
        for i in 0..n {
            let pkt = inboxes[j][i]
                .as_ref()
                .ok_or(DkgError::DealerDisqualified { dealer_idx: i })?;
            verify_goldilocks_seed_dealing(
                &session_id,
                t,
                eval_points,
                &joint_r1_digest,
                &r1_commits[i],
                &r2_opens[i],
                pkt,
                true,
            )?;
            for m in 0..256 {
                delta_bits[j][m] += pkt.f_shares[m];
            }
        }
    }

    // Global `0..n` degree-`< t` + zero-constant verification via random `GoldilocksExt2` mask poly
    let mut mask_sh = vec![GoldilocksExt2::ZERO; n];
    for party_rngs_i_item in party_rngs[..n].iter_mut() {
        let mut m_coeffs = vec![GoldilocksExt2::ZERO; t];
        for m_coeffs_k_item in m_coeffs[..t].iter_mut().skip(1) {
            *m_coeffs_k_item = (*party_rngs_i_item).next_ext2();
        }
        for p in 0..n {
            mask_sh[p] += eval_poly_ext2_at_base(&m_coeffs, eval_points[p]);
        }
        wipe_ext2(&mut m_coeffs);
    }
    let coin = run_commit_and_open_coin(
        &session_id,
        b"GL_REFRESH_DEG0_CHECK",
        &joint_r1_digest,
        party_rngs,
    )?;
    let mut ch_rng = PartyPrivateRng::from_seed(coin, b"GL_REF_CHIS");
    let mut comb = mask_sh;
    #[expect(clippy::needless_range_loop, reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows")]
    for m in 0..256 {
        let mut chi = ch_rng.next_ext2();
        if chi.ct_eq(GoldilocksExt2::ZERO) {
            chi = GoldilocksExt2::ONE;
        }
        for p in 0..n {
            comb[p] += chi.mul_base(delta_bits[p][m]);
        }
    }
    let zero_opened = commit_and_open_degree_ext2(
        &session_id,
        "gl_refresh_deg0_check",
        t,
        eval_points,
        &comb,
        party_rngs,
    )?;
    wipe_ext2(&mut comb);
    if !zero_opened.ct_eq(GoldilocksExt2::ZERO) {
        return Err(DkgError::ZeroConstantCheckFailed { dealer_idx: 0 });
    }

    for j in 0..n {
        for m in 0..256 {
            shares[j].bit_shares[m] += delta_bits[j][m];
        }
        let delta_bytes = pack_goldilocks_bits_to_bytes(&delta_bits[j]);
        for (k, delta_bytes_k_item) in delta_bytes[..32].iter().enumerate() {
            shares[j].byte_shares[k] += *delta_bytes_k_item;
        }
        wipe_goldilocks(&mut delta_bits[j]);
        shares[j].generation = shares[j].generation.saturating_add(1);
    }
    Ok(())
}

/// Dynamic Quorum Redistribution `Π_reshare` (`(t, n) -> (t', n')`, e.g. `3-of-5 -> 5-of-9`) over `Goldilocks`:
/// redistributes 256-bit `ShamirPoseidonSeedShare`s via 2-round commit-then-open sub-dealing,
/// verifies SPDZ Booleanity (`b_m^2 - b_m == 0`) & global `0..new_n` degree `< new_t` on the new
/// committee so canonical `0..=255` byte range is guaranteed even against malicious old signers,
/// and verifies the enrolled public root before volatile-wiping old shares.
/// `recompute_public_root` must run the suite-specific MPC root computation with
/// the enrolled public parameters, without reconstructing the secret. Returning
/// a constant or trusting a participant's claimed root defeats this check.
#[expect(clippy::too_many_arguments, reason = "Old/new committees and the enrolled-root verifier are separate trust-boundary inputs")]
pub fn run_dealerless_reshare_seed32_goldilocks(
    session_id: [u8; 32],
    old_t: usize,
    old_quorum_indices: &[usize],
    old_shares: &mut [ShamirPoseidonSeedShare],
    new_t: usize,
    new_eval_points: &[Goldilocks],
    new_ot_mesh: &mut OtMesh,
    old_quorum_rngs: &mut [PartyPrivateRng],
    new_party_rngs: &mut [PartyPrivateRng],
    enrolled_root: &[u8; 32],
    recompute_public_root: impl FnOnce(&[ShamirPoseidonSeedShare]) -> Result<[u8; 32], DkgError>,
) -> Result<Vec<ShamirPoseidonSeedShare>, DkgError> {
    let new_n = new_eval_points.len();
    if old_t == 0
        || old_quorum_indices.len() != old_t
        || old_quorum_rngs.len() != old_t
        || new_t == 0
        || new_t > new_n
        || new_n < 2
        || new_ot_mesh.n != new_n
        || new_party_rngs.len() != new_n
    {
        return Err(DkgError::InvalidQuorum { t: new_t, n: new_n });
    }
    validate_all_eval_points_goldilocks(new_eval_points)?;

    let mut seen = vec![false; old_shares.len()];
    let mut quorum_pts = Vec::with_capacity(old_t);
    let mut next_gen = 1u64;
    for &idx in old_quorum_indices {
        if idx >= old_shares.len() || seen[idx] {
            return Err(DkgError::DuplicateOrInvalidOldSigner { party_id: idx });
        }
        if !old_shares[idx].is_valid() {
            return Err(DkgError::ShareAlreadyInvalidated { party_id: idx });
        }
        seen[idx] = true;
        quorum_pts.push(old_shares[idx].eval_point);
        next_gen = next_gen.max(old_shares[idx].generation.saturating_add(1));
    }
    validate_all_eval_points_goldilocks(&quorum_pts)?;
    let lambdas =
        lagrange_weights_zero_goldilocks(&quorum_pts).ok_or(DkgError::InvalidEvaluationPoints)?;

    let mut r1_commits = Vec::with_capacity(old_t);
    let mut pending = Vec::with_capacity(old_t);
    let mut inboxes: Vec<Vec<Option<GoldilocksSeedPrivatePacket>>> = (0..new_n)
        .map(|_| (0..old_t).map(|_| None).collect())
        .collect();

    for (slot, &old_idx) in old_quorum_indices.iter().enumerate() {
        let mut weighted = [Goldilocks::ZERO; 256];
        for (m, weighted_m_item) in weighted[..256].iter_mut().enumerate() {
            *weighted_m_item = lambdas[slot] * old_shares[old_idx].bit_shares[m];
        }
        let (r1, pend, pkts) = deal_goldilocks_seed_round1(
            old_idx,
            new_t,
            new_eval_points,
            weighted,
            false,
            &mut old_quorum_rngs[slot],
        )?;
        wipe_goldilocks(&mut weighted);
        r1_commits.push(r1);
        pending.push(pend);
        for pkt in pkts {
            let j = pkt.recv_idx;
            inboxes[j][slot] = Some(pkt);
        }
    }

    let joint_r1_digest =
        compute_goldilocks_vec_round1_transcript(&session_id, new_t, new_eval_points, &r1_commits);
    let r2_opens: Vec<GoldilocksSeedDealerRound2Open> = pending
        .into_iter()
        .map(|pend| pend.open_round2(&session_id, new_eval_points, &joint_r1_digest))
        .collect();

    let mut new_bits = vec![[Goldilocks::ZERO; 256]; new_n];
    for j in 0..new_n {
        for slot in 0..old_t {
            let pkt = inboxes[j][slot].as_ref().ok_or(DkgError::DealerDisqualified {
                dealer_idx: old_quorum_indices[slot],
            })?;
            verify_goldilocks_seed_dealing(
                &session_id,
                new_t,
                new_eval_points,
                &joint_r1_digest,
                &r1_commits[slot],
                &r2_opens[slot],
                pkt,
                false,
            )?;
            for m in 0..256 {
                new_bits[j][m] += pkt.f_shares[m];
            }
        }
    }

    // SPDZ-MAC-authenticated Booleanity (`b_m^2 - b_m == 0`) & global `0..new_n` degree `< new_t`!
    spdz_verify_seed256_boolean_goldilocks(
        &session_id,
        new_t,
        new_eval_points,
        new_ot_mesh,
        &new_bits,
        new_party_rngs,
    )?;

    let mut out = Vec::with_capacity(new_n);
    for j in 0..new_n {
        let bits = new_bits[j];
        wipe_goldilocks(&mut new_bits[j]);
        out.push(ShamirPoseidonSeedShare::from_bit_shares(
            j,
            next_gen,
            new_eval_points[j],
            bits,
        ));
    }
    finish_reshare(old_shares, out, enrolled_root, recompute_public_root,
        ShamirPoseidonSeedShare::wipe_and_invalidate)
}

// ============================================================================
// 6. Simplex Monotonic `EpochLatchState` & Durable `fsync`-Backed `FsWalEpochLatch`
// ============================================================================

/// Error returned when a quorum latch transition violates monotonic anti-double-sign invariants.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EpochLatchError {
    InvalidParticipant {
        party: usize,
        committee_size: usize,
    },
    DuplicateParticipant {
        party: usize,
    },
    StaleEpochReplay {
        requested_epoch: u64,
        high_water: u64,
    },
    EquivocationRefused {
        epoch: u64,
    },
    QuorumInsufficient {
        accepted: usize,
        required_latch_quorum: usize,
    },
    /// A latch certificate was issued for a different committee size or threshold than the
    /// signer's, or its acknowledging set is not a set of distinct committee members.
    CertificateCommitteeMismatch,
    PersistenceFailure,
    /// A latch certificate names a different epoch than the one being signed.
    CertificateEpochMismatch {
        certified_epoch: u64,
        requested_epoch: u64,
    },
    /// A latch certificate's binding is not the one for this key, epoch and message digest.
    CertificateBindingMismatch {
        epoch: u64,
    },
}

/// Durable per-signer monotonic epoch latch state (`ThresholdMpc.EpochLatchState`).
/// Intentionally `!Clone` in public custody APIs to prevent two-time epoch cursor forking.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct EpochLatchState {
    high_water: Option<(u64, [u8; 32])>,
}

const LATCH_WIRE_MAGIC: &[u8; 8] = b"QSAGLTC1";
const FS_WAL_MAGIC: &[u8; 8] = b"QSAGWAL1";

impl EpochLatchState {
    pub const fn high_water(&self) -> Option<(u64, [u8; 32])> { self.high_water }

    pub const fn new() -> Self {
        Self { high_water: None }
    }

    #[inline]
    fn stage_copy(&self) -> Self {
        Self {
            high_water: self.high_water,
        }
    }

    /// Atomic persist-before-sign state transition:
    /// - `None` -> `Some((epoch, mu))`
    /// - `epoch > hw` -> advances to `Some((epoch, mu))`
    /// - `epoch == hw` -> idempotent retry succeeds **iff** `ct_eq_bytes32(&bound_mu, &mu)`
    /// - `epoch < hw` -> `StaleEpochReplay`
    pub fn step_epoch_latch(&mut self, epoch: u64, mu: [u8; 32]) -> Result<(), EpochLatchError> {
        match self.high_water {
            None => {
                self.high_water = Some((epoch, mu));
                Ok(())
            }
            Some((hw, bound_mu)) => {
                if epoch > hw {
                    self.high_water = Some((epoch, mu));
                    Ok(())
                } else if epoch == hw {
                    if ct_eq_bytes32(&bound_mu, &mu) {
                        Ok(())
                    } else {
                        Err(EpochLatchError::EquivocationRefused { epoch })
                    }
                } else {
                    Err(EpochLatchError::StaleEpochReplay {
                        requested_epoch: epoch,
                        high_water: hw,
                    })
                }
            }
        }
    }

    /// Serialize to an `81`-byte authenticated record (`magic || has_hw || epoch || mu || cshake256_mac`).
    pub fn to_authenticated_bytes(&self, latch_mac_key: &[u8; 32]) -> [u8; 81] {
        let mut out = [0u8; 81];
        out[0..8].copy_from_slice(LATCH_WIRE_MAGIC);
        if let Some((ep, mu)) = self.high_water {
            out[8] = 1;
            out[9..17].copy_from_slice(&ep.to_be_bytes());
            out[17..49].copy_from_slice(&mu);
        }
        let frame = encode_multi_frame(&[latch_mac_key, &out[0..49]]);
        let tag = cshake256_hash32(TAG_EPOCH_LATCH_MAC, &frame);
        out[49..81].copy_from_slice(&tag);
        out
    }

    /// Deserialize and constant-time verify an `81`-byte authenticated `EpochLatchState` record.
    pub fn from_authenticated_bytes(
        bytes: &[u8],
        latch_mac_key: &[u8; 32],
    ) -> Result<Self, DkgError> {
        if bytes.len() != 81 || !ct_eq_bytes(&bytes[0..8], LATCH_WIRE_MAGIC) || bytes[8] > 1 {
            return Err(DkgError::MalformedLatchBytes);
        }
        let frame = encode_multi_frame(&[latch_mac_key, &bytes[0..49]]);
        let expected_tag = cshake256_hash32(TAG_EPOCH_LATCH_MAC, &frame);
        let actual_tag: [u8; 32] = core::array::from_fn(|array_index| (bytes[49..81])[array_index]);
        if !ct_eq_bytes32(&expected_tag, &actual_tag) {
            return Err(DkgError::LatchAuthenticationFailed);
        }
        if bytes[8] == 0 {
            Ok(Self { high_water: None })
        } else {
            let ep = u64::from_be_bytes(core::array::from_fn(|array_index| (bytes[9..17])[array_index]));
            let mut mu = [0u8; 32];
            mu.copy_from_slice(&bytes[17..49]);
            Ok(Self {
                high_water: Some((ep, mu)),
            })
        }
    }
}

impl StatefulEpochLatch for EpochLatchState {
    fn reserve_next_epoch(
        &mut self,
        max_sigs_log2: usize,
        mu: &[u8; 32],
    ) -> Result<u64, StatefulLatchError> {
        if max_sigs_log2 == 0 || max_sigs_log2 > 62 {
            return Err(StatefulLatchError::InvalidCapacity);
        }
        let limit = 1u64 << max_sigs_log2;
        let next_ep = match self.high_water {
            None => 0u64,
            Some((hw, _)) => hw.checked_add(1).ok_or(StatefulLatchError::Exhausted)?,
        };
        if next_ep >= limit {
            return Err(StatefulLatchError::Exhausted);
        }
        self.high_water = Some((next_ep, *mu));
        Ok(next_ep)
    }

    fn retry_latched_epoch(
        &mut self,
        epoch: u64,
        mu: &[u8; 32],
    ) -> Result<u64, StatefulLatchError> {
        let Some((hw, bound_mu)) = self.high_water else {
            return Err(StatefulLatchError::EpochNotInFlight);
        };
        if epoch != hw {
            return Err(StatefulLatchError::EpochNotInFlight);
        }
        if !ct_eq_bytes32(&bound_mu, mu) {
            return Err(StatefulLatchError::EquivocationRefused);
        }
        Ok(epoch)
    }

    fn peek_next_epoch(&self) -> u64 {
        // A saturated high-water mark is refused as exhausted by every reservation.
        self.high_water.map_or(0, |(hw, _)| hw.saturating_add(1))
    }

    fn peek_in_flight(&self) -> Option<(u64, [u8; 32])> {
        self.high_water
    }

    fn reserve_epoch_at(
        &mut self,
        epoch: u64,
        max_sigs_log2: usize,
        mu: &[u8; 32],
    ) -> Result<(), StatefulLatchError> {
        if !self.check_reserve_epoch_at(epoch, max_sigs_log2, mu)? {
            self.high_water = Some((epoch, *mu));
        }
        Ok(())
    }
}

/// Encode a `97`-byte MAC-authenticated WAL record for [`MonotonicEpochLatch`].
pub fn encode_authenticated_wal_record(
    state: &MonotonicEpochLatch,
    latch_mac_key: &[u8; 32],
) -> [u8; 97] {
    let mut out = [0u8; 97];
    out[0..8].copy_from_slice(FS_WAL_MAGIC);
    out[8..16].copy_from_slice(&state.next_epoch().to_be_bytes());
    if let Some((ep, mu)) = state.in_flight() {
        out[16] = 1;
        out[17..25].copy_from_slice(&ep.to_be_bytes());
        out[25..57].copy_from_slice(&mu);
    }
    let frame = encode_multi_frame(&[latch_mac_key, &out[0..65]]);
    let tag = cshake256_hash32(TAG_FS_WAL_LATCH_MAC, &frame);
    out[65..97].copy_from_slice(&tag);
    out
}

/// Decode and constant-time verify a `97`-byte MAC-authenticated WAL record.
pub fn decode_authenticated_wal_record(
    bytes: &[u8],
    latch_mac_key: &[u8; 32],
) -> Result<MonotonicEpochLatch, StatefulLatchError> {
    if bytes.len() != 97 || !ct_eq_bytes(&bytes[0..8], FS_WAL_MAGIC) || bytes[16] > 1 {
        return Err(StatefulLatchError::PersistenceFailure);
    }
    let frame = encode_multi_frame(&[latch_mac_key, &bytes[0..65]]);
    let expected_tag = cshake256_hash32(TAG_FS_WAL_LATCH_MAC, &frame);
    let actual_tag: [u8; 32] = core::array::from_fn(|array_index| (bytes[65..97])[array_index]);
    if !ct_eq_bytes32(&expected_tag, &actual_tag) {
        return Err(StatefulLatchError::PersistenceFailure);
    }
    let next_epoch = u64::from_be_bytes(core::array::from_fn(|array_index| (bytes[8..16])[array_index]));
    let in_flight = if bytes[16] == 0 {
        None
    } else {
        let ep = u64::from_be_bytes(core::array::from_fn(|array_index| (bytes[17..25])[array_index]));
        if ep >= next_epoch {
            return Err(StatefulLatchError::PersistenceFailure);
        }
        let mut mu = [0u8; 32];
        mu.copy_from_slice(&bytes[25..57]);
        Some((ep, mu))
    };
    Ok(MonotonicEpochLatch::from_recovered_wal(
        next_epoch, in_flight,
    ))
}

/// Crash-atomic, `fsync`-backed write-ahead [`StatefulEpochLatch`] (`[P0-04]`).
///
/// ### Crash-Durability & Anti-Two-Time-Pad Contract
/// - Every `reserve_next_epoch` transition writes a `97`-byte `cSHAKE256`-authenticated WAL record
///   to `<wal_path>.tmp`, invokes `File::sync_all()` (`fsync`), atomically renames `<wal_path>.tmp`
///   onto `<wal_path>`, and invokes `File::sync_all()` on the parent directory **strictly before**
///   updating in-memory state or returning `Ok(epoch)`.
/// - Intentionally `!Clone` with redacted `fmt::Debug` and volatile `latch_mac_key` wipe on `Drop`.
#[cfg(feature = "std")]
pub struct FsWalEpochLatch {
    wal_path: std::path::PathBuf,
    record: qsag_asm::durable::LockedRecord,
    latch_mac_key: [u8; 32],
    inner: MonotonicEpochLatch,
}

#[cfg(feature = "std")]
impl fmt::Debug for FsWalEpochLatch {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("FsWalEpochLatch")
            .field("wal_path", &self.wal_path)
            .field("next_epoch", &self.inner.next_epoch())
            .field("latch_mac_key", &"[REDACTED]")
            .finish()
    }
}

#[cfg(feature = "std")]
impl Drop for FsWalEpochLatch {
    fn drop(&mut self) {
        wipe_bytes32(&mut self.latch_mac_key);
    }
}

#[cfg(feature = "std")]
impl FsWalEpochLatch {
    /// Compatibility recovery alias. Missing records fail closed; use
    /// `create_new_for_fresh_key` for explicit enrollment.
    ///
    /// Fails closed with [`StatefulLatchError::PersistenceFailure`] if an existing WAL file is
    /// truncated, corrupted, or fails constant-time `cSHAKE256` MAC verification.
    pub fn open_or_create(wal_path: impl Into<std::path::PathBuf>, latch_mac_key: [u8; 32]) -> Result<Self, StatefulLatchError> {
        Self::open_existing(wal_path, latch_mac_key)
    }

    /// Recover only; a missing record fails closed.
    pub fn open_existing(wal_path: impl Into<std::path::PathBuf>, latch_mac_key: [u8; 32]) -> Result<Self, StatefulLatchError> {
        Self::open_internal(wal_path.into(), latch_mac_key, false)
    }

    /// Explicit enrollment of a fresh key; refuses an existing lock or WAL.
    pub fn create_new_for_fresh_key(wal_path: impl Into<std::path::PathBuf>, latch_mac_key: [u8; 32]) -> Result<Self, StatefulLatchError> {
        Self::open_internal(wal_path.into(), latch_mac_key, true)
    }

    fn open_internal(wal_path: std::path::PathBuf, latch_mac_key: [u8; 32], create: bool) -> Result<Self, StatefulLatchError> {
        let record = qsag_asm::durable::LockedRecord::acquire(wal_path.clone())
            .map_err(|_| StatefulLatchError::PersistenceFailure)?;
        if create && !record.is_fresh() { return Err(StatefulLatchError::PersistenceFailure); }
        match record.read() {
            Ok(_) if create => Err(StatefulLatchError::PersistenceFailure),
            Ok(bytes) => {
                let inner = decode_authenticated_wal_record(&bytes, &latch_mac_key)?;
                Ok(Self {
                    wal_path,
                    record,
                    latch_mac_key,
                    inner,
                })
            }
            Err(e) if e.kind() == std::io::ErrorKind::NotFound && create && record.is_fresh() => {
                let latch = Self {
                    wal_path,
                    record,
                    latch_mac_key,
                    inner: MonotonicEpochLatch::new(0),
                };
                latch.persist_state_atomic(&latch.inner)?;
                Ok(latch)
            }
            Err(_) => Err(StatefulLatchError::PersistenceFailure),
        }
    }

    #[inline]
    pub fn next_epoch(&self) -> u64 {
        self.inner.next_epoch()
    }

    #[inline]
    pub fn in_flight(&self) -> Option<(u64, [u8; 32])> {
        self.inner.in_flight()
    }

    fn persist_state_atomic(&self, staged: &MonotonicEpochLatch) -> Result<(), StatefulLatchError> {
        let current = encode_authenticated_wal_record(&self.inner, &self.latch_mac_key);
        match self.record.read() {
            Ok(bytes) if bytes.as_slice() == current => {},
            Err(e) if e.kind() == std::io::ErrorKind::NotFound && self.record.is_fresh()
                && self.inner.next_epoch() == 0 => {},
            _ => return Err(StatefulLatchError::PersistenceFailure),
        }
        let mut rec = encode_authenticated_wal_record(staged, &self.latch_mac_key);
        let result = self.record.replace(&rec);
        wipe_bytes(&mut rec);
        result.map_err(|_| StatefulLatchError::PersistenceFailure)
    }
}

#[cfg(feature = "std")]
impl StatefulEpochLatch for FsWalEpochLatch {
    fn reserve_next_epoch(
        &mut self,
        max_sigs_log2: usize,
        mu: &[u8; 32],
    ) -> Result<u64, StatefulLatchError> {
        let mut staged = self.inner.stage_copy();
        let ep = staged.reserve_next_epoch(max_sigs_log2, mu)?;
        // Persist + `fsync` to disk STRICTLY BEFORE mutating `self.inner` or returning `Ok(ep)`!
        self.persist_state_atomic(&staged)?;
        self.inner = staged;
        Ok(ep)
    }

    fn retry_latched_epoch(
        &mut self,
        epoch: u64,
        mu: &[u8; 32],
    ) -> Result<u64, StatefulLatchError> {
        self.inner.retry_latched_epoch(epoch, mu)
    }

    fn peek_next_epoch(&self) -> u64 {
        self.inner.next_epoch()
    }

    fn peek_in_flight(&self) -> Option<(u64, [u8; 32])> {
        self.inner.in_flight()
    }

    fn reserve_epoch_at(
        &mut self,
        epoch: u64,
        max_sigs_log2: usize,
        mu: &[u8; 32],
    ) -> Result<(), StatefulLatchError> {
        if self.inner.check_reserve_epoch_at(epoch, max_sigs_log2, mu)? {
            return Ok(());
        }
        let mut staged = self.inner.stage_copy();
        staged.reserve_epoch_at(epoch, max_sigs_log2, mu)?;
        // Same order as `reserve_next_epoch`: the record is on disk before the state changes.
        self.persist_state_atomic(&staged)?;
        self.inner = staged;
        Ok(())
    }
}

/// The 32-byte value a committee latch quorum reserves for one signature: a commitment to the key
/// identity `(pk_seed, pk_root)`, the one-time `epoch`, and the message digest `mu`.
