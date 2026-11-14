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
