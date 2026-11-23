//! Threshold secret sharing, Shamir DKG Frobenius Booleanity verification,
//! and crash-retry-safe stateful custody primitives in `#![no_std]` safe Rust:
//! 1. `Gf256` & `Goldilocks` Shamir `eval_poly`, full-set `0..n` point validation,
//!    `lagrange_at_zero`, degree reduction, and DKG Frobenius Booleanity checks (`s^2 ⊕ s == 0`),
//! 2. 2-of-3 Replicated Secret Sharing (`RSS`) 64-lane bitsliced `rss_and_gate`, degree-reduction
//!    resharing, and Keccak `chi` lane evaluation,
//! 3. Affine `EpochLatch` transitions for caller-managed durable WAL storage (`EpochLatch::acquire_or_retry`
//!    and `epoch_latch_advance`) reject epoch equivocation and `r_rand` drift after state restoration.

use crate::goldilocks::{
    Goldilocks, goldilocks_add, goldilocks_canon, goldilocks_inv, goldilocks_mul, goldilocks_sub,
};
pub use crate::tower::ct_eq_bytes32;
use crate::tower::{
    BdozCommittedBatchOpening2Lane, BdozWireOpening2Lane, Gf256, Tower128, gf256_add,
    gf256_frobenius_residual, gf256_inv, gf256_is_boolean_frobenius, gf256_mul, verify_mac_2lane,
};

// ============================================================================
// 1. Shamir Polynomial Evaluation, Full-Set Point Validation, & Lagrange-at-Zero
// ============================================================================

/// Validate that a non-empty evaluation-point vector over `Gf256` contains strictly non-zero,
/// pairwise-distinct coordinates across **all** `0..points.len()` parties.
pub fn shamir_validate_points_gf256(points: &[Gf256]) -> bool {
    let n = points.len();
    if n == 0 {
        return false;
    }
    let mut ok = true;
    let mut i: usize = 0;
    while i < n {
        if points[i].0 == 0 {
            ok = false;
        }
        let mut j = i + 1;
        while j < n {
            if points[i].0 == points[j].0 {
                ok = false;
            }
            j += 1;
        }
        i += 1;
    }
    ok
}

/// Evaluate polynomial `coeffs[0] + coeffs[1]*x + ...` over `Gf256` via Horner's rule.
pub fn shamir_eval_poly_gf256(coeffs: &[Gf256], x: Gf256) -> Gf256 {
    let mut acc = Gf256(0);
    let mut rem = coeffs.len();
    while rem > 0 {
        rem -= 1;
        acc = gf256_add(gf256_mul(acc, x), coeffs[rem]);
    }
    acc
}

/// Evaluate polynomial `coeffs[0] + coeffs[1]*x + ...` over `Goldilocks` via Horner's rule.
pub fn shamir_eval_poly_goldilocks(coeffs: &[Goldilocks], x: Goldilocks) -> Goldilocks {
    let mut acc = Goldilocks(0);
    let mut rem = coeffs.len();
    while rem > 0 {
        rem -= 1;
        acc = goldilocks_add(goldilocks_mul(acc, x), coeffs[rem]);
    }
    acc
}

/// Compute the `i`-th Lagrange basis weight `lambda_i(0) = prod_{j != i} x_j / (x_j - x_i)` over `Gf256`.
/// Rejects out-of-bounds `i`, zero `x_i`, and duplicate points (`x_i == x_j`).
pub fn shamir_lagrange_weight_zero_gf256(points: &[Gf256], i: usize) -> Option<Gf256> {
    let t = points.len();
    if i >= t {
        return None;
    }
    let xi = points[i];
    if xi.0 == 0 {
        return None;
    }
    let mut num = Gf256(1);
    let mut den = Gf256(1);
    let mut valid = true;
    let mut j: usize = 0;
    while j < t {
        if i != j {
            let xj = points[j];
            let diff = gf256_add(xi, xj);
            if diff.0 == 0 {
                valid = false;
            } else {
                num = gf256_mul(num, xj);
                den = gf256_mul(den, diff);
            }
        }
        j += 1;
    }
    if !valid {
        return None;
    }
    match gf256_inv(den) {
        Some(den_inv) => Some(gf256_mul(num, den_inv)),
        None => None,
    }
}

/// Reconstruct Shamir secret `f(0)` over `Gf256` from `(points, shares)`.
/// Rejects empty inputs, mismatched slice lengths, zero points, and duplicate points.
pub fn shamir_lagrange_at_zero_gf256(points: &[Gf256], shares: &[Gf256]) -> Option<Gf256> {
    let t = points.len();
    if t == 0 || shares.len() != t {
        return None;
    }
    let mut secret = Gf256(0);
    let mut valid = true;
    let mut i: usize = 0;
    while i < t {
        match shamir_lagrange_weight_zero_gf256(points, i) {
            Some(lambda_i) => {
                secret = gf256_add(secret, gf256_mul(shares[i], lambda_i));
            }
            None => {
                valid = false;
            }
        }
        i += 1;
    }
    if valid { Some(secret) } else { None }
}

/// Compute the `i`-th Lagrange basis weight `lambda_i(0) = prod_{j != i} x_j / (x_j - x_i)` over `Goldilocks`.
/// Rejects out-of-bounds `i`, zero `x_i mod p`, and duplicate points mod `p`.
pub fn shamir_lagrange_weight_zero_goldilocks(
    points: &[Goldilocks],
    i: usize,
) -> Option<Goldilocks> {
    let t = points.len();
    if i >= t {
        return None;
    }
    let xi = goldilocks_canon(points[i].0);
    if xi.0 == 0 {
        return None;
    }
    let mut num = Goldilocks(1);
    let mut den = Goldilocks(1);
    let mut valid = true;
    let mut j: usize = 0;
    while j < t {
        if i != j {
            let xj = goldilocks_canon(points[j].0);
            let diff = goldilocks_sub(xj, xi);
            if diff.0 == 0 {
                valid = false;
            } else {
                num = goldilocks_mul(num, xj);
                den = goldilocks_mul(den, diff);
            }
        }
        j += 1;
    }
    if !valid {
        return None;
    }
    match goldilocks_inv(den) {
        Some(den_inv) => Some(goldilocks_mul(num, den_inv)),
        None => None,
    }
}

/// Reconstruct Shamir secret `f(0)` over `Goldilocks` from `(points, shares)`.
/// Rejects empty inputs, mismatched slice lengths, zero points, and duplicate points mod `p`.
pub fn shamir_lagrange_at_zero_goldilocks(
    points: &[Goldilocks],
    shares: &[Goldilocks],
) -> Option<Goldilocks> {
    let t = points.len();
    if t == 0 || shares.len() != t {
        return None;
    }
    let mut secret = Goldilocks(0);
    let mut valid = true;
    let mut i: usize = 0;
    while i < t {
        match shamir_lagrange_weight_zero_goldilocks(points, i) {
            Some(lambda_i) => {
                secret = goldilocks_add(secret, goldilocks_mul(shares[i], lambda_i));
            }
            None => {
                valid = false;
            }
        }
        i += 1;
    }
    if valid { Some(secret) } else { None }
}

/// Degree reduction step for 2-of-3 Shamir multiplication over `Gf256`:
/// given three local product shares `d_i = a_i * b_i` of degree `2(t-1) = 2` masked by a
/// degree-1 random re-sharing polynomial `r_i(x)` with `r_i(0) = d_i * lambda_i`,
/// computes party `target_party`'s reduced degree-1 share of `a * b`.
pub fn shamir_degree_reduce_2of3_gf256(
    points: [Gf256; 3],
    local_products: [Gf256; 3],
    reshare_slopes: [Gf256; 3],
    target_point: Gf256,
) -> Option<Gf256> {
    let x0 = points[0];
    let x1 = points[1];
    let x2 = points[2];
    if x0.0 == 0 || x1.0 == 0 || x2.0 == 0 {
        return None;
    }
    let d01 = gf256_add(x0, x1);
    let d02 = gf256_add(x0, x2);
    let d12 = gf256_add(x1, x2);
    let inv0 = match gf256_inv(gf256_mul(d01, d02)) {
        Some(v) => v,
        None => return None,
    };
    let inv1 = match gf256_inv(gf256_mul(d01, d12)) {
        Some(v) => v,
        None => return None,
    };
    let inv2 = match gf256_inv(gf256_mul(d02, d12)) {
        Some(v) => v,
        None => return None,
    };
    let lam0 = gf256_mul(gf256_mul(x1, x2), inv0);
    let lam1 = gf256_mul(gf256_mul(x0, x2), inv1);
    let lam2 = gf256_mul(gf256_mul(x0, x1), inv2);

    let c0 = gf256_mul(local_products[0], lam0);
    let c1 = gf256_mul(local_products[1], lam1);
    let c2 = gf256_mul(local_products[2], lam2);

    let s0 = gf256_add(c0, gf256_mul(reshare_slopes[0], target_point));
    let s1 = gf256_add(c1, gf256_mul(reshare_slopes[1], target_point));
    let s2 = gf256_add(c2, gf256_mul(reshare_slopes[2], target_point));
    Some(gf256_add(gf256_add(s0, s1), s2))
}

// ============================================================================
// 2. Shamir DKG Frobenius Subfield Booleanity Verification (`s^2 ⊕ s == 0`)
// ============================================================================

/// Evaluate the Beaver-triple Frobenius residual `c ⊕ eps*b ⊕ delta*a ⊕ eps*delta ⊕ s` over `Gf256`
/// where `eps = s ⊕ a` and `delta = s ⊕ b`.
/// When `c == a * b`, this algebraically equals `s^2 ⊕ s` without exposing `s` during `(eps, delta)` opening!
#[inline]
pub const fn dkg_beaver_frobenius_eval_gf256(a: Gf256, b: Gf256, c: Gf256, s: Gf256) -> Gf256 {
    let eps = gf256_add(s, a);
    let delta = gf256_add(s, b);
    let s_sq = gf256_add(
        gf256_add(c, gf256_mul(eps, b)),
        gf256_add(gf256_mul(delta, a), gf256_mul(eps, delta)),
    );
    gf256_add(s_sq, s)
}

/// Compute a party's local Shamir share of the Frobenius residual `[z] = [s^2 ⊕ s]` from
/// Shamir shares `([s], [a], [b], [c])` and opened Beaver differences `(eps, delta)`.
#[inline]
pub const fn dkg_beaver_frobenius_share_shamir_gf256(
    s_share: Gf256,
    a_share: Gf256,
    b_share: Gf256,
    c_share: Gf256,
    eps_open: Gf256,
    delta_open: Gf256,
) -> Gf256 {
    let s_sq_share = gf256_add(
        gf256_add(c_share, gf256_mul(eps_open, b_share)),
        gf256_add(
            gf256_mul(delta_open, a_share),
            gf256_mul(eps_open, delta_open),
        ),
    );
    gf256_add(s_sq_share, s_share)
}

/// Actively verify a non-empty batch of Shamir DKG key-bit shares over `Gf256`:
/// 1. Authenticates all opened Frobenius residuals `z_k = s_k^2 ⊕ s_k` via committed, random-masked
///    2-lane `Tower128` BDOZ `verify_mac_2lane`,
/// 2. Accumulates `z_k.0` across all shares in constant time (no early-exit index leak) and accepts
///    iff every key share satisfies `z_k == 0` (`s_k^2 ⊕ s_k == 0 <==> s_k in {0, 1}`).
pub fn dkg_verify_key_shares_boolean_bdoz_gf256(
    alpha_lanes: [Tower128; 2],
    batch_opening: &BdozCommittedBatchOpening2Lane,
    residual_openings: &[BdozWireOpening2Lane],
) -> bool {
    if !verify_mac_2lane(alpha_lanes, batch_opening, residual_openings) {
        return false;
    }
    let mut non_boolean_acc: u8 = 0;
    let mut i: usize = 0;
    while i < residual_openings.len() {
        non_boolean_acc |= residual_openings[i].opened_value.0;
        i += 1;
    }
    non_boolean_acc == 0
}

/// Verify that a 2-of-3 Shamir DKG key-bit sharing `(s0, s1, s2)` at `points = [x0, x1, x2]`
/// has degree `< 2` AND encodes a true prime-subfield bit `f(0) in {0, 1}` via Frobenius
/// polynomial interpolation `Q(X) = f(X)^2 ⊕ f(X)` (`Q(0) = f(0)^2 ⊕ f(0) == 0`).
/// Operates on three opened/reconstructed shares, checking degree-1 Shamir consistency
/// and Frobenius Booleanity; this is not a privacy-preserving share-opening protocol.
pub fn dkg_verify_shamir_2of3_key_bit_gf256(points: [Gf256; 3], shares: [Gf256; 3]) -> bool {
    if !shamir_validate_points_gf256(&points) {
        return false;
    }
    // Check degree < 2 consistency between {0, 1} and {1, 2} reconstructions
    let pair01_pts = [points[0], points[1]];
    let pair01_sh = [shares[0], shares[1]];
    let pair12_pts = [points[1], points[2]];
    let pair12_sh = [shares[1], shares[2]];
    let rec01 = match shamir_lagrange_at_zero_gf256(&pair01_pts, &pair01_sh) {
        Some(v) => v,
        None => return false,
    };
    let rec12 = match shamir_lagrange_at_zero_gf256(&pair12_pts, &pair12_sh) {
        Some(v) => v,
        None => return false,
    };
    if rec01.0 != rec12.0 {
        return false;
    }
    // Evaluate degree-<=2 Frobenius polynomial Q(x_i) = s_i^2 ⊕ s_i and interpolate Q(0) = f(0)^2 ⊕ f(0)
    let q_shares = [
        gf256_frobenius_residual(shares[0]),
        gf256_frobenius_residual(shares[1]),
        gf256_frobenius_residual(shares[2]),
    ];
    match shamir_lagrange_at_zero_gf256(&points, &q_shares) {
        Some(q0) => q0.0 == 0 && gf256_is_boolean_frobenius(rec01),
        None => false,
    }
}

// ============================================================================
// 3. 2-of-3 Replicated Secret Sharing (`RSS`) 64-Lane Bitsliced `and_gate`
// ============================================================================

/// 64-bit bitsliced 2-of-3 replicated secret share `(x0, x1, x2)`:
/// Party 0 holds `(x0, x1)`, Party 1 holds `(x1, x2)`, Party 2 holds `(x2, x0)`.
#[derive(Clone, Copy, Default)]
pub struct RssShare64 {
    pub x0: u64,
    pub x1: u64,
    pub x2: u64,
}

/// Pairwise correlated PRF randomness words `(r0, r1, r2)` where Party `i` holds `(r_i, r_{i+1})`.
/// Their XOR `(r0 ^ r1) ^ (r1 ^ r2) ^ (r2 ^ r0) == 0` forms a degree-reducing zero-share.
#[derive(Clone, Copy, Default)]
pub struct RssZeroSeeds64 {
    pub r0: u64,
    pub r1: u64,
    pub r2: u64,
}

/// Share a secret word using two caller-supplied masks.
#[inline]
pub const fn rss_share_u64(secret: u64, m0: u64, m1: u64) -> RssShare64 {
    RssShare64 {
        x0: m0,
        x1: m1,
        x2: secret ^ m0 ^ m1,
    }
}

/// Reconstruct the 64-bit secret word `x0 ^ x1 ^ x2` from a 2-of-3 `RssShare64`.
#[inline]
pub const fn rss_reconstruct(sh: RssShare64) -> u64 {
    sh.x0 ^ sh.x1 ^ sh.x2
}

/// Local 2-of-3 RSS bitwise XOR (`0` communication).
#[inline]
pub const fn rss_xor(a: RssShare64, b: RssShare64) -> RssShare64 {
    RssShare64 {
        x0: a.x0 ^ b.x0,
        x1: a.x1 ^ b.x1,
        x2: a.x2 ^ b.x2,
    }
}

/// Local 2-of-3 RSS bitwise NOT (`!x0 ^ x1 ^ x2 == !(x0 ^ x1 ^ x2)`).
#[inline]
pub const fn rss_not(a: RssShare64) -> RssShare64 {
    RssShare64 {
        x0: !a.x0,
        x1: a.x1,
        x2: a.x2,
    }
}

/// Single-party local AND + correlated zero-share degree reduction (Araki et al. CCS 2016):
/// uses strictly Party `i`'s 2-of-3 view `(ax_i, ax_next, bx_i, bx_next, r_i, r_next)`.
#[inline]
pub const fn rss_party_and_local(
    ax_i: u64,
    ax_next: u64,
    bx_i: u64,
    bx_next: u64,
    r_i: u64,
    r_next: u64,
) -> u64 {
    (ax_i & bx_i) ^ (ax_i & bx_next) ^ (ax_next & bx_i) ^ (r_i ^ r_next)
}

/// 64-way bitsliced 2-of-3 RSS `AND` gate with correlated zero-share degree reduction:
/// computes `z = (z0, z1, z2)` such that `rss_reconstruct(z) == rss_reconstruct(a) & rss_reconstruct(b)`.
#[inline]
pub const fn rss_and_gate(a: RssShare64, b: RssShare64, seeds: RssZeroSeeds64) -> RssShare64 {
    RssShare64 {
        x0: rss_party_and_local(a.x0, a.x1, b.x0, b.x1, seeds.r0, seeds.r1),
        x1: rss_party_and_local(a.x1, a.x2, b.x1, b.x2, seeds.r1, seeds.r2),
        x2: rss_party_and_local(a.x2, a.x0, b.x2, b.x0, seeds.r2, seeds.r0),
    }
}

/// Re-share reduced additive outputs `(z0, z1, z2)` into each party's new 2-of-3 replicated view.
#[inline]
pub const fn rss_reshare_views(z: RssShare64) -> ([u64; 2], [u64; 2], [u64; 2]) {
    ([z.x0, z.x1], [z.x1, z.x2], [z.x2, z.x0])
}

/// 64-way bitsliced 2-of-3 RSS Keccak `chi` step `a ^ ((!b) & c)`.
#[inline]
pub const fn rss_keccak_chi_lane(
    a: RssShare64,
    b: RssShare64,
    c: RssShare64,
    seeds: RssZeroSeeds64,
) -> RssShare64 {
    rss_xor(a, rss_and_gate(rss_not(b), c, seeds))
}

// ============================================================================
// 4. Crash-Retry-Safe Monotonic WAL `EpochLatch`
// ============================================================================

/// Binding to persist in the WAL for the most recently authorized stateful `Jorts` epoch:
/// the caller must persist `(epoch, msg_digest, r_rand)` before any MPC opening and restore
/// it on recovery to reject retries with a different digest or randomizer.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct BoundEpochRecord {
    pub epoch: u64,
    pub msg_digest: [u8; 32],
    pub r_rand: [u8; 32],
}

/// Explicit WAL latch slot state: `Unset` holds prior to epoch 0 or after
/// `epoch_latch_advance` seals prior epochs without a retryable `(msg_digest, r_rand)` record.
/// `Bound(rec)` holds when latched by `EpochLatch::acquire_or_retry`.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum LastBoundEpoch {
    Unset,
    Bound(BoundEpochRecord),
}

/// Affine state-transition machine guarding stateful XMSS / `Jorts` WOTS+C leaf indices.
/// The caller must durably persist the updated state to a write-ahead log before releasing
/// signing grants. This in-memory machine performs no durable writes or crash recovery.
///
/// External callers cannot reset the authorization state.
/// ```compile_fail,E0616
/// use qsag_verified::EpochLatch;
/// let mut guard = EpochLatch::new(10, [0; 32]);
/// guard.next_epoch = 0;
/// ```
pub struct EpochLatch {
    next_epoch: u64,
    max_epoch: u64,
    key_epoch_id: [u8; 32],
    last_bound: LastBoundEpoch,
}

/// Incoming stateful `Jorts` signing authorization request binding `(requested_epoch, key_epoch_id,
/// msg_digest, deterministic_r_rand)`.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct EpochSignRequest {
    pub requested_epoch: u64,
    pub key_epoch_id: [u8; 32],
    pub msg_digest: [u8; 32],
    pub deterministic_r_rand: [u8; 32],
}

/// Verified signing authorization grant emitted by `EpochLatch::acquire_or_retry`.
///
/// ```compile_fail
/// use qsag_verified::EpochAuthGrant;
/// let forged = EpochAuthGrant { authorized_epoch: 0, msg_digest: [0; 32],
///     r_rand: [0; 32], is_idempotent_retry: false };
/// ```
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct EpochAuthGrant {
    _private: (),
    pub authorized_epoch: u64,
    pub msg_digest: [u8; 32],
    pub r_rand: [u8; 32],
    pub is_idempotent_retry: bool,
}

/// Epoch-only sequential advance request (`epoch_latch_advance`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EpochRequest {
    pub requested_epoch: u64,
    pub key_epoch_id: [u8; 32],
}

/// Explicit rejection reasons when `EpochLatch::acquire_or_retry` or `epoch_latch_advance` refuses a call.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EpochLatchError {
    KeyBindingMismatch,
    CorruptedWalState,
    EpochEquivocationAttempt { epoch: u64 },
    RetryRandomizerMismatch { epoch: u64 },
    NonSequentialEpoch { expected: u64, requested: u64 },
    TreeExhausted { max_epoch: u64 },
}

impl EpochLatch {
    pub const fn next_epoch(&self) -> u64 {
        self.next_epoch
    }
    pub const fn max_epoch(&self) -> u64 {
        self.max_epoch
    }
    pub const fn key_epoch_id(&self) -> [u8; 32] {
        self.key_epoch_id
    }
    pub const fn last_bound(&self) -> LastBoundEpoch {
        self.last_bound
    }

    /// Construct a fresh `EpochLatch` at `next_epoch = 0` with `last_bound = LastBoundEpoch::Unset`.
    #[inline]
    pub const fn new(max_epoch: u64, key_epoch_id: [u8; 32]) -> Self {
        Self {
            next_epoch: 0,
            max_epoch,
            key_epoch_id,
            last_bound: LastBoundEpoch::Unset,
        }
    }

    /// Consume the latch to acquire a fresh sequential epoch or authorize an idempotent retry.
    /// Persist the returned state durably before releasing the returned signing grant.
    /// - Rejects key-domain mismatch (`KeyBindingMismatch`),
    /// - Rejects corrupted WAL states where `bound.epoch >= self.next_epoch` (`CorruptedWalState`),
    /// - If `req.requested_epoch` matches `bound.epoch`:
    ///   * rejects different `msg_digest` (`EpochEquivocationAttempt`),
    ///   * rejects different `deterministic_r_rand` (`RetryRandomizerMismatch`),
    ///   * otherwise returns `(self, grant)` idempotently with `is_idempotent_retry = true`,
    /// - Otherwise requires `req.requested_epoch == self.next_epoch < self.max_epoch`, advances
    ///   `next_epoch` to `self.next_epoch + 1`, and binds `(epoch, msg_digest, deterministic_r_rand)` in `last_bound`.
    pub const fn acquire_or_retry(
        self,
        req: EpochSignRequest,
    ) -> Result<(EpochLatch, EpochAuthGrant), EpochLatchError> {
        if !ct_eq_bytes32(&self.key_epoch_id, &req.key_epoch_id) {
            return Err(EpochLatchError::KeyBindingMismatch);
        }
        match self.last_bound {
            LastBoundEpoch::Bound(bound) => {
                if bound.epoch >= self.next_epoch {
                    return Err(EpochLatchError::CorruptedWalState);
                }
                if req.requested_epoch == bound.epoch {
                    if !ct_eq_bytes32(&bound.msg_digest, &req.msg_digest) {
                        return Err(EpochLatchError::EpochEquivocationAttempt {
                            epoch: bound.epoch,
                        });
                    }
                    if !ct_eq_bytes32(&bound.r_rand, &req.deterministic_r_rand) {
                        return Err(EpochLatchError::RetryRandomizerMismatch {
                            epoch: bound.epoch,
                        });
                    }
                    return Ok((
                        self,
                        EpochAuthGrant {
                            _private: (),
                            authorized_epoch: bound.epoch,
                            msg_digest: bound.msg_digest,
                            r_rand: bound.r_rand,
                            is_idempotent_retry: true,
                        },
                    ));
                }
            }
            LastBoundEpoch::Unset => {}
        }
        if req.requested_epoch != self.next_epoch {
            return Err(EpochLatchError::NonSequentialEpoch {
                expected: self.next_epoch,
                requested: req.requested_epoch,
            });
        }
        if self.next_epoch >= self.max_epoch {
            return Err(EpochLatchError::TreeExhausted {
                max_epoch: self.max_epoch,
            });
        }
        let assigned_epoch = self.next_epoch;
        let record = BoundEpochRecord {
            epoch: assigned_epoch,
            msg_digest: req.msg_digest,
            r_rand: req.deterministic_r_rand,
        };
        let next_state = EpochLatch {
            next_epoch: assigned_epoch + 1,
            max_epoch: self.max_epoch,
            key_epoch_id: self.key_epoch_id,
            last_bound: LastBoundEpoch::Bound(record),
        };
        let grant = EpochAuthGrant {
            _private: (),
            authorized_epoch: assigned_epoch,
            msg_digest: req.msg_digest,
            r_rand: req.deterministic_r_rand,
            is_idempotent_retry: false,
        };
        Ok((next_state, grant))
    }
}

/// Strictly monotonic non-retry epoch advance (`epoch == st.next_epoch`, `st'.next_epoch == st.next_epoch + 1`,
/// and `st'.last_bound == LastBoundEpoch::Unset` so prior bound epochs are sealed and cannot be retried).
pub const fn epoch_latch_advance(
    st: EpochLatch,
    req: EpochRequest,
) -> Result<(EpochLatch, u64), EpochLatchError> {
    if !ct_eq_bytes32(&st.key_epoch_id, &req.key_epoch_id) {
        return Err(EpochLatchError::KeyBindingMismatch);
    }
    match st.last_bound {
        LastBoundEpoch::Bound(bound) => {
            if bound.epoch >= st.next_epoch {
                return Err(EpochLatchError::CorruptedWalState);
            }
        }
        LastBoundEpoch::Unset => {}
    }
    if req.requested_epoch != st.next_epoch {
        return Err(EpochLatchError::NonSequentialEpoch {
            expected: st.next_epoch,
            requested: req.requested_epoch,
        });
    }
    if st.next_epoch >= st.max_epoch {
        return Err(EpochLatchError::TreeExhausted {
            max_epoch: st.max_epoch,
        });
    }
    let assigned_epoch = st.next_epoch;
    let next_state = EpochLatch {
        next_epoch: assigned_epoch + 1,
        max_epoch: st.max_epoch,
        key_epoch_id: st.key_epoch_id,
        last_bound: LastBoundEpoch::Unset,
    };
    Ok((next_state, assigned_epoch))
}

#[cfg(test)]
mod private_state_tests {
    use super::*;
    #[test]
    fn corrupted_epoch_state_fails_closed() {
        let key_id = [1u8; 32];
        let msg_a = [2u8; 32];
        let msg_b = [3u8; 32];
        let r0 = [4u8; 32];
        let r1 = [5u8; 32];
        // 8. Corrupted WAL state (bound.epoch >= next_epoch) MUST fail!
        let corrupted = EpochLatch {
            next_epoch: 1,
            max_epoch: 4,
            key_epoch_id: key_id,
            last_bound: LastBoundEpoch::Bound(BoundEpochRecord {
                epoch: 1,
                msg_digest: msg_a,
                r_rand: r0,
            }),
        };
        assert_eq!(
            corrupted
                .acquire_or_retry(EpochSignRequest {
                    requested_epoch: 1,
                    key_epoch_id: key_id,
                    msg_digest: msg_a,
                    deterministic_r_rand: r0,
                })
                .err(),
            Some(EpochLatchError::CorruptedWalState)
        );

        // Reject bound records at or beyond the next epoch.
        for bound_epoch in [1, 2] {
            let invalid = EpochLatch {
                next_epoch: 1,
                max_epoch: 4,
                key_epoch_id: key_id,
                last_bound: LastBoundEpoch::Bound(BoundEpochRecord {
                    epoch: bound_epoch,
                    msg_digest: msg_a,
                    r_rand: r0,
                }),
            };
            assert_eq!(
                epoch_latch_advance(
                    invalid,
                    EpochRequest {
                        requested_epoch: 1,
                        key_epoch_id: key_id,
                    }
                )
                .err(),
                Some(EpochLatchError::CorruptedWalState)
            );
        }

        // Exhaustion applies at and beyond the limit with either retry-slot state.
        for bound in [false, true] {
            for next_epoch in [2, 3] {
                let st = EpochLatch {
                    next_epoch,
                    max_epoch: 2,
                    key_epoch_id: key_id,
                    last_bound: if bound {
                        LastBoundEpoch::Bound(BoundEpochRecord {
                            epoch: 1,
                            msg_digest: msg_b,
                            r_rand: r1,
                        })
                    } else {
                        LastBoundEpoch::Unset
                    },
                };
                assert_eq!(
                    epoch_latch_advance(
                        st,
                        EpochRequest {
                            requested_epoch: next_epoch,
                            key_epoch_id: key_id,
                        }
                    )
                    .err(),
                    Some(EpochLatchError::TreeExhausted { max_epoch: 2 })
                );
            }
        }
    }
}
