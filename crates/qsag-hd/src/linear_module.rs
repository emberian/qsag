//! Linear module custody with dealerless provisioning (see `dealerless.rs` and
//! [`crate::seeds`] for the protocol, corruption model and soundness bounds).
//! Module-LWE relation t = A s1 + s2 over four ring equations and eight
//! short secret polynomials. Child derivation adds public CBD2 vectors to both
//! halves. This is a related-key derivation construction, not a security proof;
//! depth bounds do not establish ML-DSA compatibility or a concrete LWE estimate.

use alloc::sync::Arc;
use alloc::vec::Vec;
use core::fmt;
use core::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

use qsag_accel::ct::{RedactedSecret, ct_lt_u64, ct_select_u64};
use qsag_accel::keccak::{cshake256_framed_32, cshake256_framed_xof};
use qsag_addr::{KeyIdentityKind, QsagAddress, WitnessSuiteTag};

use crate::erase::{ct_zeroize_bytes, ct_zeroize_u32s};
use crate::inventory::HdError;

/// Canonical prime modulus $q = 8\_380\_417 = 2^{23} - 2^{13} + 1 \equiv 1 \pmod{512}$.
pub const MODULE_Q: u32 = 8_380_417;
/// Cyclotomic ring degree $N = 256$ ($\mathcal{R}_q = \mathbb{Z}_q[X]/(X^{256} + 1)$).
pub const MODULE_N: usize = 256;
/// Module rank $K = 4$ (rows of $\mathbf{A}$).
pub const MODULE_K: usize = 4;
/// Secret vector dimension $L = 4$ ($\mathbf{s} = (\mathbf{s}_1, \mathbf{s}_2, \mathbf{s}_3, \mathbf{s}_4)$).
pub const MODULE_L: usize = 4;
/// Total secret polynomials: four s1 and four independent error polynomials s2.
pub const MODULE_SECRET_L: usize = MODULE_L + MODULE_K;
/// Seven independent field MAC keys: q^-7 = 8380417^-7, about 2^-160.9901.
/// This is the per-attempt algebraic forgery bound; hash and sampling errors are additional.
pub const SPDZ_LANES: usize = 7;
pub const MODULE_MAC_LANES: usize = SPDZ_LANES;
/// Default maximum non-hardened derivation depth $D_{\max} = 1024$.
pub const DEFAULT_MAX_DERIVATION_DEPTH: u16 = 1024;

/// Barrett reduction for every u64 input. With mu=floor(2^64/q), the
/// quotient estimate is at most one below floor(x/q), so r is below 2q.
/// The correction mask is kept opaque to the optimizer; audit the final image.
#[inline]
pub fn ct_reduce_mod_q_u64(x: u64) -> u32 {
    const MU: u128 = (1u128 << 64) / MODULE_Q as u128;
    let quotient = ((x as u128 * MU) >> 64) as u64;
    let r = x - quotient * MODULE_Q as u64;
    let mask = core::hint::black_box(0u64.wrapping_sub((r >= MODULE_Q as u64) as u64));
    (r.wrapping_sub((MODULE_Q as u64) & mask)) as u32
}

/// Full-width reduction using four fixed base-2^32 Horner steps. Each
/// intermediate fits in u64 because the preceding remainder is below q.
#[inline]
pub fn ct_reduce_mod_q_u128(x: u128) -> u32 {
    let mut r = 0u32;
    for shift in [96, 64, 32, 0] {
        r = ct_reduce_mod_q_u64(((r as u64) << 32) | ((x >> shift) as u32 as u64));
    }
    r
}

#[inline]
pub const fn mod_q_add(a: u32, b: u32) -> u32 {
    let s = a + b;
    let over = !ct_lt_u64(s as u64, MODULE_Q as u64);
    ct_select_u64(over, s.wrapping_sub(MODULE_Q) as u64, s as u64) as u32
}

#[inline]
pub const fn mod_q_sub(a: u32, b: u32) -> u32 {
    let lt = ct_lt_u64(a as u64, b as u64);
    let diff = a.wrapping_sub(b);
    ct_select_u64(lt, diff.wrapping_add(MODULE_Q) as u64, diff as u64) as u32
}

#[inline]
pub fn mod_q_mul(a: u32, b: u32) -> u32 {
    ct_reduce_mod_q_u64((a as u64) * (b as u64))
}

/// Constant-time Fermat inversion $a^{q - 2} \bmod q$ (`0` maps to `0`).
pub fn mod_q_inv_or_zero(a: u32) -> u32 {
    let mut base = ct_reduce_mod_q_u64(a as u64);
    let mut exp = MODULE_Q - 2;
    let mut acc = 1u32;
    while exp > 0 {
        if (exp & 1) == 1 {
            acc = mod_q_mul(acc, base);
        }
        base = mod_q_mul(base, base);
        exp >>= 1;
    }
    acc
}

/// Element of $\mathcal{R}_q = \mathbb{Z}_q[X]/(X^{256} + 1)$ in canonical coefficient form `[0, q)`.
#[derive(Clone, PartialEq, Eq)]
pub struct RingPoly {
    pub coeffs: [u32; MODULE_N],
}

impl Drop for RingPoly {
    fn drop(&mut self) {
        ct_zeroize_u32s(&mut self.coeffs);
    }
}

impl Default for RingPoly {
    fn default() -> Self {
        Self::zero()
    }
}

impl fmt::Debug for RingPoly {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "RingPoly([{} coeffs mod {}])", MODULE_N, MODULE_Q)
    }
}

impl RingPoly {
    pub const fn zero() -> Self {
        Self {
            coeffs: [0u32; MODULE_N],
        }
    }

    pub fn add(&self, rhs: &Self) -> Self {
        let mut out = [0u32; MODULE_N];
        for (i, value) in out.iter_mut().enumerate() {
            *value = mod_q_add(self.coeffs[i], rhs.coeffs[i]);
        }
        Self { coeffs: out }
    }

    pub fn sub(&self, rhs: &Self) -> Self {
        let mut out = [0u32; MODULE_N];
        for (i, value) in out.iter_mut().enumerate() {
            *value = mod_q_sub(self.coeffs[i], rhs.coeffs[i]);
        }
        Self { coeffs: out }
    }

    pub fn scale(&self, scalar: u32) -> Self {
        let s = ct_reduce_mod_q_u64(scalar as u64);
        let mut out = [0u32; MODULE_N];
        for (i, value) in out.iter_mut().enumerate() {
            *value = mod_q_mul(self.coeffs[i], s);
        }
        Self { coeffs: out }
    }

    /// Fixed-schedule twisted NTT multiplication modulo X^256+1.
    pub fn mul_negacyclic(&self, rhs: &Self) -> Self {
        let mut left = forward(self);
        let right = forward(rhs);
        for (a, &b) in left.coeffs.iter_mut().zip(&right.coeffs) {
            *a = mod_q_mul(*a, b);
        }
        inverse(left)
    }

    /// Exact integer squared Euclidean norm $\sum_{m=0}^{255} c_m^2$ of centered representatives
    /// in $[-(q-1)/2, (q-1)/2]$ (`0` floating-point instructions!).
    pub fn centered_l2_norm_sq(&self) -> u64 {
        let half_q = (MODULE_Q / 2) as u64;
        let mut sum_sq = 0u64;
        for &c in &self.coeffs {
            let c64 = c as u64;
            let gt_half = ct_lt_u64(half_q, c64);
            let abs_val = ct_select_u64(gt_half, (MODULE_Q as u64) - c64, c64);
            sum_sq = sum_sq.saturating_add(abs_val * abs_val);
        }
        sum_sq
    }

    /// Sample a short centered-binomial polynomial $\text{CBD}_2$ (`[-2, 2]`) in 100% constant time
    /// via bit-popcount difference (`0` floats, `0` divisions, `0` rejection branches!).
    pub fn sample_cbd2_ct(domain: &[u8], seed: &[u8], tag_idx: u32) -> Self {
        let idx_be = tag_idx.to_be_bytes();
        let mut buf = [0u8; 128];
        cshake256_framed_xof(domain, &[seed, &idx_be], &mut buf);
        let mut coeffs = [0u32; MODULE_N];
        for (i, &byte) in buf.iter().enumerate() {
            // Two coefficients per byte (`4` bits each: `a0 + a1 - b0 - b1` in `[-2, 2]`).
            let lo = byte & 0x0F;
            let hi = byte >> 4;
            let pos_lo = ((lo & 1) + ((lo >> 1) & 1)) as u32;
            let neg_lo = (((lo >> 2) & 1) + ((lo >> 3) & 1)) as u32;
            let pos_hi = ((hi & 1) + ((hi >> 1) & 1)) as u32;
            let neg_hi = (((hi >> 2) & 1) + ((hi >> 3) & 1)) as u32;
            coeffs[2 * i] = mod_q_sub(pos_lo, neg_lo);
            coeffs[2 * i + 1] = mod_q_sub(pos_hi, neg_hi);
        }
        ct_zeroize_bytes(&mut buf);
        Self { coeffs }
    }

    /// Fixed-work 192-bit reduction. Per coefficient TV distance is below q/2^192.
    /// There is no secret-dependent retry loop or division in the reduction.
    pub fn sample_uniform_mod_q(domain: &[u8], seed: &[u8], tag_idx: u32) -> Self {
        let mut buf = [0u8; MODULE_N * 24];
        cshake256_framed_xof(domain, &[seed, &tag_idx.to_be_bytes()], &mut buf);
        let coeffs = core::array::from_fn(|i| reduce_wide_mod_q(&buf[i * 24..(i + 1) * 24]));
        ct_zeroize_bytes(&mut buf);
        Self { coeffs }
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(MODULE_N * 4);
        for &c in &self.coeffs {
            out.extend_from_slice(&c.to_le_bytes());
        }
        out
    }
}

/// Secret wrapper around `RingPoly` zeroized via `write_volatile` on `Drop` and `<REDACTED>` in `Debug`.
pub struct SecretRingPoly(RingPoly);

impl SecretRingPoly {
    pub const fn new(poly: RingPoly) -> Self {
        Self(poly)
    }

    pub const fn expose(&self) -> &RingPoly {
        &self.0
    }
}

impl fmt::Debug for SecretRingPoly {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("SecretRingPoly(<REDACTED>)")
    }
}

impl Drop for SecretRingPoly {
    fn drop(&mut self) {
        ct_zeroize_u32s(&mut self.0.coeffs);
    }
}

/// Byte-Horner reduction preserving the original big-endian 192-bit map.
fn reduce_wide_mod_q(bytes: &[u8]) -> u32 {
    let mut r = 0u32;
    for &byte in bytes {
        r = ct_reduce_mod_q_u64((r as u64) * 256 + u64::from(byte));
    }
    r
}

#[cfg(test)]
fn sample_scalar_uniform_mod_q(domain: &[u8], seed: &[u8], tag_idx: u32) -> u32 {
    let mut buf = [0u8; 24];
    cshake256_framed_xof(domain, &[seed, &tag_idx.to_be_bytes()], &mut buf);
    let value = reduce_wide_mod_q(&buf);
    ct_zeroize_bytes(&mut buf);
    value
}

/// Deterministically expand public matrix $\mathbf{A} \in \mathcal{R}_q^{K \times L}$ from `seed_a`
/// with fixed-work wide reduction (negligible nonzero bias).
pub fn expand_matrix_a(seed_a: &[u8; 32]) -> [[RingPoly; MODULE_L]; MODULE_K] {
    core::array::from_fn(|r| {
        core::array::from_fn(|c| {
            let tag = ((r as u32) << 8) | (c as u32);
            RingPoly::sample_uniform_mod_q(b"QSAG.HD.LMOD.MAT_A.V1", seed_a, tag)
        })
    })
}

/// Compute $\mathbf{A}\mathbf{s} \bmod q$ for $\mathbf{s} \in \mathcal{R}_q^L$.
pub fn mat_vec_mul(
    mat_a: &[[RingPoly; MODULE_L]; MODULE_K],
    s: &[RingPoly; MODULE_L],
) -> [RingPoly; MODULE_K] {
    let matrix = ExpandedHdMatrix::from_coefficients([0; 32], mat_a);
    matrix.multiply(s)
}

/// Compute $\mathbf{A}_{:, 0} \cdot \mathbf{r}_i \bmod q$ (column `1` in 1-based math notation).
pub fn col1_mul(
    mat_a: &[[RingPoly; MODULE_L]; MODULE_K],
    r_poly: &RingPoly,
) -> [RingPoly; MODULE_K] {
    core::array::from_fn(|row| mat_a[row][0].mul_negacyclic(r_poly))
}

///Threshold share kind supported by `PiHdLinearModule`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ShareScheme {
    /// Degree `t - 1` Shamir sharing at validated nonzero distinct evaluation point `eval_point`.
    Shamir { threshold: u16, eval_point: u32 },
    /// $n$-of-$n$ additive sharing (`party_id == 0` absorbs public linear shift $\mathbf{r}_i$).
    Additive { num_parties: u16 },
}

/// Extended descriptor for the experimental linear construction.
/// WARNING: a non-hardened chain code plus one recovered child secret exposes its
/// parent by subtracting the public tweak. Give watch-only access only to callers
/// trusted with that privilege. Use hardened provisioning to omit the chain code.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LinearModuleXPub {
    pub seed_a: [u8; 32],
    pub t_vec: [RingPoly; MODULE_K],
    /// None for hardened descriptors; never exports the private chain code.
    pub chain_code: Option<[u8; 32]>,
    matrix: Arc<ExpandedHdMatrix>,
    pub depth_used: u16,
    pub max_depth: u16,
}

/// Secret threshold share for `PiHdLinearModule` (`Redacted` `Debug`, `write_volatile` `Drop`).
pub struct LinearModulePartyShare {
    pub party_id: u16,
    pub scheme: ShareScheme,
    pub seed_a: [u8; 32],
    pub t_vec: [RingPoly; MODULE_K],
    chain_code: RedactedSecret<32>,
    chain_code_key: RedactedSecret<32>,
    hardened: bool,
    derivation_index: u32,
    s_shares: [SecretRingPoly; MODULE_SECRET_L],
    spdz_macs: [[SecretRingPoly; MODULE_SECRET_L]; MODULE_MAC_LANES],
    spdz_alpha_shares: [u32; MODULE_MAC_LANES],
    committee: Vec<(u16, u32)>,
    matrix: Arc<ExpandedHdMatrix>,
    family_id: [u8; 32],
    #[cfg(feature = "std")]
    budget: Option<Arc<std::sync::Mutex<crate::budget::DurableQueryBudget>>>,
    #[cfg(feature = "std")]
    poison_journal: Option<Arc<dyn crate::poison::HdPoisonJournal>>,
    poisoned: Arc<AtomicBool>,
    evaluation_queries: Arc<AtomicUsize>,
    pub depth_used: u16,
    pub max_depth: u16,
}

impl fmt::Debug for LinearModulePartyShare {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("LinearModulePartyShare")
            .field("party_id", &self.party_id)
            .field("scheme", &self.scheme)
            .field("chain_code", &"<REDACTED>")
            .field("s_shares", &"<REDACTED>")
            .field("spdz_macs", &"<REDACTED>")
            .field("depth_used", &self.depth_used)
            .field("max_depth", &self.max_depth)
            .finish()
    }
}

impl Drop for LinearModulePartyShare {
    fn drop(&mut self) {
        self.erase();
    }
}
impl LinearModulePartyShare {
    #[cfg(feature = "std")]
    pub fn attach_poison_journal(&mut self, journal: Arc<dyn crate::poison::HdPoisonJournal>) -> Result<(), HdError> {
        if journal.family_id() != self.family_id || journal.is_poisoned().unwrap_or(true) {
            self.poison();
            return Err(HdError::MacCheckFailed);
        }
        self.poison_journal = Some(journal);
        Ok(())
    }
    pub fn is_poisoned(&self) -> bool {
        #[cfg(feature = "std")]
        if self.poison_journal.as_ref().is_some_and(|j| j.is_poisoned().unwrap_or(true)) {
            self.poisoned.store(true, Ordering::Release);
            return true;
        }
        self.poisoned.load(Ordering::Acquire)
    }
    fn poison(&mut self) {
        self.poisoned.store(true, Ordering::Release);
        #[cfg(feature = "std")]
        if let Some(journal) = &self.poison_journal { let _ = journal.poison(); }
        self.erase();
    }
    fn erase(&mut self) {
        ct_zeroize_u32s(&mut self.spdz_alpha_shares);
        for s in &mut self.s_shares {
            ct_zeroize_u32s(&mut s.0.coeffs);
        }
        for lane in &mut self.spdz_macs {
            for mac in lane {
                ct_zeroize_u32s(&mut mac.0.coeffs);
            }
        }
    }
}

fn hash_t_vec(seed_a: &[u8; 32], t_vec: &[RingPoly; MODULE_K]) -> [u8; 32] {
    use qsag_accel::keccak::{finalize_cshake256, init_cshake256};
    let mut sponge = init_cshake256(b"", b"QSAG.HD.LMOD.PK_HASH.V1");
    sponge.absorb(&5u64.to_le_bytes());
    sponge.absorb(&32u64.to_le_bytes());
    sponge.absorb(seed_a);
    for poly in t_vec {
        sponge.absorb(&((MODULE_N * 4) as u64).to_le_bytes());
        for c in poly.coeffs {
            sponge.absorb(&c.to_le_bytes());
        }
    }
    finalize_cshake256(&mut sponge, true);
    let mut out = [0; 32];
    sponge.squeeze(&mut out);
    out
}

/// Deterministic constant-time integer expansion of $(\mathbf{r}_i, \text{child\_chain\_code})$
/// from `(chain_code, pk_digest, child_index)`.
fn expand_linear_tweak(
    chain_code: &[u8; 32],
    pk_digest: &[u8; 32],
    child_index: u32,
) -> ([RingPoly; MODULE_SECRET_L], [u8; 32]) {
    let idx_be = child_index.to_be_bytes();
    let mut tweak_seed = cshake256_framed_32(
        b"QSAG.HD.LMOD.TWEAK_SEED.V1",
        &[chain_code, pk_digest, &idx_be],
    );
    let next_chain_code = cshake256_framed_32(
        b"QSAG.HD.LMOD.NEXT_CC.V1",
        &[chain_code, pk_digest, &idx_be],
    );
    let tweaks = core::array::from_fn(|j| {
        RingPoly::sample_cbd2_ct(b"QSAG.HD.LMOD.R_POLY.V2", &tweak_seed, j as u32)
    });
    ct_zeroize_bytes(&mut tweak_seed);
    (tweaks, next_chain_code)
}

impl LinearModuleXPub {
    /// Derive non-hardened watch-only child `XPub` in **`0` online MPC rounds**:
    /// $\mathbf{t}^{(i)} = \mathbf{t} + \mathbf{A}\Delta s_1 + \Delta s_2 \bmod q$, enforcing $d + 1 \le D_{\max}$.
    pub fn derive_child(&self, child_index: u32) -> Result<Self, HdError> {
        if child_index & (1 << 31) != 0 { return Err(HdError::HardenedDerivationRequired); }
        if self.seed_a != self.matrix.seed {
            return Err(HdError::InvalidThresholdParameters);
        }
        if self.depth_used >= self.max_depth {
            return Err(HdError::DerivationBudgetExceeded {
                current: self.depth_used,
                max: self.max_depth,
            });
        }
        let pk_digest = hash_t_vec(&self.seed_a, &self.t_vec);
        let (r_poly, next_cc) = expand_linear_tweak(
            &self.chain_code.ok_or(HdError::HardenedDerivationRequired)?,
            &pk_digest,
            child_index,
        );
        // Verify exact integer norm bound on tweak (`CBD_2` has |coeff| <= 2 => l2_sq <= 256 * 4 = 1024).
        if r_poly
            .iter()
            .any(|r| r.centered_l2_norm_sq() > (MODULE_N as u64) * 4)
        {
            return Err(HdError::NormBoundExceeded);
        }
        let delta_t = self.matrix.relation(&r_poly);
        let next_t = core::array::from_fn(|row| self.t_vec[row].add(&delta_t[row]));
        Ok(Self {
            seed_a: self.seed_a,
            t_vec: next_t,
            chain_code: Some(next_cc),
            matrix: Arc::clone(&self.matrix),
            depth_used: self.depth_used + 1,
            max_depth: self.max_depth,
        })
    }

    pub fn to_address(&self, hrp: &str) -> Result<QsagAddress, HdError> {
        let pk_digest = hash_t_vec(&self.seed_a, &self.t_vec);
        Ok(QsagAddress::from_pubkey_cshake256(
            hrp,
            WitnessSuiteTag::PiHdLinearModule,
            KeyIdentityKind::SingleOrThreshold,
            &pk_digest,
        )?)
    }
}

impl LinearModulePartyShare {
    /// Stable public family binding for the durable query journal.
    pub fn family_id(&self) -> [u8; 32] {
        self.family_id
    }

    #[cfg(feature = "std")]
    pub fn attach_budget(
        &mut self,
        budget: Arc<std::sync::Mutex<crate::budget::DurableQueryBudget>>,
    ) -> Result<(), HdError> {
        if budget
            .lock()
            .map_err(|_| HdError::BudgetStorageFailed)?
            .family_id()
            != self.family_id
        {
            return Err(HdError::BudgetStorageFailed);
        }
        self.budget = Some(budget);
        Ok(())
    }

    fn burn_query(&self) -> Result<(), HdError> {
        #[cfg(feature = "std")]
        if let Some(budget) = &self.budget {
            return budget
                .lock()
                .map_err(|_| HdError::BudgetStorageFailed)?
                .reserve();
        }
        // Ephemeral accounting exists only in unit tests. No no_std fallback.
        #[cfg(test)]
        {
            let mut used = self.evaluation_queries.load(Ordering::Acquire);
            loop {
                if used >= 128 {
                    return Err(HdError::EvaluationBudgetExceeded);
                }
                match self.evaluation_queries.compare_exchange(
                    used,
                    used + 1,
                    Ordering::AcqRel,
                    Ordering::Acquire,
                ) {
                    Ok(_) => return Ok(()),
                    Err(actual) => used = actual,
                }
            }
        }
        #[cfg(not(test))]
        Err(HdError::DurableBudgetRequired)
    }

    pub const fn s_share_coord(&self, coord: usize) -> &RingPoly {
        self.s_shares[coord].expose()
    }

    pub const fn spdz_mac_s1(&self) -> &RingPoly {
        self.spdz_macs[0][0].expose()
    }

    pub const fn spdz_alpha_share(&self) -> u32 {
        self.spdz_alpha_shares[0]
    }
}

/// Validate that all `0..n` Shamir evaluation points are nonzero mod `MODULE_Q` and pairwise distinct!
/// Directly prevents the `eval_points[m] == 0` cleartext secret disclosure bug.
